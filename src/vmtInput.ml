(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

module Ids = Lib.ReservedIds

module SM = HString.HStringMap
module SS = HString.HStringSet

module HS = HStringSExpr
module D = GenericSMTLIBDriver
module I = LustreIdent


let conv = D.smtlib_string_sexpr_conv
let conv_type_of_sexpr = conv.D.type_of_sexpr
let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv


let s_set_info = HString.mk_hstring "set-info"
let s_set_option = HString.mk_hstring "set-option"
let s_set_logic = HString.mk_hstring "set-logic"
let s_declare_sort = HString.mk_hstring "declare-sort"
let s_define_sort = HString.mk_hstring "define-sort"
let s_declare_const = HString.mk_hstring "declare-const"
let s_declare_fun = HString.mk_hstring "declare-fun"
let s_define_fun = HString.mk_hstring "define-fun"
let s_next = HString.mk_hstring ":next"
let s_init = HString.mk_hstring ":init"
let s_trans = HString.mk_hstring ":trans"
let s_invar = HString.mk_hstring ":invar"
let s_invar_property = HString.mk_hstring ":invar-property"
let s_live_property = HString.mk_hstring ":live-property"
let s_ltl_property = HString.mk_hstring ":ltl-property"
let s_assert = HString.mk_hstring "assert"
let s_true = HString.mk_hstring "true"
let s_annot_op = HString.mk_hstring "!"


type system_def = {
  sorts: HString.t SM.t;
  vars: (HString.t * Type.t) list; (* All variables *)
  next_vars: SS.t; (* Set of next state variables *)
  curr_to_next: HString.t SM.t; (* Map from current var to next var *)
  init: HS.t option;
  trans: HS.t option;
  locals: (HString.t * Type.t * HS.t * Var.t) list;
  invar_props: (int * HS.t) list;
  live_props: (int * HS.t) list;
  ltl_props: (int * HS.t) list;
}

let empty_system_def = {
  sorts = SM.empty;
  vars = [];
  next_vars = SS.empty;
  curr_to_next = SM.empty;
  init = None;
  trans = None;
  locals = [];
  invar_props = [];
  live_props = [];
  ltl_props = [];
}

let rec mk_subsys_structure sys =
  { SubSystem.scope = TransSys.scope_of_trans_sys sys;
    source = sys;
    has_contract = false;
    has_impl = true;
    has_modes = false;
    subsystems =
      TransSys.get_subsystems sys
      |> List.map mk_subsys_structure;
  }


let get_prop_id s_idx =
  let str = HString.string_of_hstring s_idx in
  match int_of_string_opt str with
  | None -> failwith (Format.sprintf
    "Expecting a non-negative integer but found: %s" str)
  | Some i when i<0 -> failwith (Format.sprintf
    "Expecting a non-negative integer but found: %d" i)
  | Some i -> i

let unwrap_atom = function
| HS.Atom a -> a
| _ -> assert false


let process_definition_with_annotations sys_def term annotations =
  let rec extract_attributes acc = function
    | (HS.Atom name :: HS.Atom value :: other)
      when HString.get value 0 <> ':' ->
      extract_attributes ((name, value) :: acc) other
    | (_ :: _ :: other) -> extract_attributes acc other
    | (_ :: other) -> extract_attributes acc other
    | [] -> acc
  in
  List.fold_left
    (fun (sys_def, add_def) (name, value) ->
      if name == s_next then (
        let curr_var = unwrap_atom term in
        let next_var = value in
        (* TODO: check the variables have been declared *)
        let next_vars = SS.add next_var sys_def.next_vars in
        let curr_to_next = SM.add curr_var next_var sys_def.curr_to_next in
        {sys_def with next_vars; curr_to_next}, add_def
      )
      else if name == s_init then (
        (* TODO: Check there is only one initial state predicate *)
        {sys_def with init=Some term}, false
      )
      else if name == s_trans then (
        (* TODO: Check there is only one transition relation *)
        {sys_def with trans=Some term}, false
      )
      else if name == s_invar_property then (
        let id = get_prop_id value in
        {sys_def with invar_props=(id, term)::sys_def.invar_props},
        add_def
      )
      else if name == s_live_property then (
        let id = get_prop_id value in
        {sys_def with live_props=(id, term)::sys_def.live_props},
        add_def
      )
      else if name == s_ltl_property then (
        let id = get_prop_id value in
        {sys_def with ltl_props=(id, term)::sys_def.ltl_props},
        add_def
      )
      else if name == s_invar then (
        failwith("TODO: Invar annotation is not supported yet")
      )
      else
        sys_def, add_def
    )
    (sys_def, true)
    (extract_attributes [] annotations)

let mk_free_var symb ty =
  (* Add prefix to make sure there is no name collision with internal names *)
  let id = "_" ^ HString.string_of_hstring symb in
  Var.mk_free_var (HString.mk_hstring id) ty

let process_define_fun sys_def symb ty = function
| HS.List (HS.Atom op :: term :: annotations) when op == s_annot_op -> (
  let fv = mk_free_var symb ty in
  let sys_def, add_local_def =
    process_definition_with_annotations sys_def term annotations
  in
  if add_local_def then
    let locals = (symb, ty, term, fv) :: sys_def.locals in
    {sys_def with locals}
  else
    sys_def
)
| term -> (
  let locals = (symb, ty, term, mk_free_var symb ty) :: sys_def.locals in
  {sys_def with locals}
)

let process_define_sort sys_def sort_name sort_def =
  let rec loop sort_def =
    match SM.find_opt sort_def sys_def.sorts with
    | None ->
      let sorts = SM.add sort_name sort_def sys_def.sorts in
      { sys_def with sorts }
    | Some sd -> loop sd
  in
  loop sort_def

let get_type { sorts } ty =
  try
    conv_type_of_sexpr ty
  with e ->
    match ty with
    | HS.Atom ty -> (
      match SM.find_opt ty sorts with
      | None -> raise e
      | Some ty -> conv_type_of_sexpr (HS.Atom ty)
    )
    | _ -> raise e

let process_command sys_def = function
(* (declare-const symbol type) *)
| HS.List [HS.Atom c; HS.Atom symb; ty] when c == s_declare_const -> (
  let ty = get_type sys_def ty in
  { sys_def with vars = (symb, ty) :: sys_def.vars}
)

(* (declare-fun symbol args type) *)
| HS.List [HS.Atom c; HS.Atom symb; HS.List args; ty]
  when c == s_declare_fun -> (
  match args with
  | [] -> (
    let ty = get_type sys_def ty in
    { sys_def with vars = (symb, ty) :: sys_def.vars}
  )
  | _ -> failwith (Format.asprintf
    "Uninterpreted functions are not supported yet but found: %a"
    HString.pp_print_hstring symb)
)

(* (define-fun symbol args type term) *)
| HS.List [HS.Atom c; HS.Atom symb; HS.List args; ty; term]
  when c == s_define_fun -> (
  match args with
  | [] -> process_define_fun sys_def symb (get_type sys_def ty) term
  | _ -> failwith (Format.asprintf
    "Function definitions are not supported yet but found: %a"
    HString.pp_print_hstring symb)
)

(* (define-sort sort_name () sort_def) *)
| HS.List [HS.Atom c; HS.Atom sort_name; HS.List args; HS.Atom sort_def]
  when c == s_define_sort -> (
  match args with
  | [] -> process_define_sort sys_def sort_name sort_def
  | _ -> failwith (Format.asprintf
    "Non-constant sorts are not supported but found: %a"
    HString.pp_print_hstring sort_name)
)

| HS.List [HS.Atom c; HS.Atom t] when (c == s_assert && t == s_true) -> sys_def

(* (set-logic [...]), (set-info [...]) and (set-option [...]) are ignored *)
| HS.List (HS.Atom c :: _) 
  when (c == s_set_info || c == s_set_option || c == s_set_logic) -> sys_def

| HS.List (HS.Atom c :: _) when c == s_declare_sort ->
  failwith ("declare-sort is not supported")

| c -> failwith (Format.asprintf
  "Invalid VMT-LIB command: %a" HS.pp_print_sexpr c)

let id = ref 0

let mk_state_vars sys_name { vars; next_vars; curr_to_next  } =
  let mk_name =
    if Flags.Smt.trace () then (
      function v ->
      let n = Format.asprintf "v%d" !id in
      Debug.parse "%s -> %s" n (HString.string_of_hstring v);
      id := !id + 1; n
    )
    else (
      function v ->
      HString.string_of_hstring v
    )
  in
  vars |> List.filter_map (fun (v, t) ->
    if SS.mem v next_vars then
      None
    else
      let svar =
        let name = mk_name v in
        let scope = (sys_name :: "impl" :: I.user_scope) in
        let is_input = not (SM.mem v curr_to_next) in
        StateVar.mk_state_var
          ~is_input ~is_const:false ~for_inv_gen:true
          name scope t
      in
      Some (v, svar)
  )

let mk_conv_maps { curr_to_next; locals } symb_svars =
  let local_map =
    locals |> List.map (fun (symb, _, _, fv) -> (symb, fv))
  in
  let init_map =
    List.map
      (fun (symb, svar) ->
        (symb, Var.mk_state_var_instance svar TransSys.init_base)
      )
      symb_svars
    @ local_map
  in
  let trans_map =
    List.fold_left 
      (fun acc (symb, svar) ->
        if StateVar.is_input svar then
          (symb, Var.mk_state_var_instance svar TransSys.trans_base) :: acc
        else
          let prev_base = Numeral.pred TransSys.trans_base in
          let next_symb =
            match SM.find_opt symb curr_to_next with
            | None -> assert false
            | Some s -> s
          in
          (symb, Var.mk_state_var_instance svar prev_base) ::
          (next_symb, Var.mk_state_var_instance svar TransSys.trans_base) ::
          acc
      )
      []
      symb_svars
    @ local_map
  in
  init_map, trans_map

let add_let_bindings locals map term =
  List.fold_left
    (fun (term, vars) (_, _, def, fv) ->
      if Var.VarSet.mem fv vars then
        let def_t = conv_term_of_sexpr map def in
        Term.mk_let [(fv, def_t)] term,
        Var.VarSet.union vars (Term.vars_of_term def_t)
      else
        term, vars
    )
    (term, Term.vars_of_term term)
    locals
  |> fst


let mk_init_term { init; locals } prop_svars init_flag map =
  match init with
  | None -> failwith (
    "No function definition with the init annotation was found")
  | Some init ->
    let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.init_base
      |> Term.mk_var
    in
    let invar_prop_eqs =
      prop_svars |> List.map (fun (svar, (_, term)) ->
        let prop_def = conv_term_of_sexpr map term in
        let var = Var.mk_state_var_instance svar TransSys.init_base in
        add_let_bindings locals map
          (Term.mk_eq [Term.mk_var var; prop_def])
      )
    in
    let init_t =
      Term.mk_and
        (init_flag_t :: conv_term_of_sexpr map init :: invar_prop_eqs)
    in
    add_let_bindings locals map init_t


let mk_trans_term { trans; locals } prop_svars init_flag map =
  match trans with
  | None -> failwith (
    "No function definition with the trans annotation was found")
  | Some trans ->
    let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.trans_base
      |> Term.mk_var
    in
    let invar_prop_eqs =
      prop_svars |> List.map (fun (svar, (_, term)) ->
        let prop_def = conv_term_of_sexpr map term in
        let var = Var.mk_state_var_instance svar Numeral.zero in
        add_let_bindings locals map
          (Term.mk_eq
            [Term.mk_var var; prop_def])
        |> Term.bump_state Numeral.one
      )
    in
    let trans_t =
      Term.mk_and
        (Term.mk_not init_flag_t ::
         conv_term_of_sexpr map trans ::
         invar_prop_eqs)
    in
    add_let_bindings locals map trans_t


let mk_invar_prop_svars sys_name { invar_props } =
  invar_props |> List.map (fun (idx, fv) ->
    let name = Format.sprintf "invar_prop.%d" idx in
    let scope = (sys_name :: I.reserved_scope) in
    StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:true
      name scope Type.t_bool,
    (idx, fv)
  )

let mk_live_prop_svars sys_name { live_props } =
  live_props |> List.map (fun (idx, fv) ->
    let name = Format.sprintf "live_prop.%d" idx in
    let scope = (sys_name :: I.reserved_scope) in
    StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:true
      name scope Type.t_bool,
    (idx, fv)
  )

(* Parse from input channel *)
let of_channel in_ch = 

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  let vmt_sys_def =
    List.fold_left process_command empty_system_def sexps
  in

  let system_name = "vmt" in

  let scope = [system_name] in

  let init_flag = StateVar.mk_init_flag scope in

  let symb_svars = mk_state_vars system_name vmt_sys_def in

  let init_map, trans_map =
    mk_conv_maps vmt_sys_def symb_svars
  in

  let invar_prop_svars = mk_invar_prop_svars system_name vmt_sys_def in

  let live_prop_svars = mk_live_prop_svars system_name vmt_sys_def in

  let prop_svars = invar_prop_svars @ live_prop_svars in

  let init_term =
    mk_init_term vmt_sys_def prop_svars init_flag init_map
  in

  let trans_term =
    mk_trans_term vmt_sys_def prop_svars init_flag trans_map
  in

  let props =
    invar_prop_svars |> List.map (fun (svar, (idx, _)) ->
      let var = Var.mk_state_var_instance svar TransSys.prop_base in
      {
        Property.prop_name = Format.sprintf "invar-property-idx-%d" idx;
        prop_source = Property.PropAnnot Lib.dummy_pos;
        prop_term = Term.mk_var var;
        prop_status = Property.PropUnknown;
        prop_kind = Property.Invariant
      }
    )
  in

  (*let fg_props =
    live_prop_svars |> List.map (fun (svar, (idx, _)) ->
      let var = Var.mk_state_var_instance svar TransSys.prop_base in
      {
        FgProperty.prop_name = Format.sprintf "live-property-idx-%d" idx;
        prop_source = FgProperty.FGCheck Lib.dummy_pos;
        prop_term = Term.mk_var var;
        prop_status = FgProperty.FGPropUnknown
      }
    )
  in*)

  let state_vars =
    init_flag :: List.map snd symb_svars
    @ List.map fst prop_svars
   in

  (* All state variables are treated as output *)
  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.init_uf_string system_name)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TransSys.trans_base |> Numeral.pred)
    )
    state_vars
  in

  let trans_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.trans_uf_string system_name)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in

  let top_sys, _ =
    TransSys.mk_trans_sys
      scope
      None (* No instance variable *)
      init_flag
      state_vars
      StateVar.StateVarSet.empty (* underapproximation *)
      (StateVar.StateVarHashtbl.create 7) (* state_var_bounds *)
      [] (* global_consts *)
      [] (* ufs *)
      init_uf_symbol
      init_formals
      init_term
      trans_uf_symbol
      trans_formals
      trans_term
      [] (* subsystems *)
      props
      (* fg_props *)
      (None, []) (* mode_requires *)
      (Invs.empty ()) (* invariants *)
  in

  (* Format.printf "VMT_SYS: %a@." (TransSys.pp_print_subsystems true) top_sys; *)

  mk_subsys_structure top_sys


(* Open and parse from file *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  of_channel in_ch
