import system.io
import util.format
import util.macros
import util.io

open tactic.unsafe

universes u v w

-- tools and help functions

-- def option.mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : option α → m (option β)
-- | none       := return none
-- | (some x) := do x' ← f x, return (some x')

def list.last_option {α : Type u}: list α → option α
| []        := none
| [a]       := some a
| (a::b::l) := list.last_option (b::l)

meta def expr.local_uniq_name_option : expr → option name
| (expr.local_const n m bi t) := some n
| e                      := none

meta def expr.mvar_uniq_name_option : expr → option name
| (expr.mvar n ppn t) := some n
| e                   := none

-- set the tactic state
meta def set_state (new_state: tactic_state): tactic unit :=
  -- this is in mathlib but easier to recreate
  λ _, interaction_monad.result.success () new_state

-- types for encoding tactic state information

meta structure mvar_decl :=
(unique_name : name)
(pp_name : name)
(expr_type : expr)
(local_cxt : list expr)
(type : option expr)
(assignment : option expr)

/- There already is a local_decl type, but 
this is some more informtion for understanding 
the type better.-/
meta structure local_decl2 :=
(unique_name : name)
(pp_name : name)
(expr_type : expr)
(bi : binder_info)
(type : option expr)
(prev : option name)
(frozen : bool)
(ld : option local_decl)

meta structure univ_mvar_decl :=
(unique_name : name)
(assignment : option level)

meta inductive context.decl
| mvar_decl (mv : mvar_decl) : context.decl
| univ_mvar_decl (mv : univ_mvar_decl) : context.decl
| local_decl (loc : local_decl2) : context.decl

meta structure context :=
-- in order of dependecies
(decls : list context.decl)
(names : name_set)

meta structure tactic_state_data :=
(decls : list context.decl)
(goals : list (name × tactic.tag))

-- meta instance : has_to_format tactic.tag := sorry
-- meta instance : has_to_format context.decl := sorry
-- -- meta instance : has_to_tactic_format context.decl := sorry
-- meta instance foo' : has_to_format $ list (name × tactic.tag) := by apply_instance
-- meta instance foo : has_to_format (list decl) := by apply_instance

-- meta instance : has_to_tactic_format tactic_state_data :=
-- ⟨λ ⟨decls, goals⟩, pure $ format!"tactic_state_data.mk \n\t decls := {decls} \n\t goals := {goals}"⟩

attribute [derive [has_to_format]] mvar_decl univ_mvar_decl binder_info
attribute [derive [has_to_format]] local_decl
attribute [derive [has_to_format]] local_decl2
attribute [derive [has_to_format]] context.decl
meta instance : has_to_format tactic.tag := (by apply_instance : has_to_format (list name))

attribute [derive [has_to_format]] tactic_state_data


-- convience functions and instances

meta instance mvar_decl_has_to_string : has_to_format mvar_decl := 
⟨ λ d, format! "{{mvar_decl .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\nexpr_type := {d.expr_type},\nlocal_cxt := {d.local_cxt},\ntype := {d.type},\nassignment := {d.assignment},\n}" ⟩ 

meta instance univ_mvar_decl_has_to_string : has_to_format univ_mvar_decl := 
⟨ λ d, format! "{{univ_mvar_decl .\nunique_name := {d.unique_name},\nassignment := {d.assignment},\n}" ⟩ 

meta instance local_decl_has_to_string : has_to_format local_decl := 
⟨ λ d, format! "{{local_decl .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\ntype := {d.type},\nvalue := {d.value},\nbi := {repr d.bi},\nidx := {d.idx},\n}" ⟩ 

meta instance local_decl2_has_to_string : has_to_format local_decl2 := 
⟨ λ d, format! "{{local_decl2 .\nunique_name := {d.unique_name},\npp_name := {d.pp_name},\nexpr_type := {d.expr_type},\nbi := {repr d.bi},\ntype := {d.type},\nprev := {d.prev}\n},\nfrozen := {d.frozen},\nld := {d.ld}" ⟩ 

meta def context.decl.unique_name : context.decl -> name
| (context.decl.mvar_decl d) := d.unique_name
| (context.decl.univ_mvar_decl d) := d.unique_name
| (context.decl.local_decl d) := d.unique_name

meta instance context_decl_has_to_string : has_to_format context.decl := 
⟨ λ d, match d with
| context.decl.mvar_decl d := format! "{d}"
| context.decl.univ_mvar_decl d := format! "{d}"
| context.decl.local_decl d := format! "{d}"
end ⟩

meta instance context_has_to_string : has_to_format context := 
⟨ λ cxt, format! "{cxt.decls}" ⟩


-- constructors

meta def context.empty : context := 
{ decls := [], names := mk_name_set }

meta def context.mk1 (d : context.decl) : context :=
{ decls := [d], names := name_set.of_list [d.unique_name]}

meta def context.append (cxt1 : context) (cxt2 : context) : context :=
{ decls := cxt1.decls ++ (cxt2.decls.filter (λ d, ¬ (cxt1.names.contains d.unique_name))),
  names := cxt1.names.fold cxt2.names $ λ n ns, ns.insert n
}

meta instance context.has_append : has_append context := ⟨ context.append ⟩

/- Get univ metavariables level expression tree.-/
meta def context.process_level : level -> tactic context
| level.zero := return context.empty
| (level.succ lvl) := context.process_level lvl
| (level.max lvl1 lvl2) := do
  cxt1 <- context.process_level lvl1,
  cxt2 <- context.process_level lvl2,
  return (cxt1 ++ cxt2)
| (level.imax lvl1 lvl2) := do
  cxt1 <- context.process_level lvl1,
  cxt2 <- context.process_level lvl2,
  return (cxt1 ++ cxt2)
| (level.param _) := return context.empty
| lvl@(level.mvar nm) := do
  ass <- optional (tactic.get_univ_assignment lvl),
  let univ_decl := context.decl.univ_mvar_decl {
    unique_name := nm,
    assignment := ass
  },
  return (context.mk1 univ_decl)

def find_prev {α : Type} [decidable_eq α] (a : α) : list α -> option α
| [] := none
| [b] := none
| (b :: c :: ls) := if c = a then some b else find_prev (c :: ls)

/- Get metavariables and local constants inside an expression tree, follow recursively. -/
meta def context.process_expr : expr -> local_context -> tactic context
| (expr.var _) _ := return context.empty
| (expr.sort lvl) _ := context.process_level lvl
| (expr.const _ lvls) _ := do
  cxts <- lvls.mmap context.process_level,
  let cxt := cxts.foldl context.append context.empty,
  return cxt
| mv@(expr.mvar unique_nm pp_nm tp) _ := do
  lcxt <- type_context.run $ type_context.get_context mv,
  let local_cxt := lcxt.to_list,
  cxts <- local_cxt.mmap (λ e, e.unfold_macros >>= flip context.process_expr lcxt),
  let cxt := cxts.foldl context.append context.empty,
  tp_cxt <- tp.unfold_macros >>= flip context.process_expr lcxt,
  mv_type <- optional (tactic.infer_type mv),
  tp_cxt2 <- match mv_type with
  | (some e) := e.unfold_macros >>= flip context.process_expr lcxt
  | none := return context.empty
  end,
  assignment <- optional (tactic.get_assignment mv),
  ass_cxt <- match assignment with
  | (some e) := e.unfold_macros >>= flip context.process_expr lcxt
  | none := return context.empty
  end,
  let mv_dec := context.decl.mvar_decl {
    unique_name := unique_nm,
    pp_name := pp_nm,
    expr_type := tp,
    local_cxt := local_cxt,
    type := mv_type,
    assignment := assignment
  },
  return $ cxt ++ tp_cxt ++ tp_cxt2 ++ ass_cxt ++ (context.mk1 mv_dec)
| lconst@(expr.local_const unique_nm pp_nm bi tp) lcxt := do
  tp_cxt <- tp.unfold_macros >>= flip context.process_expr lcxt,
  loc_type <- optional (tactic.infer_type lconst),
  tp_cxt2 <- match loc_type with
  | (some e) := e.unfold_macros >>= flip context.process_expr lcxt
  | none := return context.empty
  end,
  let ld := lcxt.get_local_decl unique_nm,
  tp_cxt3 <- match ld with
  | (some ld) := ld.type.unfold_macros >>= flip context.process_expr  lcxt
  | none := return context.empty
  end,
  value_cxt <- match ld with
  | (some ld) := match ld.value with
    | (some e) := e.unfold_macros >>= flip context.process_expr lcxt
    | none := return context.empty
    end
  | none := return context.empty
  end,
  let (prev : option expr) := find_prev lconst lcxt.to_list,
  let prev_id := match prev with
  | some (expr.local_const id _ _ _) := some id
  | _ := none
  end,
  frozen_instances_opt <- tactic.frozen_local_instances,
  let frozen := match frozen_instances_opt with
  | none := ff
  | some frozen_instances := frozen_instances.any (λ e, e.local_uniq_name_option = some unique_nm)
  end,
  let loc_dec := context.decl.local_decl {
    unique_name := unique_nm,
    pp_name := pp_nm,
    expr_type := tp,
    bi := bi,
    type := loc_type,
    prev := prev_id,
    frozen := frozen,
    ld := lcxt.get_local_decl unique_nm,
  },
  return $ tp_cxt ++ tp_cxt2 ++ tp_cxt3 ++ value_cxt ++ (context.mk1 loc_dec)
| (expr.app expr1 expr2) lcxt := do
  cxt1 <- expr1.unfold_macros >>= flip context.process_expr lcxt,
  cxt2 <- expr2.unfold_macros >>= flip context.process_expr lcxt,
  return (cxt1 ++ cxt2)
| (expr.lam _ _ expr1 expr2) lcxt := do
  cxt1 <- expr1.unfold_macros >>= flip context.process_expr lcxt,
  cxt2 <- expr2.unfold_macros >>= flip context.process_expr lcxt,
  return (cxt1 ++ cxt2)
| (expr.pi _ _ expr1 expr2) lcxt := do
  cxt1 <- expr1.unfold_macros >>= flip context.process_expr lcxt,
  cxt2 <- expr2.unfold_macros >>= flip context.process_expr lcxt,
  return (cxt1 ++ cxt2)
| (expr.elet _ expr1 expr2 expr3) lcxt := do
  cxt1 <- expr1.unfold_macros >>= flip context.process_expr lcxt,
  cxt2 <- expr2.unfold_macros >>= flip context.process_expr lcxt,
  cxt3 <- expr3.unfold_macros >>= flip context.process_expr lcxt,
  return (cxt1 ++ cxt2 ++ cxt3)
| (expr.macro md deps) _ := tactic.fail format!"[process_expr] can't handle macro {expr.macro_def_name md}"

meta def context.get : tactic context := do
  lcxt <- type_context.run $ type_context.get_local_context,
  mvs <- tactic.get_goals,
  cxts <- mvs.mmap (λ e, e.unfold_macros >>= flip context.process_expr lcxt),
  let cxt := cxts.foldl context.append context.empty,
  return cxt

meta def tactic_state_data.get : tactic tactic_state_data := do
  cxt <- context.get,
  gs <- tactic.get_goals,
  goals <- gs.mmap $ λ g, do {
    nm <- g.mvar_uniq_name_option,
    tag <- tactic.get_tag g,
    return (nm, tag)
  },
  return { 
    decls := cxt.decls,
    goals := goals
  }


-- rebuilding the context

meta def swap_univ_mvs (nm_map : name_map context.decl) : level → tactic level
| (level.mvar nm) := do {
  d <- nm_map.find nm,
  nm' <- match d with
  | (context.decl.univ_mvar_decl dd) := return dd.unique_name
  | _ := tactic.failed
  end,
  return $ level.mvar nm'
}
| (level.max lvl1 lvl2) := do {
  lvl1' <- swap_univ_mvs lvl1,
  lvl2' <- swap_univ_mvs lvl2,
  return $ level.max lvl1' lvl2'
}
| (level.imax lvl1 lvl2) := do {
  lvl1' <- swap_univ_mvs lvl1,
  lvl2' <- swap_univ_mvs lvl2,
  return $ level.imax lvl1' lvl2'
}
| (level.succ lvl) := do {
  lvl' <- swap_univ_mvs lvl,
  return $ level.succ lvl'
}
| lvl := return lvl  --level.zero and level.param

meta def swap_mvs (nm_map : name_map context.decl) : expr -> tactic expr
| (expr.mvar unique_nm pp_nm tp) := do {
  d <- nm_map.find unique_nm,
  (unique_nm', tp') <- match d with
  | (context.decl.mvar_decl dd) := return (dd.unique_name, dd.expr_type)
  | _ := tactic.failed
  end,
  return $ expr.mvar unique_nm pp_nm tp'
}
| (expr.local_const unique_nm pp_nm bi tp) := do {
  d <- nm_map.find unique_nm,
  (unique_nm', tp') <- match d with
  | (context.decl.local_decl dd) := return (dd.unique_name, dd.expr_type)
  | _ := tactic.failed
  end,
  return $ expr.local_const unique_nm' pp_nm bi tp'
}
| e@(expr.var _) := return e
| (expr.sort lvl) := do {
  lvl' <- swap_univ_mvs nm_map lvl,
  return $ expr.sort lvl'
}
| (expr.const nm lvls) := do {
  lvls' <- lvls.mmap (swap_univ_mvs nm_map),
  return $ expr.const nm lvls'
}
| (expr.app expr1 expr2) := do {
  expr1' <- swap_mvs expr1.unfold_string_macros.erase_annotations,
  expr2' <- swap_mvs expr2.unfold_string_macros.erase_annotations,
  return $ expr.app expr1' expr2'
}
| (expr.lam nm bi expr1 expr2) := do {
  expr1' <- swap_mvs expr1.unfold_string_macros.erase_annotations,
  expr2' <- swap_mvs expr2.unfold_string_macros.erase_annotations,
  return $ expr.lam nm bi expr1' expr2'
}
| (expr.pi nm bi expr1 expr2) := do {
  expr1' <- swap_mvs expr1.unfold_string_macros.erase_annotations,
  expr2' <- swap_mvs expr2.unfold_string_macros.erase_annotations,
  return $ expr.pi nm bi expr1' expr2'
}
| (expr.elet nm expr1 expr2 expr3) := do {
  expr1' <- swap_mvs expr1.unfold_string_macros.erase_annotations,
  expr2' <- swap_mvs expr2.unfold_string_macros.erase_annotations,
  expr3' <- swap_mvs expr3.unfold_string_macros.erase_annotations,
  return $ expr.elet nm expr1' expr2' expr3'
}
| (expr.macro _ _) := tactic.fail "[swap_mvs] can't handle macros yet"

/- A better constructor for locals which covers 
frozen status and assignments. -/
meta def local_context.mk_local2 (pretty_name : name) (type : expr) (bi : binder_info) (frozen : bool) (assignment : option expr) (lcxt : local_context) : tactic (expr × local_context) := do
-- capture state
s <- tactic.read,
-- there are a few ways to add to local context, 
-- the most direct being local_context.mk_local
-- however that doesn't handle assignments or frozen locals,
-- so we are setting the local context as the context of a goal
-- and using intro to push a new hypothesis onto the stack
target <- match (assignment, bi) with
| (none, bi) := 
pure $ expr.pi pretty_name bi type `(true)
| (some ass, binder_info.default) :=
pure $ expr.elet pretty_name type ass `(true)
| _ := tactic.fail "Unreachable state reached" 
end,
goal_mv <- type_context.run $ type_context.mk_mvar "tmp_goal" target lcxt,
tactic.set_goals [goal_mv],
new_local <- tactic.intro_core pretty_name,
if frozen then
  tactic.freeze_local_instances
else
  pure (),
new_lcxt <- type_context.run $ type_context.get_local_context,
-- reset the state back to the beginning
_root_.set_state s,

return (new_local, new_lcxt)

meta def build_context_aux (nm_map : name_map context.decl) (loc_map : name_map local_context): context.decl -> tactic ((name_map context.decl) × (name_map local_context) × context.decl)
| (context.decl.univ_mvar_decl d) := do
  -- update dependencies
  new_assignment <- d.assignment.mmap (swap_univ_mvs nm_map),
  -- create mvar
  new_univ_mvar <- tactic.mk_meta_univ,
  new_uid <- match new_univ_mvar with
  | level.mvar nm := return nm
  | _ := tactic.failed
  end,
  -- assign mvar
  match new_assignment with 
  | some lvl := type_context.run $ type_context.level.assign new_univ_mvar lvl
  | none := return ()
  end,
  -- return new decl
  let new_decl := context.decl.univ_mvar_decl {
    unique_name := new_uid,
    assignment := new_assignment
  },
  let new_nmap := nm_map.insert d.unique_name new_decl,
  return (new_nmap, loc_map, new_decl)
| (context.decl.local_decl d) := do
  -- update dependencies
  let pp_name := d.pp_name,
  new_type <- swap_mvs nm_map (d.type.get_or_else d.expr_type).unfold_string_macros.erase_annotations,
  let (new_lcxt_option : option local_context) := do {
    unique_name <- d.prev,
    loc_map.find unique_name
  },
  let new_lcxt := new_lcxt_option.get_or_else local_context.empty,
  ld <- d.ld,
  new_assignment <- ld.value.mmap ((swap_mvs nm_map) ∘ expr.unfold_string_macros ∘ expr.erase_annotations),
  -- create local 
  (new_loc, new_lcxt) <- new_lcxt.mk_local2 pp_name new_type d.bi d.frozen new_assignment,
  (new_uid, new_tp) <- match new_loc with
  | expr.local_const nm _ bi tp := return (nm, tp)
  | _ := tactic.failed
  end,
  let (new_prev : option expr) := new_lcxt.fold (λ prev e, if e = new_loc then prev else some e) none,
  let new_prev_id := match new_prev with
  | some (expr.local_const id _ _ _) := some id
  | _ := none
  end,
  let new_decl := context.decl.local_decl {
    unique_name := new_uid,
    pp_name := pp_name,
    expr_type := new_tp,
    bi := d.bi,
    prev := new_prev_id,
    type := new_type,
    frozen := d.frozen,
    ld := new_lcxt.get_local_decl new_uid
  },
  let new_nmap := nm_map.insert d.unique_name new_decl,
  let new_loc_map := loc_map.insert d.unique_name new_lcxt,
  return (new_nmap, new_loc_map, new_decl)
  
| (context.decl.mvar_decl d) := do
  -- update dependencies
  let pp_name := d.pp_name,
  new_type <- swap_mvs nm_map (d.type.get_or_else d.expr_type).unfold_string_macros.erase_annotations,
  let (new_lcxt_option : option local_context) := do {
    last <- d.local_cxt.last_option,
    unique_name <- last.local_uniq_name_option,
    loc_map.find unique_name
  },
  let new_lcxt := new_lcxt_option.get_or_else local_context.empty,
  new_assignment <- d.assignment.mmap ((swap_mvs nm_map) ∘ expr.unfold_string_macros ∘ expr.erase_annotations),
  -- create mvar
  new_mvar <- type_context.run $ type_context.mk_mvar pp_name new_type new_lcxt,
  (new_uid, new_tp) <- match new_mvar with
  | expr.mvar nm _ tp := return (nm, tp)
  | _ := tactic.failed
  end,
  -- assign mvar
  match new_assignment with 
  | some e := type_context.run $ type_context.assign new_mvar e
  | none := return ()
  end,
  let new_decl := context.decl.mvar_decl {
    unique_name := new_uid,
    pp_name := pp_name,
    expr_type := new_tp,
    local_cxt := new_lcxt.to_list,
    type := new_type,
    assignment := new_assignment
  },
  let new_nmap := nm_map.insert d.unique_name new_decl,
  return (new_nmap, loc_map, new_decl)

meta def rebuild_context : (list context.decl) -> tactic ((name_map context.decl) × (name_map local_context))
| [] := return (mk_name_map, mk_name_map)
| (d :: ds) := do
  (nm_map, loc_map) <- rebuild_context ds,
  (nm_map, loc_map, _) <- build_context_aux nm_map loc_map d,
  return (nm_map, loc_map)

meta def mvar_id : expr -> tactic name
| (expr.mvar uid _ _) := return uid
| _ := tactic.fail "Expecting mvar"

meta def rebuild_tactic_state (ts : tactic_state_data) : tactic unit := do
  (nm_map, _) <- rebuild_context ts.decls.reverse,
  goals_and_tags <- ts.goals.mmap $ λ ⟨nm, tag⟩, do {
    d <- nm_map.find nm,
    nm' <- match d with
    | context.decl.mvar_decl dd := return dd.unique_name
    | _ := tactic.fail "Expecting mvar_decl"
    end,
    mvars <- type_context.run type_context.list_mvars,
    mv <- mvars.mfirst $ λ e, do {
      nm2 <- mvar_id e,
      if nm' = nm2 then return e else failure
    },
    return (mv, tag)
  },
  let goals := goals_and_tags.map prod.fst,
  tactic.set_goals goals,
  goals_and_tags.mmap $ λ ⟨g, tag⟩, do {
    tactic.enable_tags tt,
    tactic.set_tag g tag,
    tactic.enable_tags ff -- seems to be off by default
  },
  return ()

-- for testing

meta def refresh_context : tactic unit := do
  cxt <- context.get,
  (nm_map, _) <- rebuild_context cxt.decls.reverse,
  gs <- tactic.get_goals,
  new_goals <- gs.mmap $ λ g, do {
    nm <- mvar_id g,
    d <- nm_map.find nm,
    tactic.trace (nm, d),
    nm' <- match d with
    | context.decl.mvar_decl dd := return dd.unique_name
    | _ := tactic.fail "Expecting mvar_decl"
    end,
    mvars <- type_context.run type_context.list_mvars,
    mv <- mvars.mfirst $ λ e, do {
      nm2 <- mvar_id e,
      if nm' = nm2 then return e else failure
    },
    return mv
  },
  tactic.set_goals new_goals

meta def refresh_tactic_state : tactic unit := do
  ts_data <- tactic_state_data.get,
  -- go into a clean tactic environment and build the tactic state
  ts <- tactic.unsafe_run_io $ io.run_tactic' $ do {
    rebuild_tactic_state ts_data,
    tactic.read  -- return tactic state
  },
  -- set tactic state to new one
  _root_.set_state ts