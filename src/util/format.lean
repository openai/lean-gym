import tactic

section derive_has_to_format

meta def expr.join (tp : expr) : list expr → tactic expr := λ xs,
xs.foldr (λ e₁ acc, do {acc ← acc, tactic.to_expr ``(@list.cons %%tp %%e₁ %%acc)}) (tactic.to_expr ``(list.nil))

meta def format.join_using : format → list format → format := λ x xs,
format.join $ list.intercalate [x] (pure <$> xs)

meta def format.apply_constructor : format → list format → format := λ f fs,
match fs with
| [] := f
| fs := format.join_using " " [f, format.join ["(", format.join_using " " fs, ")"]]
end

open tactic
namespace tactic
namespace interactive

meta def mk_to_format (type : name) : tactic unit := do {
  ls ← local_context,
  (x::_) ← tactic.intro_lst [`arg],
  et ← infer_type x,
  xs ← tactic.induction x,
  xs.mmap' $ λ ⟨c, args, _⟩, do
    (args', rec_call) ← args.mpartition $ λ e, do {
      e' ← tactic.to_expr ``(format),
      bnot <$> e'.occurs <$> tactic.infer_type e
    },
    args'' ← args'.mmap (λ a, flip prod.mk a <$> (et.occurs <$> tactic.infer_type a)),
    let fn : list (bool × expr) → state_t (list expr) tactic (list expr) := λ args'', do {
      let pop : state_t (list expr) tactic (option expr) := do {
        xs ← get,
        match xs with
        | (a::as) := modify (λ _, as) *> pure (some a)
        | [] := pure none
        end
      },
      args''.mmap (λ ⟨b, a⟩, if b then do (some x) ← pop, pure x else state_t.lift $ do
      a_tp ← infer_type a,
      _inst ← mk_app ``has_to_format [a_tp] >>= mk_instance,
      tactic.to_expr ``(@has_to_format.to_format _ (%%_inst) %%a))
    },
    args''' ← prod.fst <$> (fn args'').run rec_call,
    c ← tactic.resolve_constant c,
    nm_tp ← to_expr ``(name),
    nm_fmt ← mk_app ``has_to_format [nm_tp] >>= mk_instance,
    fs ← expr.join `(format) args''',
    result ← to_expr ``(format.apply_constructor (@has_to_format.to_format %%nm_tp %%nm_fmt %%c) %%fs),
    tactic.exact result
}

meta def derive_has_to_format (pre : option name) : tactic unit := do {
  vs ← local_context,
  `(has_to_format %%f) ← target,
  env ← get_env,
  let n := f.get_app_fn.const_name,
  d ← get_decl n,
  refine ``( { to_format := _ } ),
  tgt ← target,
  extract_def (with_prefix pre n <.> "to_format") ff $ mk_to_format n
}

meta def has_to_format_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``has_to_format (derive_has_to_format nspace) [] nspace

@[derive_handler]
meta def has_to_format_derive_handler : derive_handler :=
guard_class ``has_to_format has_to_format_derive_handler'

end interactive
end tactic

end derive_has_to_format