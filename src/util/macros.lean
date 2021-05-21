section unfold_macros

meta def expr.unfold_string_macros {elab} : expr elab → expr elab
| e := match e.is_string_macro with
       | (some a) := expr.unfold_string_macros a
       | none := e
       end

meta def expr.unfold_macros (e : expr) : tactic expr := do {
  -- env ← tactic.get_env,
  -- pure $ env.unfold_all_macros e
  pure $ e.unfold_string_macros.erase_annotations
}

end unfold_macros
