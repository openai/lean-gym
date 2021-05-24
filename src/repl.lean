import tactic
import control.traversable.derive
import data.string.basic
import all
import util.io
import util.tactic
import util.json



section frontend

-- meta def read_eval_print_loop (ps : parser_state) : tactic unit :=
-- do
--   trace "\nTactic state:",
--   trace_state,
--   let rest : tactic unit := do {
--     trace "\nEnter a tactic command:",
--     tactic_string <- tactic.unsafe_run_io $ io.get_line,
--     (t, fmt) ← parse_eval_tac ps tactic_string,
--     trace "",
--     trace ("Running tactic:\n" ++ fmt.to_string),
--     tactic.run t >>= tactic.trace,  -- runs the tactic on the goal.  It is crashing
--     read_eval_print_loop
--   },  --- loops forever
--   done <|> rest
-- 
end frontend


section main

setup_tactic_parser

meta def parse_theorem_name (nm: string) : tactic name :=
do lean.parser.run_with_input ident nm 

meta def parse_open_namespace (open_ns: string) : tactic (list name) :=
do lean.parser.run_with_input (many ident) open_ns 


meta structure LeanREPLRequest : Type :=
(cmd : string)
(msg : string)


meta instance : has_from_json LeanREPLRequest := ⟨λ msg, match msg with
  | (json.array [json.of_string cmd, json.of_string msg]) := pure ⟨cmd, msg⟩
  | exc := tactic.fail format!"[has_from_json_LeanREPLRequest] unexpected: {exc}"
  end
⟩

meta instance : has_to_format LeanREPLRequest :=
  ⟨λ ⟨cmd, msg⟩, format! "LeanREPLRequest: cmd={cmd} msg={msg}"⟩


meta structure LeanREPLResponse : Type :=
(identifier : string)
(tactic_state : string)


meta def init (th_name: name) (open_ns: list name): io LeanREPLResponse := do {
  ts_str ← io.run_tactic' $ do {
    env ← tactic.get_env,
    decl ← env.get th_name,
    let g := decl.type,
    tactic.set_goal_to g,
    lean_file ← env.decl_olean th_name,
    tactic.set_env_core $ environment.for_decl_of_imported_module lean_file th_name,
    add_open_namespaces open_ns,
    (tactic.read >>= λ ts, pure ts.to_format.to_string)
  },
  -- TODO(spolu): store ts in table
  pure ⟨"0", ts_str⟩
}

meta instance : has_to_format LeanREPLResponse :=
  ⟨λ ⟨id, ts⟩, format!"BEGIN\n{id}\n{ts}\nEND"⟩


-- meta def handle_info (req : LeanREPLRequest) : io LeanREPLResponse := sorry

meta def handle_run_tac (req : LeanREPLRequest) : io LeanREPLResponse := sorry


meta def handle_request : LeanREPLRequest → io LeanREPLResponse := λ req, do {
  match req.cmd with
  | "run_tac" := handle_run_tac req
  -- | "info" := handle_info req
  | exc := io.fail' format! "[error] unknown_command: cmd={exc}"
  end
}

meta def parse_request (msg : string) : io LeanREPLRequest := do {
  match json.parse msg with
  | (some json_msg) := io.run_tactic' $ has_from_json.from_json json_msg
  | none := io.fail' format! "[error] parse_failed: msg={msg}"
  end
}

meta def main : io unit := do {
   args ← io.cmdline_args,
   th_name_str ← args.nth_except 0 "theorem name",
   open_ns_str ← args.nth_except 1 "open namespaces",
 
   th_name ← io.run_tactic' $ do {
     parse_theorem_name th_name_str
   },
   open_ns ← io.run_tactic' $ do {
     parse_open_namespace open_ns_str
   },
 
   is_theorem ← io.run_tactic' $ do {
     env ← tactic.get_env,
     do {
       decl ← env.get th_name,
       return decl.is_theorem
     } <|> pure ff
   },

   match is_theorem with
   | ff := io.fail' format! "[error] not_a_theorem: name={th_name}"
   | tt := do {
    has_to_format.to_format <$> (init th_name open_ns) >>= io.put_str_ln',
    req ← io.get_line >>= parse_request,
    handle_request req,
    io.put_str_ln' format!"HANDLED REQUEST: {req}",
    main
   }
   end
}

end main