import tactic
import control.traversable.derive
import data.string.basic
import all
import util.io
import util.tactic
import tactic.gptf.utils.util
import basic.table
import tactic.gptf.basic


section frontend

open tactic 
setup_tactic_parser

meta def read_eval_print_loop (ps : parser_state) : tactic unit :=
do
  trace "\nTactic state:",
  trace_state,
  let rest : tactic unit := do {
    trace "\nEnter a tactic command:",
    tactic_string <- tactic.unsafe_run_io $ io.get_line,
    (t, fmt) ← parse_eval_tac ps tactic_string,
    trace "",
    trace ("Running tactic:\n" ++ fmt.to_string),
    tactic.run t >>= tactic.trace,  -- runs the tactic on the goal.  It is crashing
    read_eval_print_loop
  },  --- loops forever
  done <|> rest

end frontend


section main

setup_tactic_parser

meta def parse_theorem_name (nm: string) : tactic name :=
do lean.parser.run_with_input ident nm 

meta def parse_open_namespace (open_ns: string) : tactic (list name) :=
do lean.parser.run_with_input (many ident) open_ns 


meta structure LeanREPLRequest : Type :=
(cmd : string)
(identifier : string)
(msg : string)


meta instance : has_from_json LeanREPLRequest := ⟨λ msg, match msg with
  | (json.array [json.of_string cmd, json.of_string identifier, json.of_string msg]) := pure ⟨cmd, identifier, msg⟩
  | exc := tactic.fail format!"[has_from_json_LeanREPLRequest] unexpected: {exc}"
  end
⟩

meta instance : has_to_format LeanREPLRequest :=
  ⟨λ ⟨cmd, identifier, msg⟩, format! "LeanREPLRequest: cmd={cmd} identifier=identifier msg={msg}"⟩


meta structure LeanREPLResponse : Type :=
(identifier : string)
(tactic_state : string)

meta structure LeanREPLState : Type :=
(state: dict string tactic_state)


meta def record_ts (state: LeanREPLState) (ts : tactic_state) (hash: ℕ) : (string × LeanREPLState) := do {
  let identifier := (format! "{hash}").to_string,
  let new_state := (dict.insert identifier ts state.1),
  ⟨identifier, ⟨new_state⟩⟩ 
}


meta def init
  (th_name: name)
  (open_ns: list name)
  : io (LeanREPLState × LeanREPLResponse) := do {
    r ← io.run_tactic' $ do {
      let σ₀ : LeanREPLState := ⟨dict.empty⟩,
      env ← tactic.get_env,
      decl ← env.get th_name,
      let g := decl.type,
      tactic.set_goal_to g,
      lean_file ← env.decl_olean th_name,
      tactic.set_env_core $ environment.for_decl_of_imported_module lean_file th_name,
      add_open_namespaces open_ns,
      ts ← tactic.read,
      h ← tactic_hash,
      let r₀ := (record_ts σ₀ ts h),
      let ts₀ := ts.to_format.to_string,
      let r : (string × LeanREPLState × string) := ⟨r₀.1, r₀.2, ts₀⟩,
      pure r
    },
    let s : (LeanREPLState × LeanREPLResponse) := ⟨r.2.1, ⟨r.1, r.2.2⟩⟩,
    pure s
  }

meta instance : has_to_format LeanREPLResponse :=
  ⟨λ ⟨id, ts⟩, format!"BEGIN\n{id}\n{ts}\nEND"⟩


-- meta def handle_info (req : LeanREPLRequest) : io LeanREPLResponse := sorry

meta def handle_run_tac
  (σ: LeanREPLState)
  (req : LeanREPLRequest)
  : io (LeanREPLState × LeanREPLResponse) := do {
    h ← io.run_tactic' $ do {
      let ts := σ.1.get req.identifier,
      match ts with
      | (some ts) := tactic.write ts
      | none := tactic.fail "[error] unknown_identifier: identifier={req.identifier}"
      end,
      let tac_string := req.msg,
      result_with_string ← get_tac_and_capture_result tac_string 5000 <|> do {
        let msg : format := format!"[try_get_tac_and_capture_result] parse_itactic failed on {tac_string}",
        tactic.trace msg,
        interaction_monad.mk_exception msg none <$> tactic.read
      },
      h ← tactic_hash,
      pure h
    },

  }


meta def handle_request (state: LeanREPLState): LeanREPLRequest → io (LeanREPLState × LeanREPLResponse) := λ req, do {
  match req.cmd with
  | "run_tac" := handle_run_tac state req
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
    ⟨σ₀, res₀⟩ ← init th_name open_ns,
    has_to_format.to_format <$> pure res₀ >>= io.put_str_ln',

    req ← io.get_line >>= parse_request,
    ⟨σ₁, res₁⟩ ← handle_request σ₀ req,
    has_to_format.to_format <$> pure res₁ >>= io.put_str_ln'
   }
   end
}

end main