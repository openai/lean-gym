import tactic.basic
import repl
import init.meta.json
import .debug_base

meta instance : has_to_format LeanREPLRequest :=
⟨λ req, format! "LeanREPLRequest ⟨{req.cmd}, {req.sid}, {req.tsid}, {req.tac}, {req.name}, {req.open_ns}⟩"⟩

meta def replay_proof (nm : name) : io unit := do {
  init_search_req : LeanREPLRequest ← io.run_tactic'' $ do{
    msg ← json.parse "[\"init_search\", [\"mathd_numbertheory_136\", \"\"]]",
    tactic.trace format! "MSG: {msg}",
    has_from_json.from_json msg
  },
  io.put_str_ln' $ format! "INIT SEARCH REQ: {init_search_req}",


  tac_req_1 : LeanREPLRequest ← io.run_tactic'' $ do {
    msg ← json.parse "[\"run_tac\", [\"0\",\"0\", \"intros\"]]",
    tactic.trace format! "MSG: {msg}",
    has_from_json.from_json msg
  },

  tac_req_2 : LeanREPLRequest ← io.run_tactic'' $ do {
    msg ← json.parse "[\"run_tac\", [\"0\",\"1\", \"nlinarith\"]]",
    tactic.trace format! "MSG: {msg}",
    has_from_json.from_json msg
  },
  let run_print_res
    (cmd : LeanREPLRequest → LeanREPL LeanREPLResponse)
    (req : LeanREPLRequest) : LeanREPL unit := do {
    res ← cmd req,
    monad_lift $ io.put_str_ln' format! "{res}"
  },

  let prog : LeanREPL unit := do {
      run_print_res handle_init_search init_search_req,
      run_print_res handle_run_tac tac_req_1,
      run_print_res handle_run_tac tac_req_2,
      pure ()
  },
  (flip state_t.run (⟨dict.empty, 0⟩ : LeanREPLState) $ prog) $> ()
}

-- #eval replay_proof `mathd_numbertheory_136
