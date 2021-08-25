import data.real.basic
import tactic
import util.tactic
import tactic.basic
import repl
-- import init.meta.json
import .foo_base

meta instance : has_to_format LeanREPLRequest :=
⟨λ req, format! "LeanREPLRequest ⟨{req.cmd}, {req.sid}, {req.tsid}, {req.tac}, {req.name}, {req.open_ns}⟩"⟩

meta def LeanREPL.get_ts : int → int → LeanREPL tactic_state := λ n m, do {
  σ ← get,
  let sid := (format!"{n}").to_string,
  let tsid := (format!"{m}").to_string,
  match σ.get_ts sid tsid with
  | none := alternative.failure
  | (some ts) := pure ts
  end
}

meta def replay_proof (nm : name) : io unit := do {
  init_search_req : LeanREPLRequest ← io.run_tactic'' $ do {
    msg ← json.parse "[\"init_search\", [\"usa_mo_2003_p5\", \"\"]]",
    tactic.trace format! "MSG: {msg}",
    has_from_json.from_json msg
  },
  io.put_str_ln' $ format! "INIT SEARCH REQ: {init_search_req}",


  let run_print_res
    (cmd : LeanREPLRequest → LeanREPL LeanREPLResponse)
    (req : LeanREPLRequest) : LeanREPL unit := do {
    res ← cmd req,
    monad_lift $ io.put_str_ln' format! "{res}"
  },

  let prog : LeanREPL unit := do {
      run_print_res handle_init_search init_search_req,
      σ ← get,
      -- monad_lift $ io.put_str_ln' format! "REPLSTATE: {σ.state}",
      monad_lift $ io.put_str_ln' format! "HELLO",
      σ ← get,
      -- monad_lift $ io.put_str_ln' format! "REPLSTATE: {σ.state}",
      ts ← LeanREPL.get_ts 0 0,
      monad_lift $ io.run_tactic'' $ do {
        tactic.trace format! "TS 0 1: {ts}",
        tactic.write ts,
        [g] ← tactic.get_goals,
        tactic.infer_type g >>= tactic.pp >>= λ x, tactic.trace format! "INFERRED TYPE: {x}",
        `[async {ring}],
        pf ← tactic.get_assignment g,
        tactic.pp pf >>= λ x, tactic.trace format! "PROOF: {x}",
        tp ← tactic.infer_type pf,
        tactic.pp tp >>= tactic.trace,
        validate_proof tp pf
     },
      -- run_print_res handle_run_tac tac_req_2,
      -- -- run_print_res handle_run_tac tac_req_3,
      pure ()
  },
  monad_lift $ io.put_str_ln' format! "RUNNING PROG",
  (flip state_t.run (⟨dict.empty, 0⟩ : LeanREPLState) $ prog) $> ()
}

#eval replay_proof `usa_mo_2003_p5
