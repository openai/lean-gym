/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Stanislas Polu, Jesse Michael Han

REPL implementation to interact with Lean through stdio at a specific
declaration.
-/
import tactic
import data.string.basic
import all
import util.io
import util.tactic
import basic.table
import tools.shrink_proof
import tools.try_finish

section main

setup_tactic_parser


meta structure LeanREPLRequest : Type :=
(cmd : string)
(sid: string)
(tsid: string)
(tac: string)
(name: string)
(open_ns: string)
(term: string)

meta structure LeanREPLResponse : Type :=
(sid : option string)
(tsid : option string)
(tactic_state : option string)
(error: option string)
(proof_steps : list (string × string))


meta structure parent : Type :=
(tsid : string)
(action : string)

meta structure LeanREPLState : Type :=
(state : dict string (dict string (tactic_state × option parent)))
(next_sid : ℕ)

namespace LeanREPLState

meta def insert_ts (σ : LeanREPLState) (sid) (tsid) (ts) (parent : option parent): LeanREPLState :=
  ⟨dict.insert sid (dict.insert tsid (ts, parent) (σ.1.get_default (dict.empty) sid)) σ.1, σ.2⟩

meta def get_ts_parents (σ : LeanREPLState) (sid) (tsid) : option (tactic_state × option parent) :=
  (σ.1.get_default (dict.empty) sid).get tsid

meta def get_ts (σ : LeanREPLState) (sid) (tsid) : option tactic_state :=
  option.map prod.fst $ σ.get_ts_parents sid tsid

meta def get_next_tsid (σ : LeanREPLState) (sid) : string := (format! "{(σ.1.get_default (dict.empty) sid).size}").to_string

meta def erase_search (σ : LeanREPLState) (sid) : LeanREPLState := ⟨σ.1.erase sid, σ.2⟩

meta def get_next_sid (σ : LeanREPLState) : string := (format! "{σ.2}").to_string

meta def incr_next_sid (σ : LeanREPLState) : LeanREPLState := ⟨σ.1, σ.2+1⟩

end LeanREPLState

meta instance : has_from_json LeanREPLRequest := ⟨λ msg, match msg with
  | (json.array [json.of_string cmd, json.array args]) := match cmd with
    | "run_tac" := match json.array args with
      | (json.array [json.of_string sid, json.of_string tsid, json.of_string tac]) := pure ⟨cmd, sid, tsid, tac, "", "", ""⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "conjecture_set" := match json.array args with
      | (json.array [json.of_string sid, json.of_string tsid, json.of_string term]) := pure ⟨cmd, sid, tsid, "", "", "", term⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "conjecture_assume" := match json.array args with
      | (json.array [json.of_string sid, json.of_string tsid, json.of_string term]) := pure ⟨cmd, sid, tsid, "", "", "", term⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "init_search" := match json.array args with
      | (json.array [json.of_string name, json.of_string open_ns]) := pure ⟨cmd, "", "", "", name, open_ns, ""⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "clear_search" := match json.array args with
      | (json.array [json.of_string sid]) := pure ⟨cmd, sid, "" , "", "", "", ""⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "shrink_proof" := match json.array args with
      | (json.array [json.of_string sid, json.of_string tsid]) := do
        pure ⟨cmd, sid, tsid , "", "", "", ""⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | "try_finish" := match json.array args with
      | (json.array [json.of_string sid, json.of_string tsid]) := do
        pure ⟨cmd, sid, tsid , "", "", "", ""⟩
      | exc := tactic.fail format!"request_parsing_error: cmd={cmd} data={exc}"
      end
    | exc := tactic.fail format!"request_parsing_error: data={exc}"
    end
  | exc := tactic.fail format!"request_parsing_error: data={exc}"
  end
⟩


@[reducible]
meta def LeanREPL := state_t LeanREPLState io

meta def LeanREPL.forever (x : LeanREPL unit) : LeanREPL unit := do
  σ₀ ← get,
  state_t.lift $ io.iterate σ₀ $ λ σ, do {
    (_, σ') ← x.run σ,
    return (some σ')
  },
  state_t.lift $ io.fail' $ format! "[LeanREPL.forever] unreachable code"

meta def record_ts {m} [monad m] (sid: string) (ts : tactic_state) (parent : option parent) : (state_t LeanREPLState m) string := do {
  σ ← get,
  let tsid := σ.get_next_tsid sid,
  modify $ λ σ, σ.insert_ts sid tsid ts parent,
  pure tsid
}

meta def LeanREPLResponse.to_json: LeanREPLResponse → json
| ⟨sid, tsid, ts, err, steps⟩ :=
    json.object [
      ⟨"search_id", match sid with
        | none := json.null
        | some sid := json.of_string sid
        end⟩,
      ⟨"tactic_state_id", match tsid with
        | none := json.null
        | some tsid := json.of_string tsid
        end⟩,
      ⟨"tactic_state", match ts with
        | none := json.null
        | some ts := json.of_string ts
        end⟩,
      ⟨"error", match err with
        | none := json.null
        | some err := json.of_string err
        end⟩,
      ⟨"proof_steps", json.array (steps.map $ λ ⟨ts_str, action⟩, json.array [json.of_string ts_str, json.of_string action])⟩
    ]

meta instance : has_to_format LeanREPLResponse :=
⟨has_to_format.to_format ∘ LeanREPLResponse.to_json⟩


meta def parse_theorem_name (nm: string) : tactic name :=
do lean.parser.run_with_input ident nm


meta def parse_open_namespace (open_ns: string) : tactic (list name) :=
do lean.parser.run_with_input (many ident) open_ns


meta def handle_init_search
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
   σ ← get,
   -- Parse declaration name.
   decl_name ← state_t.lift $ io.run_tactic'' $ do {
     parse_theorem_name req.name
   },
   -- Parse open namespaces.
   decl_open_ns ← state_t.lift $ io.run_tactic'' $ do {
     parse_open_namespace req.open_ns
   },
   -- Check that the declaration is a theorem.
   is_theorem ← state_t.lift $ io.run_tactic'' $ do {
     tactic.is_theorem decl_name
   } <|> pure ff,
   match is_theorem with
   -- The declaration is not a theorem, return an error.
   | ff := do {
     let err := format! "not_a_theorem: name={req.name} open_ns={req.open_ns}",
     pure ⟨none, none, none, some err.to_string, []⟩
   }
   -- The declaration is a theorem, set the env with open namespaces to it and
   -- generate a new tactic state.
   | tt := do {
     ts ← state_t.lift $ io.run_tactic'' $ do {
       env ← tactic.get_env,
       decl ← env.get decl_name,
       let g := decl.type,
       tactic.set_goal_to g,
       lean_file ← env.decl_olean decl_name,
       tactic.set_env_core $ environment.for_decl_of_imported_module lean_file decl_name,
       add_open_namespaces decl_open_ns,
       tactic.read
     },
     let sid := σ.get_next_sid,
     modify $ λ σ, σ.incr_next_sid,
     tsid ← record_ts sid ts none,
     ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts,
     pure $ ⟨sid, tsid, ts_str, none, []⟩
   }
   end
}


meta def handle_clear_search
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
   -- Simply remove the table associated with the provided search id from the state.
   modify $ λ σ, σ.erase_search req.sid,
   pure $ ⟨req.sid, none, none, none, []⟩
}


meta def finalize_proof
  (req : LeanREPLRequest)
  (ts': tactic_state) : LeanREPL LeanREPLResponse := do {
  σ ← get,
  -- Retrieve the tactic state at index 0 to extract the top-level goal metavariable.
  match σ.get_ts req.sid "0" with
  | none := do {
    let err := format! "unexpected_unknown_tsid_0: search_id={req.sid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  | (some ts₀) := do {
    result ← (state_t.lift ∘ io.run_tactic'') $ do {
      -- Set to tactic state index 0 to retrieve the meta-variable for the top goal.
      tactic.write ts₀,
      [g] ← tactic.get_goals,
      tgt ← tactic.infer_type g,
      tactic.write ts',
      pf ← tactic.get_assignment g >>= tactic.instantiate_mvars,
      tactic.capture' (validate_proof tgt pf)
    },
    match result with
    | (interaction_monad.result.success r s') := do {
      tsid ← record_ts req.sid ts' (some ⟨req.tsid, req.tac⟩),
      ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts',
      pure $ ⟨req.sid, tsid, ts_str, none, []⟩
    }
    | (interaction_monad.result.exception f p s') := do {
      let msg := (f.get_or_else (λ _, format.of_string "n/a")) (),
      let err := format! "proof_validation_failed: msg={msg}",
      pure ⟨none, none, none, some err.to_string, []⟩
    }
    end
  }
  end
}

meta def handle_conjecture
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match (σ.get_ts req.sid req.tsid) with
  | none := do {
    let err := format! "unknown_id: search_id={req.sid} tactic_state_id={req.tsid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  | (some ts) := do {
    let conj_str := req.term,
    -- Use `have` to introduce the new assumption
    result_with_string ← state_t.lift $ io.run_tactic'' $ do {
      tactic.write ts,
      conj_name ← tactic.get_unused_name "h",
      let tac_str := format! "have {conj_name} : {conj_str}",
      get_tac_and_capture_result tac_str.to_string 5000 <|> do {
          let msg : format := format!"parse_itactic failed on `{req.tac}`",
          interaction_monad.mk_exception msg none <$> tactic.read
      }
    },
    match result_with_string with
    -- `have` was successful.
    | interaction_monad.result.success _ ts' := do {
        -- Narrow the tactic state to the assumption only
        ts_narrowed ← (state_t.lift ∘ io.run_tactic'') $ do {
          tactic.write ts',
          g ← list.head <$> tactic.get_goals,
          tactic.set_goals [g],
          -- We need to revert all hypotheses, otherwise proof finalization will complain with
          -- unknown variables.
          tactic.revert_all,
          tactic.read
        },
        -- Create a new search id, this is required so that the final check are only run on the
        -- "narrowed" tactic state (tactic state of the conjecture only).
        let sid := σ.get_next_sid,
        modify $ λ σ, σ.incr_next_sid,

        tsid ← record_ts sid ts_narrowed none,
        ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts_narrowed,
        pure $ ⟨sid, tsid, ts_str, none, []⟩
    }
    | interaction_monad.result.exception fn pos ts' := do {
      state_t.lift $ do {
        let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
        let err := format! "conjecture_set_have_failed: pos={pos} msg={msg}",
        pure ⟨none, none, none, some err.to_string, []⟩
      }
    }
    end
  }
  end
}

meta def collect_proof_steps_aux (σ : LeanREPLState) (sid : string) : Π (tsid : string), io (list (tactic_state × string × tactic_state))
| tsid2 := do
  match σ.get_ts_parents sid tsid2 with
  | none := io.fail "collect_proof_steps: invalid tsid"
  | (some ⟨ts2, parent⟩) :=
    match parent with
    | none := if tsid2 = "0" then pure [] else io.fail "no parent"
    | (some ⟨tsid1, action⟩) :=
      match σ.get_ts sid tsid1 with
      | none := io.fail "parent doesn't exist"
      | (some ts1) := do {
        rest ← collect_proof_steps_aux tsid1,
        pure (⟨ts1, action, ts2⟩ :: rest)
      }
      end
    end
  end

meta def collect_proof_steps (σ : LeanREPLState) (sid tsid : string) : io (list (tactic_state × string × tactic_state)) := do
  rev_steps ← collect_proof_steps_aux σ sid tsid,
  pure $ list.reverse rev_steps

meta def handle_shrink_proof
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match (σ.get_ts req.sid req.tsid) with
  | none := do {
    let err := format! "unknown_id: search_id={req.sid} tactic_state_id={req.tsid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  | (some ts_final) := do {
    ts_str ← state_t.lift $ io.run_tactic'' $ postprocess_tactic_state ts_final,
    state_t.lift $ io.run_tac ts_final tactic.done,
    steps ← state_t.lift $ collect_proof_steps σ req.sid req.tsid,
    new_steps ← state_t.lift (shrink_proof steps),
    new_steps ← state_t.lift $ new_steps.mmap $ λ ⟨ts1, action, _⟩, do {
      ts1_str ← io.run_tactic'' $ postprocess_tactic_state ts1,
      pure (ts1_str, action)
    },
    pure ⟨req.sid, req.tsid, ts_str, none, new_steps⟩
  }
  end
  }

meta def handle_try_finish
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match (σ.get_ts req.sid req.tsid) with
  | none := do {
    let err := format! "unknown_id: search_id={req.sid} tactic_state_id={req.tsid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  | (some ts) := do {
    possible_action ← state_t.lift $ try_finish ts,
    match possible_action with
    | none := do {
      let err := format! "try_finish_failed: search_id={req.sid} tactic_state_id={req.tsid}",
      pure ⟨none, none, none, some err.to_string, []⟩
    }
    | some (action, ts') := do {
      -- TODO: refactor so that finalizing a proof is a separate top-level call
      goals ← state_t.lift $ io.run_tac ts' tactic.get_goals,
      if goals.empty then do {
        r ← finalize_proof { req with tac := action } ts',
        match r.error with
        | none := do {
          ts_str ← state_t.lift $ io.run_tactic'' $ postprocess_tactic_state ts',
          pure { r with proof_steps := [(action, ts_str)] }
        }
        | some err := pure r
        end
      } else do {
      tsid ← record_ts req.sid ts' (some ⟨req.tsid, action⟩),
      ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts',
      pure $ ⟨req.sid, tsid, ts_str, none, [(action, ts_str)]⟩
    }
    }
    end
  }
  end
}

meta def handle_assume
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match (σ.get_ts req.sid req.tsid) with
  | none := do {
    let err := format! "unknown_id: search_id={req.sid} tactic_state_id={req.tsid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  | (some ts) := do {
    let conj_str := req.term,
    -- Use `have` to introduce the new assumption
    result_with_string ← state_t.lift $ io.run_tactic'' $ do {
      tactic.write ts,
      conj_name ← tactic.get_unused_name "h",
      let tac_str := format! "have {conj_name} : {conj_str}",
      get_tac_and_capture_result tac_str.to_string 5000 <|> do {
          let msg : format := format!"parse_itactic failed on `{req.tac}`",
          interaction_monad.mk_exception msg none <$> tactic.read
      }
    },
    match result_with_string with
    -- `have` was successful.
    | interaction_monad.result.success _ ts' := do {
        -- Narrow the tactic state to the initial goal with assumption.
        ts_assumed ← (state_t.lift ∘ io.run_tactic'') $ do {
          tactic.write ts',
          (g1 :: gs) ← tactic.get_goals,
          tactic.set_goals gs,
          -- We need to revert all hypotheses, otherwise proof finalization will complain with
          -- unknown variables.
          tactic.revert_all,
          tactic.read
        },
        -- Create a new search id, this is required so that the final check are only run on the
        -- "assumed" tactic state (tactic state with additional assumption only).
        let sid := σ.get_next_sid,
        modify $ λ σ, σ.incr_next_sid,

        tsid ← record_ts sid ts_assumed (some ⟨req.tsid, req.tac⟩),
        ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts_assumed,
        pure $ ⟨sid, tsid, ts_str, none, []⟩
    }
    | interaction_monad.result.exception fn pos ts' := do {
      state_t.lift $ do {
        let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
        let err := format! "conjecture_assume_have_failed: pos={pos} msg={msg}",
        pure ⟨none, none, none, some err.to_string, []⟩
      }
    }
    end
  }
  end
}

meta def handle_parse_failed
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
    -- A little hack that use `req` to pass error message
    let err := format! "parse_failed: data={req.sid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }

meta def handle_run_tac
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match (σ.get_ts req.sid req.tsid) with
  -- Received an unknown search id, return an error.
  | none := do {
    let err := format! "unknown_id: search_id={req.sid} tactic_state_id={req.tsid}",
    pure ⟨none, none, none, some err.to_string, []⟩
  }
  -- The tactic state was retrieved from the state.
  | (some ts) := do {
    -- Set the tactic state and try to apply the tactic.
    result_with_string ← state_t.lift $ io.run_tactic'' $ do {
      tactic.write ts,
      get_tac_and_capture_result req.tac 5000 <|> do {
          let msg : format := format!"parse_itactic failed on `{req.tac}`",
          interaction_monad.mk_exception msg none <$> tactic.read
      }
    },
    match result_with_string with
    -- The tactic application was successful.
    | interaction_monad.result.success _ ts' := do {
        n ← (state_t.lift ∘ io.run_tactic'') $ do {
          tactic.write ts',
          tactic.num_goals
        },
        -- monad_lift $ io.run_tactic'' $ tactic.trace format! "REMAINING SUBGOALS: {n}",
        match n with
        -- There is no more subgoals, check that the produced proof is valid.
        | 0 := do {
          finalize_proof req ts'
        }
        -- There are remaining subgoals, return the updated tactic state.
        | n := do {
          tsid ← record_ts req.sid ts' (some ⟨req.tsid, req.tac⟩),
          ts_str ← (state_t.lift ∘ io.run_tactic'') $ postprocess_tactic_state ts',
          pure $ ⟨req.sid, tsid, ts_str, none, []⟩
        }
        end
      }
    -- The tactic application failed, potentially return an error with the failure message.
    | interaction_monad.result.exception fn pos ts' := do {
        -- Some tactics such as linarith fail but result in a tactic state with no goals. Check if
        -- that's the case and finalize the proof, otherwise error.
        n ← (state_t.lift ∘ io.run_tactic'') $ do {
          tactic.write ts',
          tactic.num_goals
        },
        -- monad_lift $ io.run_tactic'' $ tactic.trace format! "REMAINING SUBGOALS: {n}",
        match n with
        -- There is no more subgoals, check that the produced proof is valid.
        | 0 := do {
          finalize_proof req ts'
        }
        -- There are remaining subgoals, return the error.
        | _ := do {
          state_t.lift $ do {
            let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
            let err := format! "gen_tac_and_capture_res_failed: pos={pos} msg={msg}",
            pure ⟨none, none, none, some err.to_string, []⟩
          }
        }
        end
      }
    end
  }
  end
}


meta def handle_request (req : LeanREPLRequest) : LeanREPL LeanREPLResponse :=
match req.cmd with
| "run_tac" := handle_run_tac req
| "init_search" := handle_init_search req
| "clear_search" := handle_clear_search req
| "conjecture_set" := handle_conjecture req
| "conjecture_assume" := handle_assume req
| "shrink_proof" := handle_shrink_proof req
| "try_finish" := handle_try_finish req
| "parse_failed" := handle_parse_failed req
| exc := state_t.lift $ io.fail' format! "[fatal] unknown_command: cmd={exc}"
end


meta def parse_request (msg : string) : io LeanREPLRequest := do {
  match json.parse msg with
  | (some json_msg) := io.run_tactic'' $ has_from_json.from_json json_msg
  | none := pure ⟨"parse_failed", msg, "", "", "", "", ""⟩
  end
}


meta def loop : LeanREPL unit := do {
  req ← (state_t.lift $ io.get_line >>= parse_request),
  res ← handle_request req,
  state_t.lift $ io.put_str_ln' $ format! "{(json.unparse ∘ LeanREPLResponse.to_json) res}"
}

meta def main : io unit := do {
  state_t.run loop.forever ⟨dict.empty, 0⟩ $> ()
}

end main
