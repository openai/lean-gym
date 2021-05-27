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
import tactic.gptf.utils.util
import basic.table
import tactic.gptf.basic


section main

setup_tactic_parser


meta structure LeanREPLRequest : Type :=
(cmd : string)
(id : string)
(payload : string)


meta structure LeanREPLResponse : Type :=
(id : option string)
(tactic_state : option string)
(error: option string)


meta structure LeanREPLState : Type :=
(state: dict string tactic_state)

namespace LeanREPLState

meta def insert (σ : LeanREPLState) (k) (v) : LeanREPLState := ⟨dict.insert k v σ.1⟩

meta def get (σ : LeanREPLState) (k) : option tactic_state := σ.1.get k

end LeanREPLState


meta instance : has_from_json LeanREPLRequest := ⟨λ msg, match msg with
  | (json.array [json.of_string cmd, json.of_string id, json.of_string payload]) := pure ⟨cmd, id, payload⟩
  | exc := tactic.fail format!"[fatal] request_parsing_error: data={exc}"
  end
⟩


@[reducible]
meta def LeanREPL := state_t LeanREPLState io


meta def record_ts {m} [monad m] (ts : tactic_state) (hash : ℕ) : (state_t LeanREPLState m) string := do {
  let id := (format! "{hash}").to_string,
  modify $ λ σ, σ.insert id ts,
  pure id
}


meta instance : has_to_format LeanREPLResponse :=
  ⟨λ ⟨id, ts, err⟩, do {
    match id with
    | (some id) := match ts with
      | (some ts) := format!"[success] {id}\n{ts}\n[end]"
      | (none) := format!"[error] unexpected_undefined_ts\n[end]"
      end
    | none := do {
      match err with
      | some err := format!"[error] {err}\n[end]"
      | none := format!"[error] unexpected_undefined_error\n[end]"
      end
    }
    end
  }⟩

meta def init
  (th_name : name)
  (open_ns : list name)
  : io (LeanREPLState × LeanREPLResponse) := do {
  (⟨h, ts⟩ : ℕ × tactic_state) ← io.run_tactic'' $ do {
      env ← tactic.get_env,
      decl ← env.get th_name,
      let g := decl.type,
      tactic.set_goal_to g,
      lean_file ← env.decl_olean th_name,
      tactic.set_env_core $ environment.for_decl_of_imported_module lean_file th_name,
      add_open_namespaces open_ns,
      ts ← tactic.read, -- WARNING: important that this is done first
      h ← tactic_hash,
      pure $ prod.mk h ts
  },
  ⟨h_str, σ₀⟩ ← state_t.run (record_ts ts h) ⟨dict.empty⟩,
  pure $ ⟨σ₀, ⟨h_str, some ts.to_format.to_string, none⟩⟩
}


meta def handle_run_tac
  (req : LeanREPLRequest)
  : LeanREPL LeanREPLResponse := do {
  σ ← get,
  match σ.get req.id with
  | none := do { -- no-op on state
    let err := (format! "unknown_id: id={req.id}").to_string,
    pure ⟨none, none, some err⟩
  }
  | (some ts) := do {
    result_with_string ← state_t.lift $ io.run_tactic'' $ do {
      tactic.write ts,
      get_tac_and_capture_result req.payload 5000 <|> do {
          let msg : format := format!"parse_itactic failed on `{req.payload}`",
          tactic.trace msg,
          interaction_monad.mk_exception msg none <$> tactic.read
      }
    },
    match result_with_string with
    | interaction_monad.result.success s ts' := do {
        h ← (state_t.lift ∘ io.run_tactic'') $ tactic.write ts' *> tactic_hash,
        h_str ← record_ts ts' h,
        pure $ ⟨h_str, ts'.to_format.to_string, none⟩
      }
    | interaction_monad.result.exception fn pos old := state_t.lift $ do {
        let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
        let err := format! "run_tac_failed: pos={pos} msg={msg}",
        pure ⟨ none, none, some err.to_string ⟩
      }
    end
  }
  end
}


meta def handle_request (req : LeanREPLRequest) : LeanREPL LeanREPLResponse := -- spec for req cmds defined here
match req.cmd with
| "run_tac" := handle_run_tac req
-- | "info" := handle_info req
| exc := state_t.lift $ io.fail' format! "[fatal] unknown_command: cmd={exc}"
end


meta def parse_request (msg : string) : io LeanREPLRequest := do {
  match json.parse msg with
  | (some json_msg) := io.run_tactic'' $ has_from_json.from_json json_msg
  | none := io.fail' format! "[fatal] parse_failed: data={msg}"
  end
}


meta def parse_theorem_name (nm: string) : tactic name :=
do lean.parser.run_with_input ident nm


meta def parse_open_namespace (open_ns: string) : tactic (list name) :=
do lean.parser.run_with_input (many ident) open_ns


meta def loop : LeanREPL unit := do {
  req ← (state_t.lift $ io.get_line >>= parse_request),
  res ← handle_request req,
  state_t.lift $ io.put_str_ln' $ format! "{res}",
  loop
}


meta def main : io unit := do {
   args ← io.cmdline_args,
   th_name_str ← args.nth_except 0 "theorem name",
   open_ns_str ← args.nth_except 1 "open namespaces",

   th_name ← io.run_tactic'' $ do {
     parse_theorem_name th_name_str
   },
   open_ns ← io.run_tactic'' $ do {
     parse_open_namespace open_ns_str
   },

   is_theorem ← io.run_tactic'' $ do {
     tactic.is_theorem th_name
   } <|> pure ff,

   match is_theorem with
   | ff := io.fail' format! "[error] not_a_theorem: name={th_name}"
   | tt := do {
    ⟨σ₀, res₀⟩ ← init th_name open_ns,
    io.put_str_ln' $ format! "{res₀}",
    state_t.run loop σ₀ $> ()
   }
   end
}

end main
