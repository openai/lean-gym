/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Stanislas Polu

REPL implementation to interact with Lean through stdio at a specific declaration.
-/
import tactic
import control.traversable.derive
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


meta instance : has_from_json LeanREPLRequest := ⟨λ msg, match msg with
  | (json.array [json.of_string cmd, json.of_string id, json.of_string payload]) := pure ⟨cmd, id, payload⟩
  | exc := tactic.fail format!"[fatal] request_parsing_error: data={exc}"
  end
⟩

-- meta instance : has_to_format LeanREPLRequest :=
--   ⟨λ ⟨cmd, id, payload⟩, format! "LeanREPLRequest: cmd={cmd} id={id} payload={payload}"⟩

meta def record_ts (state: LeanREPLState) (ts : tactic_state) (hash: ℕ) : (string × LeanREPLState) := do {
  let id := (format! "{hash}").to_string,
  let new_state := (dict.insert id ts state.1),
  ⟨id, ⟨new_state⟩⟩ 
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
  (th_name: name)
  (open_ns: list name)
  : io (LeanREPLState × LeanREPLResponse) := do {
    r ← io.run_tactic'' $ do {
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
      let rs := (record_ts σ₀ ts h),
      let r : (LeanREPLState × LeanREPLResponse) := ⟨ rs.2, ⟨ some rs.1, some ts.to_format.to_string, none ⟩ ⟩,
      pure r
    },
    pure r
  }


meta def handle_run_tac
  (σ: LeanREPLState)
  (req : LeanREPLRequest)
  : io (LeanREPLState × LeanREPLResponse) := do {
    r ← io.run_tactic'' $ do {
      match (σ.1.get req.id) with
      | none := do {
        let err := format! "unknown_id: id={req.id}",
        let r : (LeanREPLState × LeanREPLResponse) := ⟨ σ, ⟨ none, none, some err.to_string ⟩ ⟩, 
        pure r
      }
      | (some ts) := do {
        tactic.write ts,
        result_with_string ← get_tac_and_capture_result req.payload 5000 <|> do {
          let msg : format := format!"parse_itactic failed on `{req.payload}`",
          tactic.trace msg,
          interaction_monad.mk_exception msg none <$> tactic.read
        },
        match result_with_string with
        | interaction_monad.result.success s ts' := do {
          tactic.write ts',
          h ← tactic_hash,
          -- tactic.trace format! "RECEIVED STRING {s}",
          let rs := (record_ts σ ts' h), 
          let r : (LeanREPLState × LeanREPLResponse) := ⟨ rs.2, ⟨ some rs.1, some ts'.to_format.to_string, none ⟩ ⟩,
          pure r
        }
        | interaction_monad.result.exception fn pos old := do {
          let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
          let err := format! "run_tac_failed: pos={pos} msg={msg}",
          let r : (LeanREPLState × LeanREPLResponse) := ⟨ σ, ⟨ none, none, some err.to_string ⟩ ⟩,
          pure r
        }
        end
      }
      end
    },
    pure r
  }


meta def handle_request (state: LeanREPLState): LeanREPLRequest → io (LeanREPLState × LeanREPLResponse) := λ req, do {
  match req.cmd with
  | "run_tac" := handle_run_tac state req
  -- | "info" := handle_info req
  | exc := io.fail' format! "[fatal] unknown_command: cmd={exc}"
  end
}

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


meta def loop: LeanREPLState → io unit := λ σ, do {
    req ← io.get_line >>= parse_request,
    ⟨σ', res⟩ ← handle_request σ req,
    has_to_format.to_format <$> pure res >>= io.put_str_ln',
    loop σ'
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
    loop σ₀ 
   }
   end
}

end main