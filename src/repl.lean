import tactic
import control.traversable.derive
import data.string.basic
import all
import util.io
import util.tactic

open tactic

section 

setup_tactic_parser

meta def parse_theorem_name (nm: string) : tactic name :=
do lean.parser.run_with_input ident nm 

meta def parse_open_namespace (open_ns: string) : tactic (list name) :=
do lean.parser.run_with_input (many ident) open_ns 

/-- Creates an empty tactic state. -/
meta def mk_tactic_state : tactic tactic_state :=
tactic.unsafe_run_io $ io.run_tactic' $ tactic.exact `(trivial) *> tactic.read

meta def get_ts_with_main_goal (tgt : expr) : tactic tactic_state := do {
  ts₀ ← tactic.read,
  mk_tactic_state >>= tactic.write,
  tactic.set_goal_to tgt,
  ts ← tactic.read,
  tactic.write ts₀,
  pure ts
}

/-- creates tactic_state_data as if we were proving the declaration
 (currently only theorems are supported) with name `decl_nm`. -/
meta def get_ts_at_decl (decl_nm : name) : tactic tactic_state := do {
  env ← tactic.get_env,
  decl ← env.get decl_nm,
  get_ts_with_main_goal decl.type
}

private meta def enable_full_names : tactic unit := do {                                               
  set_bool_option `pp.full_names true                                                                  
}                                                                                                      
                                                                                                       
private meta def with_full_names {α} (tac : tactic α) : tactic α :=                                    
tactic.save_options $ enable_full_names *> tac   

end 


section main

meta def main : io unit := 
do {
  args ← io.cmdline_args,
  th_name_str ← args.nth_except 0 "theorem name",
  open_ns_str ← args.nth_except 1 "open namespaces",

  io.put_str_ln' format! "READY th_name={th_name_str} open_ns={open_ns_str}",

  th_name ← io.run_tactic' $ do {
    parse_theorem_name th_name_str
  },
  open_ns ← io.run_tactic' $ do {
    parse_open_namespace open_ns_str
  },

  io.put_str_ln' format! "PARSE {th_name} {open_ns}",

  is_theorem ← io.run_tactic' $ do {
    env ← tactic.get_env,
    do {
      decl ← env.get th_name,
      return decl.is_theorem
    } <|> pure ff
  },
  
  if is_theorem then 
    io.put_str_ln' format! "FOUND theorem: theorem={th_name}"
  else
    io.fail' format! "ERROR not a theorem: theorem={th_name}",

  env₀ ← io.run_tactic' $ tactic.get_env,

  io.run_tactic' $ do {
    ts ← get_ts_at_decl th_name,
    tactic.trace format!"[repl] GOT TSD AT DECL {th_name}",
    env ← get_env_at_decl th_name,
    tactic.trace format!"[repl] GOT ENV AT DECL {th_name}",
    tactic.set_env_core env,
    tactic.trace format!"[repl] SET ENV AT DECL {th_name}",

    add_open_namespaces open_ns,
    tactic.trace format!"[repl] ADDED OPEN NAMESPACES {open_ns}",

    tactic.write ts,

    -- decl_goal_string ← format.to_string <$> (tactic.get_goals >>= tactic.pp),
    -- tactic.trace format!">> {decl_goal_string}",
    result ← with_full_names $ (tactic.read >>= λ ts, pure ts.to_format.to_string),
    tactic.trace format!">> {result}"
    
  },

  io.run_tactic' $ tactic.set_env_core env₀,
  
  io.put_str_ln' format! "DONE"
}

end main