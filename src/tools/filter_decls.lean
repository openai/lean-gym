import util.tactic
import util.io
import all

section main

section

namespace io
namespace fs

def put_str_ln_flush (h : handle) (s : string) : io unit :=
put_str h s *> put_str h "\n" *> flush h

end fs
end io

setup_tactic_parser

-- Expected file format:
-- <decl>, <import> ... <import>, <open> ... <open>

meta def parse_decl_and_metadata (input : string) : tactic (name × list name × list name) := do
 flip lean.parser.run_with_input input $ do
  name ← ident,
  tk ",",
  imports ← many ident,
  tk ",",
  opens ← many ident,
  pure (name, imports, opens)

end

def for_ {m α β} [monad m] (xs : list α) (body : α → m β) := list.mmap' body xs

meta def main_aux (names_file : string) (dest : string) : io unit := do {
  nm_strs ← (io.mk_file_handle names_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  let nm_strs := nm_strs.filter (λ x : string, x.length > 0),
  nms : list (name × list name × list name) ← io.run_tactic'' $ nm_strs.mmap parse_decl_and_metadata,
  dest_handle ← io.mk_file_handle dest io.mode.write,

  io.run_tactic'' $ do {
    env ← tactic.get_env,
    for_ (nm_strs.zip nms) $ λ ⟨nm_str, ⟨nm, imports, open_ns⟩⟩, tactic.try $ do {
      decl ← env.get nm,
      if decl.is_theorem then do {
        tactic.trace format! "[filter_defs] KEEPING {nm.to_string}",
        tactic.unsafe_run_io $ io.fs.put_str_ln_flush dest_handle nm_str
      } else do {
        tactic.trace format! "[filter_defs] DISCARDING {nm.to_string}",
        pure ()
      }
    }
  }
}

meta def main : io unit := do {
  io.put_str_ln' "ENTERING",
  args ← io.cmdline_args,
  names_file ← args.nth_except 0 "names_file",
  dest ← args.nth_except 1 "dest",
  main_aux names_file dest
}

end main
