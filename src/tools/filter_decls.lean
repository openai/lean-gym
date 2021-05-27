import util.tactic
import all
import tactic

section main

section

namespace io
namespace fs

def put_str_ln_flush (h : handle) (s : string) : io unit :=
put_str h s *> put_str h "\n" *> flush h

end fs
end io

setup_tactic_parser

meta def parse_decl_nm_and_open_ns : string → tactic (name × list name) := λ inp,
flip lean.parser.run_with_input inp $ prod.mk <$> iterate_until ident (λ nm, pure ∘ bnot $ nm = name.anonymous) 100 <*> many ident

-- #eval (["foo bar baz\n", "baz baz baz\n", "a b c d e\n"].mmap $ io.run_tactic' ∘ parse_decl_nm_and_open_ns) >>= λ x, io.put_str_ln' format!"{x}"

end

def for_ {m α β} [monad m] (xs : list α) (body : α → m β) := list.mmap' body xs


meta def main_aux (names_file : string) (dest : string) : io unit := do {
  nm_strs ← (io.mk_file_handle names_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  let nm_strs := nm_strs.filter (λ x : string, x.length > 0),
  nms : list (name × list name) ← io.run_tactic' $ nm_strs.mmap parse_decl_nm_and_open_ns,
  dest_handle ← io.mk_file_handle dest io.mode.write,

  io.run_tactic' $ do {
    env ← tactic.get_env,
    for_ nms $ λ ⟨nm, open_ns⟩, tactic.try $ do {
      decl ← env.get nm,
      if decl.is_theorem then do {
        tactic.trace format! "[filter_defs] KEEPING {nm.to_string}",
        tactic.unsafe_run_io $
          io.fs.put_str_ln_flush
            dest_handle
              (nm.to_string ++ " " ++ (" ".intercalate $ name.to_string <$> open_ns))
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
