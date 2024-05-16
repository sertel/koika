(** Generate build rules for examples and tests *)

(* Does not currently copy support files from *.etc into output directory. This
    is used for further Make-based execution of simulation and synthesis. *)
let generate_rules theory fn =
let base = Filename.remove_extension fn in
let tgt = (match fn with
  "method_call.v" -> Printf.sprintf "%s.%s" base "o"
  | "rv32i.v" -> Printf.sprintf "rv32.v"
  | "rv32e.v" -> Printf.sprintf "rv32.v"
  | _ -> Printf.sprintf "%s.%s" base "v") in
match Filename.extension fn with
    ".v" -> Printf.printf
{|(subdir %s.d
 (rule
  (action
   (write-file %s_extr.v
     "Require Coq.extraction.Extraction %s.%s.
Extraction \"%s.ml\" %s.prog.\n")))

 (coq.extraction
  (prelude %s_extr)
  (extracted_modules %s)
  (theories Ltac2 Koika %s)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target %s)
  (alias runtest)
  (deps (package koika) %s.ml)
  (action (run cuttlec %%{deps} -T all -o .))))

|}
     fn base theory base base base base base theory tgt base

   | ".lv" -> (match Filename.extension base with
                ".1" -> Printf.printf
{|(subdir %s.d
 (rule
  (target %s.v)
  (alias runtest)
  (deps (package koika) ../%s)
  (action
   (progn
     (ignore-stderr (run cuttlec %%{deps} -T all -o . --expect-errors))
     (run touch %%{target})))))

|}
       fn base fn

                  | _ -> Printf.printf
{|(subdir %s.d
 (rule
  (target %s.v)
  (alias runtest)
  (deps (package koika) ../%s)
  (action
   (progn
     (run cuttlec %%{deps} -T all -o .)
     (run touch %%{target})))))

|}
     fn base fn)

   | _ -> raise(Failure (Printf.sprintf "cannot generate rules for %s" fn))

let () =
  let args = Sys.argv |> Array.to_list |> List.tl in
  let theory = List.hd args in
  let rules = generate_rules theory in
  List.tl args |> List.sort String.compare
  |> List.iter rules
