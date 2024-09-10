(subdir rv32e.v.d
 (rule
  (action
   (write-file rv32e_extr.v
     "Require Coq.extraction.Extraction rv.rv32e.
Extraction \"rv32e.ml\" rv32e.prog.\n")))

 (coq.extraction
  (prelude rv32e_extr)
  (extracted_modules rv32e)
  (theories Ltac2 Koika rv)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target rv32.v)
  (alias runtest)
  (deps (package koika) rv32e.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir rv32i.v.d
 (rule
  (action
   (write-file rv32i_extr.v
     "Require Coq.extraction.Extraction rv.rv32i.
Extraction \"rv32i.ml\" rv32i.prog.\n")))

 (coq.extraction
  (prelude rv32i_extr)
  (extracted_modules rv32i)
  (theories Ltac2 Koika rv)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target rv32.v)
  (alias runtest)
  (deps (package koika) rv32i.ml)
  (action (run cuttlec %{deps} -T all -o .))))

