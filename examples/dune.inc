(subdir collatz.lv.d
 (rule
  (target collatz.v)
  (alias runtest)
  (deps (package koika) ../collatz.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir collatz.v.d
 (rule
  (action
   (write-file collatz_extr.v
     "Require Coq.extraction.Extraction examples.collatz.
Extraction \"collatz.ml\" collatz.prog.\n")))

 (coq.extraction
  (prelude collatz_extr)
  (extracted_modules collatz)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target collatz.v)
  (alias runtest)
  (deps (package koika) collatz.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir combinational_proof_tutorial.v.d
 (rule
  (action
   (write-file combinational_proof_tutorial_extr.v
     "Require Coq.extraction.Extraction examples.combinational_proof_tutorial.
Extraction \"combinational_proof_tutorial.ml\" combinational_proof_tutorial.prog.\n")))

 (coq.extraction
  (prelude combinational_proof_tutorial_extr)
  (extracted_modules combinational_proof_tutorial)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target combinational_proof_tutorial.v)
  (alias runtest)
  (deps (package koika) combinational_proof_tutorial.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir conflicts.v.d
 (rule
  (action
   (write-file conflicts_extr.v
     "Require Coq.extraction.Extraction examples.conflicts.
Extraction \"conflicts.ml\" conflicts.prog.\n")))

 (coq.extraction
  (prelude conflicts_extr)
  (extracted_modules conflicts)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target conflicts.v)
  (alias runtest)
  (deps (package koika) conflicts.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir conflicts_modular.v.d
 (rule
  (action
   (write-file conflicts_modular_extr.v
     "Require Coq.extraction.Extraction examples.conflicts_modular.
Extraction \"conflicts_modular.ml\" conflicts_modular.prog.\n")))

 (coq.extraction
  (prelude conflicts_modular_extr)
  (extracted_modules conflicts_modular)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target conflicts_modular.v)
  (alias runtest)
  (deps (package koika) conflicts_modular.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir cosimulation.v.d
 (rule
  (action
   (write-file cosimulation_extr.v
     "Require Coq.extraction.Extraction examples.cosimulation.
Extraction \"cosimulation.ml\" cosimulation.prog.\n")))

 (coq.extraction
  (prelude cosimulation_extr)
  (extracted_modules cosimulation)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target cosimulation.v)
  (alias runtest)
  (deps (package koika) cosimulation.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir datatypes.v.d
 (rule
  (action
   (write-file datatypes_extr.v
     "Require Coq.extraction.Extraction examples.datatypes.
Extraction \"datatypes.ml\" datatypes.prog.\n")))

 (coq.extraction
  (prelude datatypes_extr)
  (extracted_modules datatypes)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target datatypes.v)
  (alias runtest)
  (deps (package koika) datatypes.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir external_rule.v.d
 (rule
  (action
   (write-file external_rule_extr.v
     "Require Coq.extraction.Extraction examples.external_rule.
Extraction \"external_rule.ml\" external_rule.prog.\n")))

 (coq.extraction
  (prelude external_rule_extr)
  (extracted_modules external_rule)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target external_rule.v)
  (alias runtest)
  (deps (package koika) external_rule.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir fft.v.d
 (rule
  (action
   (write-file fft_extr.v
     "Require Coq.extraction.Extraction examples.fft.
Extraction \"fft.ml\" fft.prog.\n")))

 (coq.extraction
  (prelude fft_extr)
  (extracted_modules fft)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target fft.v)
  (alias runtest)
  (deps (package koika) fft.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir fir.v.d
 (rule
  (action
   (write-file fir_extr.v
     "Require Coq.extraction.Extraction examples.fir.
Extraction \"fir.ml\" fir.prog.\n")))

 (coq.extraction
  (prelude fir_extr)
  (extracted_modules fir)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target fir.v)
  (alias runtest)
  (deps (package koika) fir.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir function_call.v.d
 (rule
  (action
   (write-file function_call_extr.v
     "Require Coq.extraction.Extraction examples.function_call.
Extraction \"function_call.ml\" function_call.prog.\n")))

 (coq.extraction
  (prelude function_call_extr)
  (extracted_modules function_call)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target function_call.v)
  (alias runtest)
  (deps (package koika) function_call.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir gcd_machine.v.d
 (rule
  (action
   (write-file gcd_machine_extr.v
     "Require Coq.extraction.Extraction examples.gcd_machine.
Extraction \"gcd_machine.ml\" gcd_machine.prog.\n")))

 (coq.extraction
  (prelude gcd_machine_extr)
  (extracted_modules gcd_machine)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target gcd_machine.v)
  (alias runtest)
  (deps (package koika) gcd_machine.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir method_call.v.d
 (rule
  (action
   (write-file method_call_extr.v
     "Require Coq.extraction.Extraction examples.method_call.
Extraction \"method_call.ml\" method_call.prog.\n")))

 (coq.extraction
  (prelude method_call_extr)
  (extracted_modules method_call)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target method_call.o)
  (alias runtest)
  (deps (package koika) method_call.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir pipeline.v.d
 (rule
  (action
   (write-file pipeline_extr.v
     "Require Coq.extraction.Extraction examples.pipeline.
Extraction \"pipeline.ml\" pipeline.prog.\n")))

 (coq.extraction
  (prelude pipeline_extr)
  (extracted_modules pipeline)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target pipeline.v)
  (alias runtest)
  (deps (package koika) pipeline.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir pipeline_tutorial.v.d
 (rule
  (action
   (write-file pipeline_tutorial_extr.v
     "Require Coq.extraction.Extraction examples.pipeline_tutorial.
Extraction \"pipeline_tutorial.ml\" pipeline_tutorial.prog.\n")))

 (coq.extraction
  (prelude pipeline_tutorial_extr)
  (extracted_modules pipeline_tutorial)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target pipeline_tutorial.v)
  (alias runtest)
  (deps (package koika) pipeline_tutorial.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir save_restore.v.d
 (rule
  (action
   (write-file save_restore_extr.v
     "Require Coq.extraction.Extraction examples.save_restore.
Extraction \"save_restore.ml\" save_restore.prog.\n")))

 (coq.extraction
  (prelude save_restore_extr)
  (extracted_modules save_restore)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target save_restore.v)
  (alias runtest)
  (deps (package koika) save_restore.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir uart.v.d
 (rule
  (action
   (write-file uart_extr.v
     "Require Coq.extraction.Extraction examples.uart.
Extraction \"uart.ml\" uart.prog.\n")))

 (coq.extraction
  (prelude uart_extr)
  (extracted_modules uart)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target uart.v)
  (alias runtest)
  (deps (package koika) uart.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir vector.v.d
 (rule
  (action
   (write-file vector_extr.v
     "Require Coq.extraction.Extraction examples.vector.
Extraction \"vector.ml\" vector.prog.\n")))

 (coq.extraction
  (prelude vector_extr)
  (extracted_modules vector)
  (theories Ltac2 Koika examples)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target vector.v)
  (alias runtest)
  (deps (package koika) vector.ml)
  (action (run cuttlec %{deps} -T all -o .))))

