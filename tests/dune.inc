(subdir arrays.lv.d
 (rule
  (target arrays.v)
  (alias runtest)
  (deps (package koika) ../arrays.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir bigint.lv.d
 (rule
  (target bigint.v)
  (alias runtest)
  (deps (package koika) ../bigint.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir comparisons.lv.d
 (rule
  (target comparisons.v)
  (alias runtest)
  (deps (package koika) ../comparisons.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir cross_cycle.v.d
 (rule
  (action
   (write-file cross_cycle_extr.v
     "Require Coq.extraction.Extraction tests.cross_cycle.
Extraction \"cross_cycle.ml\" cross_cycle.prog.\n")))

 (coq.extraction
  (prelude cross_cycle_extr)
  (extracted_modules cross_cycle)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target cross_cycle.v)
  (alias runtest)
  (deps (package koika) cross_cycle.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir datatypes.lv.d
 (rule
  (target datatypes.v)
  (alias runtest)
  (deps (package koika) ../datatypes.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir double_write.v.d
 (rule
  (action
   (write-file double_write_extr.v
     "Require Coq.extraction.Extraction tests.double_write.
Extraction \"double_write.ml\" double_write.prog.\n")))

 (coq.extraction
  (prelude double_write_extr)
  (extracted_modules double_write)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target double_write.v)
  (alias runtest)
  (deps (package koika) double_write.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir errors.1.lv.d
 (rule
  (target errors.1.v)
  (alias runtest)
  (deps (package koika) ../errors.1.lv)
  (action
   (progn
     (ignore-stderr (run cuttlec %{deps} -T all -o . --expect-errors))
     (run touch %{target})))))

(subdir errors.v.d
 (rule
  (action
   (write-file errors_extr.v
     "Require Coq.extraction.Extraction tests.errors.
Extraction \"errors.ml\" errors.prog.\n")))

 (coq.extraction
  (prelude errors_extr)
  (extracted_modules errors)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target errors.v)
  (alias runtest)
  (deps (package koika) errors.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir extcall.v.d
 (rule
  (action
   (write-file extcall_extr.v
     "Require Coq.extraction.Extraction tests.extcall.
Extraction \"extcall.ml\" extcall.prog.\n")))

 (coq.extraction
  (prelude extcall_extr)
  (extracted_modules extcall)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target extcall.v)
  (alias runtest)
  (deps (package koika) extcall.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir internal_functions.v.d
 (rule
  (action
   (write-file internal_functions_extr.v
     "Require Coq.extraction.Extraction tests.internal_functions.
Extraction \"internal_functions.ml\" internal_functions.prog.\n")))

 (coq.extraction
  (prelude internal_functions_extr)
  (extracted_modules internal_functions)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target internal_functions.v)
  (alias runtest)
  (deps (package koika) internal_functions.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir large_trace.lv.d
 (rule
  (target large_trace.v)
  (alias runtest)
  (deps (package koika) ../large_trace.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir large_writeset.v.d
 (rule
  (action
   (write-file large_writeset_extr.v
     "Require Coq.extraction.Extraction tests.large_writeset.
Extraction \"large_writeset.ml\" large_writeset.prog.\n")))

 (coq.extraction
  (prelude large_writeset_extr)
  (extracted_modules large_writeset)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target large_writeset.v)
  (alias runtest)
  (deps (package koika) large_writeset.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir mul.lv.d
 (rule
  (target mul.v)
  (alias runtest)
  (deps (package koika) ../mul.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir muxelim.v.d
 (rule
  (action
   (write-file muxelim_extr.v
     "Require Coq.extraction.Extraction tests.muxelim.
Extraction \"muxelim.ml\" muxelim.prog.\n")))

 (coq.extraction
  (prelude muxelim_extr)
  (extracted_modules muxelim)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target muxelim.v)
  (alias runtest)
  (deps (package koika) muxelim.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir name_mangling.lv.d
 (rule
  (target name_mangling.v)
  (alias runtest)
  (deps (package koika) ../name_mangling.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir read1_write1_check.v.d
 (rule
  (action
   (write-file read1_write1_check_extr.v
     "Require Coq.extraction.Extraction tests.read1_write1_check.
Extraction \"read1_write1_check.ml\" read1_write1_check.prog.\n")))

 (coq.extraction
  (prelude read1_write1_check_extr)
  (extracted_modules read1_write1_check)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target read1_write1_check.v)
  (alias runtest)
  (deps (package koika) read1_write1_check.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir register_file_bypassing.v.d
 (rule
  (action
   (write-file register_file_bypassing_extr.v
     "Require Coq.extraction.Extraction tests.register_file_bypassing.
Extraction \"register_file_bypassing.ml\" register_file_bypassing.prog.\n")))

 (coq.extraction
  (prelude register_file_bypassing_extr)
  (extracted_modules register_file_bypassing)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target register_file_bypassing.v)
  (alias runtest)
  (deps (package koika) register_file_bypassing.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir shadowing.lv.d
 (rule
  (target shadowing.v)
  (alias runtest)
  (deps (package koika) ../shadowing.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir shifts.v.d
 (rule
  (action
   (write-file shifts_extr.v
     "Require Coq.extraction.Extraction tests.shifts.
Extraction \"shifts.ml\" shifts.prog.\n")))

 (coq.extraction
  (prelude shifts_extr)
  (extracted_modules shifts)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target shifts.v)
  (alias runtest)
  (deps (package koika) shifts.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir signed.lv.d
 (rule
  (target signed.v)
  (alias runtest)
  (deps (package koika) ../signed.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir struct_init.v.d
 (rule
  (action
   (write-file struct_init_extr.v
     "Require Coq.extraction.Extraction tests.struct_init.
Extraction \"struct_init.ml\" struct_init.prog.\n")))

 (coq.extraction
  (prelude struct_init_extr)
  (extracted_modules struct_init)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target struct_init.v)
  (alias runtest)
  (deps (package koika) struct_init.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir switches.v.d
 (rule
  (action
   (write-file switches_extr.v
     "Require Coq.extraction.Extraction tests.switches.
Extraction \"switches.ml\" switches.prog.\n")))

 (coq.extraction
  (prelude switches_extr)
  (extracted_modules switches)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target switches.v)
  (alias runtest)
  (deps (package koika) switches.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir taint_analysis.lv.d
 (rule
  (target taint_analysis.v)
  (alias runtest)
  (deps (package koika) ../taint_analysis.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir tmp_var.lv.d
 (rule
  (target tmp_var.v)
  (alias runtest)
  (deps (package koika) ../tmp_var.lv)
  (action
   (progn
     (run cuttlec %{deps} -T all -o .)
     (run touch %{target})))))

(subdir trivial_state_machine.v.d
 (rule
  (action
   (write-file trivial_state_machine_extr.v
     "Require Coq.extraction.Extraction tests.trivial_state_machine.
Extraction \"trivial_state_machine.ml\" trivial_state_machine.prog.\n")))

 (coq.extraction
  (prelude trivial_state_machine_extr)
  (extracted_modules trivial_state_machine)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target trivial_state_machine.v)
  (alias runtest)
  (deps (package koika) trivial_state_machine.ml)
  (action (run cuttlec %{deps} -T all -o .))))

(subdir unpack.v.d
 (rule
  (action
   (write-file unpack_extr.v
     "Require Coq.extraction.Extraction tests.unpack.
Extraction \"unpack.ml\" unpack.prog.\n")))

 (coq.extraction
  (prelude unpack_extr)
  (extracted_modules unpack)
  (theories Ltac2 Koika tests)
  (flags "-w" "-overriding-logical-loadpath"))

 (rule
  (target unpack.v)
  (alias runtest)
  (deps (package koika) unpack.ml)
  (action (run cuttlec %{deps} -T all -o .))))

