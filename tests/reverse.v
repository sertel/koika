(*! Regression test for bit reversal !*)
Require Import Koika.Frontend.

Inductive reg_t := r1.

Inductive rule_name_t := rl.

Definition R (reg: reg_t) : type := bits_t 16.

Definition r (reg: reg_t) : R reg := Bits.zero.

Definition urule  : uaction reg_t empty_ext_fn_t := {{
  write0(r1, >< read0(r1))
}}.

Definition rules (rl : rule_name_t) := tc_rule R empty_Sigma urule.

Definition package := {|
  ip_koika := {|
    koika_reg_types := R;
    koika_reg_init := r;
    koika_ext_fn_types := empty_Sigma;
    koika_rules := rules;
    koika_rule_external := fun _ => false;
    koika_scheduler := rl |> done;
    koika_module_name := "reverse"
  |};
  ip_sim := {|
    sp_ext_fn_specs := empty_ext_fn_props;
    sp_prelude := None
  |};
  ip_verilog := {|
    vp_ext_fn_specs := empty_ext_fn_props
  |}
|}.

Definition prog := Interop.Backends.register package.
Extraction "reverse.ml" prog.
