Require Import Coq.Strings.String.
Require Import SGA.Environments SGA.Types SGA.Circuits SGA.Primitives.

Section Interop.
  Inductive interop_ufn_t {custom_fn_t: Type} :=
  | UPrimFn (fn: prim_ufn_t)
  | UCustomFn (fn: custom_fn_t).

  Inductive interop_fn_t {custom_fn_t: Type} :=
  | PrimFn (fn: prim_fn_t)
  | CustomFn (fn: custom_fn_t).

  Definition interop_Sigma
             {fn_t}
             (Sigma: fn_t -> ExternalSignature)
    : @interop_fn_t fn_t -> ExternalSignature  :=
    fun fn => match fn with
           | PrimFn fn => prim_Sigma fn
           | CustomFn fn => Sigma fn
           end.

  Definition interop_uSigma
             {ufn_t fn_t}
             (uSigma: ufn_t -> type -> type -> fn_t)
             (fn: @interop_ufn_t ufn_t)
             (tau1 tau2: type)
    : @interop_fn_t fn_t  :=
    match fn with
    | UPrimFn fn => PrimFn (prim_uSigma fn tau1 tau2)
    | UCustomFn fn => CustomFn (uSigma fn tau1 tau2)
    end.

  Definition interop_sigma
             {fn_t}
             {Sigma: fn_t -> ExternalSignature}
             (sigma: forall fn: fn_t, Sigma fn)
    : forall fn: @interop_fn_t fn_t, interop_Sigma Sigma fn :=
    fun fn => match fn with
           | PrimFn fn => prim_sigma fn
           | CustomFn fn => sigma fn
           end.

  Inductive interop_empty_t :=.
  Definition interop_empty_Sigma (fn: interop_empty_t)
    : ExternalSignature := match fn with end.
  Definition interop_empty_uSigma (fn: interop_empty_t) (_ _: type)
    : interop_empty_t := match fn with end.
  Definition interop_empty_sigma fn
    : interop_empty_Sigma fn := match fn with end.

  Record VerilogPackage :=
    { vp_reg_t: Type;
      (** [vp_reg_t]: The type of registers used in the program.
          Typically an inductive [R0 | R1 | …] *)
      vp_reg_types: forall r: vp_reg_t, type;
      (** [vp_reg_types]: The type of data stored in each register. *)
      vp_reg_init: forall r: vp_reg_t, vp_reg_types r;
      (** [vp_reg_types]: The type of data stored in each register. *)
      vp_reg_finite: FiniteType vp_reg_t;
      (** [vp_reg_finite]: We need to be able to enumerate the set of registers
          that the program uses. *)
      vp_reg_Env: Env vp_reg_t;
      (** [vp_reg_env]: This describes how the program concretely stores maps
          keyed by registers (this is used in the type of [vp_circuit], which is
          essentially a list of circuits, one per register.. *)

      vp_custom_fn_t: Type;
      (** [vp_custom_fn_t]: The type of custom functions used in the program.
          The [fn_t] used by the program itself should be [interop_fn_t
          vp_custom_fn_t], so the program can call primitives using (PrimFn …)
          and custom functions using (CustomFn …). *)
      vp_custom_fn_types: forall fn: vp_custom_fn_t, ExternalSignature;
      (** [vp_custom_fn_t]: The signature of each function. *)

      vp_reg_names: forall r: vp_reg_t, string;
      (** [vp_reg_names]: This is to make the generated Verilog readable. *)
      vp_custom_fn_names: forall fn: vp_custom_fn_t, string;
      (** [vp_custom_fn_names]: This is to make the Verilog readable. *)

      vp_circuit: @state_transition_circuit
                    vp_reg_t (@interop_fn_t vp_custom_fn_t)
                    vp_reg_types (interop_Sigma vp_custom_fn_types)
                    vp_reg_Env;
      (** [vp_circuit]: The actual circuit scheduler circuit generated by the
          compiler (really a list of circuits, one per register).  This should
          use [interop_fn_t vp_custom_fn_t] as the function type (and
          [interop_fn_Sigma vp_custom_fn_types] as the environment of
          signatures). *)
    }.
End Interop.

Arguments interop_fn_t: clear implicits.
Arguments interop_ufn_t: clear implicits.

Definition interop_minimal_ufn_t := interop_ufn_t interop_empty_t.
Definition interop_minimal_fn_t := interop_fn_t interop_empty_t.
Definition interop_minimal_Sigma idx := interop_Sigma interop_empty_Sigma idx.
Definition interop_minimal_uSigma := interop_uSigma interop_empty_uSigma.
Definition interop_minimal_sigma := interop_sigma interop_empty_sigma.
