(*! Circuits | Syntax of circuits (RTL) !*)
Require Export Koika.Common Koika.Environments Koika.Primitives.

Import PrimTyped CircuitSignatures.

Section Circuit.
  Context {rule_name_t reg_t ext_fn_t: Type}.
  Context {rwdata: nat -> Type}. (* Forward declaration *)

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Inductive rwdata_field :=
  | rwdata_r0
  | rwdata_r1
  | rwdata_w0
  | rwdata_w1
  | rwdata_data0
  | rwdata_data1.

  Inductive rwcircuit_field :=
  | rwcircuit_rwdata (r: reg_t) (field: rwdata_field)
  | rwcircuit_canfire.

  Inductive circuit: nat -> Type :=
  | CMux {sz} (select: circuit 1) (c1 c2: circuit sz): circuit sz
  | CConst {sz} (cst: bits sz): circuit sz
  | CReadRegister (reg: reg_t): circuit (CR reg)
  | CUnop (fn: fbits1) (a1: circuit (arg1Sig (CSigma1 fn)))
    : circuit (retSig (CSigma1 fn))
  | CBinop (fn: fbits2) (a1: circuit (arg1Sig (CSigma2 fn))) (a2: circuit (arg2Sig (CSigma2 fn)))
    : circuit (retSig (CSigma2 fn))
  | CExternal (idx: ext_fn_t)
              (a: circuit (arg1Sig (CSigma idx)))
    : circuit (retSig (CSigma idx))
  | CBundleRef {sz} (name: rule_name_t) (regs: list reg_t)
               (bundle: context (fun r => rwdata (CR r)) regs)
               (field: rwcircuit_field) (c: circuit sz): circuit sz
  | CAnnot {sz} (annot: string) (c: circuit sz): circuit sz.
End Circuit.

Notation CAnd := (CBinop (And _)).
Notation COr := (CBinop (Or _)).
Notation CNot := (CUnop (Not _)).
Notation CRev := (CUnop (Rev _)).

Arguments circuit {rule_name_t reg_t ext_fn_t rwdata} CR CSigma sz : assert.
