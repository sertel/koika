(*! Implementation of a multiplier module !*)

Require Import Koika.Frontend Koika.Std.

Module Type Multiplier_sig.
  (* bit length of inputs *)
  Parameter n: nat.
End Multiplier_sig.

Module Type MultiplierInterface.
  Axiom reg_t : Type.
  Axiom R : reg_t -> type.
  Axiom r : forall idx: reg_t, R idx.
  Axiom enq : UInternalFunction reg_t empty_ext_fn_t.
  Axiom deq : UInternalFunction reg_t empty_ext_fn_t.
  Axiom step : UInternalFunction reg_t empty_ext_fn_t.
  Axiom enabled : UInternalFunction reg_t empty_ext_fn_t.
  Axiom FiniteType_reg_t : FiniteType reg_t.
  Axiom Show_reg_t : Show reg_t.
End MultiplierInterface.

Module ShiftAddMultiplier (s: Multiplier_sig) <: MultiplierInterface.
  Import s.

  Inductive _reg_t := valid | operand1 | operand2 | result | n_step | finished.
  Definition reg_t := _reg_t.

  Definition R r :=
    match r with
    | valid    => bits_t 1          (* A computation is being done *)
    | operand1 => bits_t n       (* The first operand *)
    | operand2 => bits_t n       (* The second operand *)
    | result   => bits_t (n+n)     (* The result being computed *)
    | n_step   => bits_t (log2 n)  (* At which step of the computation we are *)
    | finished => bits_t 1       (* Indicates if the computation has finished *)
    end.

  Definition r idx : R idx :=
    match idx with
    | valid    => Bits.zero
    | operand1 => Bits.zero
    | operand2 => Bits.zero
    | result   => Bits.zero
    | n_step   => Bits.zero
    | finished => Bits.zero
    end.

  (*
    # Start the multiplication of two given values.

    If the multiplier is not busy (valid == 0) the given
    operands will be saved into registers and the multiplier
    will be started (valid == 1).

    ## Aborts
    In case the multiplier is currently busy this
    rule aborts and the new multiplication won't start.

    The currently running multiplication won't be affected
   *)
  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): unit_t =>
         guard (!read0(valid));
         write0(valid, #Ob~1);
         write0(operand1, op1);
         write0(operand2, op2);
         write0(result, |(n+n)`d0|);
         write0(n_step, |(log2 n)`d0|)
    }}.

  (*
    # Finish off a multiplication by reading the result

    In case the multiplier is done (valid && finished)
    the multiplication result is returned and the multiplier
    is marked as available again.

    ## Aborts
    In case the multiplier is not running (valid == 0) or
    not done (finished == 0) this function will abort.
  *)
  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) =>
         guard (read1(valid) && read1(finished));
         write1(finished, #Ob~0);
         write1(valid, #Ob~0);
         read1(result)
    }}.

  (*
    # Perform a single step of computation

    For that the n'th bit of operand2 is read and in case
    it is set operand1 shifted by n will be added to the result.

    After this function has been invoked n times [finished] will
    be set.

    ## Example

    op1   op2
    ---------
    101 * 110

    - step 0: op2[0] = 0 -> nothing
    - step 1: op2[1] = 1 -> res += op1 << 1 -> res = 1010
    - step 2: op2[2] = 1 -> res += op1 << 2 -> res = 1010 + 10100 = 11110

    ## Aborts
    In case the multiplier is not running (valid == 0) or if
    it has already finished (finished == 1)
   *)
  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : unit_t =>
         guard (read0(valid) && !read0(finished));
         let n_step_val := read0(n_step) in
         (if read0(operand2)[n_step_val] then
            let partial_mul := zeroExtend(read0(operand1), n+n) << n_step_val in
            write0(result, read0(result) + partial_mul)
          else
            pass);
         if (n_step_val == #(Bits.of_nat (log2 n) (n-1))) then
           write0(finished, #Ob~1)
         else
           write0(n_step, n_step_val + |(log2 n)`d1|)
    }}.

  (*
    Always return 1 to show that the multiplier is enabled
   *)
  Definition enabled : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enabled () : bits_t 1 => Ob~1 }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
  Instance Show_reg_t : Show reg_t := _.
End ShiftAddMultiplier.

Module DummyMultiplier (s: Multiplier_sig) <: MultiplierInterface.
  Import s.

  Inductive _reg_t :=.
  Definition reg_t := _reg_t.

  Definition R (idx: reg_t) : type := match idx with end.
  Definition r idx : R idx := match idx with end.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): unit_t => pass }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) => |(n + n)`d0| }}.

  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : unit_t => pass }}.

  Definition enabled : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enabled () : bits_t 1 => Ob~0 }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.
  Instance Show_reg_t : Show reg_t := _.
End DummyMultiplier.
