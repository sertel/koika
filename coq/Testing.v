Require Import Koika.Frontend.
Require Import Coq.Program.Equality.

(* This dependently-typed function is required for the type of the context. *)
Definition input { sig : list (string * type) } := context ( fun (x : (string * type)) => type_denote (snd x) ) sig.

(**
 * # run_function'
 *
 * This function can be used to compute a koika function.
 * 
 * Note: It could also be used for actions, but we also provide
 *       [run_action'] to implicitly pass no function arguments.
 *
 * # Arguments
 * 
 * - r            : register value assignment
 * - sigma_denote : coq implementations of external functions
 * - inputs       : direct inputs to the function
 * - func         : the actual koika function to run
 * - callback     : a callback function that is run on the
 *                  function's result if it didn't fail
 *
 * # Callback Arguments
 *
 * - ctxt : a koika context, holding the new register values
 * - out  : the direct output of the function
 *
 * # Examples
 *
 * see []()
 *)
Definition run_function'
  { reg_t : Type }
 `{ FiniteType reg_t }
  { sig : tsig var_t }
  { tau }
  { ext_fn_t : Type }
  { sigma : (ext_fn_t -> ExternalSignature) }
  { R : reg_t -> type }
  ( r : (forall reg : reg_t, R reg) )
  ( sigma_denote : (forall fn: ext_fn_t, Sig_denote (sigma fn)) )
  ( inputs : input )
  ( func : action R sigma sig tau )
  ( callback : env_t ContextEnv R -> tau -> Prop )
  : Prop :=
    let env := ContextEnv.(create) r in
    match (* tc_compute? *) (interp_action env sigma_denote inputs log_empty log_empty func) with
    | Some (log,out,_) =>
      let ctxt := commit_update env log in
      callback ctxt out
    | None => False
    end.

(**
 * # run_action
 *
 * Utility function of [run_function']
 *
 * In contrast to [run_function'] this function does not expect a function input
 * this might be handy to test actions instead of functions.
 * Additionally, the callback does not provide an output, only a context.
 *
 * # Arguments
 *
 * see [run_function']
 *)
Definition run_action'
  { reg_t }
 `{ FiniteType reg_t }
  { tau }
  { ext_fn_t }
  { sigma }
  { R : reg_t -> type }
  ( r : (forall reg : reg_t, R reg) )
  ( sigma_denote : (forall fn: ext_fn_t, Sig_denote (sigma fn)) )
  ( func : action R sigma [] tau )
  ( callback : env_t ContextEnv R -> Prop )
  : Prop :=
    run_function' r sigma_denote CtxEmpty func (fun ctxt out => callback ctxt).


(**
 * # run_function
 *
 * Utility function of [run_function']
 *
 * In contrast to [run_function'] this expects an empty external function
 * signature.
 *
 * # Arguments
 *
 * see [run_function']
 *)
Definition run_function
  { reg_t : Type }
 `{ FiniteType reg_t }
  { tau }
  { sig : tsig var_t }
  { R : reg_t -> type }
  ( r : (forall reg : reg_t, R reg) )
  ( inputs : input )
  ( func : action R empty_Sigma sig tau )
  ( callback : env_t ContextEnv R -> tau -> Prop )
  : Prop :=
    run_function' r empty_sigma inputs func callback.

(**
 * # run_action
 *
 * Utility function of [run_action']
 *
 * In contrast to [run_action'] this expects an empty external function
 * signature.
 *
 * # Arguments
 *
 * see [run_action']
 *)
Definition run_action
  { reg_t }
 `{ FiniteType reg_t }
  { tau }
  { R : reg_t -> type }
  ( r : (forall reg : reg_t, R reg) )
  ( func : action R empty_Sigma [] tau )
  ( callback : env_t ContextEnv R -> Prop )
  : Prop :=
    run_action' r empty_sigma func callback.

(**
 * # run_schedule
 *
 * This function can be used to compute a koika action or function
 *
 * # Arguments
 *
 * - r            : register value assignment
 * - rules        : mapping of rule names to actions
 * - sigma_denote : implementations of external functions
 * - sched        : the scheduler to run
 * - callback     : this function is invoked on the resulting
 *                  context
 *
 * # Callback Arguments
 *
 * - ctxt     : a koika context, holding new register values
 *
 * # Examples
 *
 * TODO
 *)
Definition run_schedule
  { reg_t : Type }
  { ext_fn_t : Type }
 `{ FiniteType reg_t }
  { R : reg_t -> type }
  { rule_name_t : Type }
  { sigma : (ext_fn_t -> ExternalSignature) }

  ( r : (forall reg : reg_t, R reg) )
  ( rules : rule_name_t -> action R sigma [] unit_t )
  ( sigma_denote : (forall fn: ext_fn_t, Sig_denote (sigma fn)) )
  ( sched : scheduler )
  ( callback : env_t ContextEnv R -> Prop )

  : Prop :=
    let env := ContextEnv.(create) r in
    let log := interp_scheduler env sigma_denote rules sched in
      callback (commit_update env log).


Ltac check :=
  vm_compute; firstorder || match goal with
         | |- _ /\ _ => (split; check)
         | |- _ \/ _ => (left; check) || (right; check)
         | |- True => constructor
         | _ : False  |- _ => contradiction
         (* | |- ?A = ?B => fail "Assertion failure! The following equality does not hold: " A "=" B *)
         | |- ?ineq => idtac "Assertion failure! The following equality does not hold: " ineq
         end.