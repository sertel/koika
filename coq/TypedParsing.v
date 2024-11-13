(* Frontend | Parser for the (typed) Kôika EDSL
 * 
 * This file contains all notations which are used
 * to adjust coq's parser and enable it to parse
 * koika.
 *
 * The notations in this file are ordered by their
 * level, beginning with the lowest precedence (highest
 * level).
 *
 * Note:
 *   The notations in this file produce typed koika
 *   syntax trees. There exist very similar notations
 *   for parsing untyped koika syntax in the file
 *   Parsing.v
 *)
Require Import
  Koika.Common
  Koika.TypedSyntax
  Koika.IdentParsing
  Koika.TypedSyntaxMacros.
Require Koika.Syntax.
Require Import Unicode.Utf8.

Import Specif.SigTNotations.

Export TypedSyntaxMacros.
Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimTyped.
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

Definition pos_t := unit.
Definition var_t := string.
Definition fn_name_t := string.
(* Koika *)
(* TODO: pos_t is set to unit just like in Frontent.v - does that make sense?  *)

Definition action'
  {tau sig reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    (TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau).

Definition action
  {tau reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    (TypedSyntax.action pos_t var_t fn_name_t R Sigma [] tau).

Definition function
  {tau sig reg_t ext_fn_t}
  (R : reg_t -> type)
  (Sigma: ext_fn_t -> ExternalSignature) :=
    Types.InternalFunction' fn_name_t
      (TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau).

Declare Custom Entry koika_t.

(* This is the entry point to transition from normal
  coq (constr) to koika *)
Notation "'<{' e '}>'" := (e) (e custom koika_t).

(* koika_t_var - utility grammar
 *
 * This grammar is used throughout the parser
 * to parse identifiers as strings.
 *)
Declare Custom Entry koika_t_var.
Notation "a" := (ident_to_string a) (in custom koika_t_var at level 0, a ident, only parsing).
Notation "a" := (a) (in custom koika_t_var at level 0, a ident, format "'[' a ']'", only printing).

(* Variable references
 *
 * This typeclass is used to build a member
 * proof that a given variable name is actually
 * part of the context.
 *
 * If the proof cannot be constructed, e.g. a
 * variable was referenced out of its scope,
 * then no typeclass is found which results in
 * a type checking error.
 *)
(* TODO better error messages *)
Existing Class member.
#[export] Existing Instance MemberHd.
#[export] Existing Instance MemberTl.

(* We want to tell the typechecker that the body of the function
 * should have the function's arguments in its context (sig).
 *
 * However, using a type hint where R Sigma are kept implicit
 * like:
 * ```
 * Definition some_act : action R Sigma :=
 * <{ ... }>: action' (sig := ...) _ _.
 * ```
 * does not work since coq is then trying to infer R and Sigma from
 * the body term instead of the outer definition.
 *
 * To tell coq to infer it from the definition we need
 * bidirectionality hints and thus we need a seperate function.
 *)
Local Definition refine_sig_tau sig tau {reg_t ext_fn_t}
  {R : reg_t -> type} {Sigma : ext_fn_t -> ExternalSignature}
  (a : action' R Sigma (tau := tau) (sig := sig)) : action' R Sigma := a.
Arguments refine_sig_tau sig tau {reg_t ext_fn_t} {R Sigma} & a : assert.

(* Koika_types *)
(* TODO improve arg list to be more consistent on nil case  *)
Declare Custom Entry koika_t_binder.
Notation "'(' x ':' y ')'" := (x%string, (y : type)) (in custom koika_t_binder at level 0, x custom koika_t_var, y constr).
Notation "a  ..  b" := (cons a ..  (cons b nil) ..)  (in custom koika_t_binder at level 1, a custom koika_t_binder at next level, b custom koika_t_binder at next level).

Notation "'fun' nm args ':' ret '=>' body" :=
  (Build_InternalFunction' nm%string (refine_sig_tau args ret body))
    (in custom koika_t at level 200, nm custom koika_t_var, args custom koika_t_binder, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  args  ':'  ret  '=>' '/' body ']'").
Notation "'fun' nm '()' ':' ret '=>' body" :=
  (Build_InternalFunction' nm%string (refine_sig_tau nil ret body))
    (in custom koika_t at level 200, nm custom koika_t_var, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  '()'   ':'  ret  '=>' '/' body ']'").

Notation "'assert' a 'in' c"          := (If a c (Fail _)  ) (in custom koika_t at level 200, right associativity, format "'[v' 'assert'  a '/' 'in'  c ']'").
Notation "'assert' a 'else' b 'in' c" := (If a c b         ) (in custom koika_t at level 200, right associativity, format "'[v' 'assert'  a '/' 'else'  b '/' 'in'  c ']'").
Notation "'when' a 'do' t "           := (If a t (Const Ob)) (in custom koika_t at level 200, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "'let' a ':=' b 'in' c" := (Bind a b c) (in custom koika_t at level 200, a custom koika_t_var, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").

Notation "a ';' b" := (Seq a                          b) (in custom koika_t at level 90, b at level 200, format "'[v' a ';' '/' b ']'" ).
Notation "a ';'"   := (Seq a (Const (tau := unit_t) Ob)) (in custom koika_t at level 90). (* trailing comma *)

Notation "'set' a ':=' b" := (Assign (k := a) _ b) (in custom koika_t at level 89, a custom koika_t_var, format "'set'  a  ':='  b").

Notation "'if' a 'then' t"          := (If a t                  (Const (tau := unit_t) Ob)) (in custom koika_t at level 89, t custom koika_t at level 89, right associativity, format "'[v' 'if'  a '/' 'then'  t ']'").
Notation "'if' a 'then' t 'else' f" := (If a t                                  f         ) (in custom koika_t at level 89, t custom koika_t at level 89, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'guard' '(' a ')' "       := (If (Unop (Bits1 Not) a) (Fail (unit_t)) (Const Ob)) (in custom koika_t at level 89, right associativity, format "'guard' '(' a ')'").


(* Inspired by cpp the precedence  *)
(* https://en.cppreference.com/w/cpp/language/operator_precedence *)
(* TODO id really prefer to use || and && for logical operations and & | for bitwise *)
(* Bit operations *)
Notation "a  '||'  b"         := (Binop (Bits2 (Or       _))          a b) (in custom koika_t at level 85).
Notation "a  '^'  b"          := (Binop (Bits2 (Xor      _))          a b) (in custom koika_t at level 84).
Notation "a  '&&'  b"         := (Binop (Bits2 (And      _))          a b) (in custom koika_t at level 83).

(* Comparisons *)
Notation "a  '!='  b"         := (Binop (Eq _ true)                   a b) (in custom koika_t at level 80).
Notation "a  '=='  b"         := (Binop (Eq _ false)                  a b) (in custom koika_t at level 80).

Notation "a  '<'  b"          := (Binop (Bits2 (Compare false cLt _)) a b) (in custom koika_t at level 79).
Notation "a  '<s'  b"         := (Binop (Bits2 (Compare true  cLt _)) a b) (in custom koika_t at level 79).
Notation "a  '<='  b"         := (Binop (Bits2 (Compare false cLe _)) a b) (in custom koika_t at level 79).
Notation "a  '<s='  b"        := (Binop (Bits2 (Compare true  cLe _)) a b) (in custom koika_t at level 79).
Notation "a  '>'  b"          := (Binop (Bits2 (Compare false cGt _)) a b) (in custom koika_t at level 79).
Notation "a  '>s'  b"         := (Binop (Bits2 (Compare true  cGt _)) a b) (in custom koika_t at level 79).
Notation "a  '>='  b"         := (Binop (Bits2 (Compare false cGe _)) a b) (in custom koika_t at level 79).
Notation "a  '>s='  b"        := (Binop (Bits2 (Compare true  cGe _)) a b) (in custom koika_t at level 79).

(* Bit concatenation / shifts *)
Notation "a  '++'  b"         := (Binop (Bits2 (Concat _ _))          a b) (in custom koika_t at level 75).
Notation "a  '>>'  b"         := (Binop (Bits2 (Lsr _ _))             a b) (in custom koika_t at level 74).
Notation "a  '>>>'  b"        := (Binop (Bits2 (Asr _ _))             a b) (in custom koika_t at level 74).
Notation "a  '<<'  b"         := (Binop (Bits2 (Lsl _ _))             a b) (in custom koika_t at level 74).

(* Arithmetic *)
Notation "a  '+'  b"          := (Binop (Bits2 (Plus     _))          a b) (in custom koika_t at level 70).
Notation "a  '-'  b"          := (Binop (Bits2 (Minus    _))          a b) (in custom koika_t at level 70).
Notation "a  '*'  b"          := (Binop (Bits2 (Mul    _ _))          a b) (in custom koika_t at level 69).

(* Unary operators *)
Notation "'!' a"              := (Unop  (Bits1 (Not _))               a  ) (in custom koika_t at level 65, format "'!' a").

Notation "a '[' b ']'"        := (Binop (Bits2 (Sel _))               a b) (in custom koika_t at level 60, format "'[' a [ b ] ']'").
Notation "a '[' b ':+' c ']'" := (Binop (Bits2 (IndexedSlice _ c))    a b) (in custom koika_t at level 60, c constr at level 0, format "'[' a [ b ':+' c ] ']'").

Notation "'`' a '`'" := (a) (in custom koika_t, a constr).
Notation "'(' a ')'" := (a) (in custom koika_t, format "'[v' '(' a ')' ']'").

(* TODO does this really has to be `bits_t _` *)
(* TODO add support for enum and struct constants *)
Notation "'#' s" := (Const (tau := bits_t _) s) (in custom koika_t at level 0, s constr at level 0, only parsing).

(* ========================================================================= *)
(*                   Notations beginning with an identifier                  *)
(* ========================================================================= *)
(*
 * Note:
 *   All these notations need to be on the same level (here 0)
 *   else the parser would match on the highest level first and
 *   never even consider notations on a lower level.
 * 
 *   Likewise, all these notations need to start with a variable
 *   on the same level and in the same grammar (here a constr on level 0).
 *   Only so the parser can parse this variable first and then decide
 *   (depending on the following tokens) which notation matches.
 * 
 * Note:
 *   Some of the literal notations also start with an identifier.
 *   Thus, the same restrictions apply.
 *)
Notation "a" := (Var (k := (ident_to_string a)) _) (in custom koika_t at level 0, a constr at level 0, only parsing).
Notation "a" := (Var a) (in custom koika_t at level 0, a constr at level 0, only printing).

Declare Custom Entry koika_t_args.
Notation "'(' x ',' .. ',' y ')'" := (CtxCons (_,_) (x) .. (CtxCons (_,_) (y) CtxEmpty) ..) (in custom koika_t_args, x custom koika_t, y custom koika_t).
Notation "'(' ')'" := (CtxEmpty) (in custom koika_t_args).
Notation "'()'"    := (CtxEmpty) (in custom koika_t_args).

Notation "fn args" := (InternalCall fn args)
  (in custom koika_t at level 0, fn constr at level 0 , args custom koika_t_args, only parsing).

Notation "instance  '.(' fn ')' args" :=
  (InternalCall {|
    int_name := fn.(int_name);
    int_body := (lift (lift_fn_of instance eq_refl) _ fn.(int_body))
  |} args)
  (in custom koika_t at level 0, instance constr at level 0, fn constr, args custom koika_t_args).

Notation "'{' fn '}' args" := (InternalCall fn args)
  (in custom koika_t at level 0, fn constr, args custom koika_t_args, only parsing).


(* ========================================================================= *)
(*                                Constructors                               *)
(* ========================================================================= *)

Declare Custom Entry koika_t_struct_field.
Declare Custom Entry koika_t_struct_init.
(* struct instantiation in koika *)
(* expr at level at level 89 to stay below koika's sequence (a ; b), because it
 * uses the same separation character *)
Notation "f ':=' expr" := (field_subst f expr) (in custom koika_t_struct_field at level 0, f custom koika_t_var, expr custom koika_t at level 89).
Notation "a ';' b" := (cons a   b) (in custom koika_t_struct_init at level 0, a custom koika_t_struct_field, right associativity).
Notation "a ';'"   := (cons a nil) (in custom koika_t_struct_init at level 0, a custom koika_t_struct_field). (* trailing comma *)
Notation "a"       := (cons a nil) (in custom koika_t_struct_init at level 0, a custom koika_t_struct_field).

Notation "'struct' sig '::{' '}'" :=
  (struct_init sig []) (in custom koika_t, sig constr at level 0).
Notation "'struct' sig '::{' fields '}'" :=
  (struct_init sig fields) (in custom koika_t, sig constr at level 0, fields custom koika_t_struct_init).

Notation "sig '::{' '}'" :=
  (struct_init sig []) (in custom koika_t at level 0, sig constr at level 0).
Notation "sig '::{' fields '}'" :=
  (struct_init sig fields) (in custom koika_t at level 0, sig constr at level 0, fields custom koika_t_struct_init).

Notation "'enum' sig '::<' f '>'" :=
  (Const (tau := enum_t sig) (vect_nth sig.(enum_bitpatterns) (must (vect_index f sig.(enum_members)))))
    (in custom koika_t, sig constr at level 0, f custom koika_t_var).
Notation "sig '::<' f '>'" :=
  (Const (tau := enum_t sig) (vect_nth sig.(enum_bitpatterns) (must (vect_index f sig.(enum_members)))))
    (in custom koika_t at level 0, sig constr at level 0, f custom koika_t_var).


(* ========================================================================= *)
(*                                  Literals                                 *)
(* ========================================================================= *)

Declare Custom Entry koika_t_consts.
Notation "'1'" := (Ob~1) (in custom koika_t_consts at level 0).
Notation "'0'" := (Ob~0) (in custom koika_t_consts at level 0).
Notation "bs '~' '0'" := (Bits.cons false bs) (in custom koika_t_consts at level 1, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (Bits.cons  true bs) (in custom koika_t_consts at level 1, left associativity, format "bs '~' '1'").

Notation "'Ob' '~' number" := (Const (tau := bits_t _)   number)
    (in custom koika_t at level 0, number custom koika_t_consts, format "'Ob' '~' number").
Notation "'Ob'"            := (Const (tau := bits_t 0) Bits.nil)
    (in custom koika_t at level 0).

Local Definition len := String.length.

Notation "num ':b' sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':b'"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 1)        (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0b' num sz").
Notation "'0b' num"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 1)        (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num"    := (Const (tau := bits_t _) (Bits.of_N _                      (bin_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0b' num").

Notation "num ':o' sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':o'"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 3)        (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0o' num sz").
Notation "'0o' num"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 3)        (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num"    := (Const (tau := bits_t _) (Bits.of_N _                      (oct_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0o' num").

Notation "num ':d' sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':d'"    := (Const (tau := bits_t _) (Bits.of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num))))
                                                                                     (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0d' num sz").
Notation "'0d' num"    := (Const (tau := bits_t _) (Bits.of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num))))
                                                                                     (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num"    := (Const (tau := bits_t _) (Bits.of_N _                      (dec_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0d' num").

Notation "num ':h' sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':h'"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 4)        (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num sz" := (Const (tau := bits_t _) (Bits.of_N (sz <: nat)            (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, sz constr at level 0, format "'0x' num sz").
Notation "'0x' num"    := (Const (tau := bits_t _) (Bits.of_N ((len num) * 4)        (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num"    := (Const (tau := bits_t _) (Bits.of_N _                      (hex_string_to_N num))) (in custom koika_t at level 0, num constr at level 0, only printing,        format "'0x' num").

(* legacy number format *)
Notation "'|' a '`d' b '|'" := (Const (tau := bits_t _) (Bits.of_N (a<:nat) b%N)) (in custom koika_t at level 0, a constr at level 0 , b constr at level 0).


(* ========================================================================= *)
(*                        Closed Notations on level 0                        *)
(* ========================================================================= *)

(* TODO should work without tau .. right? *)
Notation "'pass'"  := (Const (tau := unit_t) Ob) (in custom koika_t).
(* the magic axiom can be used as value for an arbitrary type, use it with care *)
Require Magic.
Notation "'magic'" := (Magic.__magic__) (in custom koika_t).

Notation "'fail'"            := (Fail     unit_t) (in custom koika_t, format "'fail'").
Notation "'fail' '(' t ')'"  := (Fail (bits_t t)) (in custom koika_t, t constr, format "'fail' '(' t ')'").
Notation "'fail' '@(' t ')'" := (Fail          t) (in custom koika_t, t constr, format "'fail' '@(' t ')'").

Notation "'read0' '(' reg ')' "           := (Read P0 reg)        (in custom koika_t, reg constr, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' "           := (Read P1 reg)        (in custom koika_t, reg constr, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" := (Write P0 reg value) (in custom koika_t, reg constr, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" := (Write P1 reg value) (in custom koika_t, reg constr, format "'write1' '(' reg ',' value ')'").

Notation "'zeroExtend(' a ',' b ')'" := (Unop (Bits1 (ZExtL _ b)) a) (in custom koika_t, b constr, format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'"       := (Unop (Bits1 (SExt  _ b)) a) (in custom koika_t, b constr, format "'sext(' a ',' b ')'").

Notation "'ignore(' a ')'"           := (Unop (Conv _ Ignore)     a) (in custom koika_t).
Notation "'pack(' a ')'"             := (Unop (Conv _ Pack)       a) (in custom koika_t).
Notation "'unpack(' t ',' v ')'"     := (Unop (Conv t Unpack)     v) (in custom koika_t, t constr).

Notation "'extcall' method '(' arg ')'" := (ExternalCall method arg) (in custom koika_t, method constr at level 0).

Notation "'get' '(' v ',' f ')'"                    := (Unop  (Struct1 GetField _      (PrimTypeInference.find_field _ f))  v  ) (in custom koika_t,           f custom koika_t_var, format "'get' '(' v ','  f ')'").
Notation "'getbits' '(' t ',' v ',' f ')'"          := (Unop  (Bits1 (GetFieldBits t   (PrimTypeInference.find_field t f))) v  ) (in custom koika_t, t constr, f custom koika_t_var, format "'getbits' '(' t ','  v ','  f ')'").
Notation "'subst' '(' v ',' f ',' a ')'"            := (Binop (Struct2 SubstField _    (PrimTypeInference.find_field _ f))  v a) (in custom koika_t,           f custom koika_t_var, format "'subst' '(' v ','  f ',' a ')'").
Notation "'substbits' '(' t ',' v ',' f ',' a ')'"  := (Binop (Bits2 (SubstFieldBits t (PrimTypeInference.find_field t f))) v a) (in custom koika_t, t constr, f custom koika_t_var, format "'substbits' '(' t ','  v ','  f ',' a ')'").

Notation "'aref' '(' v ',' f ')'"                   := (Unop  (Array1  (GetElement         f)) v)   (in custom koika_t,           f constr, format "'aref' '(' v ','  f ')'").
Notation "'arefbits' '(' t ',' v ',' f ')'"         := (Unop  (Array1  (GetElementBits   t f)) v)   (in custom koika_t, t constr, f constr, format "'arefbits' '(' t ','  v ','  f ')'").
Notation "'asubst' '(' v ',' f ',' a ')'"           := (Binop (Array2  (SubstElement       f)) v a) (in custom koika_t,           f constr, format "'asubst' '(' v ','  f ',' a ')'").
Notation "'asubstbits' '(' t ',' v ',' f ',' a ')'" := (Binop (Array2  (SubstElementBits t f)) v a) (in custom koika_t, t constr, f constr, format "'asubstbits' '(' t ','  v ','  f ',' a ')'"). 

(* koika_t_branches - utility
 *
 * This grammar is used for the syntax
 * of match branches
 *)
Declare Custom Entry koika_t_branches.
Notation "x '=>' a "     := [(x,a)] (in custom koika_t_branches at level 0, x custom koika_t at level 200, a custom koika_t at level 200).
Notation "arg1 '|' arg2" := (arg1 ++ arg2) (in custom koika_t_branches at level 1, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (switch var default branches)
    (in custom koika_t, branches custom koika_t_branches,
        format "'match'  var  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").


(* ========================================================================= *)
(*                            scheduler notations                            *)
(* ========================================================================= *)

(* at level 60, simply because it's the level of the `cons` notation (::) *)
Notation "r '|>' s" :=
  (Syntax.Cons r s)
    (at level 60, right associativity).
Notation "'done'" :=
  Syntax.Done.

Module Type Tests.
  Parameter pos_t : Type.
  Inductive reg_t := reg1.
  Parameter ext_fn_t : Type.
  Definition R (r : reg_t) : type := bits_t 2.

  Parameter Sigma: ext_fn_t -> ExternalSignature.

  Notation _action := (action R Sigma).

  Definition test_num : _action := <{ Ob~1~1~1 }>.
  Definition test_lit  : _action := <{ Ob~1~1~0~0~1 }>.
  Definition test_lit2 : _action := <{ |10 `d 10| }>.
  Definition test_pass : _action := <{ pass }>.
 
  Definition test_var    : _action := <{ let a := Ob~1~1 in a }>.
  Definition test_seq    : _action := <{ let a := Ob~1~1 in pass; a }>.
  Definition test_assign : _action := <{ let a := Ob~1~1 in pass; set a := Ob~0~1 }>.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  Definition test_enum : _action := <{
    enum numbers_e::<ONE>
  }>.

  Definition func : function R Sigma := <{
    fun f () : bits_t 2 =>
      read0(reg1)
  }>.

  Inductive reg_t_super := sreg1 (r : reg_t).
  Definition super_R (sr : reg_t_super) := match sr with
    | sreg1 r => R r
    end.

  Definition super_func : function super_R Sigma := <{
    fun sup_f () : bits_t 2 =>
      sreg1.(func)()
  }>.

  Definition test_func2 : function R Sigma := <{
    fun f (arg1 : bits_t 1) (arg2 : bits_t 3) : bits_t 2 =>
      read0(reg1)
  }>.

  Definition test_funcall : function R Sigma := <{
    fun f () : bits_t 2 =>
      test_func2(0b"1", 0b"011")
  }>.

  Definition numbers_s := {|
    struct_name := "numbers";
    struct_fields := [
      ("one", bits_t 3);
      ("two", bits_t 3);
      ("three", bits_t 3)
    ];
  |}.

  Definition test_struct_init : _action := <{
    struct numbers_s::{
      one := Ob~1~1~1;
      two := Ob~1~1~1
    }
  }>.
  Definition test_struct_init_trailing_comma : _action := <{
    struct numbers_s::{
      two   := "100":b ;
      three := "101":b ;
    }
  }>.
  Definition test_struct_init_empty : _action := <{
    struct numbers_s::{}
  }>.
End Tests.
Module Type Tests2.
  Inductive reg_t :=
  | data0 | data1.
  Definition R (r : reg_t) := bits_t 5.
  Parameter ext_fn_t : Type.
  Parameter Sigma: ext_fn_t -> ExternalSignature.
  Definition _action {tau} := action (tau := tau) R Sigma.
  Definition test_2 : _action := <{ Ob~1~1 }>.
  Definition test_bits : _action := <{ 0b"010" }>.
  Definition test_1 : _action := <{ let yoyo := fail(2) in pass }>.
  Definition test_1' : _action := <{ let yoyo := fail(2) in yoyo }>.
  Definition test_2' : _action := <{ pass; pass }>.
  Definition test_3' : _action := <{ let yoyo := pass in set yoyo := pass ; pass }>.
  Fail Definition test_3'' : _action := <{ set yoyo := pass ; pass; }>.
  Fail Definition test_5 : _action := <{ let yoyo := set yoyo := pass in pass; }>.
  Inductive test := rData (n:nat).
  Definition test_R (r : test) := bits_t 5.
  Definition test_9 : _action := <{ read0(data0) }>.
  Definition test_10 : nat -> action test_R Sigma := (fun idx => <{ read0(rData idx) }>).
  Definition test_11 : _action := <{ (let yoyo := read0(data0) in write0(data0, Ob~1~1~1~1~1)); fail }>.
  Fail Definition test_11' : _action := <{ (let yoyo := read0(data0) in write0(data0, Ob~1~1~1~1)); fail }>.
  Definition test_12 : _action := <{ (let yoyo := if fail (1) then read0(data0) else fail (5) in write0(data0, 0b"01100"));fail }>.
  Fail Definition test_13 : _action := <{ yoyo }>.
  Set Printing Implicit.

  Definition test_14 : _action := <{ !Ob~1 && Ob~1 }>.
  Definition test_14' : _action := <{ !(Ob~1 && Ob~1) }>.
  Goal test_14 <> test_14'. compute; congruence. Qed.
  Definition test_15 : _action := <{ 0b"10011" && read0(data0) }>.
  Definition test_16 : _action := <{ !read0(data1) && !read0(data1) }>.
  Program Definition test_lit : _action (tau := bits_t 5) := (Seq (Write P0 data0 <{ Ob~1~1~0~0~1 }>) (Const (tau := bits_t _) (Bits.of_N ltac:(let x := eval cbv in ((len "01100") * 1) in exact x) (bin_string_to_N "01100")))).
  Fail Next Obligation.
  Definition test_20 : _action := <{ (0b"11001100")[ Ob~0~0~0 :+ 3 ] }>.
  Definition test_23 : function R Sigma := <{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : unit_t => pass }>.
  Definition test_24 (sz : nat) : function R Sigma := <{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => fail(sz)}>.
  Definition test_25 (sz : nat) : function R Sigma := <{fun test (arg1 : bits_t sz ) : bits_t sz => let oo := fail(sz) >> fail(sz) in oo}>.
  Definition test_26 (sz : nat) : function R Sigma := <{ fun test () : bits_t sz  => fail(sz) }>.
  Definition test_write : _action := <{ write0(data0, 0b"01101"); }>.

  #[program ]Definition idk : _action (tau := bits_t 3) := <{
    (!read0(data0))[Ob~1~1~1 :+ 3]
  }>.
  
  #[program] Definition idk2 : _action := <{
    let idk := Ob~1~1~1~0~0 in
    ignore(if (!idk)[#(Bits.of_nat 3 0) :+ 1] then (
        write0(data0, 0b"01101");
        pass
      ) else pass);
    fail
  }>.
  Fail Next Obligation.
  #[program] Definition test_27 : _action := <{
    ignore(if (!read0(data0))[#(Bits.of_nat _ 0) :+ 1] then (
      write0(data0, 0b"01101");
      let yo := if (Ob~1) then 0b"1001" else 0x"F" in
      write0(data0, yo ++ Ob~1);
      0b"00011"5
      ) else read0(data0));
    fail
  }>.
  Fail Next Obligation.
  Definition test_28 : _action :=  <{
    let var := 0b"101" in
    match var with
    | Ob~1~1~1 => pass
    | Ob~0~1~1 => pass
    return default: pass
    end
  }>.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("foo", bits_t 2); ("bar", bits_t 32)] |}.

  Definition test_30'' : _action := <{
    let upu := 0x"C0" in
    struct mem_req::{ foo := upu[#(Bits.of_nat _ 0) :+ 2] ;
                      bar := |32`d98| }
  }>.

  Program Definition test_31' : _action := <{
    let upu := 0x"C0" in
    let a := struct mem_req::{ foo := upu[#(Bits.of_nat 3 0) :+ 2] ;
                              bar := |32`d98| } in
      unpack(struct_t mem_req, pack(a))
  }>.
  Fail Next Obligation.
  
  Notation "'[|' a '=koika=' b '|]'" := ((a : _action) = (b : _action)) (at level 0, a custom koika_t at level 200, b custom koika_t at level 200).

  (* sequences in match statements without paranthesis *)
  Program Definition test_32 : [|
    let x := 0x"C0"5 in
    match |5`d10| with
    | |5`d10| => (
      write0(data0, x);
      x
    )
    | |5`d 9| => (
      x
    )
    return default: fail (5)
    end
  =koika=
    let x := 0x"C0"5 in
    match |5`d10| with
    | |5`d10| =>
      write0(data0, x);
      x
    | |5`d 9| =>
      x
    return default: fail (5)
    end
  |] := eq_refl.
  Fail Next Obligation.

  (* else branch takes single instruction from sequence *)
  Definition test_33 : [|
    if Ob~1
      then pass
      else pass;
    pass
  =koika=
    (if Ob~1
      then pass
      else pass);
    pass
  |] := eq_refl.

  (* if' then branch takes single instruction from sequence *)
  Definition test_34 : [|
    if Ob~1
      then pass;
    pass
  =koika=
    (if Ob~1 then
      pass);
    pass
  |] := eq_refl.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  (* Accessing enum constants *)
  Definition enum_test_1 := <{ enum numbers_e::< ONE > }> : _action.
  Definition enum_test_2 := <{ enum numbers_e::< TWO > }> : _action.
  Definition enum_test_3 := <{ numbers_e::< THREE > }> : _action.

  Definition numbers_s := {|
    struct_name:= "some_s";
    struct_fields :=
    [ ("one"  , bits_t 3);
      ("two"  , bits_t 3);
      ("three", bits_t 3);
      ("four" , bits_t 3);
      ("five" , enum_t numbers_e) ]
  |}.
  Definition struct_test_1 : _action := <{ struct numbers_s::{  } }>.
  Definition struct_test_3 : _action := <{ struct numbers_s::{ one := 0b"010" } }>.
  Definition struct_test_7 : _action := <{ struct numbers_s::{ one := 0b"111"; two := 0b"101"; } }>. (* trailing comma *)
  Definition struct_test_5 : _action := <{ struct numbers_s::{ five := enum numbers_e::< IDK > } }>.

  Definition num_test_b_1 : [| "01101":b     =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Definition num_test_b_2 : [| 0b"00011"     =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_3 : [| "11":b5       =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_4 : [| 0b"10"5       =koika= Ob~0~0~0~1~0 |] := eq_refl.
  Definition num_test_b_5 : [| 0b"10010110"3 =koika= Ob~1~1~0     |] := eq_refl.
  Fail Definition num_test_b_6  := <{ 0b"102"  }> : _action.
  Fail Definition num_test_b_7  := <{ 0b"10f"6 }> : _action.
  Fail Definition num_test_b_8  := <{ "f0":b5  }> : _action.
  Fail Definition num_test_b_9  := <{ "f0":b   }> : _action.
  Fail Definition num_test_b_10 := <{ "":b     }> : _action.

  Definition num_test_o_1 : [| "330":o   =koika= Ob~0~1~1~0~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_2 : [| "070":o9  =koika= Ob~0~0~0~1~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_3 : [| 0o"000"   =koika= Ob~0~0~0~0~0~0~0~0~0     |] := eq_refl.
  Definition num_test_o_4 : [| 0o"750"11 =koika= Ob~0~0~1~1~1~1~0~1~0~0~0 |] := eq_refl.
  Definition num_test_o_5 : [| 0o"751"3  =koika= Ob~0~0~1                 |] := eq_refl.
  Fail Definition num_test_o_6  := <{ 0o"108"   }> : _action.
  Fail Definition num_test_o_7  := <{ 0o"080"10 }> : _action.
  Fail Definition num_test_o_8  := <{ "f00":o10 }> : _action.
  Fail Definition num_test_o_9  := <{ "00f":o5  }> : _action.
  Fail Definition num_test_o_10 := <{ "":o      }> : _action.

  Definition num_test_d_1 : [| "33":d    =koika= Ob~1~0~0~0~0~1           |] := eq_refl.
  Definition num_test_d_2 : [| "33":d9   =koika= Ob~0~0~0~1~0~0~0~0~1     |] := eq_refl.
  Definition num_test_d_3 : [| "070":d9  =koika= Ob~0~0~1~0~0~0~1~1~0     |] := eq_refl.
  Definition num_test_d_4 : [| 0d"070"   =koika= Ob~1~0~0~0~1~1~0         |] := eq_refl.
  Definition num_test_d_5 : [| 0d"198"11 =koika= Ob~0~0~0~1~1~0~0~0~1~1~0 |] := eq_refl.
  Definition num_test_d_6 : [| 0d"15"3   =koika= Ob~1~1~1                 |] := eq_refl.
  Fail Definition num_test_d_7  := <{ 0d"1a0"   }> : _action.
  Fail Definition num_test_d_8  := <{ 0d"0z0"10 }> : _action.
  Fail Definition num_test_d_9  := <{ "f00":d10 }> : _action.
  Fail Definition num_test_d_10 := <{ "00f":d5  }> : _action.
  Fail Definition num_test_d_11 := <{ "":d      }> : _action.

  Definition num_test_h_1 : [| "fa":h    =koika= Ob~1~1~1~1~1~0~1~0         |] := eq_refl.
  Definition num_test_h_2 : [| "bb":h9   =koika= Ob~0~1~0~1~1~1~0~1~1       |] := eq_refl.
  Definition num_test_h_3 : [| "014":h   =koika= Ob~0~0~0~0~0~0~0~1~0~1~0~0 |] := eq_refl.
  Definition num_test_h_4 : [| 0x"070"   =koika= Ob~0~0~0~0~0~1~1~1~0~0~0~0 |] := eq_refl.
  Definition num_test_h_5 : [| 0x"198"11 =koika= Ob~0~0~1~1~0~0~1~1~0~0~0   |] := eq_refl.
  Definition num_test_h_6 : [| 0x"1d"3   =koika= Ob~1~0~1                   |] := eq_refl.
  Fail Definition num_test_h_7  := <{ 0x"1h0"   }> : _action.
  Fail Definition num_test_h_8  := <{ 0x"0z0"10 }> : _action.
  Fail Definition num_test_h_9  := <{ "g00":h10 }> : _action.
  Fail Definition num_test_h_10 := <{ "00k":h5  }> : _action.
  Fail Definition num_test_h_11 := <{ "":h      }> : _action.
End Tests2.
