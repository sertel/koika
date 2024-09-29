(*! Frontend | Parser for the Kôika EDSL !*)
Require Import
        Koika.Common
        Koika.Syntax
        Koika.IdentParsing.

Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimUntyped.
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

Declare Custom Entry koika.
Declare Custom Entry koika_args.
Declare Custom Entry koika_var.
Declare Custom Entry koika_types.
Declare Custom Entry koika_branches.
Declare Custom Entry koika_consts.
Declare Custom Entry koika_literal.

(* Koika_consts *)
Notation "'1'" := (Ob~1) (in custom koika_consts at level 0).
Notation "'0'" := (Ob~0) (in custom koika_consts at level 0).
Notation "bs '~' '0'" := (Bits.cons false bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (Bits.cons  true bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '1'").

Notation "'Ob' '~' number" :=
  (USugar (UConstBits number))
    (in custom koika at level 7, number custom koika_consts at level 99, format "'Ob' '~' number").

(* koika bit vector literals *)
Require BinaryString OctalString HexString HexadecimalString DecimalString.
Local Ltac eval' expr := let val := eval cbv in expr in exact val.

(* Coq's implementation just silently returns 0 on an invalid string -
  for better error recognition the methods are redefined here returning option *)
Fixpoint num_string_to_option_N' (s : string) (base : N) (convert : Ascii.ascii -> option N) (remainder : option N) : option N :=
  match s with
  | EmptyString => remainder
  | String c s' => num_string_to_option_N' s' base convert (match remainder, convert c with
    | Some rem, Some c_v => Some (N.add (N.mul base rem) c_v)
    | _, _ => None
    end)
  end.
Definition num_string_to_option_N (s : string) (base : N) (convert : Ascii.ascii -> option N) : option N :=
  match s with
  | EmptyString => None
  | String _ _ => num_string_to_option_N' s base convert (Some 0%N)
  end.

Local Definition bin_string_to_N s := (must (num_string_to_option_N s 2 BinaryString.ascii_to_digit)).
Local Definition oct_string_to_N s := (must (num_string_to_option_N s 8 OctalString.ascii_to_digit)).
Local Definition dec_string_to_N s := (must (option_map N.of_uint (DecimalString.NilZero.uint_of_string s))).
Local Definition hex_string_to_N s := (must (num_string_to_option_N s 16 HexString.ascii_to_digit)).

Local Definition len := String.length.

Notation "num ':b' sz" := (Bits.of_N (sz <: nat)                  (bin_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':b'"    := (Bits.of_N ltac:(eval' ((len num) * 1)) (bin_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0b' num sz" := (Bits.of_N (sz <: nat)                  (bin_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, format "'0b' num sz").
Notation "'0b' num"    := (Bits.of_N ltac:(eval' ((len num) * 1)) (bin_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0b' num"    := (Bits.of_N _                            (bin_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, only printing,        format "'0b' num").

Notation "num ':o' sz" := (Bits.of_N (sz <: nat)                  (oct_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':o'"    := (Bits.of_N ltac:(eval' ((len num) * 3)) (oct_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0o' num sz" := (Bits.of_N (sz <: nat)                  (oct_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, format "'0o' num sz").
Notation "'0o' num"    := (Bits.of_N ltac:(eval' ((len num) * 3)) (oct_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0o' num"    := (Bits.of_N _                            (oct_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, only printing,        format "'0o' num").

Notation "num ':d' sz" := (Bits.of_N (sz <: nat)                  (dec_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':d'"    := (Bits.of_N ltac:(eval' (1 + (N.to_nat (N.log2 (dec_string_to_N num)))))
                                                                  (dec_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0d' num sz" := (Bits.of_N (sz <: nat)                  (dec_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, format "'0d' num sz").
Notation "'0d' num"    := (Bits.of_N ltac:(eval' (1 + (N.to_nat (N.log2 (dec_string_to_N num)))))
                                                                  (dec_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0d' num"    := (Bits.of_N _                            (dec_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, only printing,        format "'0d' num").

Notation "num ':h' sz" := (Bits.of_N (sz <: nat)                  (hex_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':h'"    := (Bits.of_N ltac:(eval' ((len num) * 4)) (hex_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0x' num sz" := (Bits.of_N (sz <: nat)                  (hex_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, sz constr at level 0, format "'0x' num sz").
Notation "'0x' num"    := (Bits.of_N ltac:(eval' ((len num) * 4)) (hex_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0,                       only parsing).
Notation "'0x' num"    := (Bits.of_N _                            (hex_string_to_N num)) (in custom koika_literal at level 1, num constr at level 0, only printing,        format "'0x' num").

(* legacy number format *)
Notation "a '`d' b" := (Bits.of_N (a<:nat) b%N) (in custom koika_literal at level 1, a constr at level 0 , b constr at level 0).

(* literal inside koika - wrapped inside Usugar and UConstBits to functio as a uaction *)
Notation "'|' literal '|'" := (USugar (UConstBits literal)) (in custom koika at level 1, literal custom koika_literal at level 200).
(* literal inside constr (normal Coq) - directly usable as [bits n] *)
Notation "'|' literal '|'" := (literal) (at level 10, literal custom koika_literal at level 200).

(* Koika_args *)
Declare Custom Entry koika_middle_args.
Notation "x" := [x] (in custom koika_middle_args at level 0, x custom koika at level 99).
Notation "x ',' y" := (app x y) (in custom koika_middle_args at level 1, x custom koika_middle_args, y custom koika_middle_args, right associativity).

Notation "'()'"  := nil (in custom koika_args).
(* Notation "'( )'"  := nil (in custom koika_args). *)
Notation "'(' x ')'"  := x (in custom koika_args, x custom koika_middle_args).
(* Koika_var *)
Notation "a" := (ident_to_string a) (in custom koika_var at level 0, a constr at level 0, only parsing).
Notation "a" := (a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'", only printing).

(* Koika_types *)
Notation " '(' x ':' y ')'" := (cons (prod_of_argsig {| arg_name := x%string; arg_type := y |}) nil) (in custom koika_types at level 60, x custom koika_var at level 0, y constr at level 12 ).
Notation "a  b" := (app a b)  (in custom koika_types at level 95, a custom koika_types , b custom koika_types, right associativity).

(* Koika_branches *)
Notation "x '=>' a " := (cons (x,a) nil) (in custom koika_branches at level 60, x custom koika at level 99, a custom koika at level 99).
Notation "arg1 '|' arg2" := (app arg1 arg2) (in custom koika_branches at level 13, arg1 custom koika_branches, arg2 custom koika_branches, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

(* Koika *)
Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").

Notation "'fail'" :=
  (UFail (bits_t 0)) (in custom koika at level 1, format "'fail'").
Notation "'fail' '(' t ')'" :=
  (UFail (bits_t t)) (in custom koika at level 1, t constr at level 0, format "'fail' '(' t ')'").
Notation "'fail' '@(' t ')'" :=
  (UFail t)          (in custom koika at level 1, t constr at level 0 ,format "'fail' '@(' t ')'").
Notation "'pass'"  := (USugar (UConstBits Ob)) (in custom koika at level 1).
Notation "'magic'" := (USugar UErrorInAst    ) (in custom koika at level 1).

Notation "'let' a ':=' b 'in' c" := (UBind a b c) (in custom koika at level 91, a custom koika_var at level 1, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a ';' b" := (USeq a b) (in custom koika at level 90, format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" := (UAssign a b) (in custom koika at level 89, a custom koika_var at level 1, format "'set'  a  ':='  b").
Notation "'(' a ')'" := (a) (in custom koika at level 1, a custom koika, format "'[v' '(' a ')' ']'").

Notation "instance  '.(' method ')' args" :=
  (USugar (UCallModule instance _ method args))
    (in custom koika at level 1, instance constr at level 0, method constr, args custom koika_args at level 99).
Notation "'{' method '}' args" :=
  (USugar (UCallModule id _ method args))
    (in custom koika at level 1, method constr at level 200 , args custom koika_args at level 99, only parsing).
Notation "method args" :=
  (USugar (UCallModule id _ method args))
    (in custom koika at level 1, method constr at level 0 , args custom koika_args at level 99, only parsing).

Notation "a" := (UVar (ident_to_string a)) (in custom koika at level 1, a constr at level 0, only parsing).
Notation "a" := (UVar a) (in custom koika at level 1, a constr at level 0, only printing).

Notation "'read0' '(' reg ')' "           := (URead P0 reg)        (in custom koika at level 1, reg constr at level 13, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' "           := (URead P1 reg)        (in custom koika at level 1, reg constr at level 13, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" := (UWrite P0 reg value) (in custom koika at level 1, reg constr at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" := (UWrite P1 reg value) (in custom koika at level 1, reg constr at level 13, format "'write1' '(' reg ',' value ')'").

Notation "'if' a 'then' t 'else' f" := (UIf a t                                        f                       ) (in custom koika at level 86, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'if'' a 'then' t"         := (UIf a t                                        (USugar (UConstBits Ob))) (in custom koika at level 86, right associativity, format "'[v' 'if''  a '/' 'then'  t ']'").
Notation "'guard' '(' a ')' "       := (UIf (UUnop (UBits1 UNot) a) (UFail (bits_t 0)) (USugar (UConstBits Ob))) (in custom koika at level 86, right associativity, format "'guard' '(' a ')'").
Notation "'when' a 'do' t "         := (UIf a t                                        (USugar (UConstBits Ob))) (in custom koika at level 91, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "'zeroExtend(' a ',' b ')'" := (UUnop (UBits1 (UZExtL b)) a) (in custom koika at level 1, b constr at level 0, format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'"       := (UUnop (UBits1 (USExt b))  a) (in custom koika at level 1, b constr at level 0, format "'sext(' a ',' b ')'").
Notation "'ignore(' a ')'"           := (UUnop (UConv UIgnore)     a) (in custom koika at level 1, a custom koika).
Notation "'pack(' a ')'"             := (UUnop (UConv UPack)       a) (in custom koika at level 1, a custom koika).
Notation "'unpack(' t ',' v ')'"     := (UUnop (UConv (UUnpack t)) v) (in custom koika at level 1, t constr at level 11, v custom koika).

Notation "a  '||'  b"         := (UBinop (UBits2 UOr)                  a b) (in custom koika at level 85).
Notation "a  '^'  b"          := (UBinop (UBits2 UXor)                 a b) (in custom koika at level 85).
Notation "a  '+'  b"          := (UBinop (UBits2 UPlus)                a b) (in custom koika at level 85).
Notation "a  '-'  b"          := (UBinop (UBits2 UMinus)               a b) (in custom koika at level 85).
Notation "a  '*'  b"          := (UBinop (UBits2 UMul)                 a b) (in custom koika at level 84).
Notation "a  '++'  b"         := (UBinop (UBits2 UConcat)              a b) (in custom koika at level 80,  right associativity).
Notation "a  '&&'  b"         := (UBinop (UBits2 UAnd)                 a b) (in custom koika at level 80,  right associativity).
Notation "a  '!='  b"         := (UBinop (UEq    true)                 a b) (in custom koika at level 79).
Notation "a  '=='  b"         := (UBinop (UEq    false)                a b) (in custom koika at level 79).
Notation "a  '>>'  b"         := (UBinop (UBits2 ULsr)                 a b) (in custom koika at level 79).
Notation "a  '>>>'  b"        := (UBinop (UBits2 UAsr)                 a b) (in custom koika at level 79).
Notation "a  '<<'  b"         := (UBinop (UBits2 ULsl)                 a b) (in custom koika at level 79).
Notation "a  '<'  b"          := (UBinop (UBits2 (UCompare false cLt)) a b) (in custom koika at level 79).
Notation "a  '<s'  b"         := (UBinop (UBits2 (UCompare true cLt))  a b) (in custom koika at level 79).
Notation "a  '<='  b"         := (UBinop (UBits2 (UCompare false cLe)) a b) (in custom koika at level 79).
Notation "a  '<s='  b"        := (UBinop (UBits2 (UCompare true cLe))  a b) (in custom koika at level 79).
Notation "a  '>'  b"          := (UBinop (UBits2 (UCompare false cGt)) a b) (in custom koika at level 79).
Notation "a  '>s'  b"         := (UBinop (UBits2 (UCompare true cGt))  a b) (in custom koika at level 79).
Notation "a  '>='  b"         := (UBinop (UBits2 (UCompare false cGe)) a b) (in custom koika at level 79).
Notation "a  '>s='  b"        := (UBinop (UBits2 (UCompare true cGe))  a b) (in custom koika at level 79).
Notation "'!' a"              := (UUnop  (UBits1 UNot)                 a  ) (in custom koika at level 75, format "'!' a").
Notation "a '[' b ']'"        := (UBinop (UBits2 USel)                 a b) (in custom koika at level 75, format "'[' a [ b ] ']'").
Notation "a '[' b ':+' c ']'" := (UBinop (UBits2 (UIndexedSlice c))    a b) (in custom koika at level 75, c constr at level 0, format "'[' a [ b ':+' c ] ']'").
Notation "'`' a '`'" := (a) (in custom koika at level 99, a constr at level 99).

Notation "'fun' nm args ':' ret '=>' body" :=
  {| int_name := nm%string;
     int_argspec := args;
     int_retSig := ret;
     int_body := body |}
    (in custom koika at level 99, nm custom koika_var at level 0, args custom koika_types, ret constr at level 0, body custom koika at level 99, format "'[v' 'fun'  nm  args  ':'  ret  '=>' '/' body ']'").
Notation "'fun' nm '()' ':' ret '=>' body" :=
  {| int_name := nm%string;
     int_argspec := nil;
     int_retSig := ret;
     int_body := body |}
    (in custom koika at level 99, nm custom koika_var at level 0, ret constr at level 0, body custom koika at level 99, format "'[v' 'fun'  nm  '()'   ':'  ret  '=>' '/' body ']'").

(* Deprecated *)
Notation "'call' instance method args"  := (USugar (UCallModule instance _ method args)) (in custom koika at level 99, instance constr at level 0, method constr at level 0, args custom koika_args).
Notation "'funcall' method args"        := (USugar (UCallModule id _ method args))       (in custom koika at level 98, method   constr at level 0, args custom koika_args).
Notation "'extcall' method '(' arg ')'" := (UExternalCall method arg)                    (in custom koika at level 98, method   constr at level 0, arg custom koika).
Notation "'call0' instance method "     := (USugar (UCallModule instance _ method nil))  (in custom koika at level 98, instance constr at level 0, method constr).
Notation "'funcall0' method "           := (USugar (UCallModule id _ method nil))        (in custom koika at level 98, method   constr at level 0).

Notation "'get' '(' v ',' f ')'"                    := (UUnop  (UStruct1 (UGetField           f)) v)   (in custom koika at level 1,                       v custom koika at level 13,                             f custom koika_var at level 0, format "'get' '(' v ','  f ')'").
Notation "'getbits' '(' t ',' v ',' f ')'"          := (UUnop  (UStruct1 (UGetFieldBits     t f)) v)   (in custom koika at level 1, t constr at level 11, v custom koika at level 13,                             f custom koika_var at level 0, format "'getbits' '(' t ','  v ','  f ')'").
Notation "'subst' '(' v ',' f ',' a ')'"            := (UBinop (UStruct2 (USubstField         f)) v a) (in custom koika at level 1,                       v custom koika at level 13, a custom koika at level 13, f custom koika_var at level 0, format "'subst' '(' v ','  f ',' a ')'").
Notation "'substbits' '(' t ',' v ',' f ',' a ')'"  := (UBinop (UStruct2 (USubstFieldBits   t f)) v a) (in custom koika at level 1, t constr at level 11, v custom koika at level 13, a custom koika at level 13, f custom koika_var at level 0, format "'substbits' '(' t ','  v ','  f ',' a ')'").

Notation "'aref' '(' v ',' f ')'"                   := (UUnop  (UArray1  (UGetElement         f)) v)   (in custom koika at level 1,                       v custom koika at level 13,                             f constr at level 0,           format "'aref' '(' v ','  f ')'").
Notation "'arefbits' '(' t ',' v ',' f ')'"         := (UUnop  (UArray1  (UGetElementBits   t f)) v)   (in custom koika at level 1, t constr at level 11, v custom koika at level 13,                             f constr at level 0,           format "'arefbits' '(' t ','  v ','  f ')'").
Notation "'asubst' '(' v ',' f ',' a ')'"           := (UBinop (UArray2  (USubstElement       f)) v a) (in custom koika at level 1,                       v custom koika at level 13, a custom koika at level 13, f constr at level 0,           format "'asubst' '(' v ','  f ',' a ')'").
Notation "'asubstbits' '(' t ',' v ',' f ',' a ')'" := (UBinop (UArray2  (USubstElementBits t f)) v a) (in custom koika at level 1, t constr at level 11, v custom koika at level 13, a custom koika at level 13, f constr at level 0,           format "'asubstbits' '(' t ','  v ','  f ',' a ')'"). 

Declare Custom Entry koika_structs_init.
(* struct instantiation in koika *)
Notation "f ':=' expr" := (cons (f,expr) nil) (in custom koika_structs_init at level 20, f custom koika_var at level 0, expr custom koika at level 88).
Notation "a ';' b" := (app a b) (in custom koika_structs_init at level 91, a custom koika_structs_init).
Notation "'struct' structtype '{' fields '}'" :=
  (USugar (UStructInit structtype fields)) (in custom koika at level 1, structtype constr at level 0, fields custom koika_structs_init at level 92).
Notation "'struct' structtype '{' '}'" :=
  (USugar (UStructInit structtype [])) (in custom koika at level 1, structtype constr at level 0).

(* create struct literals in constr (normal Coq) *)
(* using Ltac to defer the typechecking until the term is fully constructed *)
Local Ltac struct_init_from_list sig l :=
  lazymatch l with
  | cons ?field ?l' => let acc := struct_init_from_list sig l' in
    constr:(BitFuns.subst_field sig.(struct_fields) (acc) (must (List_assoc (fst field) sig.(struct_fields))) (snd field))
  | nil => constr:((value_of_bits Bits.zero) : struct_t sig)
  end.

Declare Custom Entry koika_structs_init_constr.

Notation "f ':=' expr" := (pair f expr)
  (in custom koika_structs_init_constr at level 0, f custom koika_var at level 0, expr constr at level 10).
Notation "a1 ';' .. ';' an" := (cons a1 .. (cons an nil) ..)
  (in custom koika_structs_init_constr at level 1, a1 custom koika_structs_init_constr at level 0, an custom koika_structs_init_constr at level 0).

Notation "'struct' structtype '<' '>'" :=
  (value_of_bits Bits.zero : (struct_t structtype)) (at level 0, structtype constr at level 0).
Notation "'struct' structtype '<' fields '>'" :=
  (ltac:(let e := struct_init_from_list structtype fields in exact e) : (struct_t structtype)) (at level 0, structtype constr at level 0, fields custom koika_structs_init_constr at level 200, only parsing).

(* enums in koika *)
Notation "'enum' enum_type '{' f '}'" :=
  (USugar (UConstEnum enum_type f))
    (in custom koika at level 1, enum_type constr at level 1, f custom koika_var at level 1).

(* creating enums literal in constr (normal Coq) *)
Notation "'enum' enum_type '<' f '>'" :=
  ((vect_nth enum_type.(enum_bitpatterns)) (must (vect_index f enum_type.(enum_members))))
    (at level 0, enum_type constr at level 1, f custom koika_var at level 1).

Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (UBind "__reserved__matchPattern" var (USugar (USwitch (UVar "__reserved__matchPattern") default branches)))
    (in custom koika at level 30,
        var custom koika,
        branches custom koika_branches,
        default custom koika at level 99,
        format "'match'  var  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

Notation "'#' s" := (USugar (UConstBits s)) (in custom koika at level 98, s constr at level 0, only parsing).


Notation "r '|>' s" :=
  (Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Done (at level 99).

Module Type Tests.
  Parameter pos_t : Type.
  Parameter fn_name_t : Type.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Notation uaction reg_t := (uaction pos_t string fn_name_t reg_t ext_fn_t).
  Definition test_2 : uaction reg_t := {{ yo; yoyo }}.
  Definition test_3 : uaction reg_t := {{ set  yoyo := `UVar "magic" : uaction reg_t`  }}.
  Definition test_1 : uaction reg_t := {{ let yoyo := fail(2) in magic }}.
  Definition test_1' : uaction reg_t := {{ let yoyo := fail(2) in yoyo }}.
  Definition test_2' : uaction reg_t := {{ magic; magic }}.
  Definition test_3' : uaction reg_t := {{ set yoyo := magic ; magic }}.
  Definition test_4 : uaction reg_t := {{ magic ; set yoyo := magic }}.
  Definition test_5 : uaction reg_t := {{ let yoyo := set yoyo := magic in magic }}.
  Definition test_6 : uaction reg_t := {{ let yoyo := set yoyo := magic; magic in magic;magic }}.
  Definition test_7 : uaction reg_t := {{ (let yoyo := (set yoyo := magic); magic in magic;magic) }}.
  Definition test_8 : uaction reg_t := {{ (let yoyo := set yoyo := magic; magic in magic);magic }}.
  Inductive test : Set := |rData (n:nat).
  Axiom data0 : reg_t.
  Axiom data1 : reg_t.
  Definition test_9 : uaction reg_t := {{ read0(data0) }}.
  Definition test_10 : nat -> uaction test := (fun idx => {{ read0(rData idx) }}).
  Definition test_11 : uaction reg_t := {{ (let yoyo := read0(data0) in write0(data0, magic)); fail }}.
  Definition test_12 : uaction reg_t := {{ (let yoyo := if fail then read0(data0) else fail in write0(data0,magic));fail }}.
  Definition test_13 : uaction reg_t := {{ yoyo }}.
  Definition test_14 : uaction reg_t := {{ !yoyo && yoyo }}.
  Definition test_14' : uaction reg_t := {{ !(yoyo && yoyo) }}.
  Goal test_14 <> test_14'. compute; congruence. Qed.
  Definition test_15 : uaction reg_t := {{ yoyo && read0(data0) }}.
  Definition test_16 : uaction reg_t := {{ !read0(data1) && !read0(data1) }}.
  Definition test_17 : uaction reg_t := {{ !read0(data1) && magic}}.
  Definition test_18 : uaction reg_t := {{ !read0(data1) && Yoyo }}.
  Definition test_19 : uaction reg_t := {{ yoy [ oio && ab ] && Ob~1~0 }}.
  Definition test_20 : uaction reg_t := {{ yoyo [ magic :+ 3 ] && yoyo }}.
  Definition test_20' : uaction reg_t := {{ (yoyo [ magic :+ 3]  ++ yoyo) && yoyo }}.
  Definition test_20'' : uaction reg_t := {{ ( yoyo [ magic :+ 3 ] ++ yoyo ++bla) && yoyo }}.

  (* Notation "'{&' a '&}'" := (a) (a custom koika_types at level 200). *)
  (* Definition test_21 := {& "yoyo" : bits_t 2 &}. *)
  (* Definition test_22 := {& "yoyo" : bits_t 2 , "yoyo" : bits_t 2  &}. *)
  Definition test_23 : InternalFunction string string (uaction reg_t) := {{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => magic }}.
  Definition test_24 : nat -> InternalFunction string string (uaction reg_t) :=  (fun sz => {{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => magic}}).
  Definition test_25 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => {{fun test (arg1 : bits_t sz ) : bits_t sz => let oo := magic >> magic in magic}}).
  Definition test_26 : nat -> InternalFunction string string (uaction reg_t) := (fun sz => {{ fun test () : bits_t sz  => magic }}).
  Definition test_27 : uaction reg_t :=
    {{
        (if (!read0(data0)) then
           write0(data0, Ob~1);
             let yo := if (dlk == Ob~1 ) then bla else yoyo || foo
             in
             write0(data0, Ob~1)
         else
           read0(data0));
        fail
    }}.
  Definition test_28 : uaction reg_t :=  {{
                                             match var with
                                             | magic => magic
                                             return default: magic
                                             end
                                         }}.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := cons ("type", bits_t 1) nil |}.

  Definition test_30'' : uaction reg_t :=
    {{
      struct mem_req { foo := upu[#(Bits.of_nat 3 0) :+ 2] ;
                       bar := |32`d98| }
    }}.

  Definition test_31'' : uaction reg_t :=
    {{
        pack(a)
    }}.

  Definition test_31' : uaction reg_t :=
    {{
      let a := struct mem_req { foo := upu[#(Bits.of_nat 3 0) :+ 2] ;
                               bar := |32`d98| } in
        unpack(struct_t mem_req, pack(a))
    }}.
  
  Local Notation ua := (uaction reg_t).
  Notation "'[|' a '=koika=' b '|]'" := ((a : ua) = (b : ua)) (at level 0, a custom koika at level 200, b custom koika at level 200).

  (* sequences in match statements without paranthesis *)
  Definition test_32 : [|
    match |5`d10| with
    | |5`d10| => (
      write0(data0, x);
      x
    )
    | |5`d 9| => (
      x
    )
    return default: fail
    end
  =koika=
    match |5`d10| with
    | |5`d10| =>
      write0(data0, x);
      x
    | |5`d 9| =>
      x
    return default: fail
    end
  |] := eq_refl.

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
    if' Ob~1 then
      pass;
    pass
  =koika=
    (if' Ob~1 then
      pass);
    pass
  |] := eq_refl.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  (* Accessing enum constants *)
  Definition enum_test_1 := enum numbers_e < ONE >.
  Definition enum_test_2 := enum numbers_e < TWO >.
  Definition enum_test_3 :  enum numbers_e < ONE >   = |"001":b| := eq_refl.
  Definition enum_test_4 :  enum numbers_e < TWO >   = |"010":b| := eq_refl.
  Definition enum_test_5 :  enum numbers_e < THREE > = |"011":b| := eq_refl.
  Definition enum_test_6 :  enum numbers_e < IDK >   = |"111":b| := eq_refl.

  Definition numbers_s := {|
    struct_name:= "some_s";
    struct_fields :=
    [ ("one"  , bits_t 3);
      ("two"  , bits_t 3);
      ("three", bits_t 3);
      ("four" , bits_t 3);
      ("five" , enum_t numbers_e) ]
  |}.
  Definition struct_test_1 := struct numbers_s < >.
  Definition struct_test_2 :  struct numbers_s < > = value_of_bits Bits.zero := eq_refl.
  Definition struct_test_3 := struct numbers_s < one := |"010":b| >.
  Definition struct_test_4 :  struct numbers_s < one := |"010":b| ; two := |"111":b| > = (Ob~0~1~0, (Ob~1~1~1, (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, tt))))) := eq_refl.
  Definition struct_test_5 :  struct numbers_s < five := enum numbers_e < IDK > >      = (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, (Ob~1~1~1, tt))))) := eq_refl.
  Fail Definition struct_test_6 := struct numbers_s < five := enum numbers_e < WRONG > >.
  Fail Definition struct_test_7 := struct numbers_s < one := Bits.of_N 9 3 >.
  Fail Definition struct_test_8 := struct numbers_s < wrong := Bits.of_N 3 3 >.

  Definition num_test_b_1 : [| |"01101":b|       =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Definition num_test_b_2 : [| |0b"00011"|       =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_3 : [| |"11":b5|         =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_4 : [| |0b"10"5|         =koika= Ob~0~0~0~1~0 |] := eq_refl.
  Definition num_test_b_5 : [| |0b"10010110"3|   =koika= Ob~1~1~0     |] := eq_refl.
  Fail Definition num_test_b_6  := {{ |0b"102"|  }} : ua.
  Fail Definition num_test_b_7  := {{ |0b"10f"6| }} : ua.
  Fail Definition num_test_b_8  := {{ |"f0":b5|  }} : ua.
  Fail Definition num_test_b_9  := {{ |"f0":b|   }} : ua.
  Fail Definition num_test_b_10 := {{ |"":b|     }} : ua.

  Definition num_test_o_1 : [| |"330":o|   =koika= Ob~0~1~1~0~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_2 : [| |"070":o9|  =koika= Ob~0~0~0~1~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_3 : [| |0o"000"|   =koika= Ob~0~0~0~0~0~0~0~0~0     |] := eq_refl.
  Definition num_test_o_4 : [| |0o"750"11| =koika= Ob~0~0~1~1~1~1~0~1~0~0~0 |] := eq_refl.
  Definition num_test_o_5 : [| |0o"751"3|  =koika= Ob~0~0~1                 |] := eq_refl.
  Fail Definition num_test_o_6  := {{ |0o"108"|   }} : ua.
  Fail Definition num_test_o_7  := {{ |0o"080"10| }} : ua.
  Fail Definition num_test_o_8  := {{ |"f00":o10| }} : ua.
  Fail Definition num_test_o_9  := {{ |"00f":o5|  }} : ua.
  Fail Definition num_test_o_10 := {{ |"":o|      }} : ua.

  Definition num_test_d_1 : [| |"33":d|    =koika= Ob~1~0~0~0~0~1           |] := eq_refl.
  Definition num_test_d_2 : [| |"33":d9|   =koika= Ob~0~0~0~1~0~0~0~0~1     |] := eq_refl.
  Definition num_test_d_3 : [| |"070":d9|  =koika= Ob~0~0~1~0~0~0~1~1~0     |] := eq_refl.
  Definition num_test_d_4 : [| |0d"070"|   =koika= Ob~1~0~0~0~1~1~0         |] := eq_refl.
  Definition num_test_d_5 : [| |0d"198"11| =koika= Ob~0~0~0~1~1~0~0~0~1~1~0 |] := eq_refl.
  Definition num_test_d_6 : [| |0d"15"3|   =koika= Ob~1~1~1                 |] := eq_refl.
  Fail Definition num_test_d_7  := {{ |0d"1a0"|   }} : ua.
  Fail Definition num_test_d_8  := {{ |0d"0z0"10| }} : ua.
  Fail Definition num_test_d_9  := {{ |"f00":d10| }} : ua.
  Fail Definition num_test_d_10 := {{ |"00f":d5|  }} : ua.
  Fail Definition num_test_d_11 := {{ |"":d|      }} : ua.

  Definition num_test_h_1 : [| |"fa":h|    =koika= Ob~1~1~1~1~1~0~1~0         |] := eq_refl.
  Definition num_test_h_2 : [| |"bb":h9|   =koika= Ob~0~1~0~1~1~1~0~1~1       |] := eq_refl.
  Definition num_test_h_3 : [| |"014":h|   =koika= Ob~0~0~0~0~0~0~0~1~0~1~0~0 |] := eq_refl.
  Definition num_test_h_4 : [| |0x"070"|   =koika= Ob~0~0~0~0~0~1~1~1~0~0~0~0 |] := eq_refl.
  Definition num_test_h_5 : [| |0x"198"11| =koika= Ob~0~0~1~1~0~0~1~1~0~0~0   |] := eq_refl.
  Definition num_test_h_6 : [| |0x"1d"3|   =koika= Ob~1~0~1                   |] := eq_refl.
  Fail Definition num_test_h_7  := {{ |0x"1h0"|   }} : ua.
  Fail Definition num_test_h_8  := {{ |0x"0z0"10| }} : ua.
  Fail Definition num_test_h_9  := {{ |"g00":h10| }} : ua.
  Fail Definition num_test_h_10 := {{ |"00k":h5|  }} : ua.
  Fail Definition num_test_h_11 := {{ |"":h|      }} : ua.

  Definition num_test_constr_1 := |"0110":b|     : bits _.
  Definition num_test_constr_2 := |0b"0110"|     : bits _.
  Definition num_test_constr_3 := |"c0ffee":h|   : bits _.
  Definition num_test_constr_4 := |0x"deadbeef"| : bits _.
End Tests.
