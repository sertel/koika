type pos_t = Lexing.position
type size_t = int
type ptr_t = int

type bits_const = {
    bs_size: size_t;
    bs_bits: bool list;
  }

type 'prim fun_id_t =
  | CustomFn of string
  | PrimFn of 'prim

type 'prim ffi_signature = {
    ffi_name: 'prim fun_id_t;
    ffi_arg1size: size_t;
    ffi_arg2size: size_t;
    ffi_retsize: size_t
  }

type reg_signature = {
    reg_name: string;
    reg_size: size_t;
    reg_init_val: bits_const;
  }

type var_t = string
type port_t = int

type 'a locd = {
    lpos: Lexing.position;
    lcnt: 'a
  }

type ('reg_t, 'fn_t) expr =
  | Var of var_t
  | Num of int
  | Const of bool list
  | Read of port_t
            * 'reg_t locd
  | Call of 'fn_t locd
            * ('reg_t, 'fn_t) expr locd list

type ('reg_t, 'fn_t) rule =
  | Skip
  | Fail
  | Progn of ('reg_t, 'fn_t) rule locd list
  | Let of (var_t locd * ('reg_t, 'fn_t) expr locd) list
           * ('reg_t, 'fn_t) rule locd list
  | If of ('reg_t, 'fn_t) expr locd
          * ('reg_t, 'fn_t) rule locd
          * ('reg_t, 'fn_t) rule locd list
  | When of ('reg_t, 'fn_t) expr locd
            * ('reg_t, 'fn_t) rule locd list
  | Write of port_t
             * 'reg_t locd
             * ('reg_t, 'fn_t) expr locd

type scheduler =
  | Done
  | Sequence of string locd list
  | Try of string locd * scheduler locd * scheduler locd

type 'fn_t ast =
  | ADone
  | ASequence of (reg_signature, 'fn_t) rule locd list
  | ATry of (reg_signature, 'fn_t) rule locd
            * 'fn_t ast locd
            * 'fn_t ast locd

(* FIXME use a hashmap, not a list *)
type tc_unit =
  { tc_registers: reg_signature list }

type circuit_root = {
    root_reg: reg_signature;
    root_ptr: ptr_t;
  }

type 'prim circuit =
  | CNot of ptr_t
  | CAnd of ptr_t * ptr_t
  | COr of ptr_t * ptr_t
  | CMux of size_t * ptr_t * ptr_t * ptr_t
  | CConst of bits_const (* TODO: keep constants shared? *)
  | CExternal of 'prim ffi_signature * ptr_t * ptr_t
  | CReadRegister of reg_signature
  | CAnnot of size_t * string * ptr_t

let subcircuits = function
  | CNot c -> [c]
  | CAnd (c1, c2) -> [c1; c2]
  | COr (c1, c2) -> [c1; c2]
  | CMux (_sz, s, c1, c2) -> [s; c1; c2]
  | CExternal (_fn, c1, c2) -> [c1; c2]
  | CReadRegister _r -> []
  | CAnnot (_sz, _annot, c) -> [c]
  | CConst _ -> []

module PtrHash =
  struct
    type t = ptr_t
    let equal p1 p2 = p1 = p2
    let hash p = Hashtbl.hash p
  end

module PtrHashtbl = Hashtbl.Make(PtrHash)

let ptrhashtbl_update tbl k v_dflt v_fn =
  PtrHashtbl.replace tbl k
    (v_fn (match PtrHashtbl.find_opt tbl k with
           | Some v -> v
           | None -> v_dflt))

let compute_parents ptr_to_object =
  let ptr_to_parents = PtrHashtbl.create 50 in
  PtrHashtbl.iter (fun _ptr obj ->
      List.iter (fun child ->
          ptrhashtbl_update ptr_to_parents child []
            (fun children -> child :: children))
        (subcircuits obj))
    ptr_to_object;
  ptr_to_parents

exception Error of { epos: pos_t;
                     ekind: [`ParseError | `NameError | `TypeError];
                     emsg: string }
