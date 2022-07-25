Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.BinPos.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List.
Require Import Coq.Floats.Floats.
Import Coq.Lists.List.ListNotations.
From Wasm Require Import datatypes.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.

Open Scope bool_scope.

Scheme Equality for list.
Scheme Equality for prod.
Scheme Equality for Z.

Definition compile_value_type (t : value_type) : Ctypes.type :=
  match t with
  | T_i32 => Tint I32 Unsigned noattr
  | T_i64 => Tlong Unsigned noattr
  | T_f32 => Tfloat F32 noattr
  | T_f64 => Tfloat F64 noattr
  end.

(*
Definition signed_type (w : width) : Ctypes.type :=
  match w with
  | W32 => Tint I32 Signed noattr
  | W64 => Tlong Signed noattr
  end.
*)

Definition length_Z {A : Set} (l : list A) : Z :=
  Z.of_nat (length l).

Definition stack : Set := list value_type.

Module Type UNIQUE.
  Parameter t : Set.
  Parameter eqb : t -> t -> bool.
End UNIQUE.

Module Unique(Import U : UNIQUE).
  Definition store : Type := list t.
  Fixpoint get_go (i : positive) (x : t) (s : store) : positive * store :=
    match s with
    | nil => (i, cons x nil)
    | cons y s' =>
        if eqb x y
        then (i, s')
        else let (i', s'') := get_go (Pos.succ i) x s'
        in (i', cons y s'')
    end.
  Definition get : t -> store -> positive * store := get_go 1.
End Unique.

Module VarUNIQUE <: UNIQUE.
  Definition t : Set := value_type * Z.
  Definition eqb : t -> t -> bool := prod_beq value_type Z value_type_beq Z_beq.
End VarUNIQUE.

Module VarUnique := Unique(VarUNIQUE).

Definition var (t : value_type) (i : Z) (s : VarUnique.store)
  : Clight.expr * VarUnique.store :=
  let (u, s') := VarUnique.get (t, i) s
  in (Evar u (compile_value_type t), s').

(* TODO: make the conversions between Wasm and Compcert ints cleaner *)
Definition compile_const' (v : value) : Clight.expr * Ctypes.type :=
  (* let t' := compile_value_type t in *)
  match v with
  | VAL_int32 x => let t' := compile_value_type T_i32 in
                  (Econst_int (Integers.Int.mkint (Wasm_int.Int32.intval x) (Wasm_int.Int32.intrange x)) t', t')
  | VAL_int64 x => let t' := compile_value_type T_i64 in
                  (Econst_long (Integers.Int64.mkint (Wasm_int.Int64.intval x) (Wasm_int.Int64.intrange x)) t', t')
  | VAL_float32 x => let t' := compile_value_type T_f32 in
                    (Econst_single x t', t')
  | VAL_float64 x => let t' := compile_value_type T_f64 in
                    (Econst_float x t', t')
  end.

Definition compile_const (v : value) (r : ident) : Clight.statement :=
  let (e, t') := compile_const' v in Sassign (Evar r t') e.

(*
Definition makefun_1 (r : ident) (ef : signature -> external_function) (t : typ)
  (t' : type) (x : ident)
  : Clight.statement :=
  Sbuiltin
    (Some r)
    (ef (AST.mksignature [t] (Tret t) AST.cc_default))
    (Tcons t' Tnil)
    [Evar x t'].

Definition builtin_i32_1 (r : ident) (name : string) (x : ident)
  : Clight.statement :=
  makefun_1 r (EF_builtin name) AST.Tint (Tint I32 Unsigned noattr) x.

Definition builtin_i64_1 (r : ident) (name : string) (x : ident)
  : Clight.statement :=
  makefun_1 r (EF_builtin name) AST.Tlong (Tlong Unsigned noattr) x.

Definition ext_fun_f32_1 (r : ident) (name : string) (x : ident)
  : Clight.statement :=
  makefun_1 r (EF_external name) AST.Tsingle (Tfloat F32 noattr) x.

Definition ext_fun_f64_1 (r : ident) (name : string) (x : ident)
  : Clight.statement :=
  makefun_1 r (EF_external name) AST.Tfloat (Tfloat F64 noattr) x.

Definition unop_helper (t : num_type) (o : Cop.unary_operation) (r : ident) (x : ident)
  : Clight.statement :=
  let t' := compile_value_type (Num t)
  in Sassign (Evar r t') (Eunop o (Evar x t') t').

Definition compile_unop {t: num_type} (o : unop t) (r : ident) (x : ident)
  : Clight.statement :=
  match o with
  | Clz W32 => builtin_i32_1 r "__builtin_clz" x
  | Clz W64 => builtin_i64_1 r "__builtin_clzl" x
  | Ctz W32 => builtin_i32_1 r "__builtin_ctz" x
  | Ctz W64 => builtin_i64_1 r "__builtin_ctzl" x
  | Popcnt W32 => builtin_i32_1 r "__builtin_popcount" x
  | Popcnt W64 => builtin_i64_1 r "__builtin_popcountl" x
  | Abs _ => unop_helper t Oabsfloat r x
  | Neg _ => unop_helper t Oneg r x
  | Sqrt W32 => ext_fun_f32_1 r "sqrtf" x
  | Sqrt W64 => ext_fun_f64_1 r "sqrt" x
  | Ceil W32 => ext_fun_f32_1 r "ceilf" x
  | Ceil W64 => ext_fun_f64_1 r "ceil" x
  | Floor W32 => ext_fun_f32_1 r "floorf" x
  | Floor W64 => ext_fun_f64_1 r "floor" x
  | TruncF W32 => ext_fun_f32_1 r "truncf" x
  | TruncF W64 => ext_fun_f64_1 r "trunc" x
  | Nearest W32 => ext_fun_f32_1 r "roundf" x
  | Nearest W64 => ext_fun_f64_1 r "round" x
  end.

(*
Definition unsigned_of_width (w : width) : Ctypes.type :=
  match w with
  | W32 => uint32_t
  | W64 => uint64_t
  end.

Definition sx_of (s : sx) (w : width) (e : c_expr) :=
  match s with
  | Unsigned => Cast (unsigned_of_width w) e
  | Signed => e
  end.
*)

Definition makefun_2 (r : ident) (ef : signature -> external_function) (t : typ)
  (t' : type) (x : ident) (y : ident)
  : Clight.statement :=
  Sbuiltin
    (Some r)
    (ef (AST.mksignature [t; t] (Tret t) AST.cc_default))
    (Tcons t' Tnil)
    [Evar x t'; Evar y t'].

Definition ext_fun_f32_2 (r : ident) (name : string) (x : ident) (y : ident)
  : Clight.statement :=
  makefun_2 r (EF_external name) AST.Tsingle (Tfloat F32 noattr) x y.

Definition binop_helper (t : num_type) (o : Cop.binary_operation) (r : ident) (x : ident) (y : ident)
  : Clight.statement :=
  let t' := compile_value_type (Num t) in
    Sassign (Evar r t') (Ebinop o (Evar x t') (Evar y t') t').

Definition binop_helper' (s : sx) (w : width) (o : Cop.binary_operation) (r : ident) (x : ident) (y : ident)
  : Clight.statement :=
  match s with
  | Wasm.Unsigned => 
    binop_helper (Int w) o r x y
  | Wasm.Signed =>
    let t' := compile_value_type (Num (Int w)) in
    let ts := signed_type w in
      Sassign (Evar r t') (Ecast (Ebinop o (Ecast (Evar x t') ts) (Ecast (Evar y t') ts) ts) t')
  end.

Definition compile_binop {t : num_type} (o : binop t)
  (r : ident) (x : ident) (y : ident)
  : Clight.statement :=
  match o with
  | Add _ => binop_helper t Oadd r x y
  | Sub _ => binop_helper t Osub r x y
  | Mul _ => binop_helper t Omul r x y
  | DivI s w => binop_helper' s w Odiv r x y
  | DivF _ => binop_helper t Odiv r x y
  | Rem s w => binop_helper' s w Omod r x y
  | And _ => binop_helper t Oand r x y
  | Or _ => binop_helper t Oor r x y
  | Xor _ => binop_helper t Oxor r x y
  | Shl _ => binop_helper t Oshl r x y
  | Shr s w => binop_helper' s w Oshr
  | Rotl _ => FunCall "rotl" [x; y]
  | Rotr _ => FunCall "rotr" [x; y]
  | Min _ => FunCall "min" [x; y]
  | Max _ => FunCall "max" [x; y]
  | Copysign _ => FunCall "copysign" [x; y]
  end.

Definition compile_testop {t : num_type} (o : testop t) (x : c_expr) : c_expr :=
  match o with
  | Eqz _ => BinaryOp Equal x (IntLit 0)
  end.

Definition compile_relop {t : num_type} (o : relop t) (x : c_expr) (y : c_expr)
  : c_expr :=
  match o with
  | Eq _ => BinaryOp Equal x y
  | Ne _ => BinaryOp NotEqual x y
  | LtI s w => BinaryOp Less (sx_of s w x) (sx_of s w y)
  | GtI s w => BinaryOp More (sx_of s w x) (sx_of s w y)
  | LeI s w => BinaryOp LessEq (sx_of s w x) (sx_of s w y)
  | GeI s w => BinaryOp MoreEq (sx_of s w x) (sx_of s w y)
  | LtF _ => BinaryOp Less x y
  | GtF _ => BinaryOp More x y
  | LeF _ => BinaryOp LessEq x y
  | GeF _ => BinaryOp MoreEq x y
  end.

Fixpoint strip_prefix (pre : stack) (s : stack) : option stack :=
  match pre, s with
  | nil, s' => Some s'
  | cons p pre', cons t s' =>
      if value_type_beq p t
      then strip_prefix pre' s'
      else None
  | _, _ => None
  end.

Definition fmap_strip_prefix {A : Set} (pre : stack) (s : stack)
  (f : stack -> A)
  : option A :=
  match strip_prefix pre s with
  | Some s' => Some (f s')
  | None => None
  end.

Definition bind_strip_prefix {A : Set} (pre : stack) (s : stack)
  (f : stack -> option A)
  : option A :=
  match strip_prefix pre s with
  | Some s' => f s'
  | None => None
  end.

Inductive block : Set :=
  | BlockB (_ : fun_type) (_ : Z)
  | IfB (_ : fun_type) (_ : Z)
  | LoopB (_ : fun_type) (_ : Z).

(* the values required when breaking to each block; innermost block on top *)
Definition blocks : Set := list block.

Fixpoint transfer_go (bs : list value_type) (n : Z) (s : stack)
  : option (list c_stmt) :=
  match bs with
  | nil => Some nil
  | cons v bs' =>
      match s with
      | nil => None
      | cons v' s' =>
          if value_type_beq v v'
          then match transfer_go bs' n s' with
               | Some cs =>
                   Some (app cs
                           [Assign (var v (n + length_Z bs')%Z)
                              (var v' (length_Z s'))])
               | None => None
               end
          else None
      end
  end.

Definition transfer (b : block) (s : stack) : option (list c_stmt) :=
  match b with
  | BlockB (Fun _i o) n => transfer_go o n s
  | IfB (Fun _i o) n => transfer_go o n s
  | LoopB (Fun i _o) n => transfer_go i n s
  end.

Definition fmap_transfer {A : Set} (b : block) (s : stack)
  (f : list c_stmt -> A)
  : option A :=
  match transfer b s with
  | Some cs => Some (f cs)
  | None => None
  end.

Fixpoint compile_instrs_go
  (fuel : nat) (is : list instr) (s : stack) (b : blocks)
  : option (list c_stmt * stack) :=
  match fuel with
  | S fuel' =>
    match is with
    | nil => Some (nil, s)
    | cons i is' =>
        match compile_instr fuel' i s b with
        | Some (c, s') =>
            match compile_instrs_go fuel' is' s' b with
            | Some (cs, s'') => Some (app c cs, s'')
            | None => None
            end
        | None => None
        end
    end
  | Z => None
  end

with compile_instr (fuel : nat) (i : instr) (s : stack) (b : blocks)
  : option (list c_stmt * stack) :=
  match fuel with
  | S fuel' =>
    match i with
    | Num_instr i' =>
        match i' with
        | ConstN t v =>
            Some ([Assign (var (Num t) (length_Z s)) (compile_const v)],
                  cons (Num t) s)
        | UnopN t o =>
            fmap_strip_prefix [Num t] s (fun s' => 
              ([Assign (var (Num t) (length_Z s'))
                  (compile_unop o (var (Num t) (length_Z s')))],
               cons (Num t) s'))
        | BinopN t o =>
            fmap_strip_prefix [Num t; Num t] s (fun s' =>
              ([Assign (var (Num t) (length_Z s'))
                  (compile_binop o (var (Num t) (length_Z s'))
                     (var (Num t) (Z.succ (length_Z s'))))],
               cons (Num t) s'))
        | TestopN t o =>
            fmap_strip_prefix [Num t] s (fun s' =>
              ([Assign (var (Num t) (length_Z s'))
                  (compile_testop o (var (Num t) (length_Z s')))],
                cons (Num (Int W32)) s'))
        | RelopN t o => 
            fmap_strip_prefix [Num t] s (fun s' =>
              ([Assign (var (Num t) (length_Z s'))
                  (compile_relop o (var (Num t) (length_Z s'))
                     (var (Num t) (Z.succ (length_Z s'))))],
               cons (Num (Int W32)) s'))
        | CvtopN tf ti o => None (* TODO: casts *)
        end
    | Mem_instr i' =>
        match i' with
        | Load t offset _align =>
            match s with
              | cons (Num (Int W32)) s' =>
                Some ([Assign (var (Num t) (length_Z s'))
                         (Deref
                            (Cast (ptr (compile_value_type (Num t)))
                               (BinaryOp Plus
                                  (var (Num (Int W32)) (length_Z s'))
                                  (IntLit offset))))],
                      (cons (Num t) s'))
            | _ => None
            end
        | Store t offset _align =>
            bind_strip_prefix [Num t] s (fun s' =>
              match s' with
              | cons (Num (Int W32)) s'' =>
                  Some ([Assign
                           (Deref
                              (Cast (ptr (compile_value_type (Num t)))
                                 (BinaryOp Plus
                                    (var (Num (Int W32)) (length_Z s''))
                                    (IntLit offset))))
                           (var (Num t) (length_Z s'))],
                        s'')
              | _ => None
              end)
        end
    | Ctl_instr i' =>
        match i' with
        | Nop => Some ([], s)
        | Block (Fun i o) is =>
            bind_strip_prefix i s (fun s' =>
              match compile_instrs_go fuel' is s
                      (cons (BlockB (Fun i o) (length_Z s)) b) with
              | Some (cs, s'') =>
                  if list_beq value_type value_type_beq (app o s') s''
                  then Some
                         ([DoWhile
                             (cons
                               (C.If (BinaryOp MoreEq (Var "br") (IntLit 0%Z))
                                  [Assign (Var "br")
                                     (BinaryOp Minus (Var "br") (IntLit 1%Z));
                                   Break] [])
                               cs)
                             (IntLit 0%Z);
                           C.If (BinaryOp MoreEq (Var "br") (IntLit 0%Z))
                             [Continue] []],
                          s'')
                  else None
              | None => None
              end)
        | If (Fun i o) thens elses =>
            match s with
            | cons (Num (Int W32)) s'tl =>
                bind_strip_prefix i s'tl (fun s' =>
                  match compile_instrs_go fuel' thens s'tl
                          (cons (IfB (Fun i o) (length_Z s'tl)) b),
                        compile_instrs_go fuel' elses s'tl
                          (cons (IfB (Fun i o) (length_Z s'tl)) b) with
                  | Some (cthens, s''), Some (celses, s''') =>
                      if list_beq value_type value_type_beq (app o s') s''
                      && list_beq value_type value_type_beq (app o s') s'''
                      then Some
                             ([DoWhile
                                 [C.If (BinaryOp MoreEq (Var "br") (IntLit 0%Z))
                                    [Assign (Var "br")
                                       (BinaryOp Minus (Var "br") (IntLit 1%Z));
                                     Break] [];
                                  C.If (var (Num (Int W32)) (length_Z s'tl))
                                    cthens celses]
                                 (IntLit 0%Z);
                               C.If (BinaryOp MoreEq (Var "br") (IntLit 0%Z))
                                 [Continue] []],
                              s'')
                      else None
                  | _, _ => None
                  end)
            | _ => None
            end
        | Loop (Fun i o) is =>
            bind_strip_prefix i s (fun s' =>
              match compile_instrs_go fuel' is s
                      (cons (LoopB (Fun i o) (length_Z s)) b) with
              | Some (cs, s'') =>
                  if list_beq value_type value_type_beq (app o s') s''
                  then Some
                         ([DoWhile
                             (cons
                               (C.If (BinaryOp Equal (Var "br") (IntLit 0%Z))
                                 [Assign (Var "br") (IntLit (-1)%Z)] [])
                               (cons
                                 (C.If (BinaryOp More (Var "br") (IntLit 0%Z))
                                    [Assign (Var "br")
                                       (BinaryOp Minus (Var "br") (IntLit 1%Z));
                                     Break] [])
                                 cs))
                             (IntLit 0%Z);
                           C.If (BinaryOp MoreEq (Var "br") (IntLit 0%Z))
                             [Continue] []],
                          s'')
                  else None
              | _ => None
              end)
        | Br depth =>
            match nth_error b depth with
            | Some bl => fmap_transfer bl s (fun cs => (app cs [Continue], s))
                (* returning s here is *valid* but not the *fully general* type *)
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end
  | Z => None
  end.

Definition compile_instrs (is : list instr)
  : option (list c_stmt * stack) :=
  compile_instrs_go 100 is [] [].

Compute (compile_instrs
           [Num_instr (ConstN (Int W32) (Int32 2%Z));
            Num_instr (ConstN (Int W32) (Int32 3%Z));
            Num_instr (BinopN (Int W32) (Add (Int W32)))]).

Definition example : list instr
  := [Ctl_instr
        (Block
           (Fun [] [Num (Int W32)])
           [Num_instr (ConstN (Int W32) (Int32 2%Z))])].

(*
Lemma foo : compile_instrs example = None.
Proof.
  unfold compile_instrs.
  unfold compile_instrs_go.
  unfold compile_instr.
  simpl.
Admitted.
 *)
            (* Compute (compile_instrs
               [Ctl_instr (Block (Fun [] [Num (Int W32)]) [Num_instr (ConstN (Int W32) (Int32 2%Z))])]). *)
*)
