Require Import Bool Arith List.
Require Import cpdtlib.CpdtTactics.
Set Implicit Arguments.

Inductive binop: Set := And | Or.

Inductive exp: Set :=
| Const: bool -> exp
| Binop: binop -> exp -> exp -> exp.

Definition binopDenote (b: binop): bool -> bool -> bool :=
  match b with
  | And => andb
  | Or => orb
  end.

Fixpoint expDenote (e: exp): bool :=
  match e with
  | Const b => b
  | Binop op e1 e2 => (binopDenote op) (expDenote e1) (expDenote e2)
  end.

Eval simpl in expDenote (Const false).
Eval simpl in expDenote (Binop And (Const true) (Const false)).
Eval simpl in expDenote (Binop Or (Const false) (Const true)).

Inductive instr: Set :=
| iConst: bool -> instr
| iBinop: binop -> instr.

Definition prog := list instr.
Definition stack := list bool.

Definition instrDenote (i: instr) (s: stack): option stack :=
  match i with
  | iConst b => Some (b :: s)
  | iBinop op =>
    match s with
      | arg1 :: arg2 :: s' => Some ((binopDenote op) arg1 arg2 :: s')
      | _ => None
      end
  end.

Fixpoint progDenote (p: prog) (s: stack): option stack :=
  match p with
  | nil => Some s
  | i :: p' => match instrDenote i s with
    | None => None
    | Some s' => progDenote p' s'
    end
  end.

Fixpoint compile (e: exp): prog :=
  match e with
  | Const b => iConst b :: nil
  | Binop op e1 e2 => compile e2 ++ compile e1 ++ iBinop op :: nil
  end.

Lemma compile_correct_stepwise: forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e; crush.
Qed.

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intros. rewrite (app_nil_end (compile e)). apply compile_correct_stepwise.
Qed.

Inductive type : Set := Nat | Bool | Pair: type -> type -> type.

Inductive tunop : type -> type -> Set :=
| TLeftProj : forall x y, tunop (Pair x y) x
| TRightProj : forall x y, tunop (Pair x y) y. 

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool
| TPair : forall x y, tbinop x y (Pair x y).

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TUnop   : forall t t', tunop t t' -> texp t -> texp t'
| TBinop  : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Pair x y => (prod (typeDenote x) (typeDenote y))
  end.

Fixpoint teqopDenote arg
  : typeDenote arg -> typeDenote arg -> bool :=
  match arg with
  | Nat => beq_nat
  | Bool => eqb
  | Pair x y => let eqx:= teqopDenote x in
                let eqy:= teqopDenote y in
                  fun p1 p2 =>
                    let (x1, y1):= p1 in
                    let (x2, y2):= p2 in
                      andb (eqx x1 x2) (eqy y1 y2)
  end.

Definition tunopDenote arg res (u : tunop arg res)
  : typeDenote arg -> typeDenote res :=
  match u in tunop arg res
    return typeDenote arg -> typeDenote res with
    | TLeftProj _ _ => fun p => let (x, y):= p in x
    | TRightProj _ _ => fun p => let (x, y):= p in y
  end.

Fixpoint tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in tbinop arg1 arg2 res
    return typeDenote arg1 -> typeDenote arg2 -> typeDenote res with
    | TPlus => plus
    | TTimes => mult
    | TEq t => teqopDenote t
    | TLt => leb
    | TPair x y => pair
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TUnop _ _ u e => (tunopDenote u) (texpDenote e)
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Definition tstack := list type.


Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiUnop  : forall arg res s, tunop arg res -> tinstr (arg :: s) (res :: s)
| TiBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiUnop _ _ _ u => fun s => 
      let '(arg, s') := s in
        ((tunopDenote u) arg, s')
    | TiBinop _ _ _ _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TUnop _ _ u e => tconcat (tcompile e _) (TCons (TiUnop _ u) (TNil _))
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.

Extraction tcompile.