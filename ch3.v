Require Import cpdtlib.CpdtTactics.

Inductive unit: Set:= | tt.

Theorem unit_singleton: forall x: unit, x = tt.
Proof.
  induction x.
  reflexivity.
Qed.

Inductive Empty_set: Set:= .

Theorem the_sky_is_falling: forall x: Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

Definition e2u (e: Empty_set): unit := match e with end.

Inductive bool: Set:= true | false.

Definition negb (b: bool): bool:= match b with 
  | true => false
  | false => true
end.

Definition negb' (b: bool) : bool:= if b then false else true.

Theorem negb_inverse: forall b: bool, negb (negb b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq: forall b: bool, negb b <> b.
Proof.
  destruct b; discriminate.
Qed.

Inductive nat: Set:= 
  | O: nat
  | S: nat -> nat.

Definition isZero n: bool:= match n with
  | O => true
  | S _ => false
end.

Definition pred n: nat:= match n with
  | O => O
  | S n' => n'
end.

Fixpoint plus (n m: nat): nat:= 
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem O_plus_n: forall n: nat, plus O n = n.
  intro; reflexivity.
Qed.

Theorem n_plus_O: forall n: nat, plus n O = n.
Proof.
  induction n; crush.
Qed.

Theorem S_inj: forall n m, S n = S m -> n = m.
Proof.
  injection 1; trivial.
Qed.

Inductive nat_list: Set := 
| NNil : nat_list
| NCons: nat -> nat_list -> nat_list.

Fixpoint nlength ns : nat:= match ns with
| NNil => O
| NCons _ ns' => S (nlength ns')
end.

Fixpoint napp (ns1 ns2 : nat_list): nat_list :=
  match ns1 with
  | NNil => ns2
  | NCons n ns1' => NCons n (napp ns1' ns2)
  end.

Theorem nlength_napp: forall ns1 ns2, 
  nlength (napp ns1 ns2) = plus (nlength ns1) (nlength ns2).
Proof.
  induction ns1; crush.
Qed.
