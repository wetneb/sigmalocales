Require Import Coq.Logic.Decidable.

(**
   This follows Chapter 14 (Least Number Search) of
   #<a href="http://www.ps.uni-saarland.de/courses/cl-ss12/script/icl.pdf">Geert Smolka's Introduction to Computational Logic</a>#
  
   The goal is to prove, for any decidable property [P : nat -> Prop], that [(exists n, P n) -> { n : nat | P n }].

 *)

Section LNS.
  Require Import PeanoNat.

  Variable P : nat -> Prop.
  Variable Pdec : forall n, {P n} + { ~ (P n)}.

  Inductive safe (n : nat) : Prop :=
  | safeI : P n -> safe n
  | safeS : safe (S n) -> safe n.

  Definition low (n : nat) :=
    forall k, k <= n -> P k -> k = n.

  Definition min (n : nat) :=
    P n /\ low n.

  Lemma low_S : forall n, low n -> ~(P n) -> low (S n).
  Proof.
    unfold low. intros.
    destruct (proj1 (Nat.le_succ_r _ _) H1).
    (* k <= n *)
    specialize (H k H3 H2). subst.
    destruct (H0 H2).
    (* k = S n *)
    apply H3.
  Qed.

  Fixpoint firstc' (n : nat) (l : low n) (s : safe n) : { m | min m}.
  Proof.
    destruct (Pdec n).
    exact (exist _ n (conj p l)).
    apply firstc' with (n:= S n).
    destruct s.
    destruct (n0 H).
    apply low_S ; assumption.
    destruct s.
    destruct (n0 H).
    assumption.
  Qed.

  Lemma safe_O : forall n, safe n -> safe O.
  Proof.
    induction n. tauto. intro. apply IHn, safeS, H.
  Defined.

  Lemma exists_safe_O : ex P -> safe O.
  Proof.
    intros [n A]. apply (safe_O n). apply (safeI _ A).
  Qed.
  
  Proposition least_witness : (exists n, P n) -> { n : nat | min n}.
  Proof.
    intro.
    apply (firstc' O).
    unfold low. intros. inversion H0. reflexivity.
    apply (exists_safe_O H).
  Qed.

  Proposition some_witness : (exists n, P n) -> { n : nat | P n }.
  Proof.
    intro.
    apply least_witness in H.
    unfold min in H.
    apply (exist P (proj1_sig H)).
    apply (proj2_sig H).
  Defined.
End LNS.
  
Section LNS_Pi2.
  Variable P : nat -> nat -> Prop.
  Variable Pdec : forall n m, {P n m} + { ~ (P n m) }.
  
  Definition search (W : forall n, exists m, P n m) (n : nat) : { m : nat | min (P n) m }.
  Proof.
    apply (least_witness (P n) (Pdec n) (W n)).
  Qed.

End LNS_Pi2.