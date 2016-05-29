Section Bijection_Naturals.


  Require Import Coq.Arith.Wf_nat.
  Require Import ArithLemmas.
  Require Import Lt.
  Require Import Le.
  Require Import Plus.
  Require Import Compare_dec.
  Require Import Coq.Program.Wf.
  
  Definition NN := (nat*nat)%type.
  Definition NpN := (nat + nat)%type.

  (******************************************)
  (* Definition of the bijection N x N -> N *)
  (******************************************)
  
  Fixpoint bijNNp (a b : nat) : nat :=
    match a, b with
      | 0, b => S (b + b)
      | S n, b => 2 * bijNNp n b
    end.

  Definition bijNN (p : NN) : nat := pred (bijNNp (fst p) (snd p)).

  (* bijNNp is positive *)
  Lemma bijNNp_pos : forall a b, 0 < bijNNp a b.
  Proof.
    intros.
    induction a.
    simpl. apply lt_0_Sn.
    simpl.
    apply (lt_plus_trans 0 (bijNNp a b) _ IHa).
  Qed.

  (* caracterization of the image of bijNNp *)
  Lemma bijNNp_carac : forall a b, (bijNNp a b = S (b + b) /\ a = 0) \/ (even (bijNNp a b) /\ bijNNp a b = 2 * bijNNp (pred a) b).
  Proof.
    intros.
    destruct a.

    (* a = 0 *)
    apply or_introl. split. reflexivity. reflexivity.

    (* S a *)
    apply or_intror.
    simpl. split. rewrite <- plus_n_O. apply double_is_even.
    reflexivity.
  Qed.

  (* Lemmas for the termination of the reverse map *)

  Lemma n_le_S_m : forall n m, n < S m -> (n = m) \/ (n < m).
  Proof.
    intros.
    apply lt_le_S in H.
    apply le_S_n in H.
    apply or_comm.
    apply (le_lt_or_eq _ _ H).
  Defined.

  Lemma div2_n_le_n_bi : forall n, div2 (S n) < (S n) /\ div2 (S (S n)) < (S (S n)).
  Proof.
    induction n.
    (* n = 0 *)
    auto.
    (* S n *)
    destruct IHn.
    split. assumption.
    simpl. apply lt_n_S.
    destruct n. auto.
    simpl in H. apply (lt_trans _ (S (S n)) _ H).
    auto.
  Defined.

  Lemma div2_n_le : forall n, div2 (S (S n)) < (S (S n)).
  Proof.
    intro.
    apply div2_n_le_n_bi.
  Defined.

  (* Definition of the reverse map *)
  
  Program Fixpoint bijNN_rev (n : nat) { measure n } : { q : NN | (n = 0) \/ (n = S (bijNN q))} :=
    match n with
      | 0 => (0,0)
      | 1 => (0,0)
      | S (S p) =>
        match even_odd_dec n with
         | left e => let (a,pr) := bijNN_rev (S (div2 p)) in (S (fst a),(snd a))
         | right o => (0, S (div2 p))
        end
    end.
  Obligation 3.
  apply div2_n_le.
  Qed.
  Obligation 4.
  apply or_intror.
  destruct pr as [pr1|pr2].
  inversion pr1.
  apply eq_S.
  inversion pr2.
  specialize (bijNN_rev (S p)).
  destruct bijNN_rev.
  auto.
  destruct o.
  inversion H.
  unfold bijNN. simpl.
  unfold bijNN in H0.
  rewrite <- plus_n_O.
  assert (pred (S p) = pred (pred (bijNNp (fst a) (snd a) + (bijNNp (fst a) (snd a))))).
  simpl.
  rewrite pred_sum.
  rewrite <- H0.
  inversion e. inversion H2.
  rewrite <- double_plus.
  apply (even_double p H4).
  apply bijNNp_pos.
  apply bijNNp_pos.
  simpl in H1.
  rewrite H1.
  rewrite <- (S_pred _ 0).
  reflexivity.
  apply lt_pred.
  apply (plus_le_lt_compat 1 _ 0).
  apply lt_le_S.
  apply bijNNp_pos.
  apply bijNNp_pos.
  Qed.
  Obligation 5.
  apply or_intror.
  apply eq_S.
  specialize (bijNN_rev (S p)).
  destruct bijNN_rev.
  auto.
  destruct o0. inversion H.
  inversion o.
  inversion H1.
  unfold bijNN. simpl.
  apply eq_S.
  rewrite <- plus_n_Sm.
  rewrite <- double_plus.
  apply (odd_double _ H3).
  Qed.

  Definition bijNNinv (n : nat) : NN :=
    match bijNN_rev (S n) with
      | exist a P => a
    end.

Lemma bijNNp_inj : forall x y z w, bijNNp x y = bijNNp z w -> (x,y) = (z,w).
Proof.
  intro x.
  induction x.

  (* x = 0 *)
  induction y.
  
  (* x, y = 0 *)
  intros. simpl in H.
  (* case analysis on z *)
  destruct z.
  (* z = 0 *)
  (* case analysis on w *)
  destruct w.
  reflexivity.
  (* w > 0 *)
  simpl in H. inversion H.
  (* z > 0 *)
  simpl in H.
  assert (bijNNp z w > 0).
  apply bijNNp_pos.
  destruct (bijNNp z w).
  inversion H.
  rewrite plus_Sn_m in H.
  rewrite plus_Sn_m in H.
  rewrite <- plus_n_Sm in H.
  inversion H.

  (* x = 0, y > 0 *)
  intros.
  simpl in H.
  assert ((bijNNp z w = S (w + w) /\ z = 0) \/ (even (bijNNp z w) /\ bijNNp z w = 2 * bijNNp (pred z) w)).
  apply bijNNp_carac.
  (* case analysis on the carac *)
  destruct H0. destruct H0.
  rewrite H1.
  rewrite H0 in H.
  inversion H.
  rewrite <- plus_Sn_m in H3.
  apply double_injective in H3.
  rewrite <- H3.
  reflexivity.
  (* absurd case of the carac *)
  destruct H0.
  rewrite <- H in H0.
  inversion H0.
  rewrite <- plus_Sn_m in H3.
  apply (not_even_and_odd _ (double_is_even (S y))) in H3.
  inversion H3.

  (* x > 0 *)
  intros.
  simpl in H.
  rewrite <- plus_n_O in H.
  (* let's show that bijNNp z w is even and give that to carac *)
  assert ((bijNNp z w = S (w + w) /\ z = 0) \/ (even (bijNNp z w) /\ bijNNp z w = 2 * bijNNp (pred z) w)).
  apply bijNNp_carac.
  destruct H0.
  (* absurd case of the carac *)
  destruct H0.
  assert (odd (bijNNp z w)).
  rewrite H0.
  apply odd_S.
  apply double_is_even.
  assert (even (bijNNp z w)).
  rewrite <- H.
  apply double_is_even.
  apply (not_even_and_odd _ H3) in H2.
  inversion H2.
  (* good case *)
  destruct H0.
  simpl in H1.
  rewrite <- plus_n_O in H1.
  rewrite <- H in H1.
  apply double_injective in H1.
  apply IHx in H1.
  inversion H1.
  (* final case analysis *)
  destruct z.
  (* absurd case *)
  simpl in H0.
  assert (even (w + w)).
  apply double_is_even.
  inversion H0.
  apply (not_even_and_odd _ H2) in H6.
  inversion H6.
  (* good case *)
  reflexivity.
Qed.

Lemma bijNN_inj : forall p q, bijNN p = bijNN q -> p = q.
Proof.
  unfold bijNN.
  intros.
  destruct p, q.
  simpl in H.
  apply pred_inj in H.
  apply bijNNp_inj. apply H.
  apply bijNNp_pos.
  apply bijNNp_pos.
Qed.
  
Theorem bijNN_bijNNinv : forall n, bijNN (bijNNinv n) = n.
Proof.
  intros.
  unfold bijNNinv.
  destruct (bijNN_rev).
  destruct o. inversion H.
  inversion H.
  reflexivity.
Qed.


Theorem bijNNinv_bijNN : forall p, bijNNinv (bijNN p) = p.
Proof.
  intro.
  apply bijNN_inj.
  rewrite bijNN_bijNNinv.
  reflexivity.
Qed.

Proposition bijNN_surj : forall n : nat, exists p : NN, n = bijNN p.
Proof.
  intro.
  exists (bijNNinv n).
  symmetry.
  apply bijNN_bijNNinv.
Qed.

Proposition bijNNinv_surj : forall p : NN, exists n : nat, p = bijNNinv n.
Proof.
  intro.
  exists (bijNN p).
  symmetry.
  apply bijNNinv_bijNN.
Qed.

Proposition bijNNinv_inj : forall x y, bijNNinv x = bijNNinv y -> x = y.
Proof.
  intros.
  rewrite <- bijNN_bijNNinv.
  rewrite <- H.
  rewrite bijNN_bijNNinv.
  reflexivity.
Qed.

(******************************************)
(* Definition of the bijection N + N -> N *)
(******************************************)

Check (nat + nat)%type.
Definition bijNpN (p : NpN) : nat :=
  match p with
    | inl a => double a
    | inr a => S (double a)
  end.

Definition bijNpNinv (x : nat) : NpN :=
  match even_odd_dec x with
    | left e => inl (div2 x)
    | right o => inr (div2 x)
  end.

Theorem bijNpN_bij1 : forall n, bijNpN (bijNpNinv n) = n.
Proof.
  intro.
  unfold bijNpNinv.
  destruct (even_odd_dec n).

  (* n is even *)
  simpl. symmetry.
  apply (even_double _ e).

  (* n is odd *)
  simpl. symmetry.
  apply (odd_double _ o).
Qed.

Theorem bijNpN_bij2 : forall p, bijNpNinv (bijNpN p) = p.
Proof.
  intro.
  unfold bijNpN, bijNpNinv.
  destruct p.

  (* double n *)
  destruct (even_odd_dec (double n)).
  (* good case *)
  rewrite double_2times.
  rewrite div2_double. reflexivity.
  (* absurd case *)
  apply (not_even_and_odd _ (double_is_even n)) in o.
  inversion o.

  (* S (double n) *)
  destruct (even_odd_dec (S (double n))).
  (* absurd case *)
  assert (odd (S (double n))).
  apply odd_S. apply double_is_even.
  contradiction (not_even_and_odd _ e H).
  (* good case *)
  rewrite double_2times.
  rewrite div2_double_plus_one.
  reflexivity.
Qed.



End Bijection_Naturals.

  