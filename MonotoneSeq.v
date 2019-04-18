
Require Import MyNotations.
Require Import Peano.
Require Import QArith.
Require Import ZArith.BinInt.
Require Import Lia.
Require Import PreorderEquiv.

Section MonotoneSeq.

  Context {T: Type}.
  Context {Tle : Le T}.

  Instance nat_le : Le nat := Peano.le.

  Definition monotone (f : nat -> T) : Prop :=
    forall n m : nat, n ≤ m -> f n ≤ f m.

  Definition MonotoneSeq := { f : nat -> T | monotone f }.
  
End MonotoneSeq.

Section LeftReals.
  Instance q_le : Le Q := Qle.
  Instance q_equiv : Equiv Q := Qeq.
  Definition LReal := MonotoneSeq.

  Definition Qpos := { q : Q | 0 < q }.

  Definition LRle (x y : LReal)  :=
    forall ϵ : Q, ϵ > 0 -> forall n : nat, exists m : nat, (proj1_sig x) n ≤ (proj1_sig y) m + ϵ .

  Instance LRle_le : Le LReal := LRle.

  Lemma LRle_refl : forall x : LReal, LRle x x.
  Proof.
    unfold LRle ; intros.
    exists n.
    apply Qlt_le_weak.
    rewrite <- Qplus_0_r at 1.
    rewrite Qplus_lt_r.
    assumption.
  Qed.

  Lemma Q_times_two : forall x : Q, x + x = x * inject_Z 2.
  Proof.
    intros. unfold Qplus, Qmult.
    rewrite <- Zmult_plus_distr_r.
    unfold equiv, q_equiv, Qeq.
    simpl. rewrite Zpos_plus_distr.
    rewrite Zpos_mult_morphism.
    rewrite Zpos_mult_morphism.
    ring.
  Qed.

  Lemma LRle_trans : forall x y z, LRle x y -> LRle y z -> LRle x z.
  Proof.
    unfold LRle ; intros.
    set (u := ϵ / (inject_Z 2)).
    assert (ϵ = u + u).
    - unfold u.
      rewrite Q_times_two.
      rewrite Qmult_comm.
      rewrite Qmult_div_r.
      reflexivity.
      unfold inject_Z, Qeq. simpl.
      lia.
    - assert (0 < u).
      unfold u.
      apply Qlt_shift_div_l.
      unfold Qlt, Zlt. simpl. reflexivity.
      rewrite Qmult_0_l. assumption.
      pose proof (H u H3 n) as H.
      destruct H.
      pose proof (H0 u H3 x0) as H0.
      destruct H0.
      exists x1.
      apply Qle_trans with (y := (` y) x0 + u).
      assumption.
      rewrite H2.
      rewrite Qplus_assoc.
      apply Qplus_le_compat.
      assumption.
      apply Qle_refl.
   Qed.

  Definition PO_for_LR : @Preorder LReal LRle :=
    MkPreorder
      LReal
      LRle
      LRle_refl
      LRle_trans.
  Existing Instance PO_for_LR.

  Lemma LR_plus_defined : forall x y : LReal,
      monotone (fun n => ((` x) n + (` y) n)).
  Proof.
    unfold monotone; intros.
    apply Qplus_le_compat.
    apply (proj2_sig x n m H).
    apply (proj2_sig y n m H).
  Qed.

  Definition LR_plus (x y : LReal) : LReal :=
    exist monotone (fun n => (` x) n + (` y) n) (LR_plus_defined x y).

  Instance LR_plus_pomorph2 : POMorphism2 LR_plus.
  Proof.
    apply MkPOMorphism2.
    unfold LR_plus.
    intros.
    unfold "≤", LRle_le, LRle.
    intros. simpl.
    
End LeftReals.
      
      
    
  