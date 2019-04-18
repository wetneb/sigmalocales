
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

  Definition Qhalf x : Q := x / inject_Z 2.

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

  Lemma Qhalf_split : forall x : Q, Qhalf x + Qhalf x = x.
  Proof.
    intros. unfold Qhalf.
    rewrite Q_times_two.
    rewrite Qmult_comm.
    rewrite Qmult_div_r.
    reflexivity.
    unfold inject_Z.
    unfold Qeq. simpl.
    lia.
  Qed.

  Lemma Qhalf_pos : forall x, x > 0 -> Qhalf x > 0.
  Proof.
    unfold Qhalf.
    intros.
    apply Qlt_shift_div_l.
    unfold Qlt, Zlt. simpl. reflexivity.
    rewrite Qmult_0_l. assumption.
  Qed.

  Lemma LRle_trans : forall x y z, LRle x y -> LRle y z -> LRle x z.
  Proof.
    unfold LRle ; intros.
    set (u := Qhalf ϵ).
    pose proof (Qhalf_split ϵ) as Hsplit.
    - assert (0 < u).
      apply Qhalf_pos. assumption.
      pose proof (H u H2 n) as H.
      destruct H.
      pose proof (H0 u H2 x0) as H0.
      destruct H0.
      exists x1.
      apply Qle_trans with (y := (` y) x0 + u).
      assumption.
      rewrite <- Hsplit.
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
  Instance LRequiv : Equiv LReal := Feq.

  Lemma LRplus_defined : forall x y : LReal,
      monotone (fun n => ((` x) n + (` y) n)).
  Proof.
    unfold monotone; intros.
    apply Qplus_le_compat.
    apply (proj2_sig x n m H).
    apply (proj2_sig y n m H).
  Qed.

  Definition LRplus (x y : LReal) : LReal :=
    exist monotone (fun n => (` x) n + (` y) n) (LRplus_defined x y).

  Instance LRplus_pomorph2 : POMorphism2 LRplus.
  Proof.
    apply MkPOMorphism2.
    unfold LRplus, "≤", LRle_le, LRle.
    intros. simpl.
    set (u := Qhalf ϵ).
    assert (0 < u).
    apply (Qhalf_pos ϵ H1).
    pose proof (H u H2 n) as H.
    destruct H.
    pose proof (H0 u H2 n) as H0.
    destruct H0.
    set (p := max x0 x1).
    pose proof (Max.le_max_l x0 x1) as M1.
    pose proof (Max.le_max_r x0 x1) as M2.
    pose proof (proj2_sig y x0 p M1) as x0_p.
    pose proof (proj2_sig b x1 p M2) as x1_p.
    exists p.
    rewrite <- (Qhalf_split ϵ).
    rewrite <- Qplus_le_l with (z := u) in x0_p.
    rewrite <- Qplus_le_l with (z := u) in x1_p.
    pose proof (Qle_trans _ _ _ H x0_p).
    pose proof (Qle_trans _ _ _ H0 x1_p).
    rewrite Qplus_assoc.
    apply (Qplus_le_compat _ _ _ _ H3) in H4.
    rewrite Qplus_assoc in H4.
    rewrite (Qplus_comm _ ((` b) p)) in H4.
    rewrite Qplus_assoc in H4.
    unfold u in H4.
    rewrite (Qplus_comm ((`y) p)).
    assumption.
  Qed.

  Instance LRplus_plus : Plus LReal := LRplus.

  Lemma Q_to_LR_def (x : Q) : monotone (fun n => x).
  Proof.
    unfold monotone; intros.
    apply Qle_refl.
  Qed.

  Definition Q_to_LR (x : Q) :=
    exist monotone (fun n => x) (Q_to_LR_def x).

  Instance Q_to_LR_pomorph : POMorphism Q_to_LR.
  Proof.
    apply MkPOMorphism.
    unfold Q_to_LR, "≤", LRle_le, LRle; intros. simpl.
    exists n.
    apply Qlt_le_weak.
    rewrite Qplus_comm.
    rewrite <- (Qplus_0_l x).
    apply Qplus_lt_le_compat ; assumption.
  Qed.

  Definition LRzero : LReal := Q_to_LR 0.
  Instance LRzero_zero : Zero LReal := LRzero.

  Lemma LRplus_0_l : forall x : LReal, LRplus LRzero x = x.
  Proof.
    unfold LRplus, LRzero, "=", LRequiv, Feq, "≤", LRle_le, LRle. intros.
    simpl. split ; intros ; exists n ; rewrite Qplus_0_l ;
             apply Qlt_le_weak ; rewrite Qplus_comm ;
               rewrite <- (Qplus_0_l ((`x) n)) at 1 ;
               apply Qplus_lt_le_compat.
    assumption.
    apply Qle_refl.
    assumption.
    apply Qle_refl.
  Qed.         
  
End LeftReals.
      
      
    
  