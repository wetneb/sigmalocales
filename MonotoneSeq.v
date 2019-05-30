
Require Import Peano.
Require Import QArith.
Require Import ZArith.BinInt.
Require Import Lia.
Require Import PreorderEquiv.
Require Import JoinSemiLattice.
Require Import BijNat.
Require Import Rationals.
Require Import MyNotations.

Section MonotoneSeq.

  Context {T: Type}.
  Context {Tle : Le T}.
  Context {TJSL : JoinSemiLattice Tle}.

  Instance nat_le : Le nat := Peano.le.

  Definition monotone (f : nat -> T) : Prop :=
    forall n m : nat, n ≤ m -> f n ≤ f m.

  Definition MonotoneSeq := { f : nat -> T | monotone f }.

  Definition monotone_incr (f : nat -> T) : Prop :=
    forall n : nat, f n ≤ f (S n).

  Lemma monotone_equiv : forall f, monotone f <-> monotone_incr f.
  Proof.
    intros; unfold monotone, monotone_incr; split ; intros.
    - apply (H n (S n)).
      apply le_S. reflexivity.
    - induction H0.
      * apply le_refl.
      * apply (le_trans _ (f m) _).
        assumption.
        apply H.
  Qed.
  
  (** Iterated suprema of a sequence **)

  Variable f : nat -> T.
  Fixpoint sup_def (n : nat) : T :=
    match n with
    | O => f O
    | S n => f (S n) ⊔ sup_def n
    end.

  Lemma sup_def_point : forall n : nat, f n ≤ sup_def n.
  Proof.
    intros.
    destruct n ; simpl.
    - apply le_refl.
    - apply join_l.
  Qed.

  Lemma sup_def_univ : forall n : nat, forall t : T, (forall m, m ≤ n -> f m ≤ t) -> sup_def n ≤ t.
  Proof.
    induction n ; intros.
    - apply (H 0).
      reflexivity.
    - simpl.
      apply join_univ.
      apply (H (S n)).
      reflexivity.
      apply IHn.
      intros.
      apply H.
      apply le_S.
      assumption.
  Qed.

  Lemma sup_monotone : monotone sup_def.
  Proof.
    rewrite monotone_equiv.
    unfold monotone_incr.
    intro. simpl.
    apply join_r.
  Qed.

End MonotoneSeq.

Section LeftReals.
  
  Definition LReal := MonotoneSeq.

  Definition Qpos := { q : Q | 0 < q }.

  Definition LRle (x y : LReal)  :=
    forall ϵ : Q, ϵ > 0 -> forall n : nat, exists m : nat, (` x) n ≤ (` y) m + ϵ .
  
  Instance LRle_le : Le LReal := LRle.

  Lemma LRle_refl : forall x : LReal, x ≤ x.
  Proof.
    unfold "≤", LRle_le, LRle ; intros.
    exists n.
    apply Qlt_le_weak.
    rewrite <- Qplus_0_r at 1.
    rewrite Qplus_lt_r.
    assumption.
  Qed.

  Definition Qhalf x : Q := x / inject_Z 2.

  Lemma Q_times_two : forall x : Q, x + x = x * inject_Z 2.
  Proof.
    intros. unfold plus, mult, q_plus, q_mult, Qplus, Qmult.
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

  Lemma LRle_trans : forall x y z : LReal, x ≤ y -> y ≤ z -> x ≤ z.
  Proof.
    unfold "≤", LRle_le, LRle ; intros.
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

  Lemma Qle_Qplus_Qpos : forall x ϵ : Q, 0 < ϵ -> x ≤ x + ϵ.
  Proof.
    intros.
    unfold "+", q_plus.
    apply Qlt_le_weak.
    rewrite <- (Qplus_0_l x) at 1.
    rewrite (Qplus_comm x).
    apply Qplus_lt_le_compat.
    assumption.
    apply Qle_refl.
  Qed.

  Lemma Qeq_LReq : forall x y : LReal, (forall n, (` x) n = (` y) n) -> x = y.
  Proof.
    intros.
    unfold "=", LRequiv, Feq, "≤", LRle_le, LRle.
    split ; intros ; exists n ; 
    rewrite (H n); apply Qle_Qplus_Qpos ;
      assumption.
  Qed.

  Lemma LRplus_0_l : forall x : LReal, 0 + x = x.
  Proof.
    intros.
    apply Qeq_LReq.
    intros.
    simpl.
    apply Qplus_0_l.
  Qed.

  Lemma LRplus_comm : forall x y : LReal, x + y = y + x.
  Proof.
    intros ; apply Qeq_LReq ; intros.
    simpl. apply Qplus_comm.
  Qed.

  Lemma LRplus_0_r : forall x : LReal, x + 0 = x.
  Proof.
    intros.
    rewrite LRplus_comm.
    apply LRplus_0_l.
  Qed.

  Lemma LRplus_assoc : forall x y z : LReal, x + (y + z) = (x + y) + z.
  Proof.
    intros ; apply Qeq_LReq ; intros.
    simpl. apply Qplus_assoc.
  Qed.

  (* Countable supremum *)

  Existing Instance q_le.
  Existing Instance q_JSL.
  
  Definition LRsup_def (f : nat -> LReal) : nat -> Q :=
    sup_def (fun n => (` (f (bijNN1 n))) (bijNN2 n)).

  Lemma LRsup_defined : forall f, monotone (LRsup_def f).
  Proof.
    intros.
    unfold LRsup_def.
    apply sup_monotone.
  Qed.

  Definition LRsup (f : nat -> LReal) : LReal :=
    exist monotone (LRsup_def f) (LRsup_defined f).

  Lemma LRsup_point : forall f : nat -> LReal, forall n : nat, f n ≤ LRsup f.
  Proof.
    unfold le, LRle_le, LRle.
    intros.
    exists (bijNN (n,n0)).
    apply le_trans with (y := ((` (LRsup f)) (bijNN (n, n0)))).
    unfold LRsup, LRsup_def. simpl.
    set (fun n1 => (` (f (bijNN1 n1)) (bijNN2 n1))).
    apply le_trans with (y := q (bijNN (n,n0))).
    unfold q.
    rewrite bijNN1_eq, bijNN2_eq. simpl.
    apply le_refl.
    apply sup_def_point.
    apply Qle_Qplus_Qpos.
    assumption.
  Qed.
  Existing Instance nat_le.
              
  Lemma LRsup_univ : forall f : nat -> LReal, forall z : LReal, (forall n, f n ≤ z) -> LRsup f ≤ z.
  Proof.
    unfold le, LRle_le, LRle.
    intro. intro.
    induction n ; simpl.
    - apply (H (bijNN1 0) ϵ H0 (bijNN2 0)).
    - destruct IHn.
      specialize (H (bijNN1 (S n)) ϵ H0 (bijNN2 (S n))).
      destruct H.
      set (Peano.max x x0) as y.
      exists y.
      apply (@join_univ Q q_le q_JSL).
      apply (le_trans _ ((` z) x0 + ϵ) _).
      assumption.
      apply Qplus_le_compat.
      apply (proj2_sig z).
      apply Max.le_max_r.
      apply le_refl.
      apply (le_trans _ ((` z) x + ϵ) _).
      assumption.
      apply Qplus_le_compat.
      apply (proj2_sig z).
      apply Max.le_max_l.
      apply le_refl.
  Qed.
    
End LeftReals.

      
    
  