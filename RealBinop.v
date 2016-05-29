
Require Import Coq.QArith.QArith.
Require Import LeftReals.
Require Import Setoid.
Require Setoid.
Require Import Basics.
Require Import LeftReals.

Module RealBinop (Q : Poset) (F : Commonoid Q).
  Import Q.
  Module LR := LeftCompletion Q.

  Definition f_unit := LR.inj F.f_unit.

  Infix "⋅" := F.f (at level 50, no associativity) : LR_binop_scope.
  Infix "<=" := le (at level 70) : LR_binop_scope.
  Infix "⪯" := LR.le (at level 70) : LR_binop_scope.
  (* Open Scope LR_scope. *)
  Open Scope LR_binop_scope.
  
  Lemma f_le_compat :
    forall x y z w, x <= y -> z <= w -> x ⋅ z <= y ⋅ w.
  Proof.
    intros.
    apply (trans _ (x ⋅ w) _).
    apply (F.f_incr_r _ _ _ H0).
    apply (F.f_incr_l _ _ _ H).
  Qed.
                                        
Definition fSeq (u : nat -> Q.t) (v : nat -> Q.t) : (nat -> Q.t) :=
  fun n => (u n ⋅ v n).

Lemma f_of_increasing_sequences : forall {u v}, (LR.MonotoneSeq u) /\ (LR.MonotoneSeq v) -> (LR.MonotoneSeq (fSeq u v)).
Proof.
  unfold LR.MonotoneSeq.
  intros.
  destruct H as [Hu Hv].
  unfold fSeq.
  specialize (Hu x y H0).
  specialize (Hv x y H0).
  apply f_le_compat.
  assumption. assumption.
Qed.

Lemma f_of_bounded_sequences : forall {u v}, (LR.BoundedSeq u) /\ (LR.BoundedSeq v) -> (LR.BoundedSeq (fSeq u v)).
Proof.
  unfold LR.BoundedSeq.
  intros. destruct H as [Hu Hv].
  destruct Hu as [qu Hu].
  destruct Hv as [qv Hv].
  exists (qu ⋅ qv)%Q.
  intros.
  unfold fSeq.
  apply f_le_compat. apply (Hu x). apply (Hv x).
Qed.

Definition f (a : LR.t) (b : LR.t) : LR.t :=
  LR.MkLC (fSeq (LR.qlb a) (LR.qlb b))
       (f_of_increasing_sequences (conj (LR.qlb_monotone a) (LR.qlb_monotone b)))
       (f_of_bounded_sequences (conj (LR.qlb_bounded a) (LR.qlb_bounded b))).

Notation "a ⊗ b" := (f a b) (at level 50, no associativity) : LR_binop_scope.
Infix "≃" := LR.eq (at level 60) : LR_binop_scope.

Lemma f_comm : forall {u v}, u ⊗ v ≃ v ⊗ u.
Proof.
  intros.
  apply LR.eq_seqs.
  intros. simpl. apply F.f_comm.
Qed.

Lemma f_assoc : forall {u v w}, u ⊗ (v ⊗ w) ≃ (u ⊗ v) ⊗ w.
Proof.
  intros.
  apply LR.eq_seqs.
  intros. simpl. apply F.f_assoc.
Qed.

Lemma f_unit_l : forall {u}, f_unit ⊗ u ≃ u.
Proof.
  intros.
  apply LR.eq_seqs.
  intros. simpl. apply F.f_unit_l.
Qed.

Lemma f_unit_r : forall {u}, u ⊗ f_unit ≃ u.
Proof.
  intros.
  apply LR.eq_seqs.
  intros. simpl. apply F.f_unit_r.
Qed.

Lemma f_incr_l : forall {u v w}, u ⪯ v -> u ⊗ w ⪯ v ⊗ w.
Proof.
  unfold LR.le.
  intros.
  specialize (H x). destruct H as [y H].
  exists (max x y). simpl. unfold fSeq.
  apply (trans _ (LR.qlb u x ⋅ LR.qlb w (max x y)) _).
  apply F.f_incr_r. apply LR.qlb_monotone. apply NPeano.Nat.le_max_l.
  apply F.f_incr_l. apply (trans _ _ _ H).
  apply LR.qlb_monotone. apply NPeano.Nat.le_max_r.
Qed.

Lemma f_incr_r : forall {u v w}, u ⪯ v -> w ⊗ u ⪯ w ⊗ v.
Proof.
  unfold LR.le.
  intros.
  specialize (H x). destruct H as [y H].
  exists (max x y). simpl. unfold fSeq.
  apply (trans _ (LR.qlb w (max x y) ⋅ LR.qlb u x) _).
  apply F.f_incr_l. apply LR.qlb_monotone. apply NPeano.Nat.le_max_l.
  apply F.f_incr_r.
  apply (trans _ (LR.qlb v y) _ H).
  apply LR.qlb_monotone. apply NPeano.Nat.le_max_r.
Qed.

Lemma f_proper : forall {x y z t}, x ≃ y -> z ≃ t -> x ⊗ z ≃ y ⊗ t.
Proof.
  unfold LR.eq.
  intros.
  destruct H as [H1 H2].
  destruct H0 as [H3 H4].
  split.

  apply (LR.trans _ (y ⊗ z) _).
  apply (f_incr_l H1).
  apply (f_incr_r H3).

  apply (LR.trans _ (y ⊗ z) _).
  apply (f_incr_r H4).
  apply (f_incr_l H2).
Qed.

Add Morphism f : morphism_lrf.
Proof.
  intros.
  apply (f_proper H H0).
Qed.

Close Scope LR_binop_scope.
End RealBinop.


Module LRsum := (RealBinop Rat RatSumCommonoid).
Module LR := LRsum.LR.

