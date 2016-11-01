Require Import MeetSemiLattice.
Require Import MyNotations.
Require Import PreorderEquiv.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

(** * Definition of distributive lattices
    They are meet semilattices
    with joins. As our meet semilattices have smallest elements,
    we don't need to reintroduce them here. *)

Section DistrLattice_Def.

  Class DistrLattice `{T:Type} (Tle:Le T) :=
    MkDistrLattice
      {
        (* meet semilattice *)
        dl_msl :> MeetSemiLattice Tle;
        (* join *)
        dl_join :> Join T;
        join_l : forall x y, x ≤ x ⊔ y;
        join_r : forall x y, y ≤ x ⊔ y;
        join_univ : forall x y z, x ≤ z -> y ≤ z -> x ⊔ y ≤ z;
        (* distributivity *)
        bdistr_le : forall x y z, x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z);
      }.

  Context {T : Type}.
  Context {Tle : Le T}.
  Context {DL : DistrLattice Tle}.

  Existing Instance DL.
  Existing Instance Feq_equiv.

  (** ** Properties of the join *)

  Lemma join_le_l : forall x y z, x ≤ y -> x ⊔ z ≤ y ⊔ z.
  Proof.
    intros.
    apply join_univ.
    apply (le_trans _ y _ H).
    apply join_l.
    apply join_r.
  Qed.

  Lemma join_le_r : forall x y z, x ≤ y -> z ⊔ x ≤ z ⊔ y.
  Proof.    
    intros.
    apply join_univ.
    apply join_l.
    apply (le_trans _ y _ H).
    apply join_r.
  Qed.

  Lemma join_le : forall x y z w, x ≤ y -> z ≤ w -> x ⊔ z ≤ y ⊔ w.
  Proof.
    intros.
    apply (le_trans _ (x ⊔ w) _).
    apply (join_le_r _ _ _ H0).
    apply (join_le_l _ _ _ H).
  Qed.

  Add Morphism join with signature (Feq ==> Feq ==> Feq) as join_morphism.
  Proof.
    firstorder.
    apply (join_le _ _ _ _ H H0).
    apply (join_le _ _ _ _ H2 H1).
  Qed.

  Lemma join_comm : forall x y, x ⊔ y = y ⊔ x.
  Proof.
    unfold Feq.
    intros. split.
    apply join_univ. apply join_r. apply join_l.
    apply join_univ. apply join_r. apply join_l.
  Qed.

  Lemma join_assoc : forall x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.
  Proof.  
    intros.
    unfold Feq. split.

    apply join_univ.
    apply (le_trans _ (x ⊔ y) _).
    apply join_l.
    apply join_l.
    apply join_le_l.
    apply join_r.

    apply join_univ.
    apply join_le_r.
    apply join_l.
    apply (le_trans _ (y ⊔ z) _).
    apply join_r.
    apply join_r.
  Qed.

  Lemma join_idem : forall x, x ⊔ x = x.
  Proof.
    intros.
    unfold Feq. split.
    apply (join_univ x x x (le_refl x) (le_refl x)).
    apply join_l.
  Qed.

  Lemma join_bot_l : forall x, ⊥ ⊔ x = x.
  Proof.
    intros. split.
    apply join_univ. apply bot_le.
    apply le_refl.
    apply join_r.
  Qed.

  Lemma join_bot_r : forall x, x ⊔ ⊥ = x.
  Proof.
    intro. setoid_rewrite join_comm.
    apply join_bot_l.
  Qed.

  Lemma join_top_l : forall x, ⊤ ⊔ x = ⊤.
  Proof.
    intro. split.
    apply join_univ. apply le_refl.
    apply top_le.
    apply join_l.
  Qed.

  Lemma join_top_r : forall x, x ⊔ ⊤ = ⊤.
  Proof.
    intro. setoid_rewrite join_comm.
    apply join_top_l.
  Qed. 

  (** ** Equivalent definitions of the order *)
  Lemma order_join : forall x y, x ≤ y <-> x ⊔ y = y.
  Proof.
    intros.
    unfold iff. split.

    intros. split.
    apply (le_trans _ (y ⊔ y) _).
    apply (join_le_l _ _ _ H).
    setoid_rewrite (join_idem y).
    apply le_refl.
    apply join_r.

    intros. setoid_rewrite <- H.
    apply join_l.
  Qed.

  (** ** Distributivity *)
  Lemma bdistr_eq : forall x y z, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z).
  Proof.
    intros.
    split.
    - apply bdistr_le.
    - apply join_univ ; apply meet_le_r.
      apply join_l.
      apply join_r.
  Qed.

  (** ** Finite joins *)
  
  Definition Vf l :=
    fold_left (fun accu x => accu ⊔ x) l ⊥.

  Lemma Vf_singleton : forall a, Vf [a] = a.
  Proof.
    intros. unfold Vf. simpl. rewrite join_bot_l.
    reflexivity.
  Qed.

  Lemma cons_app : forall (a : T) (b : list T), a :: b ≡ [a] ++ b.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma Vf_cons : forall a b, Vf (a :: b) = a ⊔ Vf b.
  Proof.
    intros.
    unfold Vf. simpl.
    set (F := fold_left (fun accu x => accu ⊔ x)).
    assert (forall u v, F u v = v ⊔ F u ⊥).
    induction u ; intros.
    - simpl. rewrite join_bot_r. reflexivity.
    - simpl. rewrite IHu.
      assert (F u (⊥ ⊔ a0) = (⊥ ⊔ a0) ⊔ F u ⊥).
      apply IHu.
      rewrite H.
      rewrite join_bot_l.
      rewrite join_assoc.
      reflexivity.
    - assert (a ⊔ F b ⊥ = (⊥ ⊔ a) ⊔ F b ⊥).
      rewrite join_bot_l. reflexivity.
      rewrite H0.
      apply H.
  Qed.

  Lemma Vf_app : forall a b, Vf (a ++ b) = Vf a ⊔ Vf b.
  Proof.
    induction a ; intros.
    - unfold Vf. simpl.
      rewrite join_bot_l.
      reflexivity.
    - simpl.
      rewrite Vf_cons.
      rewrite Vf_cons.
      rewrite <- join_assoc.
      rewrite IHa.
      reflexivity.
  Qed.

  Instance in_contains : Contains T (list T) := (InA Feq).
  
  Lemma Vf_in_le : forall a U, a ∈ U -> a ≤ Vf U.
  Proof.
    intros.
    induction H ; rewrite Vf_cons.
    - rewrite H.
      apply join_l.
    - apply le_trans with (y0 := Vf l).
      assumption.
      apply join_r.
  Qed.
  
End DistrLattice_Def.

Add Parametric Morphism (T : Type) (Tle : Le T) (Tdl : DistrLattice Tle) : (@dl_join T Tle Tdl) with signature (Feq ==> Feq ==> Feq) as f_join_morphism.
Proof.
  apply join_morphism_Proper.
Qed.

(** * Distributive lattice morphisms *)

(* TODO *)
