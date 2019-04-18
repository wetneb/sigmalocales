Require Import MathClasses.interfaces.canonical_names.
Require Import Coq.Lists.SetoidList.

Section GeneralMapIn.

  Variable Q : Type.
  Variable Qeq : relation Q.
  Context {Qequiv : Equivalence Qeq}.
  Existing Instance Qequiv.
 Instance qequivalence : Equiv Q := Qeq.
  Instance in_containsQ : Contains Q (list Q) := (InA Qeq).

  Variable R : Type.
  Variable Req : relation R.
  Variable Requiv : Equivalence Req.
  Existing Instance Requiv.
  Instance requivalence : Equiv R := Req.
  Instance in_containsR : Contains R (list R) := (InA Req).

  Lemma map_in : forall f x U, (Proper (Qeq  ==>  Req) f) -> x ∈ U -> f x ∈ map f U.
  Proof.
    intros. unfold map.
    induction H0.
    apply InA_cons_hd.
    apply H. assumption.
    apply InA_cons_tl.
    assumption.
  Qed.

  Lemma in_map : forall (f : Q -> R) x U, x ∈ map f U -> exists y, y ∈ U /\ x = f y.
  Proof.
    intros.
    induction U.
    - inversion H.
    - set (V := map f (a :: U)) in *. assert( V ≡ map f (a :: U)) by reflexivity.
      destruct H.
      + inversion H0.
        exists a. split.
        apply InA_cons_hd. reflexivity.
        rewrite <- H2. assumption.
      + simpl in H0.
        inversion H0. subst.
        apply IHU in H.
        destruct H as [y [G K]].
        exists y. split.
        apply InA_cons_tl.
        assumption. assumption.
  Qed.

  Lemma inA_map_iff : forall (f : Q -> R) x U, Proper (Qeq ==> Req) f -> x ∈ map f U <-> exists y, y ∈ U /\ x = f y.
  Proof.
    intros.
    split.
    apply in_map.
    intro.
    destruct H0.
    destruct H0.
    rewrite H1.
    apply map_in ; assumption.
  Qed.

End GeneralMapIn.
