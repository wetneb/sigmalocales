Require Import MyNotations.
Require Import Coq.Lists.List.

Section SeqOfList.
  Context {t : Type}.
  Context {b : Bottom t}.
  Variable (teq : Equiv t).
  Variable (tequiv : Equivalence teq).

  Existing Instance b.
  Existing Instance teq.
  Existing Instance tequiv.
  
  Definition V_cons (x : t) (u : nat -> t) (n : nat) :=
    match n with
      | 0 => x
      | S n => u n
    end.
  Infix ":::" := V_cons (right associativity, at level 60).
  
  Definition V_tail (u : nat -> t) (n : nat) := u (S n).

  Instance nat_t_equal : Equiv (nat -> t) := pointwise_relation nat (=).
  Lemma V_cons_compose : forall f x u, f ∘ (V_cons x u) = V_cons (f x) (f ∘ u).
  Proof.
    intros.
    unfold compose, V_cons, equiv, nat_t_equal, pointwise_relation.
    intro.
    destruct a ; reflexivity.
  Qed.

  Fixpoint seq_of_list (l : list t) : (nat -> t) :=
    match l with
      | [] => fun _ => ⊥
      | h :: q => h ::: (seq_of_list q)
    end.



  Inductive listeq : forall u v : list t, Prop :=
  | listeq_nil : listeq nil nil
  | listeq_cons : forall a b u v, a = b -> listeq u v -> listeq (a :: u) (b :: v).
  Instance listeq_equiv : Equiv (list t) := listeq.

  Lemma listeq_refl : Reflexive listeq.
  Proof.
    unfold Reflexive.
    induction x.
    apply listeq_nil.
    apply listeq_cons ; auto.
  Qed.

  Lemma listeq_trans : Transitive listeq.
  Proof.
    unfold Transitive.        
    induction x ; intros.
    inversion H. subst. assumption.
    inversion H. inversion H0. subst.
    inversion H0. subst.
    inversion H8. subst.
    rewrite H6 in H3.
    apply listeq_cons. assumption.
    apply IHx with (y := v) ; assumption.
  Qed.

  Lemma listeq_sym : Symmetric listeq.
    unfold Symmetric.
    induction x ; intros.
    - inversion H. apply listeq_nil.
    - inversion H. subst. apply listeq_cons.
      symmetry. assumption.
      apply IHx ; assumption.
  Qed.
End SeqOfList.

Add Parametric Relation (t : Type) (teq : Equiv t) (tequiv : Equivalence teq) : (list t) (listeq teq)
    reflexivity proved by (listeq_refl teq tequiv)
    symmetry proved by (listeq_sym teq tequiv)
    transitivity proved by (listeq_trans teq tequiv) as listeq_rel.

Add Parametric Morphism (t : Type) (teq : Equiv t) (tequiv : Equivalence teq) (b : Bottom t): seq_of_list with signature
    ((listeq teq) ==> pointwise_relation nat teq) as seq_of_list_morphism.
Proof.
  unfold pointwise_relation.
  induction x ; intros ; inversion H ; subst.
  reflexivity.
  destruct a0 ; simpl.
  + assumption.
  + apply IHx. assumption.
Qed.

Infix ":::" := V_cons (right associativity, at level 60).

Section compose.
  Context {t : Type}.
  Context {b : Bottom t}.
  Context {t' : Type}.
  Context {b' : Bottom t'}.
  Variable (teq : Equiv t').
  Variable (tequiv : Equivalence teq).
  Existing Instance teq.
  Instance nat_t'_equal : Equiv (nat -> t') := pointwise_relation nat (=).

  Lemma seq_of_list_compose : forall (f: t -> t') l, f ⊥ = ⊥ -> seq_of_list (map f l) = f ∘ (seq_of_list l).
  Proof.
    induction l; unfold compose, equiv, nat_t'_equal, pointwise_relation ; intros ; simpl.
    - symmetry. assumption.
    - destruct a0.
      + reflexivity.
      + simpl. apply (IHl H).
  Qed.

End compose.