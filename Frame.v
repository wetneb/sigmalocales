
(*
Module Type Frame_Types.
  Parameter t : Type.
  Parameter le : t -> t -> Prop.
End Frame_Types. *)

Section Frame_Definition.

  Context {t : Type}.
  Context { le : t -> t -> Prop }.

  Require Import Coq.Relations.Relation_Definitions.
  Require Import Coq.Classes.Equivalence.
  Require Import Coq.Classes.Morphisms.
  Require Import Setoid.
  Require Import BijNat.

  Class Frame {t : Type} {le : t -> t -> Prop} :=
    MkFrame {
        (* preorder *)
        le_refl: forall x, le x x;
        le_trans: forall x y z, le x y -> le y z -> le x z;

        (* top, bottom *)
        top: t;
        top_le: forall x, le x top;
        bot: t;
        bot_le: forall x, le bot x;

        (* meet *)
        meet: t -> t -> t;
        meet_l: forall x y, le (meet x y) x;
        meet_r: forall x y, le (meet x y) y;
        meet_univ: forall x y z, le z x -> le z y -> le z (meet x y);

        (* join *)
        join: t -> t -> t;
        join_l: forall x y, le x (join x y);
        join_r: forall x y, le y (join x y);
        join_univ: forall x y z, le x z -> le y z -> le (join x y) z;

        (* countable joins *)
        V : (nat -> t) -> t;
        v_le: forall u : (nat -> t), forall n: nat, le (u n) (V u);
        v_univ: forall u : (nat -> t), forall z : t, (forall n : nat, le (u n) z) -> le (V u) z;

        (* distributivity *)
        cdistr_l: forall x u, le (meet x (V u)) (V (fun n => meet x (u n)));
        cdistr_r: forall x u, le (V (fun n => meet x (u n))) (meet x (V u))
      }.

  Variable F : @Frame t le.

  Infix "<=" := le (at level 70).

  Definition Feq (x y:t) : Prop :=
    (x <= y /\ y <= x).

  Lemma Feq_refl : Reflexive Feq.
  Proof.
    unfold Reflexive, Feq.
    intros. split. apply le_refl. apply le_refl.
  Qed.
  
  Lemma Feq_sym : Symmetric Feq.
  Proof.
    firstorder.
  Qed.

  Lemma Feq_trans : Transitive Feq.
  Proof.    
    unfold Transitive, Feq.
    intros.
    destruct H as [H1 H2].
    destruct H0 as [H3 H4].
    split.
    apply (le_trans _ y _ H1 H3).
    apply (le_trans _ y _ H4 H2).
  Qed.

  Definition Feq_equiv := Build_Equivalence t Feq Feq_refl Feq_sym Feq_trans.

  Add Setoid t Feq Feq_equiv as Feq_setoid.
  Infix "==" := Feq (at level 70).
  Infix "∨" := join (at level 50, left associativity).
  Infix "∧" := meet (at level 45, left associativity).
  Notation "⊥" := bot.
  Notation "⊤" := top.

  Lemma le_proper : Proper (Feq ==> Feq ==> iff) le.
  Proof.  
    unfold Proper, Feq, respectful.
    firstorder.
    apply (le_trans _ x _ H1).
    apply (le_trans _ x0 _ H3 H0).
    apply (le_trans _ y _ H).
    apply (le_trans _ y0 _ H3 H2).
  Qed.

  Add Morphism le : le_morphism. 
  Proof. apply le_proper. Qed.

  Lemma join_le_l : forall x y z, x <= y -> x ∨ z <= y ∨ z.
  Proof.
    intros.
    apply join_univ.
    apply (le_trans _ y _ H).
    apply join_l.
    apply join_r.
  Qed.

  Lemma join_le_r : forall x y z, x <= y -> z ∨ x <= z ∨ y.
  Proof.    
    intros.
    apply join_univ.
    apply join_l.
    apply (le_trans _ y _ H).
    apply join_r.
  Qed.

  Lemma join_le : forall x y z w, x <= y -> z <= w -> x ∨ z <= y ∨ w.
  Proof.
    intros.
    apply (le_trans _ (x ∨ w) _).
    apply (join_le_r _ _ _ H0).
    apply (join_le_l _ _ _ H).
  Qed.
  
  Add Morphism join : join_morphism.
  Proof.
    firstorder.
    apply (join_le _ _ _ _ H H0).
    apply (join_le _ _ _ _ H1 H2).
  Qed.

  Lemma join_comm : forall x y, x ∨ y == y ∨ x.
  Proof.
    unfold Feq.
    intros. split.
    apply join_univ. apply join_r. apply join_l.
    apply join_univ. apply join_r. apply join_l.
  Qed.

  Lemma join_assoc : forall x y z, x ∨ (y ∨ z) == (x ∨ y) ∨ z.
  Proof.  
    intros.
    unfold Feq. split.

    apply join_univ.
    apply (le_trans _ (x ∨ y) _).
    apply join_l.
    apply join_l.
    apply join_le_l.
    apply join_r.

    apply join_univ.
    apply join_le_r.
    apply join_l.
    apply (le_trans _ (y ∨ z) _).
    apply join_r.
    apply join_r.
  Qed.

  Lemma join_idem : forall x, x ∨ x == x.
  Proof.
    intros.
    unfold Feq. split.
    apply (join_univ x x x (le_refl x) (le_refl x)).
    apply join_l.
  Qed.

  Lemma join_bot_l : forall x, ⊥ ∨ x == x.
  Proof.
    intros. split.
    apply join_univ. apply bot_le.
    apply le_refl.
    apply join_r.
  Qed.

  Lemma join_bot_r : forall x, x ∨ ⊥ == x.
  Proof.
    intro. setoid_rewrite join_comm.
    apply join_bot_l.
  Qed.

  Lemma join_top_l : forall x, ⊤ ∨ x == ⊤.
  Proof.
    intro. split.
    apply join_univ. apply le_refl.
    apply top_le.
    apply join_l.
  Qed.

  Lemma join_top_r : forall x, x ∨ ⊤ == ⊤.
  Proof.
    intro. setoid_rewrite join_comm.
    apply join_top_l.
  Qed.

  (* meets *)
  Lemma meet_le_l : forall x y z, x <= y -> x ∧ z <= y ∧ z.
  Proof.
    intros.
    apply meet_univ.
    apply (le_trans _ x _).
    apply meet_l. assumption.
    apply meet_r.
  Qed.

  Lemma meet_le_r : forall x y z, x <= y -> z ∧ x <= z ∧ y.
  Proof.    
    intros.
    apply meet_univ.
    apply meet_l.
    apply (le_trans _ x _).
    apply meet_r. assumption.
  Qed.

  Lemma meet_le : forall x y z w, x <= y -> z <= w -> x ∧ z <= y ∧ w.
  Proof.
    intros.
    apply (le_trans _ (x ∧ w) _).
    apply (meet_le_r _ _ _ H0).
    apply (meet_le_l _ _ _ H).
  Qed.
  
  Add Morphism meet : meet_morphism.
  Proof.
    firstorder.
    apply (meet_le _ _ _ _ H H0).
    apply (meet_le _ _ _ _ H1 H2).
  Qed.

  Lemma meet_comm : forall x y, x ∧ y == y ∧ x.
  Proof.
    unfold Feq.
    intros. split.
    apply meet_univ. apply meet_r. apply meet_l.
    apply meet_univ. apply meet_r. apply meet_l.
  Qed.

  Lemma meet_assoc : forall x y z, x ∧ (y ∧ z) == (x ∧ y) ∧ z.
  Proof.  
    intros.
    unfold Feq. split.

    apply meet_univ.
    apply meet_le_r.
    apply meet_l.
    apply (le_trans _ (x ∧ z) _).
    apply meet_le_r.
    apply meet_r.
    apply meet_r.

    apply meet_univ.
    apply (le_trans _ (x ∧ z) _).
    apply meet_le_l.
    apply meet_l.
    apply meet_l.
    apply meet_le_l.
    apply meet_r.
  Qed.

  Lemma meet_idem : forall x, x ∧ x == x.
  Proof.
    intros.
    unfold Feq. split.
    apply meet_l.
    apply (meet_univ x x x (le_refl x) (le_refl x)).
  Qed.

  Lemma meet_bot_l : forall x, ⊥ ∧ x == ⊥.
  Proof.
    intros. split.
    apply meet_l.
    apply meet_univ.
    apply le_refl.
    apply bot_le.
  Qed.

  Lemma meet_bot_r : forall x, x ∧ ⊥ == ⊥.
  Proof.
    intros. setoid_rewrite meet_comm.
    apply meet_bot_l.
  Qed.

  Lemma meet_top_l : forall x, ⊤ ∧ x == x.
  Proof.
    intro. split.
    apply meet_r.
    apply meet_univ.
    apply top_le.
    apply le_refl.
  Qed.

  Lemma meet_top_r : forall x, x ∧ ⊤ == x.
  Proof.
    intro. setoid_rewrite meet_comm.
    apply meet_top_l.
  Qed.

  (* Equivalent definitions of the order *)
  Lemma order_join : forall x y, x <= y <-> x ∨ y == y.
  Proof.
    intros.
    unfold iff. split.

    intros. split.
    apply (le_trans _ (y ∨ y) _).
    apply (join_le_l _ _ _ H).
    setoid_rewrite (join_idem y).
    apply le_refl.
    apply join_r.

    intros. setoid_rewrite <- H.
    apply join_l.
  Qed.

  Lemma order_meet : forall x y, x <= y <-> x ∧ y == x.
  Proof.
    intros.
    unfold iff. split.

    intros. split.
    apply meet_l.
    apply (le_trans _ (x ∧ x) _).
    setoid_rewrite meet_idem. apply le_refl.
    apply meet_le_r.
    apply H.
    intro.
    setoid_rewrite <- H.
    apply meet_r.
  Qed.

  (* Countable join and binary join *)

  Definition V_cons (x : t) (u : nat -> t) (n : nat) :=
    match n with
      | 0 => x
      | S n => u n
    end.
  Infix "::" := V_cons.
  Definition V_tail (u : nat -> t) (n : nat) := u (S n).

  Lemma join_V : forall x u, x ∨ (V u) == V (x :: u).
  Proof.
    intros.
    split.
    apply join_univ.
    assert ((x :: u) 0 <= V (x :: u)).
    apply (v_le (x :: u) 0).
    simpl in H. assumption.
    apply (v_univ _ _ (fun n => v_le (x :: u) (S n))).

    apply v_univ.
    intros.
    destruct n.

    simpl. apply join_l.
    simpl. apply (le_trans _ (V u) _).
    apply v_le. apply join_r.
  Qed.

  (* Countable join is a morphism *)

  Lemma V_compat_le : forall a b, (forall n, a n <= b n) -> V a <= V b.
  Proof.
    intros.
    apply v_univ.
    intros.
    apply (le_trans _ (b n) _ (H n)).
    apply v_le.
  Qed.

  Lemma V_morphism : forall a b, (forall n, a n == b n) -> V a == V b.
    unfold Feq.
    intros.
    split.
    
    apply V_compat_le.
    firstorder.
    apply V_compat_le.
    firstorder.
  Qed.

  Add Morphism V : morphism_V.
  Proof.
    apply V_morphism.
  Qed.

  Lemma V_le_le : forall x t u, t <= u x -> t <= V u.
  Proof.
    intros.
    apply le_trans with (y := u x).
    apply H.
    apply v_le.
  Qed.

  Ltac smart_V_le n :=
    apply (V_le_le n);
    simpl;
    try (apply le_refl).

  Lemma V_const : forall u x, (forall n, u n == x) -> V u == x.
  Proof.
    intros.
    split.
    apply v_univ.
    firstorder.
    apply (le_trans _ (u 0) _).
    setoid_rewrite (H 0). apply le_refl.
    apply (v_le u 0).
  Qed.

  Lemma V_top : forall u, (exists n, u n == ⊤) -> V u == ⊤.
  Proof.
    intros.
    destruct H as [n H].
    split.
    apply top_le.
    setoid_rewrite <- H.
    apply v_le.
  Qed.

  Lemma V_bot : V (fun _ => ⊥) == ⊥.
  Proof.
    split.
    apply v_univ. intro. apply le_refl.
    apply bot_le.
  Qed.

  Lemma V_comm : forall w : nat -> nat -> t,
                   V (fun n => V (fun m => w n m)) == V (fun m => V (fun n => w n m)).
  Proof.
    intros.
    unfold Feq.
    split; repeat (apply v_univ; intro).
    (* <= *)
    apply le_trans with (y := V (fun n1 => w n1 n0)).
    smart_V_le n.
    smart_V_le n0.

    (* >= *)
    apply le_trans with (y := V (fun m => w n0 m)).
    smart_V_le n.
    smart_V_le n0.
  Qed.

  Definition my_pairer w (n : nat) : t := w (fst (bijNNinv n)) (snd (bijNNinv n)).

  Lemma V_pair : forall w : nat -> nat -> t,
            V (fun n => w (fst (bijNNinv n)) (snd (bijNNinv n))) ==
            V (fun n => V (fun m => w n m)).
  Proof.
    intro.
    unfold Feq. split.

    (* <= *)
    apply v_univ. intro.
    smart_V_le (fst (bijNNinv n)).
    smart_V_le (snd (bijNNinv n)).

    (* >= *)
    repeat (apply v_univ; intro).
    assert (w n n0 = (my_pairer w (bijNN (n,n0)))).
    unfold my_pairer.
    rewrite bijNNinv_bijNN.
    reflexivity.
    rewrite H.
    apply v_le.
  Qed.
 
  (* Distributivity *)

  Lemma cdistr : forall x u, x ∧ (V u) == V (fun n => x ∧ (u n)).
  Proof.
    intros. split.
    apply cdistr_l.
    apply cdistr_r.
  Qed.

  Lemma v_binlist : forall x y, V (x :: y :: (fun _ => ⊥)) == x ∨ y.
  Proof.
    intros.
    setoid_rewrite <- join_V.
    setoid_rewrite <- join_V.
    setoid_rewrite V_bot.
    setoid_rewrite join_bot_r.
    reflexivity.
  Qed.
  
  Lemma fdistr : forall x y z, x ∧ (y ∨ z) == (x ∧ y) ∨ (x ∧ z).
  Proof.
    intros.
    setoid_rewrite <- v_binlist.
    setoid_rewrite cdistr.
    apply V_morphism.
    intro.
    destruct n.
    simpl. reflexivity.
    destruct n. simpl. reflexivity.
    simpl. apply meet_bot_r.
  Qed.

  (* Compactness ! *)

  Fixpoint partial_V (u : (nat -> t)) (n : nat) : t :=
    match n with
      | 0 => ⊥
      | S n => (u 0) ∨ (partial_V (V_tail u) n)
    end.

  Lemma partial_V_le : forall u n, partial_V u n <= V u.
  Proof.
    intros.
    generalize u as w.
    induction n.

    (* 0 *)
    intros.
    apply bot_le.

    (* S n *)
    intros.
    simpl.
    apply join_univ.
    apply v_le.
    apply (le_trans _ (V (V_tail w)) _).
    apply IHn.
    apply v_univ.
    intro. unfold V_tail.
    apply v_le.
  Qed.

  Definition compact := forall u, (V u == ⊤) -> (exists n, partial_V u n == ⊤).

End Frame_Definition.

Section Frame_Morphism_Definition.
  Context {tA : Type}.
  Variable (leA : tA -> tA -> Prop ).
  Context  {A : @Frame tA leA}.
  
  Context {tB : Type}.
  Variable (leB : tB -> tB -> Prop ).
  Context {B : @Frame tB leB }.

  Require Import Coq.Program.Basics.

  Infix "<=A" := leA (at level 70).
  Infix "<=B" := leB (at level 70).
  Infix "∨A" := (@join tA leA A) (at level 50, left associativity).
  Infix "∨B" := (@join tB leB B) (at level 50, left associativity).
  Infix "∧A" := (@meet tA leA A) (at level 45, left associativity).
  Infix "∧B" := (@meet tB leB B) (at level 45, left associativity).
  Infix "==A" := (@Feq tA leA) (at level 70).
  Infix "==B" := (@Feq tB leB) (at level 70).

  Definition VA := (@V tA leA A).
  Definition VB := (@V tB leB B).

  Variable f : tA -> tB.

  Open Scope program_scope. (* for ∘ (function composition) *)
  
  Class FMorphism :=
    MkMorphism
      {
        (* increasing *)
        morph_le: forall x y, x <=A y -> f x <=B f y;
        (* preserves joins *)
        morph_join: forall x y, f (x ∨A y) ==B (f x) ∨B (f y);
        (* preserves meets *)
        morph_meet: forall x y, f (x ∧A y) ==B (f x) ∧B (f y);
        (* preserves countable joins *)
        morph_V: forall u, f (VA u) ==B VB (f ∘ u)
      }.
  
End Frame_Morphism_Definition.

