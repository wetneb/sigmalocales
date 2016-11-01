
Require Import MathClasses.interfaces.canonical_names.
Require Import Coq.Lists.List.
Require Import BijNat.
Require Import MeetSemiLattice.
Require Import DistrLattice.
Require Import PreorderEquiv.

(** * Definition of sigma-frames
    They are meet semilattices with countable joins, such
    that meet distributes over joins.

    We omit the sigma prefix in the coq development. *)

Section Frame_Definition.

Class Frame {t:Type} {le: Le t} :=
  MkFrame {
      frame_msl :> MeetSemiLattice le;

      (* countable joins *)
      V : (nat -> t) -> t;
      v_le: forall u : (nat -> t), forall n: nat, u n ≤ V u;
      v_univ: forall u : (nat -> t), forall z : t, (forall n : nat, u n ≤ z) -> V u ≤ z;

      (* distributivity *)
      cdistr_l: forall x u, x ⊓ (V u) ≤ (V (fun n => x ⊓ (u n)));
    }.

  Context {t : Type}.
  Context {le : Le t}.

  Variable (F : @Frame t le).
  Existing Instance Feq_equiv.

  (** ** Properties of the countable join *)
  (* Countable join is a morphism *)

  Lemma V_compat_le : forall a b, (forall n, a n ≤ b n) -> V a ≤ V b.
  Proof.
    intros.
    apply v_univ.
    intros.
    apply (le_trans _ (b n) _ (H n)).
    apply v_le.
  Qed.

  Lemma V_morphism : forall a b, (forall n, a n = b n) -> V a = V b.
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

  Lemma V_le_le : forall x t u, t ≤ u x -> t ≤ V u.
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

  Lemma V_const : forall x, V (fun _ => x) = x.
  Proof.
    intros.
    split.
    apply v_univ. intro ; apply le_refl.
    apply (V_le_le O).
    apply le_refl.
  Qed.

  Lemma V_top : forall u, (exists n, u n = ⊤) -> V u = ⊤.
  Proof.
    intros.
    destruct H as [n H].
    split.
    apply top_le.
    setoid_rewrite <- H.
    apply v_le.
  Qed.

  Lemma V_bot : V (fun _ => ⊥) = ⊥.
  Proof.
    apply V_const.
  Qed.

  Lemma V_comm : forall w : nat -> nat -> t,
                   V (fun n => V (fun m => w n m)) = V (fun m => V (fun n => w n m)).
  Proof.
    intros.
    unfold Feq.
    split; repeat (apply v_univ; intro).
    - (* <= *)
      apply le_trans with (y := V (fun n1 => w n1 n0)).
      smart_V_le n.
      smart_V_le n0.

    - (* >= *)
      apply le_trans with (y := V (fun m => w n0 m)).
      smart_V_le n.
      smart_V_le n0.
  Qed.

  Definition my_pairer w (n : nat) : t := w (fst (bijNNinv n)) (snd (bijNNinv n)).

  Lemma V_pair : forall w : nat -> nat -> t,
                   V (fun n => w (fst (bijNNinv n)) (snd (bijNNinv n))) =
                   V (fun n => V (fun m => w n m)).
  Proof.
    intro.
    unfold Feq. split.

    - (* <= *)
      apply v_univ. intro.
      smart_V_le (fst (bijNNinv n)).
      smart_V_le (snd (bijNNinv n)).

    - (* >= *)
      repeat (apply v_univ; intro).
      assert (w n n0 = (my_pairer w (bijNN (n,n0)))).
      unfold my_pairer.
      rewrite bijNNinv_bijNN.
      reflexivity.
      rewrite H.
      apply v_le.
  Qed.

  (** ** Distributivity *)

  Lemma cdistr_r: forall x u, V (fun n => x ⊓ (u n)) ≤ x ⊓ (V u).
  Proof.
    intros.
    apply v_univ. intro.
    apply meet_le.
    apply le_refl.
    eapply v_le.
  Qed.

  Lemma cdistr : forall x u, x ⊓ (V u) = V (fun n => x ⊓ (u n)).
  Proof.
    intros. split.
    apply cdistr_l.
    apply cdistr_r.
  Qed.

  Lemma V_meet : forall a b, V a ⊓ V b = V (fun n => a (bijNN1 n) ⊓ b (bijNN2 n)).
  Proof.
    intros.
    split.
    - rewrite cdistr.
      apply v_univ.
      intro.
      assert (V a ⊓ b n = b n ⊓ V a) by (apply meet_comm).
      rewrite H, cdistr.
      apply v_univ.
      intro.
      set (h := (fun n1 => a (bijNN1 n1) ⊓ b (bijNN2 n1))).
      assert (b n ⊓ a n0 = h (bijNN (n0,n))).
      unfold h ; rewrite bijNN1_eq, bijNN2_eq ; apply meet_comm.
      rewrite H0 ; apply v_le.

    - apply v_univ. intro.
      apply meet_univ.
      + apply le_trans with (y := a (bijNN1 n)).
        apply meet_l.
        apply v_le.
      + apply le_trans with (y := b (bijNN2 n)).
        apply meet_r.
        apply v_le.
  Qed.

  (** ** Finite joins
      It seems easier to first define finite joins
      and then to define binary joins, so that we 
      have a distributive lattice, even if this 
      distributive lattice gives us again the finite
      joins.

    *)
  
  Require Import SeqOfList.

  Instance t_po : Preorder le.
  Proof. apply msl_preorder. Defined.
  Existing Instance setoid_msl.
  
  Definition Vf (l : list t) : t := V (seq_of_list l).

  Add Morphism Vf : Vf_morphism.
  Proof.
    intros. unfold Vf.
    apply V_morphism.
    apply seq_of_list_morphism.
    apply setoid_msl. apply t_po.
    assumption.
  Qed.

  Lemma Vf_nil : Vf [] = ⊥.
  Proof.
    unfold Vf, seq_of_list.
    apply V_bot.
  Qed.

  Hint Resolve Vf_nil.
  
  Definition joinf (u v : list t) := u ++ v.
  Instance joinf_join : Join (list t) := joinf.

  (** ** Binary joins *)
  
  Definition joinb (u v : t) := Vf [u ; v].
  Instance joinb_join : Join t := joinb.

  Ltac unfold_joinb :=
    unfold join, joinb_join, joinb, Vf.
  
  Lemma joinb_l : forall u v : t, u ≤ u ⊔ v.
  Proof.
    intros.
    unfold_joinb. simpl.
    set (f := (u ::: v ::: (fun _ :nat => ⊥))).
    assert (u = f O) by reflexivity.
    rewrite H. apply v_le.
  Qed.

  Lemma joinb_r : forall u v : t, v ≤ u ⊔ v.
  Proof.
    intros ; unfold_joinb ; simpl.
    set (f := (u ::: v ::: (fun _ : nat => ⊥))).
    assert (v = f (S O)) by reflexivity.
    rewrite H. apply v_le.
  Qed.

  Lemma joinb_univ : forall u v w : t, u ≤ w -> v ≤ w -> u ⊔ v ≤ w.
  Proof.
    intros ; unfold_joinb ; simpl.
    apply v_univ ; intro.
    destruct n ; simpl ; try assumption.
    destruct n ; simpl ; try assumption.
    apply bot_le.
  Qed.

  Lemma joinb_distr : forall u v w, u ⊓ (v ⊔ w) ≤ (u ⊓ v) ⊔ (u ⊓ w).
  Proof.
    intros.
    unfold_joinb.
    apply le_trans with (y := V (fun n => u ⊓ (seq_of_list [v;w] n))).
    apply cdistr_l.
    unfold seq_of_list.
    apply v_univ. intro.
    destruct n ; simpl.
    smart_V_le O.
    destruct n ; simpl.
    smart_V_le (S O).
    rewrite meet_bot_r.
    apply bot_le.
  Qed.

  Instance dl_frame : DistrLattice le :=
    MkDistrLattice
      t
      le
      frame_msl
      joinb
      joinb_l
      joinb_r
      joinb_univ
      joinb_distr.



  (** ** Compactness *)

  Fixpoint partial_V (u : (nat -> t)) (n : nat) : t :=
    match n with
      | 0 => ⊥
      | S n => (u O) ⊔ (partial_V (V_tail u) n)
    end.

  Lemma partial_V_le : forall u n, partial_V u n ≤ V u.
  Proof.
    intros.
    generalize u as w.
    induction n.

    - (* 0 *)
      intros.
      apply bot_le.

    - (* S n *)
      intros.
      simpl.
      apply joinb_univ.
      apply v_le.
      apply (le_trans _ (V (V_tail w)) _).
      apply IHn.
      apply v_univ.
      intro. unfold V_tail.
      apply v_le.
  Qed.

  Definition compact := forall u, (V u = ⊤) -> (exists n, partial_V u n = ⊤).

(** One way to define finite or infinite enumerations would
     be to use streams, like this:

<<
  CoInductive enumeration (T : Type) :=
  | ENil : enumeration T
  | ECons : T -> enumeration T -> enumeration T.
>>
 
  The problem with this definition is that we can't decide
  whether the enumeration is finite or not.
 *)

End Frame_Definition.


Add Parametric Morphism (T : Type) (Tle : Le T) (Tf : Frame) : V with signature (pointwise_relation nat Feq ==> Feq) as f_V_morphism.
Proof.
  apply V_morphism.
Qed.


(** * Frame morphisms *)

Section Frame_Morphism_Definition.
  Context {tA : Type}.
  Context {leA : Le tA}.
  Existing Instance Feq_equiv.
  
  Context {tB : Type}.
  Context {leB : Le tB}.

  Require Import Coq.Program.Basics.

  Variable (FA : @Frame tA leA).
  Variable (FB : @Frame tB leB).

  Definition mslA := @frame_msl tA leA FA.
  Definition mslB := @frame_msl tB leB FB.

  Open Scope program_scope. (* for ∘ (function composition) *)
  Existing Instance joinb_join.

  Variable (f : tA -> tB).
  Class FMorphism :=
    MkFMorphism
      {
        fmorph_mslmorph : MSLMorphism mslA mslB f;
        (* preserves countable joins *)
        morph_V: forall u : nat -> tA, f (V u) = V (f ∘ u)
      }.

  Existing Instance listeq_equiv.

  Variable fmorph : FMorphism.
  Existing Instance fmorph.

  Proposition FMorphism_join : forall a b, f (a ⊔ b) = f a ⊔ f b.
  Proof.
    intros.
    unfold join, joinb_join, joinb.
    assert ([f a; f b] = map f [a; b]) by reflexivity.
    unfold Vf.
    rewrite H.
    rewrite seq_of_list_compose.
    apply morph_V.
    apply Feq_equivalence.
    apply msl_preorder.
    apply mslmorph_bot.
    apply fmorph_mslmorph.
  Qed.

End Frame_Morphism_Definition.



(* exported_tactics *)
Ltac smart_V_le n :=
  apply (V_le_le n);
  simpl;
  try (apply le_refl).
