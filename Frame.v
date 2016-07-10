
Require Import MathClasses.interfaces.canonical_names.
Require Import Coq.Lists.List.
Require Import BijNat.
Require Import MeetSemiLattice.
Require Import PreorderEquiv.

Section Frame_Definition.

Class Frame {t:Type} {le: Le t} :=
  MkFrame {
      frame_msl :> @MeetSemiLattice t le;

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


  (* Countable join and binary join *)

  (*
  Lemma join_V : forall x u, x ⊔ (V u) = V (x :: u).
  Proof.
    intros.
    split.
    apply join_univ.
    assert ((x :: u) O ≤ V (x :: u)).
    apply (v_le (x :: u) O).
    simpl in H. assumption.
    apply (v_univ _ _ (fun n => v_le (x :: u) (S n))).

    apply v_univ.
    intros.
    destruct n.

    simpl. apply join_l.
    simpl. apply (le_trans _ (V u) _).
    apply v_le. apply join_r.
  Qed.
*)
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
                   V (fun n => w (fst (bijNNinv n)) (snd (bijNNinv n))) =
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


  (****************)
  (* Finite joins *)
  (****************)

  
  Definition V_cons (x : t) (u : nat -> t) (n : nat) :=
    match n with
      | 0 => x
      | S n => u n
    end.
  Infix ":::" := V_cons (right associativity, at level 60).
  
  Definition V_tail (u : nat -> t) (n : nat) := u (S n).

  Fixpoint seq_of_list (l : list t) : (nat -> t) :=
    match l with
      | [] => fun _ => ⊥
      | h :: q => h ::: (seq_of_list q)
    end.

  Inductive listeq : forall u v : list t, Prop :=
  | listeq_nil : listeq nil nil
  | listeq_cons : forall a b u v, a = b -> listeq u v -> listeq (a :: u) (b :: v).
  Instance listeq_equiv : Equiv (list t) := listeq.
  Definition listeq_equivalence : Equivalence listeq.
  Proof.
    apply Build_Equivalence ; unfold Reflexive, Transitive, Symmetric.
    induction x.
    apply listeq_nil.
    apply listeq_cons ; auto.
    induction x ; intros.
    inversion H. apply listeq_nil.
    inversion H. subst. apply listeq_cons.
    symmetry. apply H2. apply IHx. assumption.
    induction x ; intros.
    inversion H ; subst ; assumption.
    inversion H ; subst.
    inversion H0 ; subst.
    apply listeq_cons ; auto.
    apply IHx with (y := v) ; assumption.
  Qed.
  Add Setoid (list t) listeq listeq_equivalence as listeq_setoid.

  Definition Vf (l : list t) : t := V (seq_of_list l).

  Add Morphism seq_of_list with signature
      (listeq ==> pointwise_relation nat Feq) as seq_of_list_morphism.
  Proof.
    unfold pointwise_relation.
    induction x ; intros ; inversion H ; subst.
    reflexivity.
    destruct a0 ; simpl.
    + assumption.
    + apply IHx. assumption.
  Qed.

  Add Morphism Vf : Vf_morphism.
  Proof.
    intros. unfold Vf.
    apply V_morphism.
    apply seq_of_list_morphism.
    assumption.
  Qed.

  Lemma Vf_nil : Vf [] = ⊥.
  Proof.
    unfold Vf, seq_of_list.
    apply V_bot.
  Qed.

  Hint Resolve Vf_nil.
  (****************)
  (* Binary joins *)
  (****************)
  
  Definition joinb (u v : t) := Vf [u ; v].
  Instance joinb_join : Join t := joinb.

  Ltac unfold_joinb :=
    unfold join, joinb_join, joinb, Vf.
  
  Lemma join_l : forall u v : t, u ≤ u ⊔ v.
  Proof.
    intros.
    unfold_joinb. simpl.
    set (f := (u ::: v ::: (fun _ :nat => ⊥))).
    assert (u = f O) by reflexivity.
    rewrite H. apply v_le.
  Qed.

  Lemma join_r : forall u v : t, v ≤ u ⊔ v.
  Proof.
    intros ; unfold_joinb ; simpl.
    set (f := (u ::: v ::: (fun _ : nat => ⊥))).
    assert (v = f (S O)) by reflexivity.
    rewrite H. apply v_le.
  Qed.

  Lemma join_univ : forall u v w : t, u ≤ w -> v ≤ w -> u ⊔ v ≤ w.
  Proof.
    intros ; unfold_joinb ; simpl.
    apply v_univ ; intro.
    destruct n ; simpl ; try assumption.
    destruct n ; simpl ; try assumption.
    apply bot_le.
  Qed.

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

  Lemma join_comm : forall x y:t, x ⊔ y = y ⊔ x.
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

  (* Equivalent definitions of the order *)
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

  (****************)
  (* Finite joins *)
  (****************)
  
  Definition joinf (u v : list t) := u ++ v.
  Instance joinf_join : Join (list t) := joinf.

  (*
  Lemma joinf_correct : forall u v, Vf (u ⊔ v) = Vf u ⊔ Vf v.
  Proof.
    *)

  (* Finite meets *)
  Definition meet_x_l (a : t) :=
    map (fun b => a ⊓ b).

  Definition meetf (u v : list t) :=
    concat (map (fun b => meet_x_l b u) v).
  Instance meetf_meet : Meet (list t) := meetf.

  Lemma meet_x_l_correct : forall a u, Vf (meet_x_l a u) = a ⊓ Vf u.
  Proof.
    intros.
    unfold Vf.
    rewrite cdistr.
    apply V_morphism.
    induction u ; intros.
    simpl. rewrite meet_bot_r. reflexivity.
    destruct n ; simpl.
    reflexivity.
    apply IHu.
  Qed.

  (*
  Lemma meetf_correct : forall u v, Vf (u ⊓ v) = (Vf u) ⊓ (Vf v).
  Proof.
    intro.
    induction v ; simpl.
    - rewrite Vf_nil, meet_bot_r.
      unfold meet, meetf_meet, meetf. simpl.
      rewrite Vf_nil. reflexivity.
    - unfold meet, meetf_meet, meetf, concat, map. simpl.
      
    *)  
   
  
(*
  Lemma v_binlist : forall x y, V (x :: y :: (fun _ => ⊥)) = x ⊔ y.
  Proof.
    intros.
    setoid_rewrite <- join_V.
    setoid_rewrite <- join_V.
    setoid_rewrite V_bot.
    setoid_rewrite join_bot_r.
    reflexivity.
  Qed. 

  Lemma fdistr : forall x y z, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z).
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
  Qed. *)

  (* Compactness ! *)

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

  Definition compact := forall u, (V u = ⊤) -> (exists n, partial_V u n = ⊤).

(* One way to define finite or infinite enumerations would
     be to use streams, like this:

  CoInductive enumeration (T : Type) :=
  | ENil : enumeration T
  | ECons : T -> enumeration T -> enumeration T.
 
  The problem with this definition is that we can't decide
  whether the enumeration is finite or not.
 *)

End Frame_Definition.

Add Parametric Morphism (T : Type) (Tle : Le T) (Tf : @Frame T Tle) : (@joinb T Tle Tf) with signature (Feq ==> Feq ==> Feq) as f_join_morphism.
Proof.
  apply join_morphism.
Qed.

Add Parametric Morphism (T : Type) (Tle : Le T) (Tf : Frame) : V with signature (pointwise_relation nat Feq ==> Feq) as f_V_morphism.
Proof.
  apply V_morphism.
Qed.

  (*
Add Parametric Relation (T : Type) (Tle : Le T) (Tmsl : MeetSemiLattice): T Feq
    reflexivity proved by (Feq_refl Tle Tmsl)
    symmetry proved by (Feq_sym Tle Tmsl)
    transitivity proved by (Feq_trans Tle Tmsl)
      as setoid_msl.
*)


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

End Frame_Morphism_Definition.
