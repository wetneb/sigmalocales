
(* formalization of Theorem 3.3 in 
 * Thierry Coquand , Giovanni Sambin , Jan Smith , Silvio Valentini
 * Inductively generated formal topologies
 * http://doai.io/10.1016/S0168-0072(03)00052-6
 *)

Require Import Coq.Structures.Orders.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.lattices.
Require Import BijNat.
Require Import Frame.

Section Definition_Inductive_Locale.

  (* meet semilattice of generators *)
  Variable T : Type.
  Variable Teq : Equiv T.
  Axiom Tso : Setoid T.
  Variable Tmeet : Meet T.
  Variable Tmsl : MeetSemiLattice T.
  Definition Tle := fun a b => Teq (a ⊓ b) a.
  Variable Tbot : T.
  Axiom Tbot_absorb : forall t : T, Teq (Tmeet Tbot t) Tbot.
  Variable Ttop : T.
  Axiom Ttop_id : forall t : T, Teq (Tmeet t Ttop) t.

  Definition csg_meet : CommutativeSemiGroup T.
  Proof.
    apply meet_semilattice.
    apply Tmsl.
    Show Proof.
  Defined.

  Infix "<=" := Tle (at level 70).
  
  (* For each generator, an index set for its coverings *)
  Variable Idx : forall t:T, Set.
  Axiom Idx_proper : forall x y, Teq x y -> Idx x ≡ Idx y.
  (* For each generator and index of covering, an index of *)
  (* Variable CovIdx : forall t:T, forall i:Idx t, Type.
  set to nat for our purposes
  *)
  Variable CovAx : forall t:T, forall i:Idx t, (nat -> T).
  Definition CovAx_rect : forall s t: T, Teq s t -> Idx s -> Idx t.
    intros.
    rewrite  <-(Idx_proper s t H).
    exact H0.
  Qed.
  Axiom CovAx_proper : forall s t:T, forall H : Teq s t, forall i : Idx s,
     forall n : nat, Teq (CovAx s i n) (CovAx t (CovAx_rect s t H i) n).

  (* Setoids *)
  Add Setoid T Teq Tso as setoid_T.
  Add Morphism Idx : Idx_morphism.
  Proof.
    apply Idx_proper.
  Qed.
  About Idx_morphism.
  Lemma Idx_funny_mor : CMorphisms.Proper (CMorphisms.respectful Teq CRelationClasses.arrow) Idx.
  Proof.
    unfold CMorphisms.Proper, CMorphisms.respectful.
    intros. unfold CRelationClasses.arrow.
    rewrite (Idx_morphism x y H).
    trivial.
  Qed.
(*  Add Parametric Morphism : Idx with signature (Teq ==> CRelationClasses.arrow) as Idx_fmor. *)

  (************************************************)
  (* Lemmas on the meet on generators *)
  (************************************)

  Lemma Tmeet_assoc : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
  Proof.
    intros.
    symmetry.
    apply sg_ass.
    apply comsg_setoid.
    apply semilattice_sg.
    apply meet_semilattice.
    exact Tmsl.
  Qed.

  Lemma Tmeet_comm : forall a b, a ⊓ b = b ⊓ a.
  Proof.
    intros.
    apply comsg_ass.
    apply meet_semilattice.
    exact Tmsl.
  Qed.

  Lemma Tmeet_idem : forall a, a ⊓ a = a.
  Proof.
    intro. apply (idempotency Tmeet).
    apply meet_semilattice.
    exact Tmsl.
  Qed.

  Lemma Tle_refl : forall a, a <= a.
  Proof.
    intro. unfold Tle. rewrite Tmeet_idem. reflexivity.
  Qed.

  Lemma Tmeet_le_l : forall a b, a ⊓ b <= a.
  Proof.
    intros.
    unfold Tle.
    rewrite Tmeet_comm.
    rewrite <- Tmeet_assoc.
    rewrite Tmeet_idem.
    reflexivity.
  Qed.

  Lemma Tmeet_le_r : forall a b c, a <= b -> c ⊓ a <= c ⊓ b.
  Proof.
    intros.
    (* rewrite comsg_ass *)
    unfold Tle.
    rewrite Tmeet_assoc.
    assert (a ⊓ (c ⊓ b) = c ⊓ a).
    rewrite Tmeet_comm.
    rewrite Tmeet_assoc.
    unfold Tle in H.
    rewrite Tmeet_comm in H.
    rewrite H. reflexivity.
    rewrite H0. rewrite <- Tmeet_assoc.
    rewrite (Tmeet_idem). reflexivity.
  Qed.

  Lemma Tbot_le : forall t, Tbot <= t.
  Proof.
    intro. unfold Tle.
    apply Tbot_absorb.
  Qed.

  Lemma Ttop_le : forall t, t <= Ttop.
  Proof.
    intro. unfold Tle.
    apply Ttop_id.
  Qed.
    
  Add Morphism Tle : Tle_morphism.
  Proof.
    intros x y H1 u v H2. unfold Tle.
    split ; intro.
    rewrite <- H1, <- H2. apply H.
    rewrite H1, H2. apply H.
  Qed.
  
  (*******************************************)
  (******* Operations on coverings ***********)
  (*******************************************)

  Definition down (a : T) (U : nat -> T) : nat -> T :=
    fun n => Tmeet a (U n).

  Infix "↓" := down (at level 50).


  (* Now we can define the inductive topology! *)
  Inductive covrel (a : T) : (nat -> T) -> Prop :=
  | cr_refl : forall (U : nat -> T) (n : nat), (Teq (U n) a) -> covrel a U
  | cr_inf : forall U : nat -> T, forall b : T, forall i:Idx b, a <= b -> (forall n, covrel (Tmeet a (CovAx b i n)) U) -> covrel a U
  | cr_left : forall U : nat -> T, forall b : T, a <= b -> covrel b U -> covrel a U.
  Infix "◁" := (covrel) (at level 60).

  (* covrel is a morphism *)
  Lemma covrel_Teq : forall x: T, forall U : (nat -> T), (x ◁ U) -> forall y :T,  (Teq x y) -> y ◁ U.
  Proof.
    intros x U H.
    induction H ; intros.

    (* cr_refl *)
    apply (cr_refl y U n).
    rewrite <- H0.
    apply H.

    (* cr_inf *)
    assert (forall n, (Tmeet y (CovAx b i n)) ◁ U).
    intro n.
    apply (H1 n (Tmeet y (CovAx b i n))).
    rewrite H2 ; reflexivity.
    assert (y <= b).
    unfold Tle.
    rewrite <- H2. apply H.
    apply (cr_inf y U b i H4 H3).

    (* cr_left *)
    assert (y <= b).
    unfold Tle.
    rewrite <- H1. apply H.
    apply (cr_left y U b H2).
    apply H0.
  Qed.
    
  Lemma covrel_proper : Proper (Teq ==> eq ==> iff) covrel.
  Proof.
    unfold Proper, respectful.
    intros.
    split ; intro.
    
    rewrite <- H0.
    apply (covrel_Teq x x0 H1 y H).

    rewrite H0.
    apply (covrel_Teq y y0 H1 x).
    symmetry. apply H.
  Qed.
  Add Parametric Morphism : covrel with signature (Teq ==> eq ==> iff) as covrel_morphism.
  Proof.
    intros. apply covrel_proper. apply H. reflexivity.
  Qed.

  
  (**********************************************)
  (* Preorder and equivalence between coverings *)
  (**********************************************)
  
  Definition Covrel (U : nat -> T) (V : nat -> T) :=
    forall n : nat, (U n) ◁ V.

  Infix "⩽" := Covrel (at level 60).

  Lemma cr_trans : forall (a : T) (U W : nat -> T), a ◁ U -> U ⩽ W -> a ◁ W.
  Proof.
    intros a U W CR.
    generalize W ; clear W.
    induction CR ; intros.

    (* cr_left *)
    unfold Covrel in H0.
    rewrite <- H. apply (H0 n).

    (* cr_inf *)
    assert (forall n, (Tmeet a (CovAx b i n)) ◁ W).
    intro n ; apply (H1 n). apply H2.
    apply (cr_inf a W b i H H3).
    
    (* cr_left *)
    apply cr_left with (b := b).
    apply H.
    apply IHCR ; apply H0.
  Qed.

  Lemma Covrel_refl : Reflexive Covrel.
  Proof.
    unfold Reflexive.
    intros.
    unfold Covrel.
    intro. apply cr_refl with (n:=n).
    reflexivity.
  Qed.
    
  Lemma Covrel_trans : Transitive Covrel.
  Proof.
    unfold Transitive.
    intros.
    unfold Covrel; intro.
    apply cr_trans with (U := y).
    apply (H n). apply H0.
  Qed.

  (* TODO refactor this into an independent file *)
  (* We use it everywhere already *)
  Definition Coveq (U V : nat -> T) := U ⩽ V /\ V ⩽ U.

  Lemma Coveq_refl : Reflexive Coveq.
  Proof.
    unfold Reflexive ; intro.
    unfold Coveq ; split ; apply Covrel_refl.
  Qed.

  Lemma Coveq_trans : Transitive Coveq.
  Proof.
    unfold Transitive, Coveq ; intros.
    destruct H, H0.
    split ; apply Covrel_trans with (y := y).
    apply H. apply H0. apply H2. apply H1.
  Qed.

  Lemma Coveq_sym : Symmetric Coveq.
  Proof.
    unfold Symmetric, Coveq ; intros.
    destruct H ; split.
    apply H0. apply H.
  Qed.

  Definition Coveq_equiv := Build_Equivalence Coveq Coveq_refl Coveq_sym Coveq_trans.
  Instance Coveq_equiv_ : Equiv (nat -> T) := Coveq.

  Add Setoid (nat -> T) Coveq Coveq_equiv as Coveq_setoid.
  Add Morphism Covrel : Covrel_morphism.
  Proof.
    unfold Coveq.
    intros.
    destruct H, H0.
    split.
    intro.
    apply Covrel_trans with (y := x) ; auto.
    apply Covrel_trans with (y := x0) ; auto.
    intro.
    apply Covrel_trans with (y := y) ; auto.
    apply Covrel_trans with (y := y0) ; auto.
  Qed.

  Add Morphism covrel : covrel_morphism2.
  Proof.
    intros x y Heq U W H.
    destruct H as [Hl Hr].
    split ; intro.
    apply cr_left with (b := x).
    rewrite Heq ; apply Tle_refl.
    apply cr_trans with (U := U) ; auto.

    apply cr_left with (b := y).
    rewrite Heq ; apply Tle_refl.
    apply cr_trans with (U := W) ; auto.
  Qed.
  
  (* Injection of a covering into another *)
  Definition cov_inj (U W : nat -> T) :=
    forall n, exists m, U n = W m.

  Lemma cov_inj_Covrel : forall U W, cov_inj U W -> U ⩽ W.
  Proof.
    intros.
    unfold Covrel ; intro.
    unfold cov_inj in H.
    destruct (H n) as [m Heq].
    apply cr_refl with (n:=m).
    symmetry. exact Heq.
  Qed.

  Ltac by_cov_inj :=
    try (apply cov_inj_Covrel) ;
    unfold cov_inj ;
    intro.
  
  Lemma cr_right : forall a U W, a ◁ U -> cov_inj U W -> a ◁ W.
  Proof.
    intros.
    apply cr_trans with (U := U).
    apply H.
    apply cov_inj_Covrel.
    apply H0.
  Qed.

  (******************************************)
  (* Admissibility of the localization rule *)
  (******************************************)
  
  Proposition cr_loc : forall a b U, a ◁ U -> Tmeet b a ◁ b ↓ U.
  Proof.
    intros a b U HR.
    induction HR as [a | a | a].

    (* cr_refl *)
    apply cr_refl with (n := n).
    unfold down ; simpl.
    rewrite H ; reflexivity.

    (* cr_inf *)
    apply cr_inf with (b := b0) (i := i).
    unfold Tle.
    unfold Tle in H.
    rewrite Tmeet_assoc.
    rewrite H; reflexivity.
    intro n.
    rewrite Tmeet_assoc.
    apply (H1 n).

    (* cr_left *)
    apply cr_left with (b := b ⊓ b0).
    apply Tmeet_le_r ; apply H.
    apply IHHR.    
  Qed.

  (*********************)
  (* Meet on coverings *)
  (*********************)
  Definition Meet (U : nat -> T) (W : nat -> T) : nat -> T :=
    fun n => Tmeet (U (bijNN1 n)) (W (bijNN2 n)).

  Infix "⊓" := (Meet) (at level 50).

  Ltac simpl_bijNN :=
    rewrite bijNN1_eq, bijNN2_eq ; simpl.
  Ltac Meet_refl a b :=
    apply cr_refl with (n := bijNN (a,b)) ;
    try (unfold Meet) ;
    simpl_bijNN.

  (* Commutativity of meet *)
  Lemma Meet_cov_inj_comm : forall U W, cov_inj (U ⊓ W) (W ⊓ U).
  Proof.
    intros.
    unfold cov_inj.
    intro.
    exists (bijNN (bijNN2 n,bijNN1 n)).
    unfold Meet.
    rewrite bijNN1_eq, bijNN2_eq. simpl.
    rewrite Tmeet_comm. reflexivity.
  Qed.

  Lemma Meet_comm : forall U W, U ⊓ W = W ⊓ U.
  Proof.
    intros.
    split ; apply cov_inj_Covrel ; apply Meet_cov_inj_comm.
  Qed.
  
  Lemma Meet_covrel_comm : forall a U W, a ◁ U ⊓ W -> a ◁ W ⊓ U.
  Proof.
    intros.
    apply cr_right with (U := U ⊓ W).
    apply H.
    apply Meet_cov_inj_comm.
  Qed.
  
  (* Admissibility of the meet rule *)
  Proposition cr_meet : forall a U W, a ◁ U -> a ◁ W -> a ◁ U ⊓ W.
  Proof.
    intros a U W TU TW.

    assert (Tmeet a a ◁ a ↓ U).
    apply (cr_loc a a U TU).
    rewrite Tmeet_idem in H.

    apply cr_trans with (U := a ↓ U).
    apply H.
    
    (* Covrel *)
    unfold Covrel. intros p.
    unfold down.
    apply cr_right with (U := (U p) ↓ W).
    rewrite Tmeet_comm. apply cr_loc. apply TW.
    (* cov_inj *)
    by_cov_inj.
    exists (bijNN (p,n)).
    unfold Meet. simpl_bijNN.
    unfold down. reflexivity.
  Qed.

  (* Universality of meet on coverings for ⩽ *)
  Proposition Meet_univ : forall U W Z, Z ⩽ U -> Z ⩽ W -> Z ⩽ U ⊓ W.
  Proof.
    unfold Covrel.
    intros.
    apply cr_meet.
    apply (H n).
    apply (H0 n).
  Qed.

  Proposition Meet_l : forall U W, U ⊓ W ⩽ U.
  Proof.
    unfold Covrel.
    intros.
    unfold Meet.
    apply cr_left with (b := U (bijNN1 n)).
    apply Tmeet_le_l.
    apply cr_refl with (n := bijNN1 n).
    reflexivity.
  Qed.

  Proposition Meet_r : forall U W, U ⊓ W ⩽ W.
  Proof.
    intros.
    rewrite Meet_comm.
    apply Meet_l.
  Qed.
  
  (**********************)
  (* Union of coverings *)
  (**********************)

  Definition Join (U W : nat -> T) :=
    fun n => match bijNpNinv n with
            | inl m => U m
            | inr m => W m
          end.

  Infix "⊔" := Join (at level 50).

  Lemma Join_cov_inj_comm : forall U W, cov_inj (U ⊔ W) (W ⊔ U).
  Proof.
    unfold cov_inj, Join. intros.
    destruct (bijNpNinv n).
    exists (bijNpN (inr n0)).
    rewrite bijNpN_bij2. reflexivity.
    exists (bijNpN (inl n0)).
    rewrite bijNpN_bij2. reflexivity.
  Qed.

  Lemma Join_comm : forall U W, U ⊔ W = W ⊔ U.
  Proof.
    intros.
    split ; apply cov_inj_Covrel ; apply Join_cov_inj_comm.
  Qed.

  Lemma Join_l : forall U W, U ⩽ U ⊔ W.
  Proof.
    intros.
    apply cov_inj_Covrel.
    by_cov_inj.
    exists (bijNpN (inl n)).
    unfold Join.
    rewrite bijNpN_bij2. reflexivity.
  Qed.

  Lemma Join_r : forall U W, W ⩽ U ⊔ W.
  Proof.
    intros.
    rewrite Join_comm.
    apply Join_l.
  Qed.

  Lemma Join_univ : forall U W Z, U ⩽ Z -> W ⩽ Z -> U ⊔ W ⩽ Z.
  Proof.
    intros.
    unfold Covrel ; intro.
    unfold Join ; destruct (bijNpNinv n) ;
    eapply cr_trans ; auto ; apply Covrel_refl.
  Qed.

  Lemma Join_compat_le_l : forall U W Z, U ⩽ W -> U ⊔ Z ⩽ W ⊔ Z.
  Proof.
    intros.
    apply Join_univ.
    apply Covrel_trans with (y := W) ; auto.
    apply Join_l.
    apply Join_r.
  Qed.

  Lemma Join_compat_le_r : forall U W Z, U ⩽ W -> Z ⊔ U ⩽ Z ⊔ W.
  Proof.
    intros.
    rewrite (Join_comm Z U).
    rewrite (Join_comm Z W).
    apply Join_compat_le_l ; assumption.
  Qed.

  (*******************)
  (* Contable join ! *)
  (*******************)

  Definition V (U : nat -> nat -> T) :=
    fun n => U (bijNN1 n) (bijNN2 n).

  Lemma V_le : forall U n, U n ⩽ V U.
  Proof.
    intros.
    by_cov_inj.
    exists (bijNN (n,n0)).
    unfold V.
    rewrite bijNN1_eq, bijNN2_eq.
    reflexivity.
  Qed.

  Lemma V_univ : forall U v, (forall n, U n ⩽ v) -> V U ⩽ v.
  Proof.
    intros.
    unfold V, Covrel.
    intro.
    eapply cr_trans.
    eapply cr_refl. reflexivity.
    eapply H.
  Qed.

  (******************)
  (* Distributivity *)
  (******************)

  Lemma Cdistr_l : forall a U, a ⊓ V U ⩽ V (fun n => a ⊓ U n).
  Proof.
    intros.
    unfold Meet, Covrel. intro.
    apply cr_trans with (U := (a (bijNN1 n) ↓ (V U))).
    apply cr_loc. eapply cr_refl. reflexivity.
    by_cov_inj.
    exists (bijNN (bijNN1 n0, bijNN (bijNN1 n, bijNN2 n0))).
    unfold V, down.
    repeat (rewrite bijNN1_eq, bijNN2_eq ; simpl).
    reflexivity.
  Qed.

  (***************)
  (* Top, bottom *)
  (***************)

  Definition Bot : nat -> T := fun n => Tbot.
  Notation "⊥" := Bot.

  Lemma Bot_le : forall U, ⊥ ⩽ U.
  Proof.
    intro.
    unfold Covrel.
    intro.
    apply cr_left with (b := U O).
    unfold Bot. apply Tbot_le.
    eapply cr_refl.
    reflexivity.
  Qed.

  Definition Top : nat -> T := fun n => Ttop.
  Lemma Top_le : forall U, U ⩽ Top.
  Proof.
    intro.
    unfold Covrel.
    intro.
    apply cr_left with (b := Ttop).
    apply Ttop_le.
    apply cr_refl with (n := O).
    unfold Top. reflexivity.
  Qed.

  Definition FFrame : @Frame (nat -> T) Covrel :=
    MkFrame
      (nat -> T)
      Covrel
      Covrel_refl
      Covrel_trans
      Top
      Top_le
      Bot
      Bot_le
      Meet
      Meet_l
      Meet_r
      Meet_univ
      Join
      Join_l
      Join_r
      Join_univ
      V
      V_le
      V_univ
      Cdistr_l.
  
End Definition_Inductive_Locale.