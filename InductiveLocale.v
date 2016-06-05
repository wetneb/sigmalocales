
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


Section Definition_Inductive_Locale.

  (* meet semilattice of generators *)
  Variable T : Type.
  Variable Teq : Equiv T.
  Axiom Tso : Setoid T.
  Variable Tmeet : Meet T.
  Variable Tmsl : MeetSemiLattice T.
  Definition Tle := default_meet_sl_le.

  Definition csg_meet : CommutativeSemiGroup T.
  Proof.
    apply meet_semilattice.
    apply Tmsl.
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
    unfold Tle. unfold default_meet_sl_le.
    rewrite <- H2. apply H.
    apply (cr_inf y U b i H4 H3).

    (* cr_left *)
    assert (y <= b).
    unfold Tle, default_meet_sl_le.
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
  
  Definition Covrel (U : nat -> T) (V : nat -> T) :=
    forall n : nat, (U n) ◁ V.

  Lemma cr_trans : forall (a : T) (U W : nat -> T), a ◁ U -> Covrel U W -> a ◁ W.
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

  (* Injection of a covering into another *)
  Definition cov_inj (U W : nat -> T) :=
    forall n, exists m, U n = W m.

  Lemma cr_right : forall a U W, a ◁ U -> cov_inj U W -> a ◁ W.
  Proof.
    intros.
    apply cr_trans with (U := U).
    apply H.
    unfold Covrel ; intro.
    unfold cov_inj in H0.
    destruct (H0 n) as [m Heq].
    apply cr_refl with (n:=m).
    symmetry. exact Heq.
  Qed.

  (******************************************)
  (* Admissibility of the localization rule *)
  (******************************************)

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
    

  Lemma Tmeet_le_r : forall a b c, a <= b -> c ⊓ a <= c ⊓ b.
  Proof.
    intros.
    (* rewrite comsg_ass *)
    unfold Tle, default_meet_sl_le.
    rewrite Tmeet_assoc.
    assert (a ⊓ (c ⊓ b) = c ⊓ a).
    rewrite Tmeet_comm.
    rewrite Tmeet_assoc.
    unfold Tle, default_meet_sl_le in H.
    rewrite Tmeet_comm in H.
    rewrite H. reflexivity.
    rewrite H0. rewrite <- Tmeet_assoc.
    rewrite (Tmeet_idem). reflexivity.
  Qed.    
  
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
    unfold Tle, default_meet_sl_le.
    unfold Tle, default_meet_sl_le in H.
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

  Definition coveq := pointwise_relation nat Teq.
  Lemma Meet_proper : Proper (coveq ==> coveq ==> coveq) Meet.
  Proof.
    unfold Proper, respectful, coveq, pointwise_relation.
    intros.
    unfold Meet.
    specialize (H (bijNN1 a)).
    rewrite H.
    specialize (H0 (bijNN2 a)).
    rewrite H0.
    reflexivity.
  Qed.
  
  Add Morphism Meet : Meet_morphism.
  Proof.
    apply Meet_proper.
  Qed.

  Infix "⊓" := (Meet) (at level 50).

  Ltac simpl_bijNN :=
    rewrite bijNN1_eq, bijNN2_eq ; simpl.
  Ltac Meet_refl a b :=
    apply cr_refl with (n := bijNN (a,b)) ;
    try (unfold Meet) ;
    simpl_bijNN.

  (* Commutativity of meet *)
  Lemma Meet_covrel_comm : forall a U W, a ◁ U ⊓ W -> a ◁ W ⊓ U.
  Proof.
    intros.
    apply cr_right with (U := U ⊓ W).
    apply H.
    unfold cov_inj.
    intro.
    exists (bijNN (bijNN2 n,bijNN1 n)).
    unfold Meet.
    rewrite bijNN1_eq, bijNN2_eq. simpl.
    rewrite Tmeet_comm. reflexivity.
  Qed.

  Lemma cr_refl_cr_inf :
    forall a b U W, forall i : Idx b, a <= b ->
                            (forall n, Tmeet a (CovAx b i n) ◁ W) ->
                            forall m, (U m) = a ->
                                 a ◁ U ⊓ W.
  Proof.
    intros.
    apply cr_inf with (b := b) (i := i).
    apply H.
    intro n.
    apply cr_right with (U := a ↓ W).
    assert ((Tmeet a (Tmeet a (CovAx b i n))) ◁ a ↓ W).
    apply cr_loc ; apply (H0 n).
    rewrite <- Tmeet_assoc in H2.
    rewrite Tmeet_idem in H2.
    apply H2.
    (* cov_inj *)
    unfold cov_inj ; intros p.
    exists (bijNN (m,p)).
    unfold Meet. simpl_bijNN.
    unfold down. rewrite H1. reflexivity.
  Qed.

  
  (* Admissibility of the meet rule *)
  Proposition cr_meet : forall a U W, a ◁ U -> a ◁ W -> a ◁ U ⊓ W.
  Proof.
    intros a U W TU TW.

    induction TU as [a | a | a].

    (***** cr_refl ******)
    induction TW as [ a W| a W | a W].

    (* cr_refl, cr_refl *)
    Meet_refl n n0.
    rewrite H, H0. rewrite (idempotency Tmeet a).
    reflexivity.

    (* cr_refl, cr_inf *)
    About cr_refl_cr_inf.
    apply (cr_refl_cr_inf a b U W i H0 H1 n H).
    
    (* cr_refl, cr_left *)
    apply cr_trans with (U := a ↓ W).
    (* a ◁ a ↓ W *)
    unfold Tle, default_meet_sl_le in H0.
    assert (Tmeet a b ◁ a ↓ W).
    apply cr_loc ; apply TW.
    rewrite H0 in H1.
    apply H1.
    (* Covrel *)
    unfold Covrel. intro. unfold down.
    Meet_refl n n0.
    rewrite H. reflexivity.

    (******* cr_inf *******)
    induction TW as [a | a | a].

    (* cr_inf, cr_refl *)
    apply Meet_covrel_comm.
    About cr_refl_cr_inf.
    apply (cr_refl_cr_inf a b U0 U i H H0 n H2).
    
    (* cr_inf, cr_inf *)
    (* TODO *)
    

    (******* cr_left ******)
  
End Definition_Inductive_Locale.