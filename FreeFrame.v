Require Import MathClasses.interfaces.canonical_names.
Require Import BijNat.
Require Import Frame.
Require Import MeetSemiLattice.
Require Import PreorderEquiv.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.

(**
 This module constructs the free sigma-frame generated
 by a meet semilattice, with relations on the generators.

 It is a formalization of Theorem 3.3 in 
 
 Thierry Coquand, Giovanni Sambin, Jan Smith, Silvio Valentini

 Inductively generated formal topologies
 
 #<a href="http://doai.io/10.1016/S0168-0072(03)00052-6">http://doai.io/10.1016/S0168-0072(03)00052-6</a>#
 *)

Section Free_Frame.
  
(** * Definition of the free frame *)

  (** ** Assumptions *)
  
  (** First we assume a meet semilattice of generators, [T].  Note
      that this structure comes with its own equality (setoid). As in
      the rest of this development, setoid equalities are
      denoted by [a = b], whereas coq's definitional equality is [a ≡
      b] (because we use the setoid equality much more often
      than the definitional one). *)
  Variable T : Type.
  Variable Tle : Le T.
  Variable Tmsl : @MeetSemiLattice T Tle.
  Existing Instance Feq_equiv.
 
  (**
      There are many ways to present the relations (called here
      axioms) that we want to impose on the generated structure.
      Following the paper, restrict the form of axioms to
      inequalities [a ≤ U], where [a] is a generator and [U]
      is a countable set of generators. Any axiom can be 
      written as a conjunction of these.
      These basic axioms are written [a ◁_0 U] in the paper.

      For each generator, we are given an index set for its coverings.
      This formalization allows us to accept an arbitrary number
      of axioms for each generator.

   *)
  Variable Idx : forall t:T, Set.
  (**
      For each generator and an index in its index set,
      we associate a contable family of generators:
      this is understood as enumerating the axiom [t ◁_0 CovAx t i]
  *)
  Variable CovAx : forall t:T, forall i:Idx t, (nat -> T).

  (** ** Inductive covering relation 
    
     The elements of our freely generated structure
     are formal countable unions of generators. Our task
     is therefore define the appropriate frame structure
     on them, starting with the order relation. Again,
     we first restrict the relation to the case where
     the left-hand side is a generator.

     The following inductive definition is very well
     motivated in the paper.
     *)
  Inductive covrel (a : T) : (nat -> T) -> Prop :=
  | cr_refl : forall (U : nat -> T) n, U n = a -> covrel a U
  | cr_inf : forall U : nat -> T, forall b : T, forall i:Idx b, a ≤ b -> (forall n, covrel (a ⊓ (CovAx b i n)) U) -> covrel a U
  | cr_left : forall U : nat -> T, forall b : T, a ≤ b -> covrel b U -> covrel a U.
  (** We note [a ◁ U] when the generator [a] is 
      lower than the formal union [U] *)
  Infix "◁" := (covrel) (at level 60).

  Lemma cr_n : forall U n, U n ◁ U.
  Proof. intros. apply cr_refl with (n := n). reflexivity. Qed.

  (** The covering relation ◁ respects the equality
      on the generators. *)
  Lemma covrel_Teq : forall x U, x ◁ U -> forall y, x = y -> y ◁ U.
  Proof.
    intros.
    destruct H0.
    apply cr_left with (b := x) ; assumption.
  Qed.
    
  Lemma covrel_proper : Proper ((=) ==> eq ==> iff) covrel.
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
  Add Parametric Morphism : covrel with signature ((=) ==> eq ==> iff) as covrel_morphism.
  Proof.
    intros. apply covrel_proper. apply H. reflexivity.
  Qed.
  
 
  (** ** Preorder and equivalence between coverings
      The [◁] relation can now be used to define
      the order relation on terms.
   *)
  
  Definition Covrel (U : nat -> T) (V : nat -> T) :=
    forall n : nat, (U n) ◁ V.
  Instance Covrel_le : Le (nat -> T) := Covrel.
  Ltac unfold_Covrel := unfold le, Covrel_le, Covrel.

  (** Transitivity is admissible, by induction
      on [a ◁ U]. *)
  Lemma cr_trans : forall a U W, a ◁ U -> U ≤ W -> a ◁ W.
  Proof.
    intros a U W CR.
    generalize W ; clear W.
    induction CR ; intros.

    - (* cr_left *)
      unfold Covrel in H0.
      rewrite <- H. apply (H0 n).

    - (* cr_inf *)
      assert (forall n, (a ⊓ (CovAx b i n)) ◁ W).
      intro n ; apply (H1 n). apply H2.
      apply (cr_inf a W b i H H3).
    
    - (* cr_left *)
      apply cr_left with (b := b).
      apply H.
      apply IHCR ; apply H0.
  Qed.

  (** We can now show that [≤] is a preorder *)
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

  Definition PO_for_FFrame : @Preorder (nat -> T) Covrel :=
    MkPreorder
      (nat -> T)
      Covrel
      Covrel_refl
      Covrel_trans.
  Existing Instance PO_for_FFrame.

  (** This defines an equivalence relation [=]
      on the terms: [a = b <-> a ≤ b /\ b ≤ a].

      The [◁] relation respects the equality
      on the generators (left hand side) and
      our new equality on terms (right hand side).
   *)
  
  Add Morphism covrel : covrel_morphism2.
  Proof.
    intros x y Heq U W H.
    destruct H as [Hl Hr].
    split ; intro.
    apply cr_left with (b := x).
    rewrite Heq ; apply le_refl.
    apply cr_trans with (U := U) ; auto.

    apply cr_left with (b := y).
    rewrite Heq ; apply le_refl.
    apply cr_trans with (U := W) ; auto.
  Qed.
  
  (** One simple case where [U ≤ W] is when
      [U] is contained in [W].
       *)
  Definition cov_inj (U W : nat -> T) :=
    forall n, exists m, U n = W m.

  Lemma cov_inj_Covrel : forall U W, cov_inj U W -> U ≤ W.
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

  (** If the terms contain the same generators, they are
      equal. *)
  Lemma covbij_coveq : forall U W : (nat -> T), (forall n, U n = W n) -> U = W.
  Proof.
    intros.
    split ; by_cov_inj ; exists n.
    apply H.
    symmetry. apply H.
  Qed.

  (** A useful shortcut for later: *)
  Lemma cr_right : forall a U W, a ◁ U -> cov_inj U W -> a ◁ W.
  Proof.
    intros.
    apply cr_trans with (U := U).
    apply H.
    apply cov_inj_Covrel.
    apply H0.
  Qed.

  (** ** Binary meet
    We first show the admissibility of the localization rule,
    which relates [◁] to the meet on the generators.
    *)
      
  Definition down (a : T) (U : nat -> T) : nat -> T :=
    fun n => a ⊓ (U n).

  Infix "↓" := down (at level 50).
  
  Proposition cr_loc : forall a b U, a ◁ U -> b ⊓ a ◁ b ↓ U.
  Proof.
    intros a b U HR.
    induction HR as [a | a | a].

    - (* cr_refl *)
      apply cr_refl with (n := n).
      unfold down ; simpl.
      rewrite H ; reflexivity.

    - (* cr_inf *)
      apply cr_inf with (b := b0) (i := i).
      apply le_trans with (y := a).
      apply meet_r. assumption.
      intro n.
      rewrite <- meet_assoc.
      apply (H1 n).

    - (* cr_left *)
      apply cr_left with (b := b ⊓ b0).
      apply meet_le_r ; assumption.
      apply IHHR.    
  Qed.

  (** We can now define the meet on terms:
      the set of meets of pairs of elements of
      the two terms.
    *)
  
  Definition CMeet (U : nat -> T) (W : nat -> T) : nat -> T :=
    fun n => (U (bijNN1 n)) ⊓ (W (bijNN2 n)).

  Instance CMeet_meet : Meet (nat -> T) | 50 := CMeet.

  Ltac simpl_bijNN :=
    try (rewrite bijNN1_eq) ; try (rewrite bijNN2_eq) ; simpl.
  Ltac Meet_refl a b :=
    apply cr_refl with (n := bijNN (a,b)) ;
    try (unfold Meet) ;
    simpl_bijNN.

  Lemma CMeet_cov_inj_comm : forall U W : nat -> T, cov_inj (U ⊓ W) (W ⊓ U).
  Proof.
    intros.
    unfold cov_inj.
    intro.
    exists (bijNN (bijNN2 n,bijNN1 n)).
    unfold meet, CMeet_meet, CMeet.
    simpl_bijNN.
    rewrite meet_comm. reflexivity.
  Qed.
  
  Lemma CMeet_comm : forall U W : nat -> T, U ⊓ W = W ⊓ U.
  Proof.
    intros.
    split ; apply cov_inj_Covrel ; apply CMeet_cov_inj_comm.
  Qed.
  
  Lemma CMeet_covrel_comm : forall a U W, a ◁ U ⊓ W -> a ◁ W ⊓ U.
  Proof.
    intros.
    apply cr_right with (U := U ⊓ W).
    apply H.
    apply CMeet_cov_inj_comm.
  Qed.
  
  (* Admissibility of the meet rule *)
  Proposition cr_meet : forall a U W, a ◁ U -> a ◁ W -> a ◁ U ⊓ W.
  Proof.
    intros a U W TU TW.

    assert (a ⊓ a ◁ a ↓ U).
    apply (cr_loc a a U TU).
    rewrite meet_idem in H.

    apply cr_trans with (U := a ↓ U).
    apply H.
    
    (* Covrel *)
    unfold Covrel. intros p.
    unfold down.
    apply cr_right with (U := (U p) ↓ W).
    rewrite meet_comm. apply cr_loc. apply TW.
    (* cov_inj *)
    by_cov_inj.
    exists (bijNN (p,n)).
    unfold meet, CMeet_meet, CMeet. simpl_bijNN.
    unfold down. reflexivity.
  Qed.

  Proposition Meet_univ : forall U W Z : nat -> T,
                            Z ≤ U -> Z ≤ W -> Z ≤ U ⊓ W.
  Proof.
    unfold_Covrel.
    intros.
    apply cr_meet.
    apply (H n).
    apply (H0 n).
  Qed.

  Proposition CMeet_l : forall U W, U ⊓ W ≤ U.
  Proof.
    unfold_Covrel.
    intros.
    unfold Meet.
    apply cr_left with (b := U (bijNN1 n)).
    apply meet_l.
    apply cr_refl with (n := bijNN1 n).
    reflexivity.
  Qed.

  Proposition CMeet_r : forall U W, U ⊓ W ≤ W.
  Proof.
    intros.
    rewrite CMeet_comm.
    apply CMeet_l.
  Qed.

  (* ** Countable join
     We name it [Vc] because [V] looks like a big
     join and [c] means countable. *)

  Definition Vc (U : nat -> nat -> T) :=
    fun n => U (bijNN1 n) (bijNN2 n).

  Lemma V_le : forall U n, U n ≤ Vc U.
  Proof.
    intros.
    by_cov_inj.
    exists (bijNN (n,n0)).
    unfold Vc.
    rewrite bijNN1_eq, bijNN2_eq.
    reflexivity.
  Qed.

  Lemma V_univ : forall U v, (forall n, U n ≤ v) -> Vc U ≤ v.
  Proof.
    intros.
    unfold Vc, Covrel.
    intro.
    eapply cr_trans.
    eapply cr_refl. reflexivity.
    eapply H.
  Qed.

  (** ** Distributivity of meets over joins *)

  Lemma Cdistr_l : forall a U, a ⊓ (Vc U) ≤ Vc (fun n => a ⊓ (U n)).
  Proof.
    intros.
    unfold meet, CMeet_meet, CMeet, Covrel. intro.
    apply cr_trans with (U := (a (bijNN1 n) ↓ (Vc U))).
    apply cr_loc. eapply cr_refl. reflexivity.
    by_cov_inj.
    exists (bijNN (bijNN1 n0, bijNN (bijNN1 n, bijNN2 n0))).
    unfold Vc, down.
    repeat (rewrite bijNN1_eq, bijNN2_eq ; simpl).
    reflexivity.
  Qed.

  (** ** Top and bottom elements *)

  Definition Bot : nat -> T := fun n => ⊥.
  Instance BotNatT : Bottom (nat -> T) := Bot.

  Lemma Bot_le : forall U, ⊥ ≤ U.
  Proof.
    intro.
    unfold Covrel.
    intro.
    apply cr_left with (b := U O).
    unfold Bot. apply bot_le.
    eapply cr_refl.
    reflexivity.
  Qed.

  Definition Tp : nat -> T := fun n => ⊤.
  Instance TopNatT : Top (nat -> T) := Tp.
  Lemma Top_le : forall U, U ≤ ⊤.
  Proof.
    intro.
    unfold Covrel.
    intro.
    apply cr_left with (b := ⊤).
    apply top_le.
    apply cr_refl with (n := O).
    reflexivity.
  Qed.

  Proposition Top_n : forall U n, (U n = ⊤) -> U = ⊤.
  Proof.
    intros.
    split.
    apply Top_le.
    intro. apply cr_refl with (n := n).
    unfold Top. assumption.
  Qed.

  (** This allows us to define our frame. *)

  Definition MSL_for_FFrame : @MeetSemiLattice (nat -> T) Covrel :=
    MkMSL
      (nat -> T)
      Covrel
      PO_for_FFrame
      Tp
      Top_le
      Bot
      Bot_le
      CMeet
      CMeet_l
      CMeet_r
      Meet_univ.
  Existing Instance MSL_for_FFrame.

  Definition FFrame : @Frame (nat -> T) Covrel :=
    MkFrame
      (nat -> T)
      Covrel
      MSL_for_FFrame
      Vc
      V_le
      V_univ
      Cdistr_l.
  Existing Instance FFrame.

  Definition FFeq := @Feq (nat -> T) Covrel.
  Definition FFeq_setoid := Feq_equivalence PO_for_FFrame.

  (** * Properties of the free frame
     
      Here, we prove the universal property of the
      frame we have constructed. (This part of the
      proof is implicit in the paper.)

      ** Injection of the generators
      
      The generators inject in the free frame via
      a meet semilattice morphism.
    *)

  Definition inj_gen (t : T) : (nat -> T) := fun _ => t.

  Instance inj_gen_mslmorph : MSLMorphism Tmsl MSL_for_FFrame inj_gen.
  Proof.
    apply MkMSLMorphism ; unfold inj_gen.
    - apply MkPOMorphism.
      intros.
      unfold le, Covrel. intro.
      apply cr_left with (b := y) ; try assumption.
      apply cr_refl with (n := O) ; reflexivity.
    - intros.
      reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
    
  Lemma V_inj_gen : forall u : nat -> T, V (fun n => inj_gen (u n)) = u.
  Proof.
    intro.
    unfold inj_gen.
    unfold V, FFrame, Vc.
    split ; unfold le, Covrel_le, Covrel ; intro.
    apply cr_n.
    set (g := fun a => u (bijNN1 a)).
    assert (u n = g (bijNN (n,O))).
    unfold g.
    rewrite bijNN1_eq. simpl. reflexivity.
    rewrite H.
    apply cr_n.
  Qed.
  
  Lemma inj_gen_le : forall t u, inj_gen t ≤ u <-> t ◁ u.
  Proof.
    intros.
    unfold inj_gen.
    unfold le, Covrel_le, Covrel.
    firstorder.
    apply (H O).
  Qed.

  Lemma inj_gen_meet : forall t u, inj_gen t ⊓ u = (fun x => t ⊓ x) ∘ u.
  Proof.
    intros.
    unfold inj_gen, compose, meet, msl_meet, MSL_for_FFrame, CMeet.
    split ; by_cov_inj.
    - exists (bijNN2 n). reflexivity.
    - exists (bijNN (O,n)). simpl_bijNN. reflexivity.
  Qed.

  (** ** Facts on finite joins *)

  Require Import SeqOfList.

  Definition Vl (u : list T) := seq_of_list u.

  Existing Instance msl_preorder.
  Existing Instance Feq_equivalence.
  Existing Instance MSL_for_FFrame.
  Existing Instance CMeet_meet.
  Existing Instance Covrel_le.
  Ltac unfold_meet := unfold meet, msl_meet, MSL_for_FFrame, CMeet_meet, CMeet.

  Lemma V_cons_increasing : forall x y u v, x ≤ y -> u ≤ v -> x ::: u ≤ y ::: v.
  Proof.
    intros.
    unfold V_cons, le, Covrel_le, Covrel ; intros.
    destruct n.
    apply cr_left with (b := y). assumption.
    apply cr_refl with (n := O) ; reflexivity.
    apply cr_trans with (U := v).
    apply (H0 n).
    unfold le, Covrel_le, Covrel. intro.
    apply cr_refl with (n := S n0) ; reflexivity.
  Qed.
  
  Add Morphism V_cons with signature (Feq ==> (=) ==> (=)) as V_cons_morphism.
  Proof.
    intros.
    destruct H, H0.
    split.
    apply V_cons_increasing ; assumption.
    apply V_cons_increasing ; assumption.
  Qed.

  Ltac rewrite_as_pair n :=
    assert (HbijNN : n ≡ bijNN (bijNNinv n)) by (rewrite bijNN_bijNNinv ;
                                                 reflexivity) ;
    rewrite HbijNN.

  Lemma V_cons_inj_gen : forall a b u, inj_gen a ⊓ (b ::: u) =
                                  (a ⊓ b) ::: (inj_gen a ⊓ u).
  Proof.
    intros.
    split ; by_cov_inj.
    - rewrite_as_pair n.
      destruct (bijNNinv n).
      unfold_meet.
      simpl_bijNN.
      destruct n1 ; unfold inj_gen ; simpl.
      + exists O. reflexivity.
      + exists (S (bijNN (O,n1))). simpl.
      simpl_bijNN. reflexivity.
    - destruct n ; unfold inj_gen ; simpl.
      + exists (bijNN (O,O)).
        unfold_meet. reflexivity.
      + rewrite_as_pair n.
        unfold_meet ; simpl_bijNN.
        exists (bijNN (O,S (snd (bijNNinv n)))).
        simpl_bijNN. reflexivity.
  Qed.
    
  Lemma Vl_meet : forall x u, inj_gen x ⊓ Vl u = Vl (map (fun y => x ⊓ y) u).
  Proof.
    intros.
    unfold inj_gen, Vl.
    induction u ; simpl.
    - assert ((fun _ => ⊥) = ⊥) by reflexivity.
      apply covbij_coveq ; intro.
      unfold_meet.
      meetsemilattice.
    - rewrite <- IHu.
      apply V_cons_inj_gen.
  Qed.
  
  Lemma Vl_Vf : forall u, Vl u = Vf FFrame (map inj_gen u).
  Proof.
    intros.
    unfold Vl, Vf.
    assert (V (seq_of_list (map inj_gen u)) = V (inj_gen ∘ (seq_of_list u)) ).
    apply V_morphism.
    apply seq_of_list_compose.
    apply Feq_equivalence.
    apply msl_preorder.
    reflexivity.
    rewrite H.
    unfold compose.
    symmetry.
    apply V_inj_gen.
  Qed.

  (** ** Alternative representation of binary joins
      As we have all countable joins, binary ones
      come for free, but they are computed with
      our bijection [nat * nat -> nat], which is a
      bit dirty. Here is an alternative definition.
   
   *)

  Existing Instance joinb_join.
  Proposition join_NpN : forall u v, u ⊔ v = (fun n => match bijNpNinv n with
                                        | inl a => u a
                                        | inr b => v b
                                               end).
  Proof.
    intros.
    unfold join, joinb_join, joinb, Vf, V, FFrame, Vc, seq_of_list.
    split.
    - unfold le, Covrel_le, Covrel. intro.
      destruct (bijNN1 n) ; simpl.
      apply cr_refl with (n := bijNpN (inl (bijNN2 n))).
      rewrite bijNpN_bij2. reflexivity.
      destruct n0.
      apply cr_refl with (n := bijNpN (inr (bijNN2 n))).
      rewrite bijNpN_bij2. reflexivity.
      simpl.
      apply Bot_le.
    - by_cov_inj.
      destruct (bijNpNinv n).
      exists (bijNN (O,n0)). simpl_bijNN. reflexivity.
      exists (bijNN (S O,n0)). simpl_bijNN. reflexivity.
  Qed.

  (** ** Equalities generated by the axioms *)

  Proposition CovAx_meet_gen :
    forall (b:T), forall (i : Idx b), inj_gen b = (inj_gen b) ⊓ (CovAx b i).
  Proof.
    intros.
    rewrite inj_gen_meet.
    split.
    - rewrite inj_gen_le.
      apply cr_inf with (b := b) (i := i).
      apply le_refl.
      intros. unfold compose.
      apply cr_refl with (n := n).
      reflexivity.
    - intro. unfold compose, inj_gen.
      apply cr_left with (b := b).
      apply meet_l.
      apply cr_refl with (n := O).
      reflexivity.
  Qed.

  Proposition CovAx_le_eq :
    forall (b:T), forall (i : Idx b), (forall n, CovAx b i n ≤ b) -> inj_gen b = CovAx b i.
  Proof.
    intros.
    split.
    - rewrite CovAx_meet_gen with (i := i).
      apply (@meet_r (nat -> T) Covrel_le MSL_for_FFrame).
    - intro.
      apply cr_left with (b := b).
      apply H.
      apply cr_refl with (n := O).
      reflexivity.
  Qed.

  (** ** Universality

     Let us assume that we have a meet semilattice
     morphism to an arbitrary frame R. *)
  Context {R : Type}.
  Context {Rle : Le R}.
  Variable RFrame : @Frame R Rle.

  Definition Rmsl := @frame_msl R Rle RFrame.
  Definition Rpo := @msl_preorder R Rle Rmsl.
  Variable f : T -> R.
  Variable mslmorph : MSLMorphism Tmsl Rmsl f.
  Existing Instance mslmorph.

  (** We assume that the morphism respects the axioms
      we have used to generate our free frame. *)
  Definition respects_axioms : Prop :=
    forall t : T, forall i : Idx t, f t ≤ V (f ∘ (CovAx t i)).
  Variable resp_ax : respects_axioms.

  (** We define a function from our free frame to R. *)
  Definition fframe_ext (x : nat -> T) : R :=
    V (f ∘ x).

  (** We show that this function is a frame morphism. *)
  Existing Instance Covrel_le.
  
  Lemma f_covrel : forall a U, a ◁ U -> f a ≤ V (f ∘ U).
  Proof.
    intros.
    induction H.
    - rewrite <- H.
      assert (f (U n) = (f ∘ U) n) by reflexivity.
      rewrite H0 ; apply v_le.
    - unfold respects_axioms in resp_ax.
      specialize (resp_ax b i).
      set (K := (V (fun n => f (a ⊓ CovAx b i n)))).
      apply le_trans with (y := K).
      + assert (K = f a ⊓ V (f ∘ CovAx b i)).
        * rewrite cdistr.
          apply V_morphism ; intro.
          unfold compose.
          rewrite mslmorph_meet.
          reflexivity.
          apply mslmorph.
        * rewrite H2.
          apply le_trans with (y := f a ⊓ f b).
          assert (f a ≤ f b) by (apply (pomorph_le a b H)).
          assert (f a ⊓ f b = f a) by (apply order_meet ; assumption).
          rewrite H4.
          apply le_refl.
          apply meet_le.
          apply le_refl.
          assumption.
      + unfold K.
        apply v_univ.
        assumption.
    - apply le_trans with (y := f b).
      assert (f a ≤ f b) by (apply (pomorph_le a b H)).
      assumption. assumption.
  Qed.

  Instance fframe_mor : FMorphism FFrame RFrame fframe_ext.
  Proof.
    unfold fframe_ext.
    apply MkFMorphism.
    
    - apply MkMSLMorphism.
      + apply MkPOMorphism.
        intros.
        apply v_univ ; intro.
        unfold compose.
        unfold le, Covrel in H.
        specialize (H n).
        apply f_covrel ; assumption.
      + intros.
        unfold meet, msl_meet, FFrame. simpl.
        unfold CMeet, compose.
        assert (forall n, f (x (bijNN1 n) ⊓ y (bijNN2 n)) = f (x (bijNN1 n)) ⊓ f (y (bijNN2 n))).
        intro.
        apply (@mslmorph_meet T R Tle Rle Tmsl Rmsl f mslmorph).
        setoid_rewrite H.
        symmetry.
        apply V_meet.

      + unfold compose.
        unfold bottom, msl_bot, FFrame, Bot. simpl.
        assert (pointwise_relation nat Feq (fun _ => f ⊥) (fun _ => ⊥)).
        unfold pointwise_relation ; intro.
        apply mslmorph_bot. assumption.
        rewrite H.
        apply V_bot.

      + unfold compose.
        unfold top, msl_top, FFrame. simpl.
        rewrite V_top. reflexivity.
        exists O. unfold Top. apply mslmorph_top.
        apply mslmorph.

    - intro.
      unfold compose.
      rewrite <- V_pair.
      apply V_morphism ; intro.
      unfold V, FFrame, Vc, bijNN1, bijNN2.
      reflexivity.
  Qed.
  
  Definition fframe_mslmorph := fmorph_mslmorph FFrame RFrame fframe_ext.
  Proposition fframe_factoring : fframe_ext ∘ inj_gen = f.
  Proof.
    unfold equiv, ext_equiv, respectful.
    intros.
    unfold inj_gen, fframe_ext, compose.
    rewrite <- H.
    apply V_const.
  Qed.

  Arguments fframe_factoring : default implicits.

  (** Now the uniqueness part of the universality:
     if we have another such frame morphism,
     then it is equal to fframe_ext. *)

  Variable other_fact : (nat -> T) -> R.
  Variable other_morph : FMorphism FFrame RFrame other_fact.
  Existing Instance other_morph.
  Instance other_mslmorph : MSLMorphism MSL_for_FFrame Rmsl other_fact := fmorph_mslmorph FFrame RFrame other_fact.
  Instance other_morph_po : POMorphism other_fact.
  Proof.
    apply (mslmorph_pomorph MSL_for_FFrame Rmsl).
  Qed.    
    
  Variable other_commutes : other_fact ∘ inj_gen = f.

  Existing Instance Covrel_le.
  Instance coveq_R : Equiv (nat -> R) := @ext_equiv nat (≡) R (=).
  
  Proposition other_fact_equal : forall u, other_fact u = fframe_ext u.
  Proof.
    intro.
    assert (other_fact u = other_fact (V (fun n => inj_gen (u n)))).
    rewrite V_inj_gen ; reflexivity.
    rewrite H.
    rewrite morph_V.
    unfold fframe_ext, compose.
    apply V_morphism.
    intro.
    unfold equiv, ext_equiv, respectful in other_commutes.
    apply other_commutes ; reflexivity.
    assumption.
  Qed.

  (** This shows the correctness of our construction. *)

End Free_Frame.