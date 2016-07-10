Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Setoid.
Require Import PreorderEquiv.
Require Import MathClasses.interfaces.canonical_names.

Section MeetSemiLattice_definition.
  
  Class MeetSemiLattice `{T : Type} `{Tle : Le T} :=
    MkMSL {
        (* preorder *)
        msl_preorder :> Preorder Tle;
        
        (* top, bottom *)
        msl_top :> Top T;
        top_le: forall x, x ≤ ⊤;
                       msl_bot :> Bottom T;
        bot_le: forall x, ⊥ ≤ x;

        (* meet *)
        msl_meet :> Meet T;
        meet_l: forall x y, x ⊓ y ≤ x;
        meet_r: forall x y, x ⊓ y ≤ y;
        meet_univ: forall x y z, z ≤ x -> z ≤ y -> z ≤ x ⊓ y;
      }.

  Context {T : Type}.
  Variable Tle : Le T.
  Variable MSL : @MeetSemiLattice T Tle.

  Existing Instance Feq_equiv.

  Create HintDb meetsemilattice.
  Hint Resolve le_refl top_le bot_le meet_l meet_r.
  Ltac meetsemilattice := auto with meetsemilattice.

  (* meets *)
  Lemma meet_le_l : forall x y z, x ≤ y -> x ⊓ z ≤ y ⊓ z.
  Proof.
    intros.
    apply meet_univ.
    apply (le_trans _ x _).
    apply meet_l. assumption.
    apply meet_r.
  Qed.

  Lemma meet_le_r : forall x y z, x ≤ y -> z ⊓ x ≤ z ⊓ y.
  Proof.    
    intros.
    apply meet_univ.
    apply meet_l.
    apply (le_trans _ x _).
    apply meet_r. assumption.
  Qed.

  Lemma meet_le : forall x y z w, x ≤ y -> z ≤ w -> x ⊓ z ≤ y ⊓ w.
  Proof.
    intros.
    apply (le_trans _ (x ⊓ w) _).
    apply (meet_le_r _ _ _ H0).
    apply (meet_le_l _ _ _ H).
  Qed.

  Add Parametric Morphism : meet with signature (Feq ==> Feq ==> Feq) as meet_morphism.
  Proof.
    firstorder ; apply meet_le ; assumption.
  Qed.

  Lemma meet_comm : forall x y: T, x ⊓ y = y ⊓ x.
  Proof.
    unfold Feq.
    intros. split ; (
     apply meet_univ ; [ apply meet_r | apply meet_l ]).
  Qed.

  Lemma meet_assoc : forall x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.
  Proof.  
    intros.
    unfold Feq. split ; apply meet_univ.

    - apply meet_le_r.
      apply meet_l.
    - apply (le_trans _ (x ⊓ z) _).
      apply meet_le_r.
      apply meet_r.
      apply meet_r.

    - apply (le_trans _ (x ⊓ z) _).
      apply meet_le_l.
      apply meet_l.
      apply meet_l.
    - apply meet_le_l.
      apply meet_r.
  Qed.

  Lemma meet_idem : forall x, x ⊓ x = x.
  Proof.
    intros.
    unfold Feq. split.
    apply meet_l.
    apply (meet_univ x x x (le_refl x) (le_refl x)).
  Qed.

  Lemma meet_bot_l : forall x, ⊥ ⊓ x = ⊥.
  Proof.
    intros. split.
    apply meet_l.
    apply meet_univ.
    apply le_refl.
    apply bot_le.
  Qed.

  Lemma meet_bot_r : forall x, x ⊓ ⊥ = ⊥.
  Proof.
    intros. setoid_rewrite meet_comm.
    apply meet_bot_l.
  Qed.

  Lemma meet_top_l : forall x, ⊤ ⊓ x = x.
  Proof.
    intro. split.
    apply meet_r.
    apply meet_univ.
    apply top_le.
    apply le_refl.
  Qed.

  Lemma meet_top_r : forall x, x ⊓ ⊤ = x.
  Proof.
    intro. setoid_rewrite meet_comm.
    apply meet_top_l.
  Qed.

  Lemma order_meet : forall x y, x ≤ y <-> x ⊓ y = x.
  Proof.
    intros.
    unfold iff. split.

    intros. split.
    apply meet_l.
    apply (le_trans _ (x ⊓ x) _).
    setoid_rewrite meet_idem. apply le_refl.
    apply meet_le_r.
    apply H.
    intro.
    setoid_rewrite <- H.
    apply meet_r.
  Qed.

End MeetSemiLattice_definition.


Add Parametric Morphism (T : Type) (Tle : Le T) (Tmsl : MeetSemiLattice) : (@msl_meet T Tle Tmsl) with signature (Feq ==> Feq ==> Feq) as msl_meet_morphism.
Proof.
  apply (@meet_morphism T Tle Tmsl).
Qed.

Section MeetSemiLattice_morphism.
  Context {t1 t2 : Type}.
  Context {le1 : Le t1}.
  Context {le2 : Le t2}.

  Existing Instance Feq_equiv.

  Variable msl1 : @MeetSemiLattice t1 le1.
  Variable msl2 : @MeetSemiLattice t2 le2.

  Class MSLMorphism (f : t1 -> t2) :=
    MkMSLMorphism {
        mslmorph_pomorph :> POMorphism f;
        (* preserves meets *)
        mslmorph_meet : forall x y : t1, f (x ⊓ y) = (f x) ⊓ (f y);
        (* preserves bot *)
        mslmorph_bot : f ⊥ = ⊥          
      }.

End MeetSemiLattice_morphism.

Section MeetSemiLattice_composition.

  Context {t1 t2 t3 : Type}.
  Context {le1 : Le t1} {le2 : Le t2} {le3 : Le t3}.
  Context {msl1 : @MeetSemiLattice t1 le1}.
  Context {msl2 : @MeetSemiLattice t2 le2}.
  Context {msl3 : @MeetSemiLattice t3 le3}.

  Context {f : t1 -> t2} {g : t2 -> t3}.

  Definition MSLcomp (gm : MSLMorphism msl2 msl3 g)
                     (fm: MSLMorphism msl1 msl2 f) :
                     
    MSLMorphism msl1 msl3 (g ∘ f).
  Proof.
    apply MkMSLMorphism ; unfold compose.
    - apply POcomp.
      apply mslmorph_pomorph with (msl4 := msl1) (msl5 := msl2).
      assumption.
      apply mslmorph_pomorph with (msl4 := msl2) (msl5 := msl3).
      assumption.
    - intros.
      rewrite mslmorph_meet.
      rewrite mslmorph_meet.
      reflexivity.
      exact gm.
      exact fm.
    - intros.
      rewrite mslmorph_bot.
      rewrite mslmorph_bot.
      reflexivity.
      exact gm.
      exact fm.
  Qed.
  
End MeetSemiLattice_composition.


