Require Import MyNotations.
Require Import Frame.
Require Import MeetSemiLattice.
Require Import PreorderEquiv.
Require Import LogicalFrames.
Require Import Cantor.

(** * Definition of the points

   Points are defined as frame morphisms to the initial frame [SigmaFrame].
   We also define classical points as frame morphisms to [Nabla2Frame].
  *)

Section Point.

  Context {T: Type}.
  Context {Tle : Le T}.

  Variable Tframe : Frame.

  Definition Point := { f : T -> Sigma | FMorphism Tframe SigmaFrame f }.

  Definition ClPoint := { f : T -> Nabla2 | FMorphism Tframe Nabla2Frame f }.
  
End Point.

(** * Points of Cantor space 
  
     We prove here the correspondance between
     - functions [nat -> bool]
     - points of the Cantor space

     We make our proofs slightly more general to prepare
     for the second correspondance:
     - functions [nat -> Nabla2]
     - classical points of the Cantor space
   *)

Section CantorPoints.
  Require Import Bool.
  Require Import Coq.Lists.List.
  
  Context {R : Type}.
  Context {Rle : Le R}.
  Existing Instance Rle.
  Context {RFrame : Frame}.
  Existing Instance RFrame.
  Instance Rmsl : (@MeetSemiLattice R Rle) := (@frame_msl R Rle RFrame).
  Existing Instance Feq_equiv.

  (** ** Definition of a Cantor point from a binary sequence *)
  Variable f : nat -> bool.
  (** Given [f], we construct the corresponding frame morphism.
      We start by defining a meet semilattice morphism from 
      the Cantor MSL to (generators of) Sigma. *)
  
  Fixpoint isPrefix_list (l : list bool) (n:nat) :=
    match l with
      | [] => ⊤
      | h :: t =>
        match bool_dec h (f n) with
          | left p => isPrefix_list t (S n)
          | right p => ⊥
        end
    end.

  Existing Instance CantorGenMSL.
  Existing Instance Le_CantorGen.
  Definition isPrefix (c : CantorGen) :=
    match c with
      | Bot => ⊥
      | Cyl s => isPrefix_list s O
    end.

  Instance isprefix_le : Le (list bool) := isprefix.
  Lemma isPrefix_list_monotone : forall a b, b ≤ a -> forall n, isPrefix_list a n ≤ isPrefix_list b n.
  Proof.
    intros a b H.
    induction H ; intros ; simpl.
    + apply top_le.
    + destruct (bool_dec h (f n)).
      apply IHisprefix.
      apply le_refl.
  Qed.

  Notation "a ≰ b" := (~ a ≤ b) (at level 40).
  Lemma isPrefix_list_nprefix : forall a b, a ≰ b -> b ≰ a -> forall n, isPrefix_list a n ⊓ isPrefix_list b n = ⊥.
  Proof.
    induction a ; intros.
    destruct H ; apply isprefix_nil.
    destruct b.
    destruct H0 ; apply isprefix_nil.
    destruct (bool_dec a b).
    * subst.
      assert (a0 ≰ b0). intro. destruct H. apply isprefix_cons ; assumption.
      assert (b0 ≰ a0). intro. destruct H0. apply isprefix_cons ; assumption.
      specialize (IHa b0 H1 H2 (S n)).
      simpl. destruct (bool_dec b (f n)). assumption.
      meetsemilattice.
    * simpl.
      destruct a, b, (f n) ;
        try (destruct n0 ; reflexivity) ;
        simpl ;
        meetsemilattice.
  Qed.
    
  
  Lemma isPrefix_monotone : forall a b, a ≤ b -> isPrefix a ≤ isPrefix b.
  Proof.
    intros.
    destruct H ; simpl.
    - apply bot_le.
    - apply (isPrefix_list_monotone b a H O).
  Qed.
  
  Existing Instance CantorGenmeet_meet.
  Lemma isPrefix_meet : forall u v, isprefix u v ->
                               isPrefix (Cyl u ⊓ Cyl v) =
                               isPrefix_list u O ⊓ isPrefix_list v O.
  Proof.
    intros.
    rewrite isprefix_meet.
    rewrite meet_comm.
    rewrite order_then_meet.
    reflexivity.
    apply isPrefix_list_monotone ; assumption.
    assumption.
  Qed.

  Instance isPrefix_pomor : POMorphism isPrefix.
  Proof.
    apply MkPOMorphism.
    apply isPrefix_monotone.
  Qed.

  Instance toCantorPoint_MSLmorph : MSLMorphism CantorGenMSL Rmsl isPrefix.
  Proof.
    apply MkMSLMorphism.
    - exact isPrefix_pomor.
    - intros.
      destruct x, y ; simpl ; meetsemilattice.
      destruct (isprefix_dec l l0) ; destruct (isprefix_dec l0 l).
      * apply isPrefix_meet ; assumption.
      * apply isPrefix_meet ; assumption.
      * rewrite meet_comm.
        assert (Cyl l ⊓ Cyl l0 = Cyl l0 ⊓ Cyl l).
        apply (@meet_comm CantorGen Le_CantorGen CantorGenMSL).
        rewrite H1.
        apply isPrefix_meet ; assumption.
      * rewrite notprefix_bot ; try assumption.
        simpl.
      
      + symmetry.
        apply isPrefix_list_nprefix ; assumption.
    - reflexivity.
    - reflexivity.
  Qed.
     
End CantorPoints.

(** ** Definition of a binary sequence from a frame morphism *)

(* TODO
Section CantorPointSigma.
  Require Import FreeFrame.
  Existing Instance SigmaLe.
  Instance SigmaMSL : MeetSemiLattice SigmaLe := @frame_msl Sigma SigmaLe SigmaFrame.


  Existing Instance Feq_equiv.

  Variable f : Cantor -> Sigma.
  Variable fmorph : FMorphism CantorFrame SigmaFrame f.

  Definition i := inj_gen CantorGen.

  (* Let's define a function (nat -> bool) out of this! *)
  Existing Instance Le_CantorGen.
  Existing Instance Feq_equivalence.
  Existing Instance CantorGenMSL.
  Existing Instance CantorLe.

  Definition mymor := fmorph_mslmorph CantorFrame SigmaFrame f.
  Existing Instance mymor.
  (*
  Instance cs_eq : Equiv (CantorGen -> Sigma) := @ext_equiv CantorGen (Feq:Equiv CantorGen) Sigma Feq. *)

  Lemma step : forall s, f (i (Cyl s)) = ⊤ -> { b | f (i (Cyl (s ++ [b]))) = ⊤ }.
  Proof.
    intros.
    assert ({ f (i (Cyl (s++[false]))) = ⊤ } + { f (i (Cyl (s++[true]))) = ⊤}).
    apply Sigma_join_top.
    rewrite <- FMorphism_join.
    rewrite <- Cyls01. assumption.
    apply fmorph.
    destruct H0.
    - exists false. assumption.
    - exists true. assumption.
  Qed.

  Existing Instance TopNatT.
  Existing Instance CantorMSL.
  
  Lemma nth_prefix : forall n, { s | f (i (Cyl s)) = ⊤ /\ length s ≡ n }.
  Proof.
    induction n.
    - exists []. split.
      assert ((i (Cyl []) = ⊤)).
      unfold top, TopNatT, Tp, i, inj_gen, top, msl_top, FFrame, CantorMSL, CantorGenTop. reflexivity.
      rewrite H.
      unfold equiv, Feq_equiv.
      apply (@mslmorph_top _ _ _ _ CantorMSL SigmaMSL f mymor).
      reflexivity.
    - destruct IHn, a.
      apply step in H.
      destruct H.
      exists (x ++ [x0]).
      split.
      assumption.
      rewrite app_length.
      simpl.
      rewrite H0. rewrite <- plus_n_Sm.
      rewrite <- plus_n_O.
      reflexivity.
  Qed.

  Definition seq_of_point : nat -> bool.
    intro n.
    (* TODO *)
    
    
  Existing Instance SigmaLe.
  Existing Instance SigmaFrame.

  
  
  Definition toCantorPoint : Point CantorFrame.
    unfold Point.
    apply exist with (x := toCantorPoint_ext f).
    apply MkFMorphism.
    - apply MkMSLMorphism.
      + apply MkPOMorphism.
        intros.
        unfold toCantorPoint_ext.
        apply v_univ ; intro.
        specialize (H n).
        unfold le, FreeFrame.Covrel in H.

 *)
