Require Import InductiveLocale.
Require Import List.
Require Import Bool.
Require Import MathClasses.interfaces.canonical_names.

Lemma eqb_sym : forall a b, eqb a b ≡ eqb b a.
Proof.
  intros.
  destruct a, b ; reflexivity.
Qed.

Lemma bool_dec_refl : forall a, bool_dec a a ≡ left (eq_refl a).
Proof.
  intro a.
  destruct a ; reflexivity.
Qed.

Section CantorLocale.
  Open Scope list_scope.

  (* Our generators for the Cantor locale are *)
  Inductive T :=
  | Bot : T (* bottom *)
  | Cyl : list bool -> T. (* "cylinders" *)
  (* Cyl s represents the set of infinite sequences *)
  (* beginning with s *)

  Definition bcons (h : bool) (t : T) :=
    match t with
      | Bot => Bot
      | Cyl t => Cyl (h :: t)
    end.
  
  (* We define the meet on these generators. First, *)
  (* we define it on strings only (ignoring Bot for the moment *)
  Fixpoint mbword (a b : list bool) :=
    match a with
      | nil => Cyl b
      | (ha :: ta) =>
        match b with
          | nil => Cyl (ha :: ta)
          | (hb :: tb) =>
            match bool_dec ha hb with
              | left eq =>
                match mbword ta tb with
                  | Bot => Bot
                  | Cyl u => Cyl (ha :: u)
                end
              | right neq =>
                Bot
            end
        end
    end.

  Infix "♮" := mbword (at level 40).

  Proposition mbword_comm : forall a b, a ♮ b ≡ b ♮ a.
  Proof.
    intro.
    induction a as [|ha ta].
    (* nil *)
    intro.
    simpl.
    destruct b ; reflexivity.
    (* ha :: ta *)
    intro.
    destruct b ; simpl.
    reflexivity.
    destruct (bool_dec b ha).
    (* = *)
    rewrite e.
    rewrite (IHta b0).
    rewrite bool_dec_refl.
    reflexivity.
    (* ≠ *)
    destruct b, ha ; auto ; try (destruct n) ; reflexivity.
  Qed.

  (* We define the prefix relation on strings *)
  Inductive isprefix : forall (a b : list bool), Prop :=
  | isprefix_nil : forall b, isprefix nil b
  | isprefix_cons : forall h a b, isprefix a b -> isprefix (h::a) (h::b).

  Infix "⪯" := isprefix (at level 50).
  Notation "a ⊀ b" := (~ (a ⪯ b)) (at level 50).

  (* Basic lemmas on the prefix relation *)
  Lemma isprefix_refl : forall a, a ⪯ a.
  Proof.
    induction a as [|ha ta].
    (* nil *)
    apply isprefix_nil.
    (* ha :: ta *)
    apply isprefix_cons. assumption.
  Qed.

  Lemma isprefix_trans : forall a b c, a ⪯ b -> b ⪯ c -> a ⪯ c.
  Proof.
    induction a as [|ha ta] ; intros.
    (* nil *)
    apply isprefix_nil.
    (* ha :: ta *)
    destruct b ; inversion H.
    destruct c ; inversion H0.
    apply isprefix_cons.
    apply IHta with (b := b0) ; assumption.
  Qed.

  (* Order relation on the generators *)
  Inductive Tle : forall (a b : T), Prop :=
  | le_Bot : forall a, Tle Bot a
  | le_Pref : forall a b, a ⪯ b -> Tle (Cyl b) (Cyl a).

  Instance Le_T : Le T := Tle.
  
  Lemma Tle_refl : forall a, a ≤ a.
  Proof.
    induction a.
    apply le_Bot.
    apply le_Pref.
    apply isprefix_refl.
  Qed.

  Ltac solve_Tle :=
    match goal with
      | [ |- Bot ≤ ?a ] => apply le_Bot
      | [ H : Cyl ?a ≤ Bot |- _ ] => inversion H
      | [ H : ?a ⪯ ?b |- Cyl ?b ≤ Cyl ?a ] => apply (le_Pref a b H)
    end.

  Lemma Tle_trans : forall a b c, a ≤ b -> b ≤ c -> a ≤ c.
  Proof.
    intros.
    destruct a, b, c ; try solve_Tle.
    inversion H ; inversion H0. subst.
    apply le_Pref.
    apply isprefix_trans with (b := l0).
    assumption. assumption.
  Qed.

  Lemma isprefix_ntrans1 : forall a b c, a ⪯ b -> a ⊀ c -> b ⊀ c.
  Proof.
    intros.
    intro.
    assert (a ⪯ c) by (apply (isprefix_trans a b c H H1)).
    contradiction H0.
  Qed.

  Lemma isprefix_ntrans2 : forall a b c, b ⪯ c -> a ⊀ c -> a ⊀ b.
  Proof.
    intros.
    intro.
    assert (a ⪯ c) by (apply (isprefix_trans a b c H1 H)).
    contradiction H0.
  Qed.

  Lemma isprefix_dec : forall a b, a ⪯ b \/ a ⊀ b.
  Proof.
    induction a ; intros.
    (* nil *)
    left ; apply isprefix_nil.
    (* cons *)
    destruct b.
    right ; intro ; inversion H.
    destruct (bool_dec a b).
    rewrite e.
    destruct (IHa b0).
    left ; apply isprefix_cons ; assumption.
    right ; intro. inversion H0. apply (H H2).
    right ; intro. inversion H. apply (n H3).
  Qed.

  Lemma isprefix_antisym : forall a b, a ⪯ b -> b ⪯ a -> a ≡ b.
  Proof.
    induction a ; intros ; destruct b.
    reflexivity.
    inversion H0.
    inversion H.
    inversion H.
    inversion H0.
    rewrite (IHa b0 H2 H7).
    reflexivity.
  Qed.

  Lemma isprefix_common : forall a b c, a ⪯ c -> b ⪯ c -> (a ⪯ b \/ b ⪯ a).
  Proof.
    induction a as [|ha ta]; intros.
    (* nil *)
    left ; apply isprefix_nil.
    (* cons *)
    destruct c as [|hc tc] ; inversion H.
    destruct b as [|hb tb].
    right ; apply isprefix_nil.
    inversion H0. subst.
    destruct (IHta tb tc H2 H7).
    left ; eapply isprefix_cons ; assumption.
    right ; eapply isprefix_cons ; assumption.
  Qed.
  
  Lemma isprefix_mbword : forall a b, a ⪯ b -> a ♮ b ≡ Cyl b.
  Proof.
    intro a.
    induction a as [|ha ta] ; intros.
    - (* nil *)
      reflexivity.
    - (* ha :: ta *)
      induction b as [|hb tb].
      (* nil *)
      inversion H.
      (* hb tb *)
      inversion H.
      simpl.
      rewrite bool_dec_refl.
      rewrite (IHta tb) ; try assumption.
      reflexivity.
  Qed.

  Lemma mbword_case : forall a b, a ♮ b ≡ Bot \/ a ⪯ b \/ b ⪯ a.
  Proof.
    induction a as [|ha ta] ; intros.
    - (* nil *)
      right ; left.
      apply isprefix_nil.
    - (* ha :: ta *)
      induction b as [|hb tb].
      (* nil *)
      right ; right ; apply isprefix_nil.
      simpl.
      destruct (bool_dec ha hb).
      (* ha = hb *)
      rewrite e.
      destruct (IHta tb).
      rewrite H ; left ; reflexivity.
      destruct H ; apply isprefix_mbword in H as Heq.
      (* ta ♮ tb *)
      rewrite Heq.
      right ; left ; apply isprefix_cons ; assumption.
      (* tb ♮ ta *)
      rewrite mbword_comm in Heq.
      rewrite Heq.
      right ; right ; apply isprefix_cons ; assumption.
      (* Bot *)
      left ; reflexivity.
  Qed.

  (* We now define the meet on the generators *)
  Definition Tmeet (a b : T) :=
    match a, b with
      | Bot, _ => Bot
      | _, Bot => Bot
      | Cyl a', Cyl b' => mbword a' b'
    end.

  Instance Tmeet_meet : Meet T := Tmeet.
  
  Proposition meet_comm : forall a b:T, a ⊓ b ≡ b ⊓ a.
  Proof.
    intros. unfold meet, Tmeet_meet, Tmeet.
    destruct a, b ; auto.
    rewrite mbword_comm.
    reflexivity.
  Qed.

  Proposition meet_case : forall a b, a ⊓ b ≡ Bot \/ a ⊓ b ≡ a \/ a ⊓ b ≡ b.
  Proof.
    intros.
    destruct a as [|a] ; destruct b as [|b] ; auto.
    unfold meet.
    destruct (mbword_case a b).
    - (* a ♮ b = Bot *)
      left ; assumption.
    - (* a ♮ b = a \/ a ♮ b = b *)
      right.
      destruct H ; apply isprefix_mbword in H.
      right ; assumption.
      rewrite mbword_comm in H.
      left ; assumption.
  Qed.

  Lemma meet_ind : forall x a b u,
                     a ♮ b ≡ Cyl u ->
                     Cyl (x :: a) ⊓ Cyl (x :: b) ≡ Cyl (x :: u).
  Proof.
    intros.
    unfold meet, Tmeet_meet, Tmeet, mbword.
    unfold mbword in H.
    rewrite bool_dec_refl, H.
    reflexivity.
  Qed.

  Definition Top := Cyl nil.
  Proposition Cnil_unit_l : forall a, Top ⊓ a ≡ a.
  Proof.
    intros.
    unfold Top, meet, Tmeet_meet, Tmeet.
    destruct a ; auto.
  Qed.
  
  Proposition Cnil_unit_r : forall a, a ⊓ Top ≡ a.
  Proof.
    intros.
    rewrite meet_comm.
    apply Cnil_unit_l.
  Qed.

  Proposition Cnil_Bot_l : forall a, Bot ⊓ a ≡ Bot.
  Proof.
    auto.
  Qed.

  Proposition Cnil_Bot_r : forall a, a ⊓ Bot ≡ Bot.
  Proof.
    intros.
    rewrite meet_comm.
    apply Cnil_Bot_l.
  Qed.

  Lemma Top_le : forall a, a ≤ Top.
  Proof.
    intro. destruct a.
    apply le_Bot.
    apply le_Pref.
    apply isprefix_nil.
  Qed.
  
  Hint Rewrite Cnil_unit_l Cnil_unit_r Cnil_Bot_l Cnil_Bot_r.

  Lemma isprefix_meet : forall a b, a ⪯ b -> Cyl a ⊓ Cyl b ≡ Cyl b.
  Proof.
    intros.
    unfold meet.
    apply isprefix_mbword.
    assumption.
  Qed.

  Proposition meet_idem : forall a, a ⊓ a ≡ a.
  Proof.
    destruct a as [|a].
    reflexivity.
    apply (isprefix_meet a a (isprefix_refl a)).
  Qed.

  Hint Rewrite meet_idem.

  Lemma isprefix_meet_comm : forall a b, a ⪯ b -> Cyl b ⊓ Cyl a ≡ Cyl b.
  Proof.
    intros.
    rewrite meet_comm.
    apply isprefix_meet. assumption.
  Qed.

  Lemma notprefix_bot : forall a b, a ⊀ b -> b ⊀ a -> Cyl a ⊓ Cyl b ≡ Bot.
  Proof.
    intros.
    destruct (mbword_case a b).
    unfold meet ; assumption.
    destruct H1.
    destruct H ; assumption.
    destruct H0 ; assumption.
  Qed.
  
  (* Lemmas on the meet *)
  Lemma Tmeet_le_l : forall a b, a ⊓ b ≤ a.
  Proof.
    intros.
    destruct a, b ; try apply le_Bot.
    unfold le, Le_T.
    destruct (isprefix_dec l l0).
    rewrite (isprefix_meet).
    apply le_Pref. assumption.
    assumption.
    destruct (isprefix_dec l0 l).
    rewrite meet_comm.
    rewrite isprefix_meet.
    apply le_Pref. apply isprefix_refl.
    assumption.
    rewrite notprefix_bot. apply le_Bot.
    assumption. assumption.
  Qed.

  Lemma Tmeet_le_r : forall a b, a ⊓ b ≤ b.
  Proof.
    intros.
    rewrite meet_comm.
    apply Tmeet_le_l.
  Qed.

  Lemma Tmeet_univ : forall a b c, c ≤ a -> c ≤ b -> c ≤ a ⊓ b.
  Proof.
    intros.
    destruct a, b, c ; autorewrite with core ; try solve_Tle.
    inversion H.
    inversion H0. subst.
    destruct (isprefix_common l l0 l1) ; try assumption.
    rewrite (isprefix_meet l l0 H1).
    solve_Tle.
    rewrite (isprefix_meet_comm l0 l H1).
    solve_Tle.
  Qed.

  Require Import MeetSemiLattice.
  Instance CantorMSL : MeetSemiLattice :=
    MkMSL
      T
      Tle
      Tle_refl
      Tle_trans
      Top
      Top_le
      Bot
      le_Bot
      Tmeet
      Tmeet_le_l
      Tmeet_le_r
      Tmeet_univ.

  
End CantorLocale.
  
    
    
    

  
              
              