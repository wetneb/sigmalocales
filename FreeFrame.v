Require Import Frame.
Require Import BijNat.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.Setoids.Setoid.

Section FreeFrame_Definition.
  Open Scope list_scope.
  Context {genT:Type}.

  Inductive term : Type :=
  | Top : term
  | Bot : term
  | Gen : genT -> term 
  | Join : term -> term -> term
  | Meet : term -> term -> term
  | Cjoin : (nat -> term) -> term.

  Definition t := term.
  Infix "∨" := Join (at level 50, left associativity) : free_frame_def_scope.
  Infix "∧" := Meet (at level 45, left associativity) : free_frame_def_scope.
  Open Scope free_frame_def_scope.

  Context {genR : term -> term -> Type}.
 
  Inductive rel : term -> term -> Prop :=
  | ax : forall {a b} (r : genR a b), rel a b
  | Refl : forall x, rel x x
  | Trans : forall x y z, rel x y -> rel y z -> rel x z
  | Top_le : forall x, rel x Top
  | Bot_le : forall x, rel Bot x
  | Meet_l : forall x y, rel (x ∧ y) x
  | Meet_r : forall x y, rel (x ∧ y) y
  | Meet_univ : forall x y z, rel z x -> rel z y -> rel z (x ∧ y)
  | Join_l : forall x y, rel x (x ∨ y)
  | Join_r : forall x y, rel y (x ∨ y)
  | Join_univ : forall x y z, rel x z -> rel y z -> rel (x ∨ y) z
  | V_le : forall u n, rel (u n) (Cjoin u)
  | V_univ : forall u z, (forall n, rel (u n) z) -> rel (Cjoin u) z
  | Cdistr_l : forall x u, rel (x ∧ (Cjoin u)) (Cjoin (fun n => x ∧ (u n)))
  | Cdistr_r : forall x u, rel (Cjoin (fun n => x ∧ (u n))) (x ∧ (Cjoin u)).
  Close Scope free_frame_def_scope.

  Definition FFrame :=
    @MkFrame term rel
      Refl
      Trans
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
      Cjoin
      V_le
      V_univ
      Cdistr_l
      Cdistr_r.

  Definition feq := @Feq term rel.
  Infix "==" := (feq) (at level 70).
  Infix "∨" := Join (at level 50, left associativity).
  Infix "∧" := Meet (at level 45, left associativity).
  Notation "⊥" := Bot.
  Notation "⊤" := Top.

  Add Setoid term feq (@Feq_equiv term rel FFrame) as Feq_setoid.
  Add Morphism rel : rel_morphism.
  Proof.
    apply (le_proper FFrame).
  Qed.
  Add Morphism Join : Join_morphism.
  Proof.
    apply (join_morphism FFrame).
  Qed.
  Add Morphism Meet : Meet_morphism.
  Proof.
    apply (meet_morphism FFrame).
  Qed.
  Add Morphism Cjoin : Cjoin_morphism.
    apply (V_morphism FFrame).
  Qed.

  Ltac smart_V_le n :=
  apply (V_le_le FFrame n);
  simpl;
  try (apply Refl).
 
  
  (* A general form is a family of lists of generators *)
  (* understood as the countable join of their finite meets. *)
  (* Some meets can be absent, in which case they represent bottom. *)
  About V_comm.

  Definition GenMeet := list genT.
  Definition GeneralForm := nat -> option GenMeet.
  Definition ofGenM (gm : option GenMeet) : t :=
    match gm with
      | None => Bot
      | Some l => 
        fold_left (fun t g => t ∧ (Gen g)) l ⊤ end.
  Definition toEnum (gf : GeneralForm) : (nat -> t) :=
    fun n => ofGenM (gf n).
  Definition ofGF (gf : GeneralForm) : t :=
    Cjoin (toEnum gf).
  Definition cstGF (v: option GenMeet) (n : nat) := v.

  Definition concatOGenMeet (a b : option GenMeet) :=
    match a, b with
      | Some u, Some v => Some (app u v)
      | _, _ => None
    end.

  (* Operations on general forms *)
  Definition gf_join (x y : GeneralForm) : GeneralForm :=
     fun n => match bijNpNinv n with
                | inl n => x n
                | inr n => y n
           end.
  
  Definition gf_meet (x y : GeneralForm) : GeneralForm :=
        fun n => let p := bijNNinv n in
              concatOGenMeet (x (fst p)) (y (snd p)).

  Definition gf_cjoin (x : nat -> GeneralForm) : GeneralForm :=
        fun n => let p := bijNNinv n in
              x (fst p) (snd p).
  
  (* Lemmas for the forthcoming obligations *)
  
  Lemma refold_toEnum_t : forall gf n, ofGenM (gf n) = toEnum gf n.
  Proof. reflexivity. Qed.

  Lemma refold_toEnum_f : forall gf, (fun n => ofGenM (gf n)) = toEnum gf.
  Proof. reflexivity. Qed.

  Ltac rewrite_toEnum :=
    repeat (rewrite refold_toEnum_t);
    repeat (rewrite refold_toEnum_f).
  
  Lemma gf_join_left : forall x y n, toEnum x n = toEnum (gf_join x y) (bijNpN (inl n)).
  Proof.
    intros.
    unfold gf_join, toEnum.
    rewrite bijNpN_bij2. reflexivity.
  Qed.

  Lemma gf_join_right : forall x y n, toEnum y n = toEnum (gf_join x y) (bijNpN (inr n)).
  Proof.
    intros.
    unfold gf_join, toEnum.
    rewrite bijNpN_bij2. reflexivity.
  Qed.
  
  Lemma gf_join_correct : forall x y, ofGF (gf_join x y) == (ofGF x) ∨ (ofGF y).
  Proof.
    intros.
    unfold feq, Feq. split.

    (* <= *)
    unfold ofGF.
    apply V_univ.
    intro. unfold gf_join.
    unfold toEnum.
    destruct (bijNpNinv n).
    (* left *)
    apply (Trans _ (Cjoin (fun n1 => ofGenM (x n1)))).
    smart_V_le n0.
    apply Join_l.
    (* right *)
    apply (Trans _ (Cjoin (fun n1 => ofGenM (y n1)))).
    smart_V_le n0.
    apply Join_r.

    (* >= *)
    unfold ofGF, gf_join.
    apply Join_univ.
    (* left *)
    apply V_univ.
    intro.
    rewrite gf_join_left with (y := y).
    apply V_le.
    (* right *)
    apply V_univ.
    intro.
    rewrite gf_join_right with (x := x).
    apply V_le.
  Qed.

  Lemma fold_meet : forall (l : GenMeet) (u : term),
                    fold_left (fun t g => Meet t (Gen g)) l u ==
                    u ∧ fold_left (fun t g => Meet t (Gen g)) l Top.
  Proof.
    intro.
    induction l ; intro ; simpl.
    (* nil *)
    symmetry. apply (meet_top_r FFrame).
    (* cons *)
    rewrite IHl.
    rewrite <- (meet_assoc FFrame).
    rewrite (IHl (Top ∧ Gen a)).
    rewrite (meet_top_l FFrame).
    reflexivity.
  Qed.
    
  Lemma concatOGenMeet_correct : forall p q, ofGenM (concatOGenMeet p q) == ofGenM p ∧ ofGenM q.
  Proof.
    intros.
    induction p as [|a] ;
      induction q as [|b] ;
      try
        (unfold ofGenM, concatOGenMeet;
         try rewrite (meet_bot_r FFrame);
         try rewrite (meet_bot_l FFrame);
         reflexivity).
    (* p = Some a *)
    (* q = Some b *)
    rename a0 into b.
    induction a ;
    (* nil *)
    simpl ; try (rewrite (meet_top_l FFrame)).
    reflexivity.
    (* cons *)
    unfold ofGenM, concatOGenMeet in IHa.
    repeat (rewrite fold_meet with (u := (Top ∧ Gen a))).
    rewrite (meet_top_l FFrame).
    rewrite IHa.
    rewrite <- (meet_assoc FFrame).
    reflexivity.
  Qed.

  Lemma gf_meet_correct : forall x y, ofGF (gf_meet x y) == ofGF x ∧ ofGF y.
  Proof.
    intros.
    unfold feq, Feq. split.

    (* <= *)
    apply Meet_univ.
    (* left *)
    unfold ofGF, gf_meet.
    apply V_univ. intro.
    apply Trans with (y := (ofGenM (x (fst (bijNNinv n))))).
    unfold toEnum.
    rewrite concatOGenMeet_correct.
    apply (Meet_l).
    (* right *)
    rewrite_toEnum.
    smart_V_le (fst (bijNNinv n)).
    unfold ofGF, gf_meet.
    apply V_univ. intro.
    apply Trans with (y := (ofGenM (y (snd (bijNNinv n))))).
    unfold toEnum.
    rewrite concatOGenMeet_correct.
    apply Meet_r.
    rewrite_toEnum.
    smart_V_le (snd (bijNNinv n)).

    (* >= *)
    unfold ofGF.
    rewrite (cdistr FFrame).
    setoid_rewrite (meet_comm FFrame).
    setoid_rewrite (cdistr FFrame).
    unfold gf_meet, toEnum.
    setoid_rewrite concatOGenMeet_correct.
    repeat (apply (v_univ); intro).
    smart_V_le (bijNN (n0,n)).
    rewrite bijNNinv_bijNN.
    apply (meet_comm FFrame).
  Qed.

   Program Fixpoint general_form (t:term) (n:nat) : option GenMeet :=
    match t with
      | Top => Some nil
      | Bot => None
      | Gen x => Some (cons x nil)
      | Join a b =>
        gf_join (general_form a) (general_form b) n
      | Meet a b =>
        gf_meet (general_form a) (general_form b) n
      | Cjoin u =>
        gf_cjoin (fun m => general_form (u m)) n
    end.

   Theorem general_form_correct :
     forall t : term, ofGF (general_form t) == t.
   Proof.
     intro t.
     induction t ; unfold general_form.
     
     (** Top **)
     unfold ofGF, toEnum.
     apply (V_const FFrame). intro.
     reflexivity.

     (** Bot **)
     unfold ofGF, toEnum.
     apply (V_const FFrame).
     intro. reflexivity.

     (** Gen **)
     unfold ofGF, toEnum.
     simpl.
     apply (V_const FFrame).
     intro. simpl.
     setoid_rewrite (meet_top_l FFrame).
     reflexivity.

     (** Fin join **)
     rewrite gf_join_correct.
     rewrite IHt1.
     rewrite IHt2.
     reflexivity.

     (** Fin meet **)
     rewrite gf_meet_correct.
     rewrite IHt1, IHt2.
     reflexivity.

     Definition my_proxy (u:nat -> term) mgf (a b:nat):=
       ofGenM (mgf (u a) b).
     Lemma my_proxy_lemma : forall u mgf, (fun n => ofGenM (mgf (u (fst (bijNNinv n))) (snd (bijNNinv n)))) = (fun n => my_proxy u mgf (fst (bijNNinv n)) (snd (bijNNinv n))).
     Proof. reflexivity. Qed.

     (** Countable join **)
     unfold gf_cjoin, ofGF.
     unfold toEnum.
     setoid_rewrite (my_proxy_lemma t0 (general_form)).
     setoid_rewrite (V_pair FFrame (my_proxy t0 general_form)).
     unfold my_proxy.
     apply (V_morphism FFrame). intro.
     destruct (general_form (t0 n)). simpl. exact 0.
     unfold ofGF in H.
     rewrite_toEnum.
     rewrite H.
     reflexivity.
     unfold ofGF in H. unfold toEnum in H.
     exact (H n).
   Qed.

End FreeFrame_Definition.

Section Initial_Frame.
  (* We define here the initial object in the category of frames *)
  
  (* Sigma has no generators (and no relations) *)
  Definition st := @term False.
  Inductive  sr (a b: @term False) : Type := .
  Definition Σ := @FFrame False sr.

  Definition Seq := (@feq False sr).
  Infix "==" := (Seq) (at level 70).
  Infix "∨" := Join (at level 50, left associativity).
  Infix "∧" := Meet (at level 45, left associativity).
  Notation "⊥" := (@Bot False).
  Notation "⊤" := (@Top False).
  Add Setoid term Seq (Feq_equiv Σ) as Seq_setoid.
  Add Morphism (@Join False) : SJoin_morphism.
  Proof. apply (join_morphism Σ). Qed.
End Initial_Frame.

Section Frame_Spectrum.
  Context {t : Type}.
  Variable (le : t -> t -> Prop).
  Context {F : @Frame t le}.

  Set Printing All.
  About FMorphism.
  Definition FPoints := @FMorphism t le F (@term False) (@rel False sr) Σ.
  
End Frame_Spectrum.

Section ProductFrame.

  (* Family of carriers *)
  Variable A : nat -> Type.
  (* Family of relations *)
  Variable R : forall n : nat, A n -> A n -> Prop.
  (* Family of frames on these carriers and relations *)
  Variable F : forall n, Frame (t := A n) (le := R n).

  (* Term generators *)
  Inductive genC : forall n : nat, Type :=
  | genTop : forall {n}, genC n
  | genCons : forall {n}, (A n) -> genC (S n) -> genC n.

  Inductive genT : Type :=
  | GenT (l:(@genC 0)): genT.

  (* Operations on sequences of terms *)

  (* Extract the n-th component *)
  Fixpoint genC_nth (n m : nat) (g :genC m) : A (n+m).
  Proof.
    destruct g.

    (* g = genTop *)
    exact top.

    (* genCons a g *)
    destruct n as [|n'].
    (* m = 0 *)
    rewrite plus_O_n. exact a.
    (* m = S m' *)
    specialize (genC_nth n' (S n0) g).
    rewrite plus_Sn_m.
    rewrite plus_n_Sm.
    exact genC_nth.
  Defined.

  (* This does the pointwise meet of sequences of terms *)
  Definition genMeetN : forall n : nat, genC n -> genC n -> genC n.
  Proof.
    intro n.
    intro a.
    induction a as [|n ha ta].
    (* a = gTop, we return b *)
    exact (fun x => x).
    (* a = gCons n ha ta *)
    intro b.
    destruct b as [|n hb tb].
    (* b = gTop, we return a *)
    exact (genCons ha ta).
    (* b = gCons n hb tb, we return the meet recursively *)
    exact (genCons (meet ha hb) (IHta tb)).
    Show Proof.
  Defined.

  About nat_rect.

  Definition genMeet := genMeetN 0.

  (* This overrides the element at the nth position in the sequence *)
  Require Import Coq.Logic.JMeq.
  Program Fixpoint override_fix (n m : nat) (x : A (n+m)) (l : genC m) : {l':genC m | genC_nth n m l' = x} :=
    match n with
      | 0 =>
        match l with
          | genTop _ => genCons x genTop
          | genCons _ _ ta => genCons x ta
        end
      | S n' =>
        match l with
          | genTop _ =>
            genCons top (override_fix n' (S m) x genTop)
          | genCons _ a ta =>
            genCons a (override_fix n' (S m) x ta)
        end
    end.
  Obligation 2.
  unfold genC_nth.
  simpl. admit.
  Defined.
  Obligation 5.
  unfold genC_nth. simpl. admit.
  Defined.
  Obligation 6.
  rewrite plus_Sn_m. rewrite plus_n_Sm.
  reflexivity.
  Defined.
  Obligation 7.
  (* this looks horrible *)
  simpl. rewrite e.
  unfold override_fix_obligation_6. simpl.
  Defined.
  Obligation 8.
  rewrite plus_Sn_m. rewrite plus_n_Sm.
  reflexivity.
  Defined.
  Obligation 12.
  (* this sounds even more horrible *)
  unfold 

  Definition override_fix (n : nat) : forall m, A (n+m) -> genC m -> genC m.
  Proof.
    induction n ; intro m.
    (* n = 0 *)
    rewrite plus_O_n.
    intro a.
    intro l.
    induction l as [|n ha ta].
    (* genTop *)
    exact (genCons a genTop).
    (* genCons ha ta *)
    exact (genCons a ta).

    (* S n *)
    rewrite plus_Sn_m. rewrite plus_n_Sm.
    intro a ; intro l.
    induction l as [m|m ha ta].
    (* genTop *)
    specialize (IHn (S m)).
    exact (genCons top (IHn a genTop)).

    (* genCons *)
    specialize (IHn (S m)).
    exact (genCons ha (IHn a ta)).
  Defined.

  Definition override (n : nat) (x : A n) (g: genC 0) : genC 0 :=
    override_fix n 0 (match plus_n_O n in _ = y0 return A y0 with eq_refl => x end) g.

  Lemma override_fix_correct : forall (n m : nat) (x : A (n+m)) (g: genC m), genC_nth n m (override_fix n m x g) = x.
  Proof.
    
    
  (*
  Inductive relC : forall {n : nat} (a : genC n) (b : genC n), Type :=
  | relTop : forall {n} (c : genC n), relC c genTop
  | relCons : forall {n} {a b : A n} (r : R n a b) (c d : genC (S n)) (rtl : relC c d), relC (genCons a c) (genCons b d).
  *)

  (* Injection of generators into the term algebra of
     the free frame *)
  Definition inj u := Gen (GenT u).
  
  Inductive genR : term (genT := genT) -> term (genT := genT)  -> Type :=
  (* meets of generators are computed pointwise (two inequalities) *)
  | MeetL : forall a b, genR (inj (genMeet a b)) (Meet (inj a) (inj b))
  | MeetR : forall a b, genR (Meet (inj a) (inj b)) (inj (genMeet a b))
  (* joins distribute *)

  Definition product := FFrame (genT := genT) (genR := genR).

End ProductFrame.

About product.
Theorem tychonoff : forall F, (forall n, compact (F n)) -> compact (product F).
  
  
                     
                     

  

  
  
  