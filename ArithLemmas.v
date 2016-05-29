
(* These lemmas are used in the bijections of BijNat *)
(* N x N -> N *)
(* N + N -> N *)

Require Export Coq.Arith.Div2.
Require Export Coq.Arith.Even.

Section Arithmetic_Lemmas.
  (* Preliminaries on predecessors *)

  Lemma pred_sum : forall a b, a > 0 -> b > 0 -> pred (pred (a + b)) = pred a + pred b.
  Proof.
    intros.
    destruct a, b.
    inversion H.
    inversion H.
    inversion H0.
    simpl.
    rewrite <- plus_n_Sm.
    reflexivity.
  Qed.

  Lemma pred_inj : forall a b, a > 0 -> b > 0 -> pred a = pred b -> a = b.
  Proof.
    intros.
    destruct a,b.
    inversion H.
    inversion H.
    inversion H0.
    simpl in H1. rewrite H1. reflexivity.
  Qed.

  Lemma even_pred : forall a, (a > 0) -> even (pred a) -> odd a.
  Proof.
    intro. destruct a.
    intros. inversion H.
    simpl. intros. apply odd_S. assumption.
  Qed.

  (* Preliminaries on doubles *)
  
  Lemma double_is_even : forall n, even (double n).
  Proof.
    unfold double.
    induction n.
    rewrite plus_O_n. apply even_O.
    rewrite plus_Sn_m.
    rewrite <- plus_n_Sm.
    apply even_S. apply odd_S. assumption.
  Qed.
  
  Lemma double_plus : forall n, double n = n + n.
  Proof.
    reflexivity.
  Qed.

  Lemma double_injective : forall a b, double a = double b -> a = b.
  Proof.
    intro a. induction a.
    intros. unfold double in H. rewrite <- plus_n_O in H.
    destruct b. reflexivity. rewrite plus_Sn_m in H.
    inversion H.
    
    intros. destruct b.
    unfold double in H. rewrite <- plus_n_O in H.
    rewrite plus_Sn_m in H. inversion H.
    rewrite double_S in H.
    rewrite double_S in H.
    inversion H. apply IHa in H1. rewrite H1. reflexivity.
  Qed.

  Lemma double_2times : forall n, double n = 2*n.
  Proof.
    intro.
    simpl. rewrite <- plus_n_O.
    reflexivity.
  Qed.

End Arithmetic_Lemmas.