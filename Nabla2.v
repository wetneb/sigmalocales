Require Import MyNotations.
Require Import PreorderEquiv.
Require Import Frame.

Section PropFrame.
  Definition implies (a b : Prop) := a -> b.
  Hint Unfold implies.

  Definition V (P : nat -> Prop) := exists n, P n.

  Definition PropFrame : @Frame Prop implies.
  Proof.
    apply MkFrame with (top := True) (bot := False) (meet := and) (join := or) (V := V) ; unfold implies, V ; firstorder.
  Defined.

End PropFrame.

Section Nabla2.
  Require Import Omega.
  Require Import MarkovSearch.

  Hint Unfold equiv le.
  Ltac unfold_selected := repeat autounfold with *.

  (* Prop *)
  Instance Prop_equiv : Equiv Prop := iff.
  Hint Unfold Prop_equiv.

  Definition Nabla2 := { p : Prop | ~~p -> p }.

  Definition N2eq (x y : Nabla2) : Prop := `x  = ` y.
  Instance N2eq_equiv : Equiv Nabla2 := N2eq.
  Hint Unfold N2eq_equiv N2eq.
  
  Ltac projNabla2 :=
    repeat (match goal with
      | [ x : Nabla2 |- _ ] => progress (
        match goal with
          | [ H : (~~ `x -> `x) |- _ ] => idtac
          | [ |- _ ] => assert (~~`x -> `x) by (apply proj2_sig)
        end)
    end).

  (* Nabla2 is ~~-separated *)
  Proposition Nabla2_nnsep : forall x y : Nabla2, ~~(x = y) -> x = y.
  Proof.
    unfold_selected.
    intros.
    projNabla2.
    tauto.
  Qed.
  
  (* Nabla2 is a frame *)
  Definition N2le (x y : Nabla2) := ` x -> ` y.
  Instance N2le_le : Le Nabla2 := N2le.
  Hint Unfold N2le_le N2le.
  
  Definition N2and (x y : Nabla2) : Nabla2.
    apply exist with (x := `x /\ `y).
    projNabla2. firstorder.
  Defined.
  Instance N2and_meet : Meet Nabla2 := N2and.
  Hint Unfold N2and_meet N2and.

  Definition N2or (x y : Nabla2) : Nabla2.
    apply exist with (x := ~~ (`x \/ `y)).
    projNabla2. firstorder.
  Defined.
  Instance N2or_join : Join Nabla2 := N2or.
  Hint Unfold N2or_join N2or.

  Definition N2V (P : nat -> Nabla2) : Nabla2.
    apply exist with (x := ~~ (exists n : nat, (` (P n)):Prop)).
    firstorder.
  Defined.
  Hint Unfold N2V.

  Definition N2top : Nabla2.
    apply exist with (x := True). firstorder.
  Defined.
  Instance N2top_top : Top Nabla2 := N2top.
  Hint Unfold N2top_top N2top.

  Definition N2bot : Nabla2.
    apply exist with (x := False). firstorder.
  Defined.
  Instance N2bot_bot : Bottom Nabla2 := N2bot.
  Hint Unfold N2bot_bot N2bot.

  Theorem Nabla2Frame : @Frame Nabla2 N2le.
  Proof.
    apply MkFrame with (top := N2top)
                         (bot := N2bot)
                         (meet := N2and)
                         (join := N2or)
                         (V := N2V) ;
    intros ; projNabla2 ; firstorder.
  Defined.

End Nabla2.