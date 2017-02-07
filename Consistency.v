Require Import FormalSystem Translation Classical
        EqualityArithmetic.

(* -------------------------- *)

Fixpoint intf f : Prop :=
  match f with
  | Tr => True
  | Fa => False
  | And g h => intf g /\ intf h
  | Or g h => intf g \/ intf h
  | Impl g h => intf g -> intf h
  | @All A P => forall x:A, intf (P x)
  | @Ex A P => exists x:A, intf (P x)
  | Atom p => p
  end.


Lemma intf_soundness (L:_->Prop):
  (forall g, L g -> intf g) ->
  forall f, L ⊢ f -> intf f.
Proof.
  intros H' f H. induction H; simpl in *; try auto.
  - exfalso. apply IHderiv, H'.
  - intro. apply IHderiv. intros g0 H1. case H1.
    + apply H'.
    + intro H2. rewrite H2. assumption.
  - apply IHderiv, H'.
  - apply IHderiv, H'.
  - case IHderiv1. apply H'.
    + intro. apply IHderiv2. intros g0 H1'. case H1'.
      * apply H'.
      * intro H1''. rewrite H1''. assumption.
    + intro. apply IHderiv3. intros g0 H1'. case H1'.
      * apply H'.
      * intro H1''. rewrite H1''. assumption.
  - exists t. auto.
  - apply (@ex_ind _ (fun x => intf (P x))).
    + intros. apply (H0 x). intros g H1'. case H1'.
      * apply H'.
      * intro H1''. rewrite H1''. assumption.
    + 