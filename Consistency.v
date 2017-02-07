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


Lemma intf_soundness (L:_->Prop) f:
  (forall g, L g -> intf g) ->
  L ⊢ f -> intf f.
Proof.
  intros H' H. induction H; simpl in *; try auto.
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
  - destruct IHderiv.
    + assumption.
    + apply (H0 x). intros g H''. case H''.
      * apply H'.
      * intro H3. rewrite H3. exact H2.
Qed.


Lemma intf_E A f:
  E A f ->
  intf f.
Proof.
  intro H; case H; simpl in *.
  + reflexivity.
  + symmetry. assumption.
  + intros. transitivity y; assumption.
Qed.


Lemma intf_A f:
  A f ->
  intf f.
Proof.
  intro H; case H; simpl in *.
  + apply O_S.
  + apply eq_add_S.
  + intros P. apply (nat_ind (fun x => intf (P x))).
Qed.



Lemma PA_consistency :
  ~ (Ø ⊢ₚ Fa).
Proof.
  intro.
  assert (Ø ⊢ₕ Fa).
  - apply (deriv_substitution (nnt_ctx Ø ⋃ HA)).
    + apply (nnt_ha Ø Fa). assumption.
    + intros. destruct H0.
      * destruct H0 as [g [H' H'']]. exfalso. apply H'.
      * apply ax; right; assumption.
  - apply (intf_soundness (Ø ⋃ HA) Fa).
    + destruct 1.
      * exfalso. apply H1.
      * destruct H1. apply intf_A. assumption.
        apply (intf_E nat). assumption.
    + assumption.
Qed.
        