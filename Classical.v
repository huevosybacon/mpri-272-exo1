Require Import FormalSystem Translation.

(*-----------------------------*)


(** * Classical derivability *)

Inductive classic : form -> Prop :=
  Cem P : classic (Or P (!P)).




Definition U_theory L L' : form -> Prop :=
  fun f => L f \/ L' f.

Notation "L ⋃ T" := (U_theory L T)
                      (at level 99).





Definition deriv_classic L f : Prop :=
  U_theory L classic ⊢ f.

Notation "L ⊢ₖ f" := (deriv_classic L f)
                       (at level 99).

(* Question 3.1 *)
Lemma c_nnt f :
  classic f ->
  forall L, L ⊢ nnt f.
Proof.
  intro H. induction H.
  intro. simpl in *.
  apply imp_i, (imp_e _ (Or (nnt P) (Impl (nnt P) Fa))).
  - apply ax. right. reflexivity.
  - apply or_i2, imp_i, (imp_e _ (Or (nnt P) (Impl (nnt P) Fa))).
    + apply ax. left. right. reflexivity.
    + apply or_i1, ax. right. reflexivity.
Qed.




(* Question 3.2 *)
Lemma nnt_lem L f :
  L ⊢ₖ f ->
  nnt_ctx L ⊢ nnt f.
Proof.
  intro H.
  assert (nnt_ctx (L ⋃ classic) ⊢ nnt f).
  - apply nnt_soundness. assumption.
  - apply (deriv_substitution (nnt_ctx (L ⋃ classic))).
    + assumption.
    + intros f0 H'. destruct H' as [x [H' H'']]. rewrite H''.
      case H'. 
      * intro. apply nnt_soundness, ax. assumption.
      * intro. apply c_nnt. assumption.
Qed.




