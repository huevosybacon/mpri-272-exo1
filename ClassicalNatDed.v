Require Import FormalSystem Translation.

(*-----------------------------*)
(*Classical Logic*)

(*Schema of Excluded Middle*)
Inductive classic : form -> Prop :=
  Cem P : classic (Or P (!P)).


(*The union of two theories/contexts*)
Definition U_theory L L' : form -> Prop :=
  fun f => L f \/ L' f.
Notation "L ⋃ T" := (U_theory L T)
                      (at level 99).


(*Classical derivability*)
Definition deriv_classic L f : Prop :=
  L ⋃ classic ⊢ f.
Notation "L ⊢ₖ f" := (deriv_classic L f)
                       (at level 99).


(*Question 3.1.1*)
(*There is always an intuitionistic proof of nnt(A + ¬A)*)
Lemma c_nnt f :
  classic f ->
  forall L, L ⊢ nnt f.
Proof.
  intro H. induction H; simpl in *; intros.
  apply imp_i, (imp_e _ (Or (nnt P) (!(nnt P)))).
  - apply ax. right. reflexivity.
  - apply or_i2, imp_i, (imp_e _ (Or (nnt P) (!(nnt P)))).
    + apply ax. left. right. reflexivity.
    + apply or_i1, ax. right. reflexivity.
Qed.




(* Question 3.2.1 *)
(*Elimination of EM under the translation*)
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




