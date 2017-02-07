Require Import FormalSystem.

(*---------------------------------*)

Definition nt : form -> form :=
  fun f => (Impl f Fa).
Notation "! f" := (nt f) (at level 99).



Fixpoint nnt (f : form) : form :=
  match f with
  | Tr => Tr
  | Fa => Fa
  | And f g => And (nnt f) (nnt g)
  | Or f g => !!(Or (nnt f) (nnt g))
  | Impl f g => Impl (nnt f) (nnt g)
  | All P => All (fun x => nnt (P x))
  | Ex P => !! (Ex (fun x => nnt (P x)))
  | Atom P => !! (Atom P) end.


Lemma nnt_and {L} f g (H:L ⊢ (!!(And (nnt f) (nnt g)))) :
  (L ⊢ !! (nnt f)) * (L ⊢ !!(nnt g)).
Proof.
  split; apply imp_i;
    [ apply (imp_e _ (nnt f) _) | apply (imp_e _ (nnt g) _)].
  - apply ax. right. reflexivity.
  - apply Fa_e, (imp_e _ (! And (nnt f) (nnt g))).
    * apply wkn, H.
    * apply imp_i, (imp_e _ (nnt f)).
        apply ax. left. right. reflexivity.
        apply (and_e1 _ _ (nnt g)), ax. right. reflexivity.
  - apply ax. right. reflexivity.
  - apply Fa_e, (imp_e _ (! And (nnt f) (nnt g))).
    * apply wkn, H.
    * apply imp_i, (imp_e _ (nnt g)).
        apply ax. left. right. reflexivity.
        apply (and_e2 _ (nnt f) _), ax. right. reflexivity.
Qed.



Lemma f_nnt {L} f (H:L ⊢ f) :
  L ⊢ !!f.
Proof.
  apply imp_i, (imp_e _ f Fa).
  - apply ax. right. reflexivity.
  - apply wkn. assumption.
Defined.



Lemma nnt_nt {L} f (H:L ⊢ !!! f) :
  L ⊢ !f.
Proof.
  apply imp_i, (imp_e _ (!!f) Fa).
  - apply wkn, H. 
  - apply f_nnt, ax. right. reflexivity.
Defined.



Lemma nnt_dne (f : form) :
  forall L, L ⊢ (!! (nnt f)) ->
            L ⊢ nnt f.
Proof.
  induction f; intros; cbn; simpl in *;
    try (apply nnt_nt; assumption).
  - apply Tr_i.
  - apply (imp_e _ (! Fa) (Fa)). 
    + apply H.
    + apply imp_i, ax. right. reflexivity.
  - apply and_i.
    + apply IHf1, (fst (nnt_and f1 f2 H)).
    + apply IHf2, (snd (nnt_and f1 f2 H)).
  - apply imp_i, IHf2, imp_i, (imp_e _ (! Impl (nnt f1) (nnt f2))).
    + apply wkn, wkn, H.
    + apply imp_i, (imp_e _ (nnt f2)).
      * apply ax. left. right. reflexivity.
      * apply (imp_e _ (nnt f1)). apply ax. right. reflexivity.
        apply ax. left. left. right. reflexivity.
  - apply all_i. intro t. apply H, imp_i, (imp_e _ (!nnt(All f))).
    apply wkn, H0. cbn. apply imp_i, (imp_e _ (nnt(f t))).
    + apply ax. left. right. reflexivity.
    + apply (all_e _ (fun x:A => nnt (f x))).
      apply ax. right. reflexivity.
Qed.



Definition nnt_ctx L : form ->  Prop :=
  fun f => exists f', L f' /\ f=nnt f'.

Lemma nnt_ctx_ext L f g :
  nnt_ctx (L⋯f) ⊢ g ->
  nnt_ctx L ⋯ nnt f ⊢ g. 
Proof.
  intro H. apply (deriv_substitution (nnt_ctx (L⋯f))).
  - exact H.
  - intros f0 H0. destruct H0 as [f' [p q]].
    case p.
    + intro. apply ax. left. exists f'.
      split; assumption.
    + intro H0. apply ax. right. rewrite H0  in q.
      exact q.
Qed.  

Lemma nnt_soundness f L :
  L ⊢ f -> nnt_ctx L ⊢ nnt f.
Proof.
  intro H. induction H; intros; simpl in *;
            try apply f_nnt; try (econstructor; assumption).
  - apply ax. exists f. split. apply H. reflexivity.
  - apply imp_i. apply nnt_ctx_ext. assumption.
  - apply (imp_e _ (nnt f)); assumption.
  - apply (and_e1 _ _ (nnt g)); assumption.
  - apply (and_e2 _ (nnt f)); assumption.
  - apply nnt_dne, imp_i.
    apply (imp_e _ (! Or (nnt f) (nnt g))).
    apply wkn; assumption. apply imp_i.
    apply (or_e _ (nnt f) (nnt g)).
    + apply ax. right. reflexivity.
    + apply (imp_e _ (nnt h)).
      * apply ax. left. left. right. reflexivity.
      * apply (deriv_weakening (nnt_ctx L⋯(nnt f))).
        apply nnt_ctx_ext. assumption.
        intros f0 H'. case H'.
        intros. left. left. left. assumption.
        intros. right. assumption.
    + apply (imp_e _ (nnt h)).
      * apply ax. left. left. right. reflexivity.
      * apply (deriv_weakening (nnt_ctx L⋯(nnt g))).
        apply nnt_ctx_ext. assumption.
        intros f0 H'. case H'.
        intros. left. left. left. assumption.
        intros. right. assumption.
  - apply (ex_i _ _ t). assumption.
  - apply (ex_e _ (fun t => nnt (P t)) _).
    + intro. apply nnt_ctx_ext, H0.
    + apply (ex_i.
  - apply (all_e _ (fun t => nnt (P t))).
    assumption.
Qed.


