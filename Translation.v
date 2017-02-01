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


Lemma nnt_and {L} f g :
  L ⊢ (!!(And (nnt f) (nnt g))) ->
  (L ⊢ !! (nnt f)) * (L ⊢ !!(nnt g)).
Proof.
  intros; split; apply imp_i;
    [ apply (imp_e _ (nnt f) _) | apply (imp_e _ (nnt g) _)].
  - apply ax; right; reflexivity.
  - apply Fa_e, (imp_e _ (! And (nnt f) (nnt g))).
    * apply wkn, H.
    * apply imp_i, (imp_e _ (nnt f)).
        apply ax; left; right; reflexivity.
        apply (and_e1 _ _ (nnt g)), ax; right; reflexivity.
  - apply ax; right; reflexivity.
  - apply Fa_e, (imp_e _ (! And (nnt f) (nnt g))).
    * apply wkn, H.
    * apply imp_i, (imp_e _ (nnt g)).
        apply ax; left; right; reflexivity.
        apply (and_e2 _ (nnt f) _), ax; right; reflexivity.
Qed.

  
Lemma soundness (f : form) :
  forall L, L ⊢ (!! (nnt f)) ->
            L ⊢ nnt f.
Proof.
  induction f; intros.
  - apply Tr_i.
  - apply (imp_e _ (! Fa) (Fa)). 
    + apply H.
    + apply imp_i, ax; right; reflexivity.
  - cbn; cbn in H; apply and_i.
    + apply IHf1, (fst (nnt_and _ _ _)).
      