Require Import FormalSystem.

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
    + apply IHf1, imp_i. apply (imp_e _ (nnt f1) _).
       apply ax; right; reflexivity.
      * apply Fa_e, (imp_e _ (! And (nnt f1) (nnt f2))).
        
    
    