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


Lemma c_nnt f :
  classic f ->
  forall L, L ⊢ nnt f.
Proof.
  intro H. induction H. simpl in *.
  intros L.
  apply imp_i, (imp_e _ (Or (nnt P) (Impl (nnt P) Fa))).
  - apply ax. right. reflexivity.
  - 