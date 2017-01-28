
Set Printing Universes.

(* The inductive type of formulae. Note that the definition is 
  universe-polymorphic. If All or Ex quantifies over a type in a universe 
  the resulting formula is in a strictly higher universe. In particular,
  they cannot quantify over form. *)
Inductive form :=
| Tr   : form (* true/top *)
| Fa   : form (*absurd*)
| And  : form -> form -> form (*conjunction*)
| Or   : form -> form -> form (*disjunction*)
| Impl : form -> form -> form (*implication*)
| All  : forall {A : Type}, (A -> form) -> form (*Universal quantifier*)
| Ex   : forall {A : Type}, (A -> form) -> form (*Existential quantifier*)
| Atom : Prop -> form.


(* Context extension *)
Definition L_ext : (form -> Prop) -> form -> form -> Prop :=
  fun L f g => or (L g) (g = f).
Notation "L ⋯ f" := (L_ext L f) (at level 99).


(* One might be tempted by the following bad definition, of "removing a 
   hypothesis from a context"

Definition L_rm : (form -> Prop) -> form -> form -> Prop :=
  fun L A B => and (L B) (~ B = A).  *)



(* The inductive family of derivations, indexed over contexts and formulae *)
Inductive deriv : (form -> Prop) -> form -> Prop :=
| ax    : forall (L:_ -> Prop) f, L f -> deriv L f
| Tr_i  : forall L, deriv L Tr
| Fa_e  : forall L f, deriv L Fa -> deriv L f
| imp_i : forall (L:_ -> Prop) f g, deriv (L⋯f) g -> deriv L (Impl f g) .
| 



Notation "L ⊢ f" := (deriv L f) (at level 5).

Lemma deriv_weakening (L L' : form -> Prop) f :
  L ⊢ f ->
  (forall f, L f -> L' f) ->
  L' ⊢ f.
Proof.
  intros.
  induction H.
  apply ax, H0, H.
  apply Tr_i.
  apply Fa_e, IHderiv, H0.f
  apply imp_i.
  