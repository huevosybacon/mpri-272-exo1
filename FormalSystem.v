
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
| Atom : Prop -> form. (*Atomic propositions*)




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
| ax     : forall (L:_ -> Prop) f, L f -> deriv L f
| Tr_i   : forall L, deriv L Tr
| Fa_e   : forall L f, deriv L Fa -> deriv L f
| imp_i  : forall (L:_ -> Prop) f g, deriv (L⋯f) g -> deriv L (Impl f g)
| imp_e  : forall L f g, deriv L (Impl f g) -> deriv L f -> deriv L g
| and_i  : forall L f g, deriv L f -> deriv L g -> deriv L (And f g)
| and_e1 : forall L f g, deriv L (And f g) -> deriv L f
| and_e2 : forall L f g, deriv L (And f g) -> deriv L g
| or_i1  : forall L f g, deriv L f -> deriv L (Or f g)
| or_i2  : forall L f g, deriv L g -> deriv L (Or f g)
| or_e   : forall L f g h, deriv L (Or f g) -> deriv (L⋯f) h -> deriv (L⋯g) h ->
                      deriv L h
| ex_i   : forall L {A:Type} (P:A -> form) t, deriv L (P t) -> deriv L (Ex P)
| ex_e   : forall L {A:Type} (P:A -> form) f, (forall t, deriv (L⋯P t) f) -> deriv L f 
| all_i  : forall L {A:Type} (P:A -> form), (forall t, deriv L (P t)) -> deriv L (All P)
| all_e  : forall L {A:Type} (P:A -> form), deriv L (All P) -> forall t, deriv L (P t).
Notation "L ⊢ f" := (deriv L f) (at level 99).


(* Weakening lemma *)
Lemma deriv_weakening_strong (L : form -> Prop) f :
  L ⊢ f ->
  forall L':_-> Prop, (forall f, L f -> L' f) ->
  L' ⊢ f.
Proof.
  intro H.
  induction H; intros.
  - apply ax, H0, H.
  - apply Tr_i.
  - apply Fa_e, IHderiv, H0. 
  - apply imp_i, IHderiv.
    intros.
    case H1.
    + intro; left; apply H0, H2.
    + intro; right; assumption.
  - apply (imp_e _ f g). apply IHderiv1, H1.
    apply IHderiv2, H1.
  - apply and_i.
    + apply IHderiv1, H1.
    + apply IHderiv2, H1.
  - apply (and_e1 _ _ g), IHderiv, H0.
  - apply (and_e2 _ f _), IHderiv, H0.
  - apply or_i1, IHderiv, H0.
  - apply or_i2, IHderiv, H0.
  - apply (or_e _ f g).
    + apply IHderiv1, H2.
    + apply IHderiv2; intros; case H3.
      * intro; left; apply H2; assumption.
      * intro; right; assumption.
    + apply IHderiv3; intros; case H3.
      * intro; left; apply H2; assumption.
      * intro; right; assumption.
  - apply (ex_i _ _ t), IHderiv, H0.
  - apply (ex_e _ P f); intro t1; apply (H0 t1).
    intros; case H2.
    + intro; left; apply H1; assumption.
    + intro; right; assumption.
  - apply all_i. intro; apply H0, H1.
  - apply all_e, IHderiv, H0.
Defined.

Lemma deriv_weakening (L L' : form -> Prop) f :
  L ⊢ f ->
  (forall f, L f -> L' f) ->
  L' ⊢ f.
Proof.
  intros; apply (deriv_weakening_strong L); assumption.
Defined.

(*The usual form of the weakening inference rule*)
Lemma wkn (L : form -> Prop) g f :
  L ⊢ f -> (L⋯g) ⊢ f.
Proof.
  intro; apply (deriv_weakening L (L⋯_)).
  - assumption.
  - intros; left; assumption.
Defined.


(*Substitution*)

Lemma deriv_substitution_strong (L : form -> Prop) f :
  deriv L f ->
  forall L', (forall f, L f -> deriv L' f) ->
        deriv L' f.
Proof.
  intros H; induction H; intros.
  - apply H0, H.
  - apply Tr_i.
  - apply Fa_e, IHderiv, H0. 
  - apply imp_i, IHderiv.
    intros. case H1.
    + intro; apply wkn.
      apply H0, H2. 
    + intro; apply ax; right; assumption.
  - apply (imp_e _ f g). apply IHderiv1, H1.
    apply IHderiv2, H1.
  - apply and_i.
    + apply IHderiv1, H1.
    + apply IHderiv2, H1.
  - apply (and_e1 _ _ g), IHderiv, H0.
  - apply (and_e2 _ f _), IHderiv, H0.
  - apply or_i1, IHderiv, H0.
  - apply or_i2, IHderiv, H0.
  - apply (or_e _ f g).
    + apply IHderiv1, H2.
    + apply IHderiv2; intros; case H3.
      * intro; apply wkn, H2, H4.
      * intro; apply ax; right; assumption.
    + apply IHderiv3. intros; case H3.
      * intro; apply wkn, H2, H4. 
      * intro; apply ax; right; assumption.
  - apply (ex_i _ _ t), IHderiv, H0.
  - apply (ex_e _ P f); intro t1; apply (H0 t1).
    intros; case H2.
    + intro; apply wkn, H1; assumption.
    + intro. apply ax; right; assumption.
  - apply all_i. intro; apply H0, H1.
  - apply all_e, IHderiv, H0.
Defined.

