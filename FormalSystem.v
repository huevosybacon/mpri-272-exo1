Set Printing Universes.

(*The inductive type of formulae. Note that if All or Ex quantifies over a type in a universe, then the resulting form is in a strictly higher universe. In particular, neither can quantify over *all* terms of type form. Note also that the definition is universe-polymorphic, thus the All and Ex constructors of a form at a higher level can quantify over a form at a lower level*)
Inductive form :=
| Tr : form (*true/⊤*)
| Fa : form (*absurd*)
| And : form -> form -> form (*conjunction*)
| Or : form -> form -> form (*disjunction*)
| Impl : form -> form -> form (*implication*)
| All : forall {A : Type}, (A -> form) -> form (*Universal quantifier*)
| Ex : forall {A : Type}, (A -> form) -> form (*Existential quantifier*)
| Atom : Prop -> form. (*Atomic propositions*)

Notation "f ⇒ g" := (Impl f g)
                     (at level 99, right associativity).


(*---------------------------------*)
(*Contexts --- are represented by terms L:form → Prop*)


(*Empty context*)
Definition Ø (f:form) := False.


(*Context extension*)
Definition L_ext : (form -> Prop) -> form -> form -> Prop :=
  fun L f g => (L g) \/ (g = f).
Notation "L ⋯ f" := (L_ext L f) (at level 99).


(*One might be tempted to make the following definition of "removing a hypothesis from a context", i.e. of discarding *all* occurrences of the formula from the context. This is unwise for the usual reasons ---

Definition L_rm : (form -> Prop) -> form -> form -> Prop :=
  fun L A B => and (L B) (~ B = A).*)


(*--------------------------------*)
(*Derivations/Judgements*)

(*Question 1.1.1*)
(*The inductive family of derivations, indexed over contexts and formulae, and valued in Prop. We choose to place ourselves in Natural Deduction.*)
Inductive deriv : (form -> Prop) -> form -> Prop :=
| ax     : forall (L:_ -> Prop) f,
             L f -> deriv L f
| Tr_i   : forall L, deriv L Tr
| Fa_e   : forall L f, deriv L Fa -> deriv L f
| imp_i  : forall L f g,
             deriv (L⋯f) g -> deriv L (Impl f g)
| imp_e  : forall L f g,
             deriv L (Impl f g) -> deriv L f -> deriv L g
| and_i  : forall L f g,
             deriv L f -> deriv L g -> deriv L (And f g)
| and_e1 : forall L f g,
             deriv L (And f g) -> deriv L f
| and_e2 : forall L f g,
             deriv L (And f g) -> deriv L g
| or_i1  : forall L f g,
             deriv L f -> deriv L (Or f g)
| or_i2  : forall L f g,
             deriv L g -> deriv L (Or f g)
| or_e   : forall L f g h,
             deriv L (Or f g) -> deriv (L⋯f) h -> deriv (L⋯g) h -> deriv L h
| ex_i   : forall L {A:Type} (P:A -> form) t,
             deriv L (P t) -> deriv L (Ex P)
| ex_e   : forall L {A:Type} (P:A -> form) f,
             (forall t, deriv (L⋯P t) f) -> (deriv L (Ex P)) -> deriv L f
(*Note the side condition that the standard formulaion of the rule above requires, namely that no instantiation of L and f contain t (This is usually stated by explicitly instantiating L and f with a context(-variable) and a formula(-variable), and t with a term-variable x, and requiring that x appear free neither in the instantiation of L nor in that of f). This is guaranteed by the fact that L and f are bound — in the Coq lambda-term/the meta-term — above the binder for t, thus t cannot be captured by any substitution for L or f. Note also that this meta-binding inside the scope of L and f is *precisely* what we mean when we say that the term-variable in the auxiliary premiss of the ∃-elim rule is free neither in the rest of the context nor in the conclusion.*)

| all_i  : forall L {A:Type} (P:A -> form),
             (forall t, deriv L (P t)) -> deriv L (All P)
(*same remark for the side condition in the rule above*)
                                                
| all_e  : forall L {A:Type} (P:A -> form),
             deriv L (All P) -> forall t, deriv L (P t).
Notation "L ⊢ f" := (deriv L f) (at level 99).



(* ---------------------------------------------  *)
(*The admissible inference rules*)


(*Weakening*)
Lemma deriv_weakening_strong (L : form -> Prop) f {H:L ⊢ f} :
  forall L':_-> Prop,
    (forall f, L f -> L' f) ->
    L' ⊢ f.
Proof.
  induction H; intros.
  - apply ax, H0, H.
  - apply Tr_i.
  - apply Fa_e, IHderiv, H0. 
  - apply imp_i, IHderiv. intros.
    case H1.
    + intro; left; apply H0. assumption.
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
    + apply IHderiv2. intros. case H3.
      * intro; left; apply H2; assumption.
      * intro; right; assumption.
    + apply IHderiv3; intros; case H3.
      * intro; left; apply H2; assumption.
      * intro; right; assumption.
  - apply (ex_i _ _ t), IHderiv, H0.
  - apply (ex_e _ P f). intro t1. apply (H0 t1).
    intros. case H3.
    + intro; left; apply H2; assumption.
    + intro; right; assumption.
    + apply IHderiv. assumption.
  - apply all_i. intro; apply H0, H1.
  - apply all_e, IHderiv, H0.
Defined.


(*Question 1.2.1*)
(*A logically equivalent statement, but where the induction tactic does not 
produce strong enough hypotheses for the proof to go through*)
Lemma deriv_weakening (L L' : form -> Prop) f :
  L ⊢ f ->
  (forall f, L f -> L' f) ->
  L' ⊢ f.
Proof.
  intros; apply (deriv_weakening_strong L); assumption.
Defined.

(*The usual form of the weakening rule*)
Lemma wkn (L : form -> Prop) g f :
  L ⊢ f -> (L⋯g) ⊢ f.
Proof.
  intro; apply (deriv_weakening L (L⋯_)).
  - assumption.
  - intros; left; assumption.
Defined.




(*Substitution/Cut/Context morphisms*)

(*A statement phrased in a way to let Coq's induction tactic go through*)
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
  - apply (ex_e _ P f). intro t1; apply (H0 t1).
    intros; case H3.
    + intro; apply wkn, H2; assumption.
    + intro. apply ax; right; assumption.
    + apply IHderiv. assumption.
  - apply all_i. intro; apply H0, H1.
  - apply all_e, IHderiv, H0.
Defined.


(*Question 1.2.2*)
(*A statement equivalent to the one above*)
Lemma deriv_substitution (L L' : form -> Prop) f :
  deriv L f ->
  (forall f, L f -> deriv L' f) ->
  deriv L' f.
Proof.
  intros.
  apply (deriv_substitution_strong L); assumption.
Defined.

(*Fin*)


