Require Import FormalSystem Translation Classical.

(* ——————————————————————— *)

(* Question 4.1 *)

(* Equality *)


Notation "f ⇒ g" := (Impl f g)
                     (at level 99, right associativity).
Notation "x ≈ y" := (Atom (x=y))
                     (at level 99).
Notation "∀ P" := (All P)
                   (at level 99).

Inductive E (A:Type) : form -> Prop :=
| E_refl (x:A)      : E A (x≈x) (*forall x:A, x=x*)
| E_symm (x y:A)    : E A ((x≈y) ⇒ (y≈x))
| E_trans (x y z:A) : E A ((x≈y) ⇒ (y≈z) ⇒ (x≈z)).

Inductive E' (A:Type) : form -> Prop :=
| E'_refl : E' A (All (fun x:A => x≈x)) (*forall x:A, x=x*)
| E'_symm : E' A (All (fun x:A =>
                       All (fun y:A =>
                              (x≈y) ⇒ (y≈x))))
| E'_trans : E' A (All (fun x:A =>
                        All (fun y:A =>
                               All (fun z:A =>
                                      (x≈y) ⇒ (y≈z) ⇒ (x≈z))))).


Inductive A : form -> Prop :=
| PA3 (n:nat)  : A (!(0 ≈ S n))
| PA4 (m n:nat): A (S(m) ≈ S(n) ⇒ m≈n)
| PA5  P       : A (P 0 ⇒
                       (All (fun k => P k ⇒ P (S k)) ⇒
                            All (fun k => P k)))
.

Lemma plusnSm n m :
  E' nat ⊢ (S n +  m ≈ S (n + m)).
Proof.
  simpl. apply (all_e _ (fun x => x≈x)). apply ax, E'_refl.
Qed.


Definition PA := A ⋃ (E nat) ⋃ classic.
Definition HA := A ⋃ (E nat).
Definition deriv_PA L f := L ⋃ PA ⊢ f.
Definition deriv_HA L f := L ⋃ HA ⊢ f.

Notation "L ⊢ₚ f " := (deriv_PA L f)
                        (at level 99).
Notation "L ⊢ₕ f " := (deriv_HA L f)
                        (at level 99).


(*Question 4.2*)

Lemma nnt_helper L f :
  L⋯(!f) ⊢ f ->
  L ⊢ !!f.
Proof.
  intro. apply imp_i, (imp_e _ f).
  - apply ax. right. reflexivity.
  - assumption.
Defined.

Lemma imp_helper L f g :
  L⋯(f ⇒ g) ⊢ f ->
  L ⊢ ((f ⇒ g) ⇒ g).
Proof.
  intro. apply imp_i, (imp_e _ f).
  - apply ax. right. reflexivity.
  - assumption.
Defined.


Lemma E_nnt A f :
  E A f -> E A ⊢ nnt f.
Proof.
  intro H. induction H; simpl in *.
  - apply nnt_helper.
    apply ax. left. constructor.
  - apply imp_i, imp_i, (imp_e _ (!(x ≈ y))).
    + apply ax. left. right. reflexivity.
    + apply imp_i, (imp_e _ (y≈x)).
      * apply ax. left. right. reflexivity.
      * apply (imp_e _ (x≈y)); apply ax;
          [ left; left; left; constructor | right; reflexivity].
  - do 3 apply imp_i. apply (imp_e _ (!(y≈z))).
    + apply ax. left. right. reflexivity.
    + apply imp_i. apply (imp_e _ (!(x≈y))).
      * apply ax. left. left. left. right. reflexivity.
      * apply imp_i, (imp_e _ (x≈z)).
        apply ax; do 2 left; right; reflexivity.
        apply (imp_e _ (y≈z));[apply (imp_e _ (x≈y)); apply ax;
                               [do 5 left; constructor | right; reflexivity]
                              | apply ax; left; right; reflexivity].
Qed.


Lemma A_nnt f :
  A f -> A ⊢ nnt f.
Proof.
  intro H. induction H; simpl in *.
  - apply nnt_helper. apply ax; left; constructor.
  - apply imp_i, imp_i, (imp_e _ (!(S m≈S n))).
    + apply ax; left; right; reflexivity.
    + apply imp_i, (imp_e _ (m≈n)).
      * apply ax; left; right; reflexivity.
      * apply (imp_e _ (S m≈S n)); apply ax; [do 3 left; constructor
                                             |right; reflexivity].
  - apply ax, (PA5 (fun x => nnt (P x))).
Qed.

Lemma nnt_ha L f:
  L ⊢ₚ f ->
  nnt_ctx L ⊢ₕ nnt f.
Proof.
  intro H.
  assert (nnt_ctx (L ⋃ PA) ⊢ nnt f).
  - apply nnt_soundness. assumption.
  - apply (deriv_substitution (nnt_ctx (L ⋃ PA))).
    + assumption.
    + clear H H0. intros g H. destruct H as [h [H H']]. rewrite H'.
      clear H' g. case H.
      * intro. apply (deriv_substitution (nnt_ctx L)).
        -- apply nnt_soundness, ax; assumption.
        -- intros. apply ax. left. assumption.
      * intro H1. case H1.
        -- intro. case H0.
           ++ intro. apply (deriv_substitution A).
              ** apply A_nnt; assumption.
              ** intros. apply ax; right; left; assumption.
           ++ intro. apply (deriv_substitution (E nat)).
              --- apply E_nnt; assumption.
              --- intros. apply ax; right; right; assumption.
        -- intro. apply c_nnt; assumption.
Qed.