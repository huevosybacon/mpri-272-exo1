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
| PA3 (n:nat)     : A (!(0 ≈ S n))
| PA4 (m n:nat)   : A (S(m) ≈ S(n) ⇒ m≈n)
| PA5 (m n:nat) P : A (P 0 ⇒
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

(*Question 4.2*)

Lemma nnt_helper L f :
  L⋯(!f) ⊢ f ->
  L ⊢ !!f.
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
  - apply imp_i, nnt_helper.