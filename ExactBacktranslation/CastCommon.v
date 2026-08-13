Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.

(** Syntax and typing utilities shared by the [CastEq]-based coercion
    interpreters.  This module is intentionally independent of any equality
    certificate representation. *)
Definition tm_app : Tm -> Tm -> Tm := StlcIso.SpecSyntax.app.

Definition cast_pair_ty (A B : Ty) : Ty :=
  tprod (tarr A B) (tarr B A).

Definition id_cast (A : Ty) : Tm := abs A (var 0).

Lemma typing_weaken {Gamma t T U} :
  ⟪ Gamma i⊢ t : T ⟫ -> ⟪ Gamma r▻ U i⊢ t[wkm] : T ⟫.
Proof.
  intros Ht. eapply typing_sub; [exact Ht|].
  apply wtSub_wkm.
Qed.

Lemma id_cast_typing {Gamma A} :
  ValidTy A -> ⟪ Gamma i⊢ id_cast A : tarr A A ⟫.
Proof.
  intros VA. unfold id_cast.
  apply WtAbs; [apply WtVar; constructor|exact VA].
Qed.
