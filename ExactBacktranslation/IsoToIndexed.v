Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import CompilerIE.Compiler.
Require Import StlcIso.SpecAnnot.
Require Import RecTypes.LemmasTypes.

Module IA := StlcIso.SpecAnnot.
Module CIE := CompilerIE.Compiler.

(** A concrete presentation of the erased Iso program in the indexed Equi
    frontend.  Fold and unfold become ordinary Equi conversions, whose
    certificates are computed solely from their two endpoint types. *)
Fixpoint iso_to_indexed (t : IA.TmA) : ICTm :=
  match t with
  | IA.ia_var i => ic_var i
  | IA.ia_abs A B body => ic_abs A B (iso_to_indexed body)
  | IA.ia_app A B f x => ic_app A B (iso_to_indexed f) (iso_to_indexed x)
  | IA.ia_unit => ic_unit
  | IA.ia_true => ic_true
  | IA.ia_false => ic_false
  | IA.ia_ite A b x y =>
      ic_ite A (iso_to_indexed b) (iso_to_indexed x) (iso_to_indexed y)
  | IA.ia_pair A B x y =>
      ic_pair A B (iso_to_indexed x) (iso_to_indexed y)
  | IA.ia_proj₁ A B x => ic_proj1 A B (iso_to_indexed x)
  | IA.ia_proj₂ A B x => ic_proj2 A B (iso_to_indexed x)
  | IA.ia_inl A B x => ic_inl A B (iso_to_indexed x)
  | IA.ia_inr A B x => ic_inr A B (iso_to_indexed x)
  | IA.ia_caseof A B C s l r =>
      ic_case A B C (iso_to_indexed s) (iso_to_indexed l)
        (iso_to_indexed r)
  | IA.ia_seq A x y => ic_seq A (iso_to_indexed x) (iso_to_indexed y)
  | IA.ia_fold_ body x =>
      let unfolded := body[beta1 (trec body)] in
      match decide_casteq unfolded (trec body) with
      | Some d => ic_coerce unfolded (trec body) d (iso_to_indexed x)
      | None => ic_unit
      end
  | IA.ia_unfold_ body x =>
      let unfolded := body[beta1 (trec body)] in
      match decide_casteq (trec body) unfolded with
      | Some d => ic_coerce (trec body) unfolded d (iso_to_indexed x)
      | None => ic_unit
      end
  end.

Lemma fold_endpoint_tyeq body :
  Tyeq body[beta1 (trec body)] (trec body).
Proof. constructor. apply tyeq_refl. Qed.

Lemma unfold_endpoint_tyeq body :
  Tyeq (trec body) body[beta1 (trec body)].
Proof. constructor. apply tyeq_refl. Qed.

Theorem iso_to_indexed_typing {Gamma t A} :
  IA.AnnotTyping Gamma t A -> ICTyping Gamma (iso_to_indexed t) A.
Proof.
  induction 1; cbn; eauto using ICTyping.
  - change (ICTyping Γ
      (match decide_casteq τ[beta1 (trec τ)] (trec τ) with
       | Some d => ic_coerce τ[beta1 (trec τ)] (trec τ) d
           (iso_to_indexed t)
       | None => ic_unit
       end) (trec τ)).
    pose proof (ValidTy_unfold_trec H0) as Vunfolded.
    destruct (decide_casteq (τ[beta1 (trec τ)]) (trec τ))
      as [d|] eqn:Hdec.
    + eapply IC_WtCoerce; eauto.
    + exfalso.
      destruct (decide_casteq_complete _ _ Vunfolded H0
        (fold_endpoint_tyeq τ)) as [d Hd].
      congruence.
  - change (ICTyping Γ
      (match decide_casteq (trec τ) τ[beta1 (trec τ)] with
       | Some d => ic_coerce (trec τ) τ[beta1 (trec τ)] d
           (iso_to_indexed t)
       | None => ic_unit
       end) τ[beta1 (trec τ)]).
    pose proof (ValidTy_unfold_trec H0) as Vunfolded.
    destruct (decide_casteq (trec τ) (τ[beta1 (trec τ)]))
      as [d|] eqn:Hdec.
    + eapply IC_WtCoerce; eauto.
    + exfalso.
      destruct (decide_casteq_complete _ _ H0 Vunfolded
        (unfold_endpoint_tyeq τ)) as [d Hd].
      congruence.
Qed.

(** On well-typed annotated syntax, the impossible failure arms in
    [iso_to_indexed] disappear, so certificate erasure is definitionally the
    repository's existing Iso-to-Equi annotated compiler. *)
Theorem erase_iso_to_indexed_annot {Gamma t A} :
  IA.AnnotTyping Gamma t A ->
  erase_indexed_certificate (iso_to_indexed t) = CIE.compie_annot t.
Proof.
  induction 1; cbn; try congruence.
  - change
      (erase_indexed_certificate
        (match decide_casteq τ[beta1 (trec τ)] (trec τ) with
         | Some d => ic_coerce τ[beta1 (trec τ)] (trec τ) d
             (iso_to_indexed t)
         | None => ic_unit
         end) = CIE.compie_annot (IA.ia_fold_ τ t)).
    pose proof (ValidTy_unfold_trec H0) as Vunfolded.
    destruct (decide_casteq (τ[beta1 (trec τ)]) (trec τ))
      as [d|] eqn:Hdec; cbn.
    + now rewrite IHAnnotTyping.
    + exfalso.
      destruct (decide_casteq_complete _ _ Vunfolded H0
        (fold_endpoint_tyeq τ)) as [d Hd].
      congruence.
  - change
      (erase_indexed_certificate
        (match decide_casteq (trec τ) τ[beta1 (trec τ)] with
         | Some d => ic_coerce (trec τ) τ[beta1 (trec τ)] d
             (iso_to_indexed t)
         | None => ic_unit
         end) = CIE.compie_annot (IA.ia_unfold_ τ t)).
    pose proof (ValidTy_unfold_trec H0) as Vunfolded.
    destruct (decide_casteq (trec τ) (τ[beta1 (trec τ)]))
      as [d|] eqn:Hdec; cbn.
    + now rewrite IHAnnotTyping.
    + exfalso.
      destruct (decide_casteq_complete _ _ H0 Vunfolded
        (unfold_endpoint_tyeq τ)) as [d Hd].
      congruence.
Qed.
