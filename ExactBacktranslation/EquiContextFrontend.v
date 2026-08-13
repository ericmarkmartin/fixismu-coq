Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.EquiToIndexed.
Require Import ExactBacktranslation.IndexedContexts.
Require Import StlcEqui.SpecAnnot.
Require Import StlcIso.SpecAnnot.

Module EACF := StlcEqui.SpecAnnot.
Module IACF := StlcIso.SpecAnnot.

(** Structural elaboration of an existing annotated Equi context.  The hole
    stays in its original evaluation position.  As for terms, [result]
    supplies the target endpoint at an enclosing conversion. *)
Fixpoint equi_context_to_indexed (result : Ty)
    (C : EACF.PCtxA) : ICCtx :=
  match C with
  | EACF.ea_phole => icc_hole
  | EACF.ea_pabs A B C0 =>
      icc_abs A B (equi_context_to_indexed B C0)
  | EACF.ea_papp₁ A B C0 x =>
      icc_app1 A B (equi_context_to_indexed (tarr A B) C0)
        (equi_to_indexed A x)
  | EACF.ea_papp₂ A B f C0 =>
      icc_app2 A B (equi_to_indexed (tarr A B) f)
        (equi_context_to_indexed A C0)
  | EACF.ea_pite₁ A C0 x y =>
      icc_ite1 A (equi_context_to_indexed tbool C0)
        (equi_to_indexed A x) (equi_to_indexed A y)
  | EACF.ea_pite₂ A b C0 y =>
      icc_ite2 A (equi_to_indexed tbool b)
        (equi_context_to_indexed A C0) (equi_to_indexed A y)
  | EACF.ea_pite₃ A b x C0 =>
      icc_ite3 A (equi_to_indexed tbool b) (equi_to_indexed A x)
        (equi_context_to_indexed A C0)
  | EACF.ea_ppair₁ A B C0 y =>
      icc_pair1 A B (equi_context_to_indexed A C0)
        (equi_to_indexed B y)
  | EACF.ea_ppair₂ A B x C0 =>
      icc_pair2 A B (equi_to_indexed A x)
        (equi_context_to_indexed B C0)
  | EACF.ea_pproj₁ A B C0 =>
      icc_proj1 A B (equi_context_to_indexed (tprod A B) C0)
  | EACF.ea_pproj₂ A B C0 =>
      icc_proj2 A B (equi_context_to_indexed (tprod A B) C0)
  | EACF.ea_pinl A B C0 => icc_inl A B (equi_context_to_indexed A C0)
  | EACF.ea_pinr A B C0 => icc_inr A B (equi_context_to_indexed B C0)
  | EACF.ea_pcaseof₁ A B R C0 l r =>
      icc_case1 A B R (equi_context_to_indexed (tsum A B) C0)
        (equi_to_indexed R l) (equi_to_indexed R r)
  | EACF.ea_pcaseof₂ A B R s C0 r =>
      icc_case2 A B R (equi_to_indexed (tsum A B) s)
        (equi_context_to_indexed R C0) (equi_to_indexed R r)
  | EACF.ea_pcaseof₃ A B R s l C0 =>
      icc_case3 A B R (equi_to_indexed (tsum A B) s)
        (equi_to_indexed R l) (equi_context_to_indexed R C0)
  | EACF.ea_pseq₁ A C0 y =>
      icc_seq1 A (equi_context_to_indexed tunit C0)
        (equi_to_indexed A y)
  | EACF.ea_pseq₂ A x C0 =>
      icc_seq2 A (equi_to_indexed tunit x)
        (equi_context_to_indexed A C0)
  | EACF.ea_pcoerce A C0 =>
      match decide_casteq A result with
      | Some d => icc_coerce A result d (equi_context_to_indexed A C0)
      | None => icc_hole
      end
  end.

Theorem equi_context_to_indexed_typing
    {Gamma0 A0 Gamma C A} :
  EACF.PCtxTypingAnnot Gamma0 A0 Gamma C A ->
  ICCtxTyping Gamma0 A0 Gamma (equi_context_to_indexed A C) A.
Proof.
  induction 1; cbn;
    eauto using ICCtxTyping, equi_to_indexed_typing.
  change (ICCtxTyping Gamma0 A0 Γ
    (match decide_casteq T U with
     | Some d => icc_coerce T U d (equi_context_to_indexed T C)
     | None => icc_hole
     end) U).
  destruct (decide_casteq T U) as [d|] eqn:Hdec.
  - eapply ICC_Coerce; eauto.
  - exfalso.
    destruct (decide_casteq_complete T U H1 H2 H) as [d Hd].
    congruence.
Qed.

Theorem erase_equi_context_to_indexed_annot
    {Gamma0 A0 Gamma C A} :
  EACF.PCtxTypingAnnot Gamma0 A0 Gamma C A ->
  erase_indexed_context (equi_context_to_indexed A C) = C.
Proof.
  induction 1; cbn;
    try solve [repeat f_equal;
      eauto using erase_equi_to_indexed_annot].
  change
    (erase_indexed_context
      (match decide_casteq T U with
       | Some d => icc_coerce T U d (equi_context_to_indexed T C)
       | None => icc_hole
       end) = EACF.ea_pcoerce T C).
  destruct (decide_casteq T U) as [d|] eqn:Hdec; cbn.
  - now rewrite IHPCtxTypingAnnot.
  - exfalso.
    destruct (decide_casteq_complete T U H1 H2 H) as [d Hd].
    congruence.
Qed.

Definition compile_equi_context_annot (result : Ty)
    (C : EACF.PCtxA) : IACF.PCtxA :=
  compile_indexed_context_annot (equi_context_to_indexed result C).

Definition compile_equi_context_raw (result : Ty)
    (C : EACF.PCtxA) : StlcIso.SpecSyntax.PCtx :=
  IACF.eraseAnnot_pctx (compile_equi_context_annot result C).

Theorem compile_equi_context_annot_typing
    {Gamma0 A0 Gamma C A} :
  EACF.PCtxTypingAnnot Gamma0 A0 Gamma C A ->
  IACF.PCtxTypingAnnot Gamma0 A0 Gamma
    (compile_equi_context_annot A C) A.
Proof.
  intros HC. apply compile_indexed_context_annot_typing.
  now apply equi_context_to_indexed_typing.
Qed.

Theorem erase_compile_equi_context_annot (result : Ty)
    (C : EACF.PCtxA) :
  IACF.eraseAnnot_pctx (compile_equi_context_annot result C) =
  compile_indexed_context (equi_context_to_indexed result C).
Proof. apply erase_compile_indexed_context_annot. Qed.

Theorem compile_equi_context_raw_typing
    {Gamma0 A0 Gamma C A} :
  EACF.PCtxTypingAnnot Gamma0 A0 Gamma C A ->
  StlcIso.SpecTyping.PCtxTyping Gamma0 A0 Gamma
    (compile_equi_context_raw A C) A.
Proof.
  intros HC. apply IACF.eraseAnnot_pctxT,
    compile_equi_context_annot_typing. exact HC.
Qed.
