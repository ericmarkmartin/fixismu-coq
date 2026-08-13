Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import StlcEqui.SpecAnnot.

Module EAF := StlcEqui.SpecAnnot.

(** Computational elaboration of the repository's existing annotated Equi
    syntax.  The expected result type supplies the right endpoint omitted by
    [ea_coerce]; every other recursive expected type is already recorded by
    the repository's annotations. *)
Fixpoint equi_to_indexed (result : Ty) (t : EAF.TmA) : ICTm :=
  match t with
  | EAF.ea_var i => ic_var i
  | EAF.ea_abs A B body => ic_abs A B (equi_to_indexed B body)
  | EAF.ea_app A B f x =>
      ic_app A B (equi_to_indexed (tarr A B) f) (equi_to_indexed A x)
  | EAF.ea_unit => ic_unit
  | EAF.ea_true => ic_true
  | EAF.ea_false => ic_false
  | EAF.ea_ite A b x y =>
      ic_ite A (equi_to_indexed tbool b) (equi_to_indexed A x)
        (equi_to_indexed A y)
  | EAF.ea_pair A B x y =>
      ic_pair A B (equi_to_indexed A x) (equi_to_indexed B y)
  | EAF.ea_proj₁ A B x => ic_proj1 A B (equi_to_indexed (tprod A B) x)
  | EAF.ea_proj₂ A B x => ic_proj2 A B (equi_to_indexed (tprod A B) x)
  | EAF.ea_inl A B x => ic_inl A B (equi_to_indexed A x)
  | EAF.ea_inr A B x => ic_inr A B (equi_to_indexed B x)
  | EAF.ea_caseof A B C s l r =>
      ic_case A B C (equi_to_indexed (tsum A B) s)
        (equi_to_indexed C l) (equi_to_indexed C r)
  | EAF.ea_seq A x y =>
      ic_seq A (equi_to_indexed tunit x) (equi_to_indexed A y)
  | EAF.ea_coerce A x =>
      match decide_casteq A result with
      | Some d => ic_coerce A result d (equi_to_indexed A x)
      | None => ic_unit
      end
  end.

Theorem equi_to_indexed_typing {Gamma t A} :
  EAF.AnnotTyping Gamma t A -> ICTyping Gamma (equi_to_indexed A t) A.
Proof.
  induction 1; cbn; eauto using ICTyping.
  change (ICTyping Γ
    (match decide_casteq T U with
     | Some d => ic_coerce T U d (equi_to_indexed T t)
     | None => ic_unit
     end) U).
  destruct (decide_casteq T U) as [d|] eqn:Hdec.
  - eapply IC_WtCoerce; eauto.
  - exfalso.
    destruct (decide_casteq_complete T U H0 H1 H) as [d Hd].
    congruence.
Qed.

Theorem erase_equi_to_indexed_annot {Gamma t A} :
  EAF.AnnotTyping Gamma t A ->
  erase_indexed_certificate (equi_to_indexed A t) = t.
Proof.
  induction 1; cbn; try congruence.
  change
    (erase_indexed_certificate
      (match decide_casteq T U with
       | Some d => ic_coerce T U d (equi_to_indexed T t)
       | None => ic_unit
       end) = EAF.ea_coerce T t).
  destruct (decide_casteq T U) as [d|] eqn:Hdec; cbn.
  - now rewrite IHAnnotTyping.
  - exfalso.
    destruct (decide_casteq_complete T U H0 H1 H) as [d Hd].
    congruence.
Qed.

(** The user-facing compiler infers a certificate at each annotated
    conversion and then invokes the certificate interpreter. *)
Definition compile_equi_annot (result : Ty) (t : EAF.TmA) :
    StlcIso.SpecSyntax.Tm :=
  compile_indexed (equi_to_indexed result t).

Theorem compile_equi_annot_typing {Gamma t A} :
  EAF.AnnotTyping Gamma t A ->
  StlcIso.SpecTyping.Typing Gamma (compile_equi_annot A t) A.
Proof.
  intros Ht. apply compile_indexed_typing, equi_to_indexed_typing. exact Ht.
Qed.

Lemma compile_equi_coerce_strict {T U t} :
  Tyeq T U -> ValidTy T -> ValidTy U ->
  exists d,
    decide_casteq T U = Some d /\
    compile_equi_annot U (EAF.ea_coerce T t) =
      StlcIso.SpecSyntax.app (compile_global_up d)
        (compile_equi_annot T t).
Proof.
  intros HE VT VU.
  destruct (decide_casteq_complete T U VT VU HE) as [d Hd].
  exists d. split; [exact Hd|].
  unfold compile_equi_annot. cbn [equi_to_indexed]. now rewrite Hd.
Qed.
