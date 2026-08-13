Require Import ExactBacktranslation.IsoRoundTrip.
Require Import ExactBacktranslation.IsoToIndexed.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import StlcIso.SpecAnnot.

Module IATest := StlcIso.SpecAnnot.

Definition iso_fold_unfold_unit : IATest.TmA :=
  IATest.ia_unfold_ tunit (IATest.ia_fold_ tunit IATest.ia_unit).

Lemma iso_fold_unfold_unit_typing :
  IATest.AnnotTyping empty iso_fold_unfold_unit tunit.
Proof.
  unfold iso_fold_unfold_unit.
  apply IATest.ia_WtUnfold.
  - apply IATest.ia_WtFold.
    + apply IATest.ia_WtUnit.
    + apply RecTypes.LemmasTypes.ValidTy_rec; constructor.
  - apply RecTypes.LemmasTypes.ValidTy_rec; constructor.
Qed.

Example iso_fold_unfold_translation_uses_computed_casts :
  exists df du,
    iso_to_indexed iso_fold_unfold_unit =
      ic_coerce (trec tunit) tunit du
        (ic_coerce tunit (trec tunit) df ic_unit).
Proof. vm_compute. eauto. Qed.

Example iso_fold_unfold_exact_roundtrip :
  StlcIso.SpecEquivalent.PCtxEquivalent empty
    (compile_indexed (iso_to_indexed iso_fold_unfold_unit))
    (IATest.eraseAnnot iso_fold_unfold_unit) tunit.
Proof. exact (exact_iso_roundtrip_annot iso_fold_unfold_unit_typing). Qed.

Example iso_erasure_exact_full_abstraction :
  (StlcIso.SpecEquivalent.PCtxEquivalent empty
      (IATest.eraseAnnot iso_fold_unfold_unit)
      (IATest.eraseAnnot iso_fold_unfold_unit) tunit <->
   StlcEqui.SpecEquivalent.PCtxEquivalent empty
      (CompilerIE.Compiler.compie
        (IATest.eraseAnnot iso_fold_unfold_unit))
      (CompilerIE.Compiler.compie
        (IATest.eraseAnnot iso_fold_unfold_unit)) tunit).
Proof.
  exact (exact_iso_annot_full_abstraction
    iso_fold_unfold_unit_typing iso_fold_unfold_unit_typing).
Qed.
