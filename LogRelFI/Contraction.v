Require Import LogRelFI.PseudoType.

Require Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Module B := Coq.Init.Datatypes.

Require Import RecTypes.Contraction.

Require Import Coq.micromega.Lia.

Inductive SimplePContr : PTy → Prop :=
  | SimpContrPUnit : SimplePContr ptunit
  | SimpContrPBool : SimplePContr ptbool
  | SimpContrPArrow {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptarr τ τ')
  | SimpContrPSum {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptsum τ τ')
  | SimpContrPProd {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptprod τ τ')
  | SimpContrPEmulDV {n p τ} : SimpleContr τ → SimplePContr (pEmulDV n p τ).
