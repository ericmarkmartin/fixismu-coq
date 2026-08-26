Require Import LogRelFI.PseudoType.

From Stdlib Require Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.

Module B := Corelib.Init.Datatypes.

Require Import RecTypes.Contraction.

From Stdlib Require Import micromega.Lia.

Inductive SimplePContr : PTy → Prop :=
  | SimpContrPUnit : SimplePContr ptunit
  | SimpContrPBool : SimplePContr ptbool
  | SimpContrPArrow {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptarr τ τ')
  | SimpContrPSum {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptsum τ τ')
  | SimpContrPProd {τ τ'} : SimplePContr τ → SimplePContr τ' → SimplePContr (ptprod τ τ')
  | SimpContrPEmulDV {n p τ} : SimpleContr τ → SimplePContr (pEmulDV n p τ).
