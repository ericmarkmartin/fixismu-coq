Require Export Coq.Unicode.Utf8.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Set Maximal Implicit Insertion.

(* Function composition. *)
Definition fcomp {X Y Z: Type} (f: X → Y) (g: Y → Z) : X → Z :=
  fun x => g (f x).
Arguments fcomp {_ _ _} f g i /.
Notation "f >-> g" := (fcomp f g) (at level 56).

(* Injectivity property. *)
Definition Inj {A B} (f: A → B) : Prop :=
  ∀ x y, f x = f y → x = y.

(** * Basic definitions

    This Section contains basic definitions for the de Bruijn representation
    of the abstract syntax.  *)

(** ** Domains *)

(** [Dom] is the representation of domains of typing contexts
    or of simultaneous renamings/substitutions. For the de
    Bruijn representation with a single sort with variables,
    we can represent domains as natural numbers. *)
Definition Dom: Set := nat.

Fixpoint dunion (δ₁ δ₂: Dom) {struct δ₂} : Dom :=
  match δ₂ with
    | O    => δ₁
    | S δ₂ => S (dunion δ₁ δ₂)
  end.
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 55, left associativity).

Section FoldlDom.

  Context {X : Type}.
  Variable s : X → X.

  Fixpoint foldlDom (δ: Dom) (x: X) : X :=
    match δ with
      | O   => x
      | S δ => foldlDom δ (s x)
    end.

End FoldlDom.

(** ** De Bruijn indices. *)
Definition Ix : Set := nat.

Reserved Notation "γ ∋ i" (at level 80).
Inductive wsIx : Dom → Ix → Prop :=
  | ws0 γ   :         S γ ∋ 0
  | wsS γ i : γ ∋ i → S γ ∋ S i
where "γ ∋ i" := (wsIx γ i).

(** ** Substitutions

    Substitutions are mapping from indices to values. The argument of 'Sub'
    indicates the sort of the substitures. A renaming is simply a substitution
    that substitutes indices for indices 'Sub Ix'.
 *)

Definition Sub (X: Type) : Type := Ix → X.
Definition snoc {X: Type} (ξ: Sub X) (x: X) : Sub X :=
  fun i =>
    match i with
      | O   => x
      | S i => ξ i
    end.
Notation "ξ · x" := (snoc ξ x) (at level 55, left associativity).
Arguments snoc {_} ξ x !i.

(** * Syntax related type-classes *)

Section Vars.

  (** Class for syntactic sorts with variables. *)
  Class Vr (X: Type) :=
    { vr: Sub X;
      vr_inj: Inj vr
    }.
  Arguments vr {_ _} i.

  Definition idm X {vrX: Vr X} : Sub X := vr.
  Global Arguments idm _ {_} i /.

End Vars.

Section Weaken.

  (** Class for syntactic sorts that can be weakened. *)
  Class Wk (X: Type) {vrX: Vr X} :=
    { wk: X → X;
      wk_inj: Inj wk;
      wk_vr: ∀ (i: Ix), wk (vr i) = vr (S i)
    }.
  Global Arguments wk {_ _ _} x.
  Definition wk_vr' := @wk_vr.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.

  Fixpoint wks (δ: Dom) (x: X) {struct δ} : X :=
    match δ with
      | O   => x
      | S δ => wk (wks δ x)
    end.
  Global Arguments wks !δ x.

  Definition wkm : Sub X := vr >-> wk.
  Global Arguments wkm i/.

  Fixpoint wkms (δ: Dom) {struct δ} : Sub X :=
    match δ with
      | O   => idm X
      | S δ => wkms δ >-> wk
    end.

  Definition up (ξ: Sub X) : Sub X :=
    (ξ >-> wk) · vr 0.
  Global Arguments up ξ !i.

  Fixpoint ups (ξ: Sub X) (δ: Dom) {struct δ} : Sub X :=
    match δ with
      | O   => ξ
      | S δ => up (ups ξ δ)
    end.
  Global Arguments ups ξ !δ i.

End Weaken.

Notation "ξ ↑" := (up ξ)
  (at level 8, left associativity, format "ξ ↑").
Notation "x ↑⋆ δ" := (ups x δ)
  (at level 53, left associativity).

Section Lift.

  (* Lifting terms of sort X to terms of sort Y. *)
  Class Lift (X Y: Type) {vrX: Vr X} {vrY: Vr Y} :=
    { lift: X → Y;
      lift_inj: Inj lift;
      lift_vr: ∀ (i: Ix), lift (vr i) = vr i
    }.

  Context {X: Type}.
  Context {vrX: Vr X}.

  #[refine] Global Instance liftXX : Lift X X := {| lift := fun x => x |}.
  Proof. unfold Inj; auto. reflexivity. Defined.

  Lemma liftXX_id (x: X) : lift x = x.
  Proof. reflexivity. Qed.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {liftXY: Lift X Y}.

  Definition liftSub (ξ: Sub X) : Sub Y :=
    ξ >-> lift.
  Global Arguments liftSub ξ i /.

End Lift.

Notation "⌈ ξ ⌉" := (liftSub ξ) (format "⌈ ξ ⌉").

Reserved Notation "t '[' ξ ']'"
  (at level 8, left associativity, format "t [ ξ ]").
Reserved Notation "ξ >=> ζ" (at level 56).

Section Application.

  (** Application of a substitution for sort Y to a term of sort X. *)
  Class Ap (X Y: Type) {vrY: Vr Y} :=
    { ap: Sub Y → X → X;
      ap_id: ∀ (x: X), ap (idm Y) x = x;
    }.
  Global Arguments ap {_ _ _ _} ζ !t /.
  Notation "t '[' ξ ']'" := (ap ξ t).

  Definition comp {X Y} {vrY: Vr Y} {apXY: Ap X Y}
    (ξ: Sub X) (ζ: Sub Y) : Sub X := fun i => (ξ i)[ζ].
  Global Arguments comp {_ _ _ _} ξ ζ i /.
  Notation "ξ >=> ζ" := (comp ξ ζ).

End Application.

Notation "t '[' ξ ']'" := (ap ξ t).
Notation "ξ >=> ζ" := (comp ξ ζ).

(* Class Subst (X: Type) {vrX: Vr X} {wkX: Wk X} {ap_X: Ap X X} := {}. *)

(** ** Ix Instances *)
Section Indices.

  #[refine] Global Instance vrIx: Vr Ix := {| vr := fun i => i |}.
  Proof. unfold Inj; auto. Defined.
  #[refine] Global Instance wkIx: Wk Ix := {| wk := S |}.
  Proof. unfold Inj; auto. reflexivity. Defined.
  #[refine] Global Instance apIxIx: Ap Ix Ix := {| ap := fun ξ i => ξ i |}.
  Proof. reflexivity. Defined.
  #[refine] Global Instance liftIx {X} {vrX: Vr X}: Lift Ix X := {| lift := vr |}.
  Proof. apply vr_inj. reflexivity. Defined.
  (* Global Instance sbIx: Subst Ix. *)

  (* The concrete weakening function 'wk' should be considered as an
     implementation detail and the user code should only ever see the abstract
     weakening morphism 'wkm'. Especially on indices the function constantly
     pops up during simplifications and often even reduces to an application of
     the successor constructor 'S'. To avoid this we capture the essentials of
     the 'wk' on indices in the following lemmas and make the 'Wk Ix' instance
     opaque to prevent simplification.

     The first two lemmas encode the reduction behaviour of snoc and up in the
     successor case. The remaining lemmas replace occurrences of 'wk' in
     contexts a substitution is expected by occurrences of the abstract
     weakening 'wkm'.

     In the case of an "unsnoc" operation -- such as in the definition of
     beta -- the successor constructor should be used instead of 'wk'.

     UPDATE: autorewrites replaced by a tactic
   *)

  (* Lemma snoc_wk {X: Type} (ζ: Sub X) (x: X) (i : Ix) : *)
  (*   snoc ζ x (wk i) = ζ i. *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma up_wk {X: Type} {vrX: Vr X} {wkX: Wk X} (ζ: Sub X) (i : Ix) : *)
  (*   (up ζ) (wk i) = wk (ζ i). *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma wk_up : wk↑ = wkm↑. *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma wk_ups (δ: Dom) : wk ↑⋆ δ = wkm ↑⋆ δ. *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma wk_ap {X: Type} {apX: Ap X Ix} (x: X) : x[wk] = x[wkm]. *)
  (* Proof. reflexivity. Qed. *)

  (* Lemma wk_liftSub (X: Type) {vrX: Vr X} : ⌈wk⌉ = ⌈wkm⌉. *)
  (* Proof. reflexivity. Qed. *)

  Global Opaque wkIx.

End Indices.

(** ** Beta substitution *)
Section Beta.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.

  (* Substitute the last δ variables by values determined by 'ζ' and
     leave the remaining variables alone. This means if (ζ: Δ => Γ)
     and (δ = dom Δ) then (beta δ ζ: Γ ,Δ => Γ).
  *)
  Fixpoint beta (δ: Dom) (ζ: Sub X) {struct δ} : Sub X :=
    match δ with
      | O   => idm X
      | S δ => snoc (beta δ (S >-> ζ)) (ζ 0)
    end.
  Global Arguments beta !δ ζ / i.

  Definition beta1 : X → Sub X :=
    fun x => beta 1 (idm X · x).
  Global Arguments beta1 x i/.

End Beta.

Class Ws (T: Type) := ws: Dom → T → Prop.
Notation "⟨  γ ⊢ t  ⟩" := (ws γ t) (at level 0, γ at level 99, t at level 99).
#[export]
Instance WsIx : Ws Ix := { ws := wsIx }.

Definition WsSub {X Y} {wsX: Ws X} {wsY : Ws Y} (γ δ: Dom) (ξ: Sub Y) : Prop :=
  ∀ (i: Ix), γ ∋ i → ⟨ δ ⊢ ξ i ⟩.
Notation "⟨ ξ : γ => δ ⟩" := (WsSub γ δ ξ)
 (at level 0, ξ at level 99, γ at level 99, δ at level 99).

Section BasicLemmas.

  Class WsVr (X: Type) {wsX: Ws X} {vrX: Vr X} :=
    {wsVr: ∀ (δ: Dom) (i: Ix), δ ∋ i → ⟨ δ ⊢ (vr (X := X) i) ⟩;
     wsiVr: ∀ (δ: Dom) (i: Ix), ⟨ δ ⊢ (vr (X := X) i) ⟩ → δ ∋ i
    }.
  Class WsWk (X: Type) {wsX: Ws X} {vrX: Vr X} {wkX: Wk X} :=
    {wsWk: ∀ (δ: Dom) (x: X), ⟨ δ ⊢ x ⟩ → ⟨ S δ ⊢ wk x ⟩;
     (* wsiWk: ∀ (δ: Dom) (x: X), ⟨ S δ ⊢ wk x ⟩ → ⟨ δ ⊢ x ⟩ *)
    }.
  Class WsAp (X Y: Type) {vrY: Vr Y} {ap: Ap X Y} {wsX: Ws X} {wsY: Ws Y} :=
    {wsAp: ∀ {ξ γ δ x}, ⟨ ξ : γ => δ ⟩ → ⟨ γ ⊢ x ⟩ → ⟨ δ ⊢ x[ξ] ⟩;
     wsApExt: ∀ {γ x}, ⟨ γ ⊢ x ⟩ →
              ∀ {ξ ζ} (Hξζ: ∀ i, γ ∋ i → ξ i = ζ i),
                x[ξ] = x[ζ]
    }.
  Class WsLift (X Y: Type) {vrX: Vr X} {vrY: Vr Y} {liftXY: Lift X Y} {wsX: Ws X} {wsY: Ws Y} :=
    {wsLift: ∀ (δ: Dom) (x: X), ⟨ δ ⊢ x ⟩ → ⟨ δ ⊢ lift x ⟩}.

End BasicLemmas.

Section AdvancedLemmas.

  Variable X Y Z: Type.
  Context {vrY: Vr Y}.
  Context {apXY: Ap X Y}.
  Context {vrZ: Vr Z}.

  Class LemApInj : Prop :=
    ap_inj: ∀ (m: Sub Y), Inj m → Inj (ap m).
  Class LemApComp {apXZ: Ap X Z} {apYZ: Ap Y Z} : Prop :=
    ap_comp: ∀ (x: X) (ξ: Sub Y) (ζ: Sub Z), x[ξ][ζ] = x[ξ >=> ζ].
  Class LemApLiftSub {apXIx: Ap X Ix} : Prop :=
    ap_liftSub: ∀ (t: X) (ξ: Sub Ix), t[⌈ξ⌉] = t[ξ].

  Context {vrX: Vr X}.

  Class LemApVr {liftYX: Lift Y X} : Prop :=
    ap_vr: ∀ (ξ: Sub Y) (i: Ix), (vr i)[ξ] = lift (ξ i).
  Class LemApLift {liftXZ: Lift X Z} {apZY: Ap Z Y}: Prop :=
    ap_lift: ∀ (ζ: Sub Y) (x: X), (lift x)[ζ] = lift x[ζ].

  Context {wkX: Wk X}.
  Context {wkY: Wk Y}.

  Class LemApWk : Prop :=
    ap_wk: ∀ (x: X), @wk X _ _ x = x[@wkm Y _ _].
  Class LemCompUp : Prop :=
    comp_up: ∀ (ξ : Sub X) (ζ : Sub Y), (ξ >=> ζ)↑ = (ξ↑) >=> (ζ↑).

End AdvancedLemmas.

Arguments ap_inj {_ _ _ _ _ m} _ [_ _] _.
Arguments ap_comp {_ _ _ _ _ _ _ _ _} x ξ ζ.
Arguments ap_vr {_ _ _ _ _ _ _} ξ i.
Arguments ap_lift {_ _ _ _ _ _ _ _ _ _} ζ x.
Arguments ap_wk {_ _ _ _ _ _ _ _} x.
Arguments comp_up {_ _ _ _ _ _ _ _} ξ ζ.
Arguments ap_liftSub {_ _ _ _ _ _} t ξ.

Section IndexInstances.

  #[refine] Global Instance compUpIx: LemCompUp Ix Ix := {}.
  Proof. intros; extensionality i; destruct i; reflexivity. Qed.
  #[refine] Global Instance apLiftSubIx: LemApLiftSub Ix Ix := {}.
  Proof. reflexivity. Qed.
  #[refine] Global Instance apVrIx: LemApVr Ix Ix := {}.
  Proof. reflexivity. Qed.
  #[refine] Global Instance wkApIxIx: LemApWk Ix Ix := {}.
  Proof. reflexivity. Qed.
  #[refine] Global Instance apCompIxIxIx: LemApComp Ix Ix Ix := {}.
  Proof. reflexivity. Qed.
  Global Instance wsVrIx : WsVr Ix.
  Proof. constructor; auto. Qed.
  Global Instance wsWkIx : WsWk Ix.
  Proof.
    constructor.
    - now constructor.
    (* - now inversion 1. *)
  Qed.
  Global Instance wsApIxIx : WsAp Ix Ix.
  Proof. constructor; auto. Qed.
  Global Instance wsLiftIx {X} `{WsVr X} : WsLift Ix X.
  Proof. constructor; eauto using wsVr. Qed.

End IndexInstances.

#[export]
Instance wsLiftXX {X} {vrX: Vr X} {wsX: Ws X} : WsLift X X.
Proof. now constructor. Qed.

Arguments liftXX_id _ {_} _.

#[export]
Instance wkT {T} {vrT: Vr T}
  {apT: ∀ {Y} {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y T}, Ap T Y}
  {apVrT: ∀ {Y} {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y T}, LemApVr T Y}
  {apTIxInj: LemApInj T Ix} : Wk T :=
  {| wk := ap wk;
     wk_inj := ap_inj wk_inj;
     wk_vr := ap_vr wk
  |}.

Create HintDb ws.
#[export]
Hint Constructors wsIx : ws.

Ltac crushDbSyntaxMatchH :=
  match goal with
    | [H: False   |- _] => elim H
    | [H: True    |- _] => clear H
    | [H: _ ∧ _   |- _] => destruct H

    | [H: ?x                   = ?x                   |- _] => clear H
    | [H: ?x                   ≠ ?x                   |- _] => elim H; reflexivity
    | [H: S _                  = S _                  |- _] => apply eq_add_S in H
    | [H: @vr ?X ?vrX _        = @vr ?X ?vrX _        |- _] => eapply vr_inj in H; eauto with typeclass_instances
    | [H: @wk ?X ?vrX ?wkX _   = @wk ?X ?vrX ?wkX _   |- _] => eapply wk_inj in H; eauto with typeclass_instances
    | [H: @lift ?X ?Y ?liftX _ = @lift ?X ?Y ?liftX _ |- _] => eapply lift_inj in H; eauto with typeclass_instances

    | [|- ?x                   = ?x                   ] => reflexivity
    | [|- S _                  = S _                  ] => f_equal
    | [|- @vr ?X ?vrX _        = @vr ?X ?vrX _        ] => apply (f_equal (@vr X vrX))
    | [|- @wk ?X ?vrX ?wkX _   = @wk ?X ?vrX ?wkX _   ] => apply (f_equal (@wk X vrX wkX))
    | [|- @lift ?X ?Y ?vrX ?vrY ?liftXY _ = @lift ?X ?Y ?vrX ?vrY ?liftXY _ ] =>
      apply (f_equal (@lift X Y vrX vrY liftXY))

    (* | |- context[@lift _ _ _ _ liftXX ?x      ] => change (@lift _ _ _ _ liftXX x) with x *)
    | |- context[@vr Ix vrIx ?i               ] => change (@vr Ix vrIx i) with i
    | |- context[(?ζ · ?x) (wk ?i)            ] => change ((ζ · _) (wk i)) with (ζ i)
    | |- context[?ζ↑ (wk ?i)                  ] => change (ζ↑ (wk i)) with (wk (ζ i))
    | |- context[wk↑                          ] => change wk↑ with (@wkm Ix _ _)↑
    | |- context[wk ↑⋆ ?δ                     ] => change (wk ↑⋆ δ) with (@wkm Ix _ _ ↑⋆ δ)
    | |- context[?x[wk]                       ] => change x[wk] with x[@wkm Ix _ _]
    | |- context[⌈wk⌉                         ] => change ⌈wk⌉ with ⌈@wk⌉
    | |- context[wk (vr ?i)                   ] => change (wk (vr i)) with (vr (wk i))
    | |- context[@wk _ _ ?wkX (vr ?i)         ] => rewrite (@wk_vr _ _ wkX i)
    | |- context[@ap _ _ _ ?apXY (idm _) ?x   ] => rewrite (@ap_id _ _ _ apXY x)
    | |- context[@lift _ _ _ _ ?liftXY (vr ?i)] => rewrite (@lift_vr _ _ _ _ liftXY i)
    end.

