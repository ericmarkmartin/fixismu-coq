Require Import StlcFix.SpecSyntax.

#[export]
Hint Constructors PCtx : pctx.

(* Lemmas to solve program context equations via eauto. *)
Lemma eq_pctx_papp₁ c t c₁ t₂ :
  c = papp₁ c₁ t₂ → app (pctx_app t c₁) t₂ = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_papp₁ : pctx.

Lemma eq_pctx_papp₂ c t t₁ c₂ :
  c = papp₂ t₁ c₂ → app t₁ (pctx_app t c₂) = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_papp₂ : pctx.

(* Lemma eq_pctx_pite₁ c t c₁ t₂ t₃ : *)
(*   c = pite₁ c₁ t₂ t₃ → ite (pctx_app t c₁) t₂ t₃ = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_pite₁ : pctx. *)

(* Lemma eq_pctx_ppair₁ c t c₁ t₂ : *)
(*   c = ppair₁ c₁ t₂ → pair (pctx_app t c₁) t₂ = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_ppair₁ : pctx. *)

(* Lemma eq_pctx_ppair₂ c t t₁ c₂ : *)
(*   c = ppair₂ t₁ c₂ → pair t₁ (pctx_app t c₂) = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_ppair₂ : pctx. *)

(* Lemma eq_pctx_pproj₁ c t c₁ : *)
(*   c = pproj₁ c₁ → proj₁ (pctx_app t c₁) = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_pproj₁ : pctx. *)

(* Lemma eq_pctx_pproj₂ c t c₁ : *)
(*   c = pproj₂ c₁ → proj₂ (pctx_app t c₁) = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_pproj₂ : pctx. *)

Lemma eq_pctx_pinl c t c₁ :
  c = pinl c₁ → inl (pctx_app t c₁) = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_pinl : pctx.

Lemma eq_pctx_pinr c t c₁ :
  c = pinr c₁ → inr (pctx_app t c₁) = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_pinr : pctx.

Lemma eq_pctx_pcaseof₁ c t c₁ t₂ t₃ :
  c = pcaseof₁ c₁ t₂ t₃ → caseof (pctx_app t c₁) t₂ t₃ = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_pcaseof₁ : pctx.

(* Lemma eq_pctx_pseq₁ c t c₁ t₂ : *)
(*   c = pseq₁ c₁ t₂ → seq (pctx_app t c₁) t₂ = pctx_app t c. *)
(* Proof. intros; subst; reflexivity. Qed. *)
(* Hint Resolve eq_pctx_pseq₁ : pctx. *)

Lemma eq_pctx_pfixt c t τ₁ τ₂ c₁ :
  c = pfixt τ₁ τ₂ c₁ → fixt τ₁ τ₂ (pctx_app t c₁) = pctx_app t c.
Proof. intros; subst; reflexivity. Qed.
#[export]
Hint Resolve eq_pctx_pfixt : pctx.
