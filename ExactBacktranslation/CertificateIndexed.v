Require Export RecTypes.SpecTypes.
Require Export RecTypes.Contraction.

From Coq Require Import Lists.List Program.Equality.
Import ListNotations.

Definition PairEnv := list (Ty * Ty).

(** Right unfolding is used only after the left endpoint has reached a
    non-recursive head. This makes proof search deterministic when both sides
    are recursive; left unfolding is chosen first. *)
Inductive NotMu : Ty -> Type :=
| not_mu_unit : NotMu tunit
| not_mu_bool : NotMu tbool
| not_mu_var x : NotMu (tvar x)
| not_mu_arr A B : NotMu (tarr A B)
| not_mu_prod A B : NotMu (tprod A B)
| not_mu_sum A B : NotMu (tsum A B).

(** Computational membership, retaining the endpoint indices. *)
Inductive Assumed : PairEnv -> Ty -> Ty -> Type :=
| assumed_here {H A B} : Assumed ((A, B) :: H) A B
| assumed_there {H A B C D} :
    Assumed H A B -> Assumed ((C, D) :: H) A B.

Definition assumed_nil_absurd {A B} (m : Assumed nil A B) : False :=
  match m with end.

(** A certificate is a finite cyclic derivation. Every proper equality rule
    extends the environment with its own conclusion; [ce_back] can therefore
    close a branch by pointing to an ancestor pair. *)
Inductive CastEq : PairEnv -> Ty -> Ty -> Type :=
| ce_back {H A B} : Assumed H A B -> CastEq H A B
| ce_step {H A B} : CastNode H A B -> CastEq H A B
with CastNode : PairEnv -> Ty -> Ty -> Type :=
| cn_unit H : CastNode H tunit tunit
| cn_bool H : CastNode H tbool tbool
| cn_var H x : CastNode H (tvar x) (tvar x)
| cn_arr H A1 A2 B1 B2 :
    CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1 ->
    CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2 ->
    CastNode H (tarr A1 A2) (tarr B1 B2)
| cn_prod H A1 A2 B1 B2 :
    CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1 ->
    CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2 ->
    CastNode H (tprod A1 A2) (tprod B1 B2)
| cn_sum H A1 A2 B1 B2 :
    CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1 ->
    CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2 ->
    CastNode H (tsum A1 A2) (tsum B1 B2)
| cn_mu_l H body B :
    CastEq ((trec body, B) :: H) body[beta1 (trec body)] B ->
    CastNode H (trec body) B
| cn_mu_r H A body :
    NotMu A ->
    CastEq ((A, trec body) :: H) A body[beta1 (trec body)] ->
    CastNode H A (trec body).

Scheme CastEq_rect_mut := Induction for CastEq Sort Type
with CastNode_rect_mut := Induction for CastNode Sort Type.

Definition ClosedCastEq (A B : Ty) := CastEq nil A B.

Inductive CastEqView {H A B} : CastEq H A B -> Type :=
| casteq_view_back (m : Assumed H A B) : CastEqView (ce_back m)
| casteq_view_step (node : CastNode H A B) : CastEqView (ce_step node).

Definition casteq_view {H A B} (d : CastEq H A B) : CastEqView d :=
  match d as d0 return CastEqView d0 with
  | ce_back m => casteq_view_back m
  | ce_step node => casteq_view_step node
  end.

(** Frames give operational meaning to assumptions: the head assumption is
    backed by the node that introduced it. *)
Inductive Frames : PairEnv -> Type :=
| frames_nil : Frames nil
| frames_cons {H A B} : CastNode H A B -> Frames H ->
    Frames ((A, B) :: H).

Inductive NodeFocus (A B : Ty) : Type :=
| node_focus {H} : CastNode H A B -> Frames H -> NodeFocus A B.

Inductive Focus (A B : Ty) : Type :=
| focus {H} : CastEq H A B -> Frames H -> Focus A B.

Arguments frames_cons {H A B} _ _.
Arguments node_focus {A B H} _ _.
Arguments focus {A B H} _ _.

(** Index-computed destructors keep frame lookup computational and preserve
    the definitional equality between a backreference and its ancestor
    frame. *)
Definition FrameHeadType (H : PairEnv) : Type :=
  match H with
  | nil => Datatypes.unit
  | (A, B) :: tail => CastNode tail A B
  end.

Definition FrameTailType (H : PairEnv) : Type :=
  match H with
  | nil => Datatypes.unit
  | _ :: tail => Frames tail
  end.

Definition frames_head_any {H} (fs : Frames H) : FrameHeadType H :=
  match fs with
  | frames_nil => tt
  | frames_cons node _ => node
  end.

Definition frames_tail_any {H} (fs : Frames H) : FrameTailType H :=
  match fs with
  | frames_nil => tt
  | frames_cons _ tail => tail
  end.

Fixpoint lookup_frame {H A B}
  (m : Assumed H A B) : Frames H -> NodeFocus A B :=
  match m in Assumed H0 A0 B0
        return Frames H0 -> NodeFocus A0 B0 with
  | @assumed_here H0 A0 B0 => fun fs =>
      node_focus (frames_head_any fs) (frames_tail_any fs)
  | @assumed_there H0 A0 B0 C D m' => fun fs =>
      lookup_frame m' (frames_tail_any fs)
  end.

Definition expose {A B} (f : Focus A B) : NodeFocus A B :=
  match f with
  | @focus _ _ H d fs =>
      match d in CastEq H0 A0 B0
            return Frames H0 -> NodeFocus A0 B0 with
      | ce_back m => fun fs0 => lookup_frame m fs0
      | ce_step node => fun fs0 => node_focus node fs0
      end fs
  end.

(** One observable layer of equality, parameterized by recursive states. *)
Inductive EqView (R : Ty -> Ty -> Type) : Ty -> Ty -> Type :=
| ev_unit : EqView R tunit tunit
| ev_bool : EqView R tbool tbool
| ev_var x : EqView R (tvar x) (tvar x)
| ev_arr A1 A2 B1 B2 :
    R A1 B1 -> R A2 B2 -> EqView R (tarr A1 A2) (tarr B1 B2)
| ev_prod A1 A2 B1 B2 :
    R A1 B1 -> R A2 B2 -> EqView R (tprod A1 A2) (tprod B1 B2)
| ev_sum A1 A2 B1 B2 :
    R A1 B1 -> R A2 B2 -> EqView R (tsum A1 A2) (tsum B1 B2)
| ev_mu_l body B :
    R body[beta1 (trec body)] B -> EqView R (trec body) B
| ev_mu_r A body :
    R A body[beta1 (trec body)] -> EqView R A (trec body).

Definition observe_node {A B} (nf : NodeFocus A B) : EqView Focus A B.
Proof.
  dependent destruction nf. pose (whole := c). dependent destruction c.
  - exact (ev_unit Focus).
  - exact (ev_bool Focus).
  - exact (ev_var Focus x).
  - eapply ev_arr.
    + exact (focus c (frames_cons whole f)).
    + exact (focus c0 (frames_cons whole f)).
  - eapply ev_prod.
    + exact (focus c (frames_cons whole f)).
    + exact (focus c0 (frames_cons whole f)).
  - eapply ev_sum.
    + exact (focus c (frames_cons whole f)).
    + exact (focus c0 (frames_cons whole f)).
  - eapply ev_mu_l. exact (focus c (frames_cons whole f)).
  - eapply ev_mu_r. exact (focus c (frames_cons whole f)).
Defined.

Definition observe {A B} (f : Focus A B) : EqView Focus A B :=
  observe_node (expose f).

CoFixpoint focus_sound {A B} (f : Focus A B) : Tyeq A B :=
  match observe f with
  | ev_unit _ => EqPrim
  | ev_bool _ => EqBool
  | ev_var _ x => EqVar
  | ev_arr _ _ _ _ _ l r => EqArr (focus_sound l) (focus_sound r)
  | ev_prod _ _ _ _ _ l r => EqProd (focus_sound l) (focus_sound r)
  | ev_sum _ _ _ _ _ l r => EqSum (focus_sound l) (focus_sound r)
  | ev_mu_l _ _ _ child => EqMuL (focus_sound child)
  | ev_mu_r _ _ _ child => EqMuR (focus_sound child)
  end.

Theorem casteq_sound {A B} : ClosedCastEq A B -> Tyeq A B.
Proof.
  intros d. exact (focus_sound (focus d frames_nil)).
Qed.

Definition ty_eq_dec (A B : Ty) : {A = B} + {A <> B}.
Proof. decide equality; apply PeanoNat.Nat.eq_dec. Defined.

Fixpoint assumed_find (H : PairEnv) (A B : Ty) {struct H} :
  option (Assumed H A B).
Proof.
  destruct H as [|[C D] H].
  - exact None.
  - destruct (ty_eq_dec A C) as [->|HAC].
    + destruct (ty_eq_dec B D) as [->|HBD].
      * exact (Some assumed_here).
      * destruct (assumed_find H C B) as [m|].
        -- exact (Some (assumed_there m)).
        -- exact None.
    + destruct (assumed_find H A B) as [m|].
      * exact (Some (assumed_there m)).
      * exact None.
Defined.

Definition option_map2 {X Y Z : Type} (f : X -> Y -> Z)
  (x : option X) (y : option Y) : option Z :=
  match x, y with
  | Some x', Some y' => Some (f x' y')
  | _, _ => None
  end.

Definition not_mu_dec (A : Ty) : option (NotMu A) :=
  match A as A0 return option (NotMu A0) with
  | tunit => Some not_mu_unit
  | tbool => Some not_mu_bool
  | tvar x => Some (not_mu_var x)
  | tarr X Y => Some (not_mu_arr X Y)
  | tprod X Y => Some (not_mu_prod X Y)
  | tsum X Y => Some (not_mu_sum X Y)
  | trec _ => None
  end.

(** Executable depth-bounded proof search. Backreferences are checked before
    consuming fuel, so closing a discovered cycle is immediate. *)
Fixpoint search_casteq_bounded (fuel : nat) (H : PairEnv) (A B : Ty) {struct fuel} :
  option (CastEq H A B) :=
  match assumed_find H A B with
  | Some back => Some (ce_back back)
  | None =>
      match fuel with
      | 0 => None
      | S fuel' =>
          match A as A0, B as B0 return option (CastEq H A0 B0) with
          | tunit, tunit => Some (ce_step (cn_unit H))
          | tbool, tbool => Some (ce_step (cn_bool H))
          | tvar x, tvar y =>
              match PeanoNat.Nat.eq_dec x y with
              | left e =>
                  match e in _ = y0 return option (CastEq H (tvar x) (tvar y0)) with
                  | eq_refl => Some (ce_step (cn_var H x))
                  end
              | right _ => None
              end
          | tarr A1 A2, tarr B1 B2 =>
              option_map2
                (fun l r => ce_step (cn_arr H A1 A2 B1 B2 l r))
                (search_casteq_bounded fuel'
                   ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
                (search_casteq_bounded fuel'
                   ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
          | tprod A1 A2, tprod B1 B2 =>
              option_map2
                (fun l r => ce_step (cn_prod H A1 A2 B1 B2 l r))
                (search_casteq_bounded fuel'
                   ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
                (search_casteq_bounded fuel'
                   ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
          | tsum A1 A2, tsum B1 B2 =>
              option_map2
                (fun l r => ce_step (cn_sum H A1 A2 B1 B2 l r))
                (search_casteq_bounded fuel'
                   ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
                (search_casteq_bounded fuel'
                   ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
          | trec body, B0 =>
              match search_casteq_bounded fuel' ((trec body, B0) :: H)
                      body[beta1 (trec body)] B0 with
              | Some child => Some (ce_step (cn_mu_l H body B0 child))
              | None => None
              end
          | A0, trec body =>
              match not_mu_dec A0 with
              | Some nm =>
                  match search_casteq_bounded fuel' ((A0, trec body) :: H)
                          A0 body[beta1 (trec body)] with
                  | Some child =>
                      Some (ce_step (cn_mu_r H A0 body nm child))
                  | None => None
                  end
              | None => None
              end
          | _, _ => None
          end
      end
  end.

Definition search_closed_bounded (fuel : nat) (A B : Ty) :
  option (ClosedCastEq A B) := search_casteq_bounded fuel nil A B.

Theorem search_closed_bounded_sound fuel A B d :
  search_closed_bounded fuel A B = Some d -> Tyeq A B.
Proof. intros _. now apply casteq_sound. Qed.
