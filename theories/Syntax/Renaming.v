(** * Renommages : lemmes de base et calcul sur les variables *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.

Section Renaming.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).
Local Notation kit := (kit Sym).
Local Notation sub := (sub Sym).

(** ** Calcul des opérations sur les variables de [Λ ++ Γ] *)

Lemma upr_vl Λ {Γ Δ} (ρ : ren Γ Δ) {σ} (z : var Λ σ) : upr Λ ρ σ (vl Γ z) = vl Δ z.
Proof. unfold upr; rewrite vsplit_vl; reflexivity. Qed.

Lemma upr_vr Λ {Γ Δ} (ρ : ren Γ Δ) {σ} (y : var Γ σ) : upr Λ ρ σ (vr Λ y) = vr Λ (ρ σ y).
Proof. unfold upr; rewrite vsplit_vr; reflexivity. Qed.

Lemma kup_vl Λ {Γ Δ} (K : kit Γ Δ) {σ} (z : var Λ σ) : kup Λ K σ (vl Γ z) = inl (vl Δ z).
Proof. unfold kup; rewrite vsplit_vl; reflexivity. Qed.

Lemma kup_vr Λ {Γ Δ} (K : kit Γ Δ) {σ} (y : var Γ σ) : kup Λ K σ (vr Λ y) = eshift Λ (K σ y).
Proof. unfold kup; rewrite vsplit_vr; reflexivity. Qed.

Lemma inst_kit_vl Θ {Ξ} (a : args Ξ Θ) fs {σ} (z : var Θ σ) :
  inst_kit Θ a fs σ (vl Ξ z) = inr (aget z a, all_get z fs).
Proof. unfold inst_kit; rewrite vsplit_vl; reflexivity. Qed.

Lemma inst_kit_vr Θ {Ξ} (a : args Ξ Θ) fs {σ} (y : var Ξ σ) :
  inst_kit Θ a fs σ (vr Θ y) = inl y.
Proof. unfold inst_kit; rewrite vsplit_vr; reflexivity. Qed.

Lemma sapp_vl {Θ Γ Δ} (a : args Δ Θ) (τ : sub Γ Δ) {σ} (z : var Θ σ) :
  sapp a τ σ (vl Γ z) = aget z a.
Proof. unfold sapp; rewrite vsplit_vl; reflexivity. Qed.

Lemma sapp_vr {Θ Γ Δ} (a : args Δ Θ) (τ : sub Γ Δ) {σ} (y : var Γ σ) :
  sapp a τ σ (vr Θ y) = τ σ y.
Proof. unfold sapp; rewrite vsplit_vr; reflexivity. Qed.

End Renaming.

#[export] Hint Rewrite @upr_vl @upr_vr @kup_vl @kup_vr @inst_kit_vl @inst_kit_vr
  @sapp_vl @sapp_vr : vsimpl.

(** [vcase x] : distingue si [x : var (Λ ++ Γ) σ] est liée par [Λ] ou vient de [Γ]. *)
Ltac vcase x :=
  let T := type of x in
  let T' := eval cbn [dom cod] in T in
  change T' in x;
  match T' with
  | var (?Λ ++ _) _ =>
      let z := fresh "z" in let E := fresh "E" in
      destruct (vsplit_case Λ x) as [[z [-> E]]|[z [-> E]]]; clear E
  end.

(** Simplification des opérations sur les variables et des entrées de kit. *)
Ltac vsimp := repeat progress (autorewrite with vsimpl; cbn beta iota delta [eshift]).

Section RenLemmas.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).

Lemma upr_ext Λ {Γ Δ} (ρ ρ' : ren Γ Δ) :
  (forall σ x, ρ σ x = ρ' σ x) -> forall σ x, upr Λ ρ σ x = upr Λ ρ' σ x.
Proof. intros H σ x; vcase x; autorewrite with vsimpl; [reflexivity|now rewrite H]. Qed.

Lemma ren_ext_mut :
  (forall Γ s (t : tm Γ s) Δ (ρ ρ' : ren Γ Δ),
      (forall σ x, ρ σ x = ρ' σ x) -> ren_tm t ρ = ren_tm t ρ') /\
  (forall Γ Θ (a : args Γ Θ) Δ (ρ ρ' : ren Γ Δ),
      (forall σ x, ρ σ x = ρ' σ x) -> ren_args a ρ = ren_args a ρ').
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - rewrite H0; f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. apply H; apply upr_ext; assumption.
Qed.

Lemma ren_ext {Γ s} (t : tm Γ s) {Δ} (ρ ρ' : ren Γ Δ) :
  (forall σ x, ρ σ x = ρ' σ x) -> ren_tm t ρ = ren_tm t ρ'.
Proof. apply ren_ext_mut. Qed.

Lemma ren_args_ext {Γ Θ} (a : args Γ Θ) {Δ} (ρ ρ' : ren Γ Δ) :
  (forall σ x, ρ σ x = ρ' σ x) -> ren_args a ρ = ren_args a ρ'.
Proof. apply ren_ext_mut. Qed.

Lemma ren_tms_ext {Γ σ} (u : tms Γ σ) {Δ} (ρ ρ' : ren Γ Δ) :
  (forall σ x, ρ σ x = ρ' σ x) -> ren_tms u ρ = ren_tms u ρ'.
Proof. intros H; apply ren_ext, upr_ext, H. Qed.

Lemma upr_id Λ {Γ} σ (x : var (Λ ++ Γ) σ) : upr Λ (@rid _ Γ) σ x = x.
Proof. vcase x; autorewrite with vsimpl; reflexivity. Qed.

Lemma ren_id_mut :
  (forall Γ s (t : tm Γ s), ren_tm t rid = t) /\
  (forall Γ Θ (a : args Γ Θ), ren_args a rid = a).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. rewrite (ren_ext t _ rid); [assumption|apply upr_id].
Qed.

Lemma ren_id {Γ s} (t : tm Γ s) : ren_tm t rid = t.
Proof. apply ren_id_mut. Qed.

Lemma ren_args_id {Γ Θ} (a : args Γ Θ) : ren_args a rid = a.
Proof. apply ren_id_mut. Qed.

Lemma ren_tms_id {Γ σ} (u : tms Γ σ) : ren_tms u rid = u.
Proof. unfold ren_tms; rewrite (ren_ext u _ rid); [apply ren_id|apply upr_id]. Qed.

Lemma upr_comp Λ {Γ Δ Ξ} (ρ : ren Γ Δ) (ξ : ren Δ Ξ) σ (x : var (Λ ++ Γ) σ) :
  upr Λ ξ σ (upr Λ ρ σ x) = upr Λ (rcomp ρ ξ) σ x.
Proof. vcase x; autorewrite with vsimpl; reflexivity. Qed.

Lemma ren_ren_mut :
  (forall Γ s (t : tm Γ s) Δ Ξ (ρ : ren Γ Δ) (ξ : ren Δ Ξ),
      ren_tm (ren_tm t ρ) ξ = ren_tm t (rcomp ρ ξ)) /\
  (forall Γ Θ (a : args Γ Θ) Δ Ξ (ρ : ren Γ Δ) (ξ : ren Δ Ξ),
      ren_args (ren_args a ρ) ξ = ren_args a (rcomp ρ ξ)).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. rewrite H. apply ren_ext. intros; apply upr_comp.
Qed.

Lemma ren_ren {Γ s} (t : tm Γ s) {Δ Ξ} (ρ : ren Γ Δ) (ξ : ren Δ Ξ) :
  ren_tm (ren_tm t ρ) ξ = ren_tm t (rcomp ρ ξ).
Proof. apply ren_ren_mut. Qed.

Lemma ren_args_ren {Γ Θ} (a : args Γ Θ) {Δ Ξ} (ρ : ren Γ Δ) (ξ : ren Δ Ξ) :
  ren_args (ren_args a ρ) ξ = ren_args a (rcomp ρ ξ).
Proof. apply ren_ren_mut. Qed.

Lemma ren_tms_ren {Γ σ} (u : tms Γ σ) {Δ Ξ} (ρ : ren Γ Δ) (ξ : ren Δ Ξ) :
  ren_tms (ren_tms u ρ) ξ = ren_tms u (rcomp ρ ξ).
Proof. unfold ren_tms; rewrite ren_ren; apply ren_ext; intros; apply upr_comp. Qed.

Lemma aget_ren {Γ Θ σ} (z : var Θ σ) (a : args Γ Θ) {Δ} (ρ : ren Γ Δ) :
  aget z (ren_args a ρ) = ren_tms (aget z a) ρ.
Proof.
  revert a; induction z as [Θ0 σ0|Θ0 σ0 τ0 z IH]; intros a;
    rewrite (args_eta a); cbn; [reflexivity|apply IH].
Qed.

End RenLemmas.
