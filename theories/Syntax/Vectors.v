(** * Vecteurs : substitutions comme listes finies de termes

    Un vecteur de Γ vers Δ est une liste de termes [t1,...,tn] avec
    [Δ ⊢ ti : σi] pour Γ = [σ1,...,σn]. C'est exactement une liste
    d'arguments : [vec Γ Δ := args Δ Γ].

    Comme un vecteur est un objet fini, deux vecteurs dont toutes les
    composantes coïncident sont égaux ([args_ext]) : l'algèbre des
    substitutions s'énonce donc par de vraies égalités, *sans aucun axiome*.
    Les substitutions fonctionnelles [sub] restent un outil interne des
    preuves (on n'y énonce que des égalités point par point). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition.

Section Vectors.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).
Local Notation sub := (sub Sym).

(** ** Vecteurs de termes *)

Definition vec Γ Δ : Type := args Δ Γ.

(** La substitution (fonctionnelle) associée à un vecteur. *)
Definition vget {Γ Δ} (v : vec Γ Δ) : sub Γ Δ := fun σ x => aget x v.

Lemma vec_ext {Γ Δ} (v w : vec Γ Δ) : (forall σ x, vget v σ x = vget w σ x) -> v = w.
Proof. apply args_ext. Qed.

(** Image composante par composante. *)
Fixpoint vmap {Δ Ξ} (f : forall σ, tms Δ σ -> tms Ξ σ) Γ : args Δ Γ -> args Ξ Γ :=
  match Γ return args Δ Γ -> args Ξ Γ with
  | [] => fun _ => anil
  | σ :: Γ' => fun v => acons (f σ (ahd v)) (vmap f Γ' (atl v))
  end.

Lemma aget_vmap {Δ Ξ} (f : forall σ, tms Δ σ -> tms Ξ σ) {Γ σ} (x : var Γ σ) (v : args Δ Γ) :
  aget x (vmap f Γ v) = f σ (aget x v).
Proof. revert v; induction x; intros v; cbn; [reflexivity|apply IHx]. Qed.

(** Concaténation : le vecteur [a ++ v] de [Θ ++ Γ] vers [Ξ]. *)
Fixpoint vcat {Ξ} Θ {Γ} : args Ξ Θ -> args Ξ Γ -> args Ξ (Θ ++ Γ) :=
  match Θ return args Ξ Θ -> args Ξ Γ -> args Ξ (Θ ++ Γ) with
  | [] => fun _ b => b
  | σ :: Θ' => fun a b => acons (ahd a) (vcat Θ' (atl a) b)
  end.

Lemma aget_vcat_l {Ξ Θ Γ σ} (z : var Θ σ) (a : args Ξ Θ) (b : args Ξ Γ) :
  aget (vl Γ z) (vcat Θ a b) = aget z a.
Proof. revert a; induction z; intros a; cbn; [reflexivity|apply IHz]. Qed.

Lemma aget_vcat_r {Ξ} Θ {Γ σ} (y : var Γ σ) (a : args Ξ Θ) (b : args Ξ Γ) :
  aget (vr Θ y) (vcat Θ a b) = aget y b.
Proof. revert a; induction Θ as [|τ Θ IH]; intros a; cbn; [reflexivity|apply IH]. Qed.

(** Vecteur identité : chaque variable par son η-expansé. *)
Definition vid Γ : vec Γ Γ := etas (Sym:=Sym) Γ (fun ρ z => z).

Lemma aget_vid {Γ σ} (x : var Γ σ) : aget x (vid Γ) = eta σ x.
Proof. apply aget_etas. Qed.

(** ** Substitution par un vecteur *)

Definition vsubst {Γ s} (t : tm Γ s) {Δ} (v : vec Γ Δ) : tm Δ s := subst t (vget v).
Definition vsubst_args {Γ Θ} (a : args Γ Θ) {Δ} (v : vec Γ Δ) : args Δ Θ := subst_args a (vget v).
Definition vsubst_tms {Γ σ} (u : tms Γ σ) {Δ} (v : vec Γ Δ) : tms Δ σ := subst_tms u (vget v).

(** Composition des vecteurs (ordre diagrammatique) :
    [vcomp v w] substitue d'abord par [v], puis par [w]. *)
Definition vcomp {Γ Δ Ξ} (v : vec Γ Δ) (w : vec Δ Ξ) : vec Γ Ξ :=
  vmap (fun σ u => vsubst_tms u w) Γ v.

(** Renommage de toutes les composantes. *)
Definition vren {Γ Δ Ξ} (v : vec Γ Δ) (ξ : ren Δ Ξ) : vec Γ Ξ :=
  vmap (fun σ u => ren_tms u ξ) Γ v.

(** Relèvement sous les lieurs [Λ]. *)
Definition vup Λ {Γ Δ} (v : vec Γ Δ) : vec (Λ ++ Γ) (Λ ++ Δ) :=
  vcat Λ (etas (Sym:=Sym) Λ (fun ρ z => vl Δ z)) (vren v (wk Λ)).

(** ** Extensionnalité point par point des substitutions fonctionnelles *)

Lemma subst_ext {Γ s} (t : tm Γ s) {Δ} (τ τ' : sub Γ Δ) :
  (forall σ x, τ σ x = τ' σ x) -> subst t τ = subst t τ'.
Proof. intros H; apply trav_ext; intros σ x; unfold sub_kit; now rewrite H. Qed.

Lemma subst_args_ext {Γ Θ} (a : args Γ Θ) {Δ} (τ τ' : sub Γ Δ) :
  (forall σ x, τ σ x = τ' σ x) -> subst_args a τ = subst_args a τ'.
Proof. intros H; apply trav_args_ext; intros σ x; unfold sub_kit; now rewrite H. Qed.

Lemma subst_tms_ext {Γ σ} (u : tms Γ σ) {Δ} (τ τ' : sub Γ Δ) :
  (forall σ x, τ σ x = τ' σ x) -> subst_tms u τ = subst_tms u τ'.
Proof.
  intros H; apply trav_ext, kup_ext; intros σ' x; unfold sub_kit; now rewrite H.
Qed.

Lemma aget_subst_args {Γ Θ σ} (z : var Θ σ) (a : args Γ Θ) {Δ} (τ : sub Γ Δ) :
  aget z (subst_args a τ) = subst_tms (aget z a) τ.
Proof. apply aget_trav. Qed.

(** ** Algèbre des vecteurs : de vraies égalités, sans axiome *)

Lemma vsubst_vid {Γ s} (t : tm Γ s) : vsubst t (vid Γ) = t.
Proof.
  unfold vsubst; rewrite (subst_ext t _ ids); [apply subst_id|].
  intros σ x; apply aget_vid.
Qed.

Lemma vsubst_args_vid {Γ Θ} (a : args Γ Θ) : vsubst_args a (vid Γ) = a.
Proof.
  unfold vsubst_args; rewrite (subst_args_ext a _ ids); [apply subst_args_id|].
  intros σ x; apply aget_vid.
Qed.

Lemma vsubst_tms_vid {Γ σ} (u : tms Γ σ) : vsubst_tms u (vid Γ) = u.
Proof.
  unfold vsubst_tms; rewrite (subst_tms_ext u _ ids); [apply subst_tms_id|].
  intros σ' x; apply aget_vid.
Qed.

Lemma vsubst_vsubst {Γ s} (t : tm Γ s) {Δ Ξ} (v : vec Γ Δ) (w : vec Δ Ξ) :
  vsubst (vsubst t v) w = vsubst t (vcomp v w).
Proof.
  unfold vsubst; rewrite subst_subst; apply subst_ext; intros σ x.
  unfold vget, vcomp; rewrite aget_vmap; reflexivity.
Qed.

Lemma vsubst_args_vsubst {Γ Θ} (a : args Γ Θ) {Δ Ξ} (v : vec Γ Δ) (w : vec Δ Ξ) :
  vsubst_args (vsubst_args a v) w = vsubst_args a (vcomp v w).
Proof.
  unfold vsubst_args; rewrite subst_args_subst; apply subst_args_ext; intros σ x.
  unfold vget, vcomp; rewrite aget_vmap; reflexivity.
Qed.

Lemma vsubst_tms_vsubst {Γ σ} (u : tms Γ σ) {Δ Ξ} (v : vec Γ Δ) (w : vec Δ Ξ) :
  vsubst_tms (vsubst_tms u v) w = vsubst_tms u (vcomp v w).
Proof.
  unfold vsubst_tms; rewrite subst_tms_subst; apply subst_tms_ext; intros σ' x.
  unfold vget, vcomp; rewrite aget_vmap; reflexivity.
Qed.

Lemma aget_vcomp {Γ Δ Ξ σ} (x : var Γ σ) (v : vec Γ Δ) (w : vec Δ Ξ) :
  aget x (vcomp v w) = vsubst_tms (aget x v) w.
Proof. unfold vcomp; rewrite aget_vmap; reflexivity. Qed.

Lemma vcomp_vid_l {Γ Δ} (w : vec Γ Δ) : vcomp (vid Γ) w = w.
Proof.
  apply vec_ext; intros σ x; unfold vget.
  rewrite aget_vcomp, aget_vid; exact (eta_subst x (vget w)).
Qed.

Lemma vcomp_vid_r {Γ Δ} (v : vec Γ Δ) : vcomp v (vid Δ) = v.
Proof.
  apply vec_ext; intros σ x; unfold vget.
  rewrite aget_vcomp; apply vsubst_tms_vid.
Qed.

Lemma vcomp_assoc {Γ Δ Ξ Ω} (u : vec Γ Δ) (v : vec Δ Ξ) (w : vec Ξ Ω) :
  vcomp (vcomp u v) w = vcomp u (vcomp v w).
Proof.
  apply vec_ext; intros σ x; unfold vget.
  rewrite !aget_vcomp; apply vsubst_tms_vsubst.
Qed.

(** Composer une concaténation. *)
Lemma vcomp_vcat Θ {Γ Δ Ξ} (a : args Δ Θ) (v : vec Γ Δ) (w : vec Δ Ξ) :
  vcomp (vcat Θ a v) w = vcat Θ (vsubst_args a w) (vcomp v w).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp.
  vcase x; rewrite ?aget_vcat_l, ?aget_vcat_r.
  - unfold vsubst_args; rewrite aget_subst_args; reflexivity.
  - rewrite aget_vcomp; reflexivity.
Qed.

(** ** Application héréditaire et vecteurs *)

(** La β-réduction héréditaire est la substitution par [a ++ id]. *)
Lemma happ_vsubst σ {Ξ} (u : tms Ξ σ) (a : args Ξ (dom σ)) :
  happ σ u a = vsubst u (vcat (dom σ) a (vid Ξ)).
Proof.
  rewrite happ_subst; unfold vsubst; apply subst_ext; intros σ' x; unfold vget.
  vcase x; autorewrite with vsimpl; rewrite ?aget_vcat_l, ?aget_vcat_r; [reflexivity|].
  rewrite aget_vid; reflexivity.
Qed.

Lemma vsubst_happ σ {Ξ Ξ'} (u : tms Ξ σ) (a : args Ξ (dom σ)) (w : vec Ξ Ξ') :
  vsubst (happ σ u a) w = happ σ (vsubst_tms u w) (vsubst_args a w).
Proof. apply subst_happ. Qed.

Lemma vsubst_eta {Γ Δ σ} (x : var Γ σ) (v : vec Γ Δ) : vsubst_tms (eta σ x) v = aget x v.
Proof. exact (eta_subst x (vget v)). Qed.

(** Substitution d'un argument : relèvement sous ses lieurs. *)
Lemma vsubst_tms_vup {Γ σ} (u : tms Γ σ) {Δ} (v : vec Γ Δ) :
  vsubst_tms u v = vsubst u (vup (dom σ) v).
Proof.
  unfold vsubst_tms, vsubst; rewrite subst_tms_up; apply subst_ext; intros σ' x.
  unfold vget, up_sub, vup, vren, sr_comp.
  vcase x; autorewrite with vsimpl; rewrite ?aget_vcat_l, ?aget_vcat_r; [reflexivity|].
  rewrite aget_vmap; reflexivity.
Qed.

(** ** Interactions avec les renommages *)

Lemma ren_vsubst {Γ s} (t : tm Γ s) {Δ Ξ} (v : vec Γ Δ) (ξ : ren Δ Ξ) :
  ren_tm (vsubst t v) ξ = vsubst t (vren v ξ).
Proof.
  unfold vsubst; rewrite ren_subst; apply subst_ext; intros σ x.
  unfold vget, vren, sr_comp; rewrite aget_vmap; reflexivity.
Qed.

Lemma ren_vsubst_tms {Γ σ} (u : tms Γ σ) {Δ Ξ} (v : vec Γ Δ) (ξ : ren Δ Ξ) :
  ren_tms (vsubst_tms u v) ξ = vsubst_tms u (vren v ξ).
Proof.
  unfold vsubst_tms; rewrite ren_subst_tms; apply subst_tms_ext; intros σ' x.
  unfold vget, vren, sr_comp; rewrite aget_vmap; reflexivity.
Qed.

(** Un renommage, puis un vecteur : on réindexe le vecteur. *)
Fixpoint vpre {Δ Ξ} Γ (ρ : ren Γ Δ) (w : vec Δ Ξ) : vec Γ Ξ :=
  match Γ return ren Γ Δ -> vec Γ Ξ with
  | [] => fun _ => anil
  | σ :: Γ' => fun r => acons (aget (r σ vz) w) (vpre Γ' (fun σ' y => r σ' (vs y)) w)
  end ρ.

Lemma aget_vpre {Δ Ξ Γ σ} (x : var Γ σ) (ρ : ren Γ Δ) (w : vec Δ Ξ) :
  aget x (vpre Γ ρ w) = aget (ρ σ x) w.
Proof. revert ρ; induction x; intros ρ; cbn; [reflexivity|apply (IHx (fun σ' y => ρ σ' (vs y)))]. Qed.

Lemma vsubst_ren {Γ s} (t : tm Γ s) {Δ Ξ} (ρ : ren Γ Δ) (w : vec Δ Ξ) :
  vsubst (ren_tm t ρ) w = vsubst t (vpre Γ ρ w).
Proof.
  unfold vsubst; rewrite subst_ren; apply subst_ext; intros σ x.
  unfold vget, rs_comp; rewrite aget_vpre; reflexivity.
Qed.

(** Un renommage est la substitution par un vecteur de variables η-expansées. *)
Lemma ren_as_vsubst {Γ s} (t : tm Γ s) {Δ} (ρ : ren Γ Δ) :
  ren_tm t ρ = vsubst t (vpre Γ ρ (vid Δ)).
Proof.
  rewrite ren_as_subst; unfold vsubst; apply subst_ext; intros σ x.
  unfold vget, rs_comp, ids; rewrite aget_vpre, aget_vid; reflexivity.
Qed.

Lemma vren_vcomp {Γ Δ Ξ Ω} (v : vec Γ Δ) (w : vec Δ Ξ) (ξ : ren Ξ Ω) :
  vren (vcomp v w) ξ = vcomp v (vren w ξ).
Proof.
  apply vec_ext; intros σ x; unfold vget, vren.
  rewrite aget_vmap, !aget_vcomp; apply ren_vsubst_tms.
Qed.

Lemma vren_id {Γ Δ} (v : vec Γ Δ) : vren v rid = v.
Proof. apply vec_ext; intros σ x; unfold vget, vren; rewrite aget_vmap; apply ren_tms_id. Qed.

Lemma vren_vren {Γ Δ Ξ Ω} (v : vec Γ Δ) (ξ : ren Δ Ξ) (ζ : ren Ξ Ω) :
  vren (vren v ξ) ζ = vren v (rcomp ξ ζ).
Proof.
  apply vec_ext; intros σ x; unfold vget, vren; rewrite !aget_vmap; apply ren_tms_ren.
Qed.

End Vectors.

Arguments vec {Srt} Sym Γ Δ.
Arguments vmap {Srt Sym Δ Ξ} f {Γ} v.
Arguments vcat {Srt Sym Ξ} Θ {Γ} a b.
Arguments vid {Srt Sym} Γ.
Arguments vpre {Srt Sym Δ Ξ} {Γ} ρ w.

(** ** La tactique [asimpl], sans extensionnalité fonctionnelle *)

#[export] Hint Rewrite
  @ren_ren @ren_args_ren @ren_tms_ren @ren_id @ren_args_id @ren_tms_id
  @vsubst_vsubst @vsubst_args_vsubst @vsubst_tms_vsubst
  @vsubst_vid @vsubst_args_vid @vsubst_tms_vid
  @vcomp_vid_l @vcomp_vid_r @vcomp_assoc @vcomp_vcat
  @vsubst_happ @happ_eta @vsubst_eta
  @ren_vsubst @ren_vsubst_tms @vsubst_ren
  @vren_vcomp @vren_id @vren_vren
  @aget_vmap @aget_vcat_l @aget_vcat_r @aget_vid @aget_vcomp @aget_vpre
  : vsigma.

Ltac asimpl := autorewrite with vsigma vsimpl; try reflexivity.

Tactic Notation "asimpl" "in" hyp(H) := autorewrite with vsigma vsimpl in H.
