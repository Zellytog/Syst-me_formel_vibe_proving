(** * Jugements logiques : règles de déduction et dérivabilité

    On fixe un système de calcul [C] et une sorte de propositions [P].
    Une formule dans le contexte Γ est un terme de sorte [P] ; un jugement
    est [Γ | Ξ ⊢ φ], où Ξ est une liste de formules de Γ.

    Une règle de déduction est un schéma : un contexte de métavariables Θ,
    une liste de prémisses et une conclusion. Une prémisse peut étendre le
    contexte de termes (par Λ, pour les variables propres des
    quantificateurs) et les hypothèses. On l'instancie par un vecteur de Θ
    vers Γ, relevé sous Λ.

    La dérivabilité est engendrée par l'axiome, la conversion modulo [C] et
    les instances de règles. L'affaiblissement des hypothèses, la
    réindexation (substitution dans le contexte de termes, affaiblissement
    compris) et la coupure sont démontrés une fois pour toutes, pour toute
    famille de règles. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System.

(** ** Calculs auxiliaires sur les vecteurs *)

Section VecAux.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation tms := (Terms.tms Sym).
Local Notation vec := (Vectors.vec Sym).

(** Substituer par un vecteur relevé, après affaiblissement. *)
Lemma vsubst_wk Λ {Γ Δ s} (t : tm Γ s) (w : vec Γ Δ) :
  vsubst (ren_tm t (wk Λ)) (vup Λ w) = ren_tm (vsubst t w) (wk Λ).
Proof.
  unfold vsubst; rewrite subst_ren, ren_subst; apply subst_ext; intros σ y.
  unfold rs_comp, sr_comp, vget, wk, vup. rewrite aget_vcat_r. unfold vren; rewrite aget_vmap.
  reflexivity.
Qed.

Lemma vsubst_tms_wk Λ {Γ Δ σ} (u : tms Γ σ) (w : vec Γ Δ) :
  vsubst_tms (ren_tms u (wk Λ)) (vup Λ w) = ren_tms (vsubst_tms u w) (wk Λ).
Proof.
  unfold vsubst_tms; rewrite subst_tms_ren, ren_subst_tms; apply subst_tms_ext; intros ρ y.
  unfold rs_comp, sr_comp, vget, wk, vup. rewrite aget_vcat_r. unfold vren; rewrite aget_vmap.
  reflexivity.
Qed.

(** Relever puis composer, c'est composer puis relever. *)
Lemma vup_vcomp Λ {Θ Γ Δ} (v : vec Θ Γ) (w : vec Γ Δ) :
  vcomp (vup Λ v) (vup Λ w) = vup Λ (vcomp v w).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. unfold vup at 1 3.
  vcase x; rewrite ?aget_vcat_l, ?aget_vcat_r.
  - rewrite !aget_etas, vsubst_eta. unfold vup; rewrite aget_vcat_l, aget_etas; reflexivity.
  - unfold vren; rewrite !aget_vmap, aget_vcomp. apply vsubst_tms_wk.
Qed.

Lemma vup_nil {Θ Γ} (v : vec Θ Γ) : vup [] v = v.
Proof.
  apply vec_ext; intros σ x; unfold vget, vup, vren; cbn [vcat].
  rewrite aget_vmap. rewrite (ren_tms_ext _ _ rid); [apply ren_tms_id|reflexivity].
Qed.

Lemma ren_wk_nil {Γ s} (t : tm Γ s) : ren_tm t (wk []) = t.
Proof. rewrite (ren_ext t _ rid); [apply ren_id|reflexivity]. Qed.

(** Une variable sans argument, substituée, donne sa composante. *)
Lemma happ_nil {Ξ} b (u : tms Ξ (Spec [] b)) : happ (Spec [] b) u anil = u.
Proof. rewrite happ_vsubst; apply vsubst_vid. Qed.

Lemma vsubst_mv {Θ Γ b} (x : var Θ (Spec [] b)) (v : vec Θ Γ) :
  vsubst (@tvar _ Sym _ (Spec [] b) x anil) v = aget x v.
Proof. exact (happ_nil b (aget x v)). Qed.

Lemma vsubst_tsym {Θ Γ σ} (c : Sym σ) (a : Terms.args Sym Θ (dom σ)) (v : vec Θ Γ) :
  vsubst (tsym c a) v = tsym c (vsubst_args a v).
Proof. reflexivity. Qed.

Lemma vsubst_args_acons {Θ Γ σ L} (u : tms Θ σ) (a : Terms.args Sym Θ L) (v : vec Θ Γ) :
  vsubst_args (acons u a) v = acons (vsubst_tms u v) (vsubst_args a v).
Proof. reflexivity. Qed.

Lemma vsubst_args_anil {Θ Γ} (v : vec Θ Γ) : vsubst_args (@anil _ Sym Θ) v = anil.
Proof. reflexivity. Qed.

Lemma vsubst_tms_nil {Θ Γ} b (u : tms Θ (Spec [] b)) (v : vec Θ Γ) :
  vsubst_tms (σ := Spec [] b) u v = vsubst u v.
Proof. rewrite vsubst_tms_vup; cbn [dom]; rewrite vup_nil; reflexivity. Qed.

End VecAux.

#[export] Hint Rewrite @vsubst_tsym @vsubst_args_acons @vsubst_args_anil
  @vsubst_tms_nil @vsubst_mv : inst.

(** ** Règles de déduction *)

Section Rules.

Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).

Definition form (Γ : ctx Srt) : Type := Terms.tm Sym Γ P.

Record premise (Θ : ctx Srt) := {
  p_ext : ctx Srt;                       (* variables propres ajoutées *)
  p_hyps : list (form (p_ext ++ Θ));     (* hypothèses ajoutées *)
  p_goal : form (p_ext ++ Θ)             (* formule à dériver *)
}.

Record drule := {
  d_ctx : ctx Srt;                       (* métavariables *)
  d_prems : list (premise d_ctx);
  d_concl : form d_ctx
}.

(** Une prémisse sans extension du contexte de termes. *)
Definition prem {Θ} (hyps : list (form Θ)) (goal : form Θ) : premise Θ :=
  {| p_ext := []; p_hyps := hyps; p_goal := goal |}.

(** Une prémisse qui étend le contexte de termes par Λ. *)
Definition premx {Θ} (Λ : ctx Srt) (hyps : list (form (Λ ++ Θ))) (goal : form (Λ ++ Θ)) :
  premise Θ := {| p_ext := Λ; p_hyps := hyps; p_goal := goal |}.

End Rules.

Arguments form {Srt} Sym P Γ.
Arguments premise {Srt} Sym P Θ.
Arguments drule {Srt} Sym P.
Arguments p_ext {Srt Sym P Θ} p : rename.
Arguments p_hyps {Srt Sym P Θ} p : rename.
Arguments p_goal {Srt Sym P Θ} p : rename.
Arguments d_ctx {Srt Sym P} r : rename.
Arguments d_prems {Srt Sym P} r : rename.
Arguments d_concl {Srt Sym P} r : rename.
Arguments prem {Srt Sym P Θ} hyps goal.
Arguments premx {Srt Sym P Θ} Λ hyps goal.

(** ** Dérivabilité *)

Section Deriv.

Context {Srt : Type} {Sym : spec Srt -> Type} (C : system Sym) (P : Srt).
Context {I : Type} (R : I -> drule Sym P).
Implicit Types (Λ Θ Γ Δ D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation form := (form Sym P).
Local Notation vec := (Vectors.vec Sym).

Definition vsubst_list {Γ Δ} (L : list (form Γ)) (w : vec Γ Δ) : list (form Δ) :=
  map (fun χ => vsubst χ w) L.

Definition wk_list Λ {Γ} (L : list (form Γ)) : list (form (Λ ++ Γ)) :=
  map (fun χ => ren_tm χ (wk Λ)) L.

(** Instance d'une prémisse par un vecteur [v], sous les hypothèses Ξ. *)
Definition inst_goal {Θ} (p : premise Sym P Θ) {Γ} (v : vec Θ Γ) : form (p_ext p ++ Γ) :=
  vsubst (p_goal p) (vup (p_ext p) v).

Definition inst_hyps {Θ} (p : premise Sym P Θ) {Γ} (v : vec Θ Γ) (Ξ : list (form Γ)) :
  list (form (p_ext p ++ Γ)) :=
  vsubst_list (p_hyps p) (vup (p_ext p) v) ++ wk_list (p_ext p) Ξ.

Inductive deriv : forall Γ, list (form Γ) -> form Γ -> Prop :=
| d_ax Γ Ξ φ : In φ Ξ -> deriv Γ Ξ φ
| d_conv Γ Ξ φ ψ : conv C φ ψ -> deriv Γ Ξ φ -> deriv Γ Ξ ψ
| d_rule Γ Ξ (i : I) (v : vec (d_ctx (R i)) Γ) :
    (forall p, In p (d_prems (R i)) -> deriv _ (inst_hyps p v Ξ) (inst_goal p v)) ->
    deriv Γ Ξ (vsubst (d_concl (R i)) v).

(** Appliquer une règle donnée par une égalité [R i = r]. *)
Lemma d_rule_eq Γ Ξ (i : I) (r : drule Sym P) (v : vec (d_ctx r) Γ) :
  R i = r ->
  (forall p, In p (d_prems r) -> deriv _ (inst_hyps p v Ξ) (inst_goal p v)) ->
  deriv Γ Ξ (vsubst (d_concl r) v).
Proof. intros <-; apply d_rule. Qed.

(** *** Affaiblissement des hypothèses *)

Theorem deriv_weaken {Γ Ξ φ} : deriv Γ Ξ φ -> forall Ξ', incl Ξ Ξ' -> deriv Γ Ξ' φ.
Proof.
  induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH]; intros Ξ' Hinc.
  - apply d_ax, Hinc, Hin.
  - eapply d_conv; [exact Hc|apply IH, Hinc].
  - apply d_rule; intros p Hin. apply IH; [exact Hin|].
    unfold inst_hyps, wk_list. apply incl_app_app; [apply incl_refl|apply incl_map, Hinc].
Qed.

(** *** Réindexation : substitution dans le contexte de termes *)

Lemma vsubst_list_app {Γ Δ} (L L' : list (form Γ)) (w : vec Γ Δ) :
  vsubst_list (L ++ L') w = vsubst_list L w ++ vsubst_list L' w.
Proof. apply map_app. Qed.

Theorem deriv_subst {Γ Ξ φ} : deriv Γ Ξ φ ->
  forall Δ (w : vec Γ Δ), deriv Δ (vsubst_list Ξ w) (vsubst φ w).
Proof.
  induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH]; intros Δ w.
  - apply d_ax; unfold vsubst_list; exact (in_map (fun χ => vsubst χ w) _ _ Hin).
  - eapply d_conv; [apply conv_subst; [exact Hc|apply arel_refl]|apply IH].
  - rewrite vsubst_vsubst. apply d_rule; intros p Hin.
    specialize (IH p Hin _ (vup (p_ext p) w)).
    unfold inst_goal in *. rewrite vsubst_vsubst, vup_vcomp in IH.
    unfold inst_hyps in *. rewrite vsubst_list_app in IH.
    replace (vsubst_list (vsubst_list (p_hyps p) (vup (p_ext p) v)) (vup (p_ext p) w))
      with (vsubst_list (p_hyps p) (vup (p_ext p) (vcomp v w))) in IH.
    2:{ unfold vsubst_list; rewrite map_map; apply map_ext; intros χ.
        rewrite vsubst_vsubst, vup_vcomp; reflexivity. }
    replace (vsubst_list (wk_list (p_ext p) Ξ) (vup (p_ext p) w))
      with (wk_list (p_ext p) (vsubst_list Ξ w)) in IH.
    2:{ unfold vsubst_list, wk_list; rewrite !map_map; apply map_ext; intros χ.
        symmetry; apply vsubst_wk. }
    exact IH.
Qed.

(** Cas particulier : affaiblissement du contexte de termes. *)
Corollary deriv_wk Λ {Γ Ξ φ} : deriv Γ Ξ φ -> deriv (Λ ++ Γ) (wk_list Λ Ξ) (ren_tm φ (wk Λ)).
Proof.
  intros H. pose proof (deriv_subst H _ (vpre (wk Λ) (vid (Λ ++ Γ)))) as H'.
  rewrite <- ren_as_vsubst in H'.
  replace (wk_list Λ Ξ) with (vsubst_list Ξ (vpre (wk Λ) (vid (Λ ++ Γ)))); [exact H'|].
  unfold vsubst_list, wk_list; apply map_ext; intros χ; symmetry; apply ren_as_vsubst.
Qed.

(** *** Coupure *)

Theorem deriv_cut_gen {Γ Ξ' ψ} : deriv Γ Ξ' ψ ->
  forall Ξ, (forall χ, In χ Ξ' -> deriv Γ Ξ χ) -> deriv Γ Ξ ψ.
Proof.
  induction 1 as [Γ Ξ' φ Hin|Γ Ξ' φ ψ Hc H IH|Γ Ξ' i v Hp IH]; intros Ξ HΞ.
  - apply HΞ, Hin.
  - eapply d_conv; [exact Hc|apply IH, HΞ].
  - apply d_rule; intros p Hin. apply IH; [exact Hin|].
    intros χ Hχ. unfold inst_hyps in Hχ |- *. apply in_app_or in Hχ as [Hχ|Hχ].
    + apply d_ax, in_or_app; left; exact Hχ.
    + unfold wk_list in Hχ; apply in_map_iff in Hχ as [χ0 [<- H0]].
      apply (deriv_weaken (deriv_wk (p_ext p) (HΞ χ0 H0))).
      apply incl_appr, incl_refl.
Qed.

Theorem deriv_cut {Γ Ξ φ ψ} : deriv Γ Ξ φ -> deriv Γ (φ :: Ξ) ψ -> deriv Γ Ξ ψ.
Proof.
  intros Hφ Hψ. apply (deriv_cut_gen Hψ). intros χ [<-|Hχ]; [exact Hφ|apply d_ax, Hχ].
Qed.

End Deriv.

Arguments deriv {Srt Sym} C P {I} R Γ Ξ φ.
Arguments vsubst_list {Srt Sym P Γ Δ} L w.
Arguments wk_list {Srt Sym P} Λ {Γ} L.
Arguments inst_goal {Srt Sym P Θ} p {Γ} v.
Arguments inst_hyps {Srt Sym P Θ} p {Γ} v Ξ.

(** ** Simplification des instances de prémisses sans extension *)

Lemma wk_list_nil {Srt} {Sym : spec Srt -> Type} {P Γ} (L : list (form Sym P Γ)) :
  wk_list [] L = L.
Proof. unfold wk_list; rewrite (map_ext _ (fun χ => χ)); [apply map_id|intros; apply ren_wk_nil]. Qed.

Ltac inst_simpl :=
  unfold inst_hyps, inst_goal, vsubst_list; cbn [p_ext p_hyps p_goal d_ctx d_prems d_concl prem premx];
  rewrite ?vup_nil, ?wk_list_nil; cbn [map app];
  autorewrite with inst; cbn [aget ahd atl].

(** ** Systèmes logiques *)

Record logic {Srt : Type} (Sym : spec Srt -> Type) := {
  l_calc : system Sym;          (* le système de calcul sous-jacent *)
  l_prop : Srt;                 (* la sorte des propositions *)
  l_idx : Type;
  l_rules : l_idx -> drule Sym l_prop
}.

Definition provable {Srt} {Sym : spec Srt -> Type} (L : logic Sym) Γ Ξ φ :=
  deriv (l_calc Sym L) (l_prop Sym L) (l_rules Sym L) Γ Ξ φ.
