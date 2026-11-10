(** * Extensions par définition : correction de la traduction

    On fixe une logique L = (C, R) sur [Sym], qui contient ∧, ⊤ et, à la
    sorte b, ∃ et l'égalité de Leibniz, ainsi qu'une couche fonctionnelle
    (lambda, app). La traduction [tr] de [Definitional.v] élimine le
    symbole f. Ce fichier établit les propriétés logiques de la traduction :
    - la congruence vis-à-vis des continuations ([tr_cong]) ;
    - le remplacement des formules équivalentes dans une formule de L
      ([repl]) ;
    - l'ouverture : sous la totalité, on peut nommer la valeur d'un terme
      appliqué à une pile ([open_mut]) ;
    - la stabilité par substitution ([hoistA_mut], [hoistF_mut]), qui est
      le cœur de la preuve ;
    - le respect de β, de η et des règles de calcul de L, par réécriture en
      contexte ([cconv_eqv]).

    Les équivalences sont au niveau objet : [equiv Ξ A B] signifie que
    A, Ξ ⊢ B et B, Ξ ⊢ A. *)

From Stdlib Require Import List Eqdep_dec.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant.
From SF.Extensions Require Import Definitional.

Local Notation ι a := (Spec [] a).

(** ** Équivalences et renommage des dérivations *)

Section Equiv.
Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).
Context (C : system Sym) {I : Type} (R : I -> drule Sym P).

Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ ψ" := (deriv C P R _ Ξ ψ) (at level 70).

Definition ren_list {Γ Δ} (Ξ : list (form Γ)) (ρ : ren Γ Δ) : list (form Δ) :=
  map (fun χ => ren_tm χ ρ) Ξ.

Definition equiv {Γ} (Ξ : list (form Γ)) (A B : form Γ) : Prop := (A :: Ξ) ⊢ B /\ (B :: Ξ) ⊢ A.

Lemma deriv_ren {Γ Ξ ψ} Δ (ρ : ren Γ Δ) : Ξ ⊢ ψ -> ren_list Ξ ρ ⊢ ren_tm ψ ρ.
Proof.
  intros Hd. rewrite ren_as_vsubst.
  replace (ren_list Ξ ρ) with (vsubst_list Ξ (vpre ρ (vid Δ))).
  - apply deriv_subst, Hd.
  - unfold vsubst_list, ren_list; apply map_ext; intros; symmetry; apply ren_as_vsubst.
Qed.

Lemma deriv_rw {Γ} (Ξ : list (form Γ)) ψ ψ' : ψ = ψ' -> Ξ ⊢ ψ -> Ξ ⊢ ψ'.
Proof. intros <-; exact (fun H => H). Qed.

Lemma deriv_rwh {Γ} (Ξ Ξ' : list (form Γ)) ψ : Ξ = Ξ' -> Ξ ⊢ ψ -> Ξ' ⊢ ψ.
Proof. intros <-; exact (fun H => H). Qed.

Lemma deriv_cut' {Γ} (Ξ : list (form Γ)) A B : Ξ ⊢ A -> (A :: Ξ) ⊢ B -> Ξ ⊢ B.
Proof. apply deriv_cut. Qed.

Lemma deriv_mono {Γ} (Ξ Ξ' : list (form Γ)) ψ : Ξ ⊢ ψ -> incl Ξ Ξ' -> Ξ' ⊢ ψ.
Proof. intros Hd Hi; exact (deriv_weaken C P R Hd Ξ' Hi). Qed.

(** Remplacer l'hypothèse de tête par une hypothèse plus forte. *)
Lemma deriv_head {Γ} (Ξ : list (form Γ)) A A' B : (A' :: Ξ) ⊢ A -> (A :: Ξ) ⊢ B -> (A' :: Ξ) ⊢ B.
Proof.
  intros H1 H2. apply (deriv_cut' _ A); [exact H1|].
  eapply deriv_mono; [exact H2|]. intros χ [<-|Hχ]; [left; reflexivity|right; right; exact Hχ].
Qed.

Lemma equiv_refl {Γ} (Ξ : list (form Γ)) A : equiv Ξ A A.
Proof. split; apply d_ax; left; reflexivity. Qed.

Lemma equiv_sym {Γ} (Ξ : list (form Γ)) A B : equiv Ξ A B -> equiv Ξ B A.
Proof. intros [H1 H2]; split; assumption. Qed.

Lemma imp_trans {Γ} (Ξ : list (form Γ)) A B D : (A :: Ξ) ⊢ B -> (B :: Ξ) ⊢ D -> (A :: Ξ) ⊢ D.
Proof.
  intros H1 H2. apply (deriv_cut' _ B); [exact H1|].
  eapply deriv_mono; [exact H2|]. intros χ [<-|Hχ]; [left; reflexivity|right; right; exact Hχ].
Qed.

Lemma equiv_trans {Γ} (Ξ : list (form Γ)) A B D : equiv Ξ A B -> equiv Ξ B D -> equiv Ξ A D.
Proof. intros [H1 H2] [H3 H4]; split; eapply imp_trans; eassumption. Qed.

Lemma equiv_mp {Γ} (Ξ : list (form Γ)) A B : equiv Ξ A B -> Ξ ⊢ A -> Ξ ⊢ B.
Proof. intros [H _] HA; exact (deriv_cut' _ _ _ HA H). Qed.

Lemma equiv_mono {Γ} (Ξ Ξ' : list (form Γ)) A B : equiv Ξ A B -> incl Ξ Ξ' -> equiv Ξ' A B.
Proof.
  intros [H1 H2] Hi; split; (eapply deriv_mono; [eassumption|]); apply incl_cons;
    [left; reflexivity| |left; reflexivity|]; intros χ Hχ; right; apply Hi, Hχ.
Qed.

Lemma incl_ren_list {Γ Δ} (Ξ Ξ' : list (form Γ)) (ρ : ren Γ Δ) : incl Ξ Ξ' -> incl (ren_list Ξ ρ) (ren_list Ξ' ρ).
Proof. intros Hi; apply incl_map, Hi. Qed.

Lemma ren_list_ren {Γ Δ Ω} (Ξ : list (form Γ)) (ρ : ren Γ Δ) (ξ : ren Δ Ω) :
  ren_list (ren_list Ξ ρ) ξ = ren_list Ξ (rcomp ρ ξ).
Proof. unfold ren_list; rewrite map_map; apply map_ext; intros; apply ren_ren. Qed.

Lemma ren_list_ext {Γ Δ} (Ξ : list (form Γ)) (ρ ρ' : ren Γ Δ) :
  (forall σ x, ρ σ x = ρ' σ x) -> ren_list Ξ ρ = ren_list Ξ ρ'.
Proof. intros He; unfold ren_list; apply map_ext; intros; apply ren_ext, He. Qed.

Lemma ren_list_id {Γ} (Ξ : list (form Γ)) : ren_list Ξ rid = Ξ.
Proof. unfold ren_list. rewrite (map_ext _ (fun χ => χ)); [apply map_id|intros; apply ren_id]. Qed.

Lemma equiv_ren {Γ Δ} (Ξ : list (form Γ)) A B (ρ : ren Γ Δ) :
  equiv Ξ A B -> equiv (ren_list Ξ ρ) (ren_tm A ρ) (ren_tm B ρ).
Proof. intros [H1 H2]; split; [exact (deriv_ren _ ρ H1)|exact (deriv_ren _ ρ H2)]. Qed.

End Equiv.

Arguments ren_list {Srt Sym P Γ Δ} Ξ ρ.
Arguments equiv {Srt Sym P} C {I} R {Γ} Ξ A B.

(** ** Monotonie de ∃ et ∧ *)

Section Mono.
Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).
Context (C : system Sym) {I : Type} (R : I -> drule Sym P).
Context `{HasAnd Srt Sym P} `{Includes _ Sym P I and_idx R and_rules}.

Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ ψ" := (deriv C P R _ Ξ ψ) (at level 70).

Lemma vsubst_cancel1 {Γ s P'} (B : Terms.tm Sym (ι s :: Γ) P') :
  vsubst (ren_tm B (upr [ι s] (wk [ι s]))) (inst1 (var0 vz)) = B.
Proof.
  rewrite vsubst_ren. rewrite <- (vsubst_vid B) at 2. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre, aget_vid. revert ρ x. refine (var_inv _ _ _).
  - reflexivity.
  - intros ρ y. change (upr [ι s] (wk [ι s]) ρ (vs y)) with (vr [ι s] (wk [ι s] ρ y)).
    change (aget (vs y) (vid (Sym := Sym) (ι s :: Γ)) = eta ρ (vs y)). apply aget_vid.
Qed.

Lemma and_mono {Γ} (Ξ : list (form Γ)) A1 A2 B1 B2 :
  (A1 :: Ξ) ⊢ A2 -> (B1 :: Ξ) ⊢ B2 -> (And A1 B1 :: Ξ) ⊢ And A2 B2.
Proof.
  intros HA HB. apply (and_I C P R).
  - eapply deriv_head; [apply (and_E1 C P R _ _ B1), d_ax; left; reflexivity|exact HA].
  - eapply deriv_head; [apply (and_E2 C P R _ A1), d_ax; left; reflexivity|exact HB].
Qed.

Section Ex.
Context (s : Srt) {HE : HasExists Sym P s} `{Includes _ Sym P I ex_idx R (ex_rules s)}.

Lemma ex_mono {Γ} (Ξ : list (form Γ)) A B :
  (A :: wk_list [ι s] Ξ) ⊢ B -> (Ex s A :: Ξ) ⊢ Ex s B.
Proof.
  intros Hd. apply (ex_E C P R s _ A); [apply d_ax; left; reflexivity|].
  change (ren_tm (Ex s B) (wk [ι s])) with (Ex s (ren_tm B (upr [ι s] (wk [ι s])))).
  apply (ex_I C P R s _ _ (var0 vz)). apply (deriv_rw P C R _ B); [symmetry; apply vsubst_cancel1|].
  eapply deriv_mono; [exact Hd|]. apply incl_cons; [left; reflexivity|].
  intros χ Hχ; right; right; exact Hχ.
Qed.
End Ex.

End Mono.

(** ** La traduction dans la logique L *)

Section Trans.
Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).
Context (Sdec : forall s s' : Srt, {s = s'} + {s <> s'}).
Context (Df : ctx Srt) (b : Srt).
Context {HA : HasAnd Sym P} {HT : HasTop Sym P} {HE : HasExists Sym P b} {HQ : HasEq Sym P b}.
Context `{FS : Functional Srt Sym} (view : forall σ (c : Sym σ), symview σ c).
Context (φ : form Sym P (ι b :: Df)).
Context (C : system Sym) {I : Type} (R : I -> drule Sym P).
Context {IA : Includes R and_rules} {IT : Includes R top_rules}
        {IE : Includes R (ex_rules b)} {IQ : Includes R (eq_rules b)}.

Local Notation tm := (Terms.tm Sym).
Local Notation XSym := (xsym Sym Df b).
Local Notation tm' := (Terms.tm XSym).
Local Notation args' := (Terms.args XSym).
Local Notation form := (form Sym P).
Local Notation vec := (vec Sym).
Local Notation "Ξ ⊢ ψ" := (deriv C P R _ Ξ ψ) (at level 70).
Local Notation TR := (tr Sdec Df b view φ).
Local Notation TRA := (tra Sdec Df b view φ).
Local Notation eqv := (equiv C R).

(** *** Affaiblissements de listes d'hypothèses *)

Lemma wk_plug Θ {Δ s} (Ξ : list (form Δ)) (τ : tm (Θ ++ Δ) s) :
  vsubst_list (wk_list [ι s] Ξ) (@acons _ Sym (Θ ++ Δ) (ι s) Δ τ (wkv Θ Δ)) = wk_list Θ Ξ.
Proof.
  unfold vsubst_list, wk_list. rewrite map_map. apply map_ext; intros χ.
  rewrite vsubst_ren, vpre_wk1. unfold wkv. rewrite <- ren_vsubst, vsubst_vid. reflexivity.
Qed.

Lemma wk_sub0 σ0 Θ0 {Δ} (Ξ : list (form Δ)) (A : Terms.tms Sym (Θ0 ++ Δ) σ0) :
  vsubst_list (wk_list (σ0 :: Θ0) Ξ) (@acons _ Sym (Θ0 ++ Δ) σ0 _ A (vid (Θ0 ++ Δ))) = wk_list Θ0 Ξ.
Proof.
  unfold vsubst_list, wk_list. rewrite map_map. apply map_ext; intros χ.
  rewrite vsubst_ren, ren_as_vsubst. f_equal. apply vec_ext; intros ρ y; unfold vget.
  rewrite !aget_vpre. reflexivity.
Qed.

Lemma wk_perm c Θ0 {Δ} (Ξ : list (form Δ)) :
  ren_list (wk_list (ι c :: Θ0) Ξ) (perm Θ0 (ι c)) = wk_list Θ0 (wk_list [ι c] Ξ).
Proof.
  unfold wk_list. fold (ren_list Ξ (wk (ι c :: Θ0))). fold (ren_list Ξ (wk [ι c])).
  fold (ren_list (ren_list Ξ (wk [ι c])) (wk Θ0)). rewrite !ren_list_ren. apply ren_list_ext.
  intros σ y. unfold rcomp, wk. cbn [vr]. apply perm_vs_vr.
Qed.

Lemma wk_fK {Δ} (Ξ : list (form Δ)) :
  ren_list (wk_list [ι b] Ξ) (upr [ι b] (wk Df)) = wk_list [ι b] (wk_list Df Ξ).
Proof.
  unfold wk_list. fold (ren_list Ξ (wk [ι b])). fold (ren_list Ξ (wk Df)).
  fold (ren_list (ren_list Ξ (wk Df)) (wk [ι b])). rewrite !ren_list_ren. apply ren_list_ext.
  intros σ y. unfold rcomp. change (wk [ι b] σ y) with (vr [ι b] y). rewrite upr_vr. reflexivity.
Qed.

(** *** Congruence vis-à-vis des continuations *)

Lemma subst_imp {Γ Δ} (Ξ : list (form Γ)) K1 K2 (v : vec Γ Δ) Ξ' :
  (K1 :: Ξ) ⊢ K2 -> vsubst_list Ξ v = Ξ' -> (vsubst K1 v :: Ξ') ⊢ vsubst K2 v.
Proof. intros Hd <-. exact (deriv_subst C P R Hd _ v). Qed.

Lemma ren_imp {Γ Δ} (Ξ : list (form Γ)) K1 K2 (ρ : ren Γ Δ) Ξ' :
  (K1 :: Ξ) ⊢ K2 -> ren_list Ξ ρ = Ξ' -> (ren_tm K1 ρ :: Ξ') ⊢ ren_tm K2 ρ.
Proof. intros Hd <-. exact (deriv_ren P C R _ ρ Hd). Qed.

Lemma wk_list_app_ren Λ Λ' {Δ} (Ξ : list (form Δ)) :
  ren_list (wk_list Λ Ξ) (upr Λ (wk Λ')) = wk_list Λ (wk_list Λ' Ξ).
Proof.
  unfold wk_list. fold (ren_list Ξ (wk Λ)). fold (ren_list Ξ (wk Λ')).
  fold (ren_list (ren_list Ξ (wk Λ')) (wk Λ)). rewrite !ren_list_ren. apply ren_list_ext.
  intros σ y. unfold rcomp. change (wk Λ σ y) with (vr Λ y). rewrite upr_vr. reflexivity.
Qed.

Lemma Sdec_self x : Sdec x x = left eq_refl.
Proof. destruct (Sdec x x) as [e|n]; [|contradiction]. rewrite (UIP_dec Sdec e eq_refl). reflexivity. Qed.

(** Un lambda devant une pile non vide de mêmes sortes. *)
Lemma trlam_cons {Γ a0 b0 c Δ r} (B : TrT P (ι a0 :: Γ) b0) (w : vec Γ Δ) (w1 : Arr a0 b0 c) (v : tm Δ a0)
  (sp : spine Δ b0 r) (K : form (ι r :: Δ)) :
  trlam Sdec B w (scons w1 v sp) K = B Δ r (@acons _ Sym Δ (ι a0) Γ v w) sp K.
Proof. unfold trlam. rewrite !Sdec_self. reflexivity. Qed.

Lemma wk_spK {Δ c r} (Ξ : list (form Δ)) (sp : spine Δ c r) :
  vsubst_list (wk_list [ι r] Ξ)
    (@acons _ Sym (ι c :: Δ) (ι r) Δ (apps (var0 vz) (ren_sp sp (wk [ι c]))) (wkv [ι c] Δ)) = wk_list [ι c] Ξ.
Proof. exact (wk_plug [ι c] Ξ _). Qed.

Theorem tr_cong_mut :
  (forall Γ s (t : tm' Γ s) Δ r (w : vec Γ Δ) (sp : spine Δ s r) (Ξ : list (form Δ)) K1 K2,
      (K1 :: wk_list [ι r] Ξ) ⊢ K2 -> (TR t Δ r w sp K1 :: Ξ) ⊢ TR t Δ r w sp K2) /\
  (forall Γ Θ (a : args' Γ Θ) Δ (w : vec Γ Δ) (Ξ : list (form Δ)) K1 K2,
      (K1 :: wk_list Θ Ξ) ⊢ K2 -> (TRA a Δ w K1 :: Ξ) ⊢ TRA a Δ w K2).
Proof.
  apply tm_args_ind2.
  - intros Γ σx x a IH _ Δ r w sp Ξ K1 K2 HK. cbn [tr]. apply IH. apply subst_imp with (Ξ := wk_list [ι (cod σx)] Ξ).
    + unfold spK, plug. apply subst_imp with (1 := HK). apply wk_spK.
    + apply wk_plug.
  - intros Γ σx c a IH Hc Δ r w sp Ξ K1 K2 HK. destruct c as [σ1 c0|]; cbn [tr].
    + revert a IH Hc sp. destruct (view σ1 c0) as [a0 b0 c1 w0|a0 b0 c1 w0|σ2 c2]; intros a IH Hc sp.
      * pose proof (Hc _ vz) as Ht. cbn [aget] in Ht. rewrite (args1_inv a). cbn beta iota zeta.
        change (cod (Spec [Spec [ι a0] b0] c1)) with c1 in *.
        revert K1 K2 HK. destruct sp as [s0|a1 b1 c2 r1 w1 v sp']; intros K1 K2 HK; [apply d_ax; left; reflexivity|].
        unfold trlam. destruct (Sdec a1 a0) as [e1|]; [|apply d_ax; left; reflexivity].
        destruct (Sdec b1 b0) as [e2|]; [|apply d_ax; left; reflexivity]. subst a1 b1. cbn [eq_rect].
        apply Ht, HK.
      * pose proof (Hc _ vz) as HF. pose proof (Hc _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
        rewrite (args2_inv a). cbn beta iota zeta. cbn [fst snd].
        apply Hu. apply HF. apply ren_imp with (1 := HK). exact (wk_list_app_ren [ι r] [ι a0] Ξ).
      * apply IH. apply subst_imp with (Ξ := wk_list [ι (cod σ2)] Ξ).
        -- unfold spK, plug. apply subst_imp with (1 := HK). apply wk_spK.
        -- apply wk_plug.
    + apply IH. unfold fK. apply (ex_mono P C R b). apply (and_mono P C R); [apply d_ax; left; reflexivity|].
      apply ren_imp with (Ξ := wk_list [ι b] Ξ); [|apply wk_fK].
      unfold spK, plug. apply subst_imp with (1 := HK). apply wk_spK.
  - intros Γ Δ w Ξ K1 K2 HK. cbn [tra]. rewrite wk_list_nil in HK. exact HK.
  - intros Γ σx Θ u IHu a IHa Δ w Ξ K1 K2 HK. destruct σx as [Λ c]. cbn [tra].
    destruct (Sdec c P) as [e|n].
    + apply IHa. apply subst_imp with (1 := HK). apply wk_sub0.
    + destruct Λ as [|λ Λ]; [|apply d_ax; left; reflexivity].
      apply IHu, IHa. apply ren_imp with (1 := HK). apply wk_perm.
Qed.

Lemma tr_cong {Γ s} (t : tm' Γ s) {Δ r} (w : vec Γ Δ) (sp : spine Δ s r) (Ξ : list (form Δ)) K1 K2 :
  eqv (wk_list [ι r] Ξ) K1 K2 -> eqv Ξ (TR t Δ r w sp K1) (TR t Δ r w sp K2).
Proof. intros [H1 H2]; split; apply (proj1 tr_cong_mut); assumption. Qed.

Lemma tra_cong {Γ Θ} (a : args' Γ Θ) {Δ} (w : vec Γ Δ) (Ξ : list (form Δ)) K1 K2 :
  eqv (wk_list Θ Ξ) K1 K2 -> eqv Ξ (TRA a Δ w K1) (TRA a Δ w K2).
Proof. intros [H1 H2]; split; apply (proj2 tr_cong_mut); assumption. Qed.


(** *** Renommage de la traduction *)

Lemma tr_ren {Γ s} (t : tm' Γ s) {Δ Δ' r} (w : vec Γ Δ) (sp : spine Δ s r) K (ρ : ren Δ Δ') :
  ren_tm (TR t Δ r w sp K) ρ = TR t Δ' r (vren w ρ) (ren_sp sp ρ) (ren_tm K (upr [ι r] ρ)).
Proof.
  rewrite ren_as_vsubst, tr_vsubst, vcomp_vpre_vid, <- ren_sp_as_vsubst. f_equal.
  apply (vsubst_vup_vpre [ι r] K ρ).
Qed.

Lemma vren_vup Λ {Γ Δ Δ'} (v : vec Γ Δ) (ρ : ren Δ Δ') : vren (vup Λ v) (upr Λ ρ) = vup Λ (vren v ρ).
Proof.
  apply vec_ext; intros σ x; unfold vget. unfold vren at 1. rewrite aget_vmap. vcase x.
  - rewrite !aget_vup_l, eta_ren, upr_vl. reflexivity.
  - rewrite !aget_vup_r'. unfold vren. rewrite aget_vmap, !ren_tms_ren. apply ren_tms_ext.
    intros σ' y. unfold rcomp, wk. rewrite upr_vr. reflexivity.
Qed.

Lemma Sdec_refl : Sdec P P = left eq_refl.
Proof. destruct (Sdec P P) as [e|n]; [|contradiction]. rewrite (UIP_dec Sdec e eq_refl). reflexivity. Qed.

Lemma tra_inst1 {Γ Θ c} (a : args' Γ Θ) {Δ} (w : vec Γ Δ) (K : form (Θ ++ ι c :: Δ)) (X : tm Δ c) :
  vsubst (TRA a (ι c :: Δ) (vren w (wk [ι c])) K) (inst1 X) = TRA a Δ w (vsubst K (vup Θ (inst1 X))).
Proof. rewrite tra_vsubst. f_equal. apply vcomp_vren_wk_inst1. Qed.

(** *** La formule φ instanciée *)

Definition phi {Δ} (a : Terms.args Sym Δ Df) (y : tm Δ b) : form Δ :=
  vsubst φ (@acons _ Sym Δ (ι b) Df y a).

Lemma phi_ren {Δ Δ'} (a : Terms.args Sym Δ Df) (y : tm Δ b) (ρ : ren Δ Δ') :
  ren_tm (phi a y) ρ = phi (ren_args a ρ) (ren_tm y ρ).
Proof.
  unfold phi. rewrite ren_vsubst. f_equal. apply vec_ext; intros σ x; unfold vget. unfold vren.
  rewrite aget_vmap. revert σ x. refine (var_inv _ _ _); [apply ren_tms_nil|].
  intros σ z. cbn [aget atl]. rewrite aget_ren. reflexivity.
Qed.

Lemma phi_inst {Δ} (a : Terms.args Sym Δ Df) (y : tm Δ b) :
  vsubst (phi (ren_args a (wk [ι b])) (var0 vz)) (inst1 y) = phi a y.
Proof.
  unfold phi. rewrite vsubst_vsubst. f_equal. apply vec_ext; intros σ x; unfold vget.
  rewrite aget_vcomp. revert σ x. refine (var_inv _ _ _).
  - cbn [aget ahd]. rewrite vsubst_tms_nil. apply vsubst_var0.
  - intros σ z. cbn [aget atl]. rewrite aget_ren, vsubst_tms_ren'.
    change (vpre (wk [ι b]) (inst1 y)) with (vpre (wk [ι b]) (@acons _ Sym Δ (ι b) Δ y (vid Δ))).
    rewrite vpre_wk1, vsubst_tms_vid. reflexivity.
Qed.

Lemma fK_inst {Δ} (K : form (ι b :: Δ)) (a : Terms.args Sym Δ Df) :
  vsubst (fK Df b φ K) (vcat Df a (vid Δ)) = Ex b (And (phi (ren_args a (wk [ι b])) (var0 vz)) K).
Proof.
  unfold fK, Ex. rewrite vsubst_Qnt, vsubst_tms_vup. cbn [dom]. unfold And. rewrite vsubst_Bin. f_equal. f_equal.
  - unfold phi. rewrite vsubst_ren. f_equal. apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
    revert σ x. refine (var_inv _ _ _); [reflexivity|].
    intros σ z. cbn [vl]. change (aget (vs (vl Δ z)) (vup [ι b] (vcat Df a (vid Δ))))
      with (aget (vl Δ z) (vren (vcat Df a (vid Δ)) (wk [ι b]))).
    unfold vren. rewrite aget_vmap, aget_vcat_l. cbn [aget atl]. rewrite aget_ren. reflexivity.
  - etransitivity; [exact (vsubst_ren_upr_wk_cat [ι b] Df K a (vid Δ))|].
    etransitivity; [|apply (vsubst_vid K)]. f_equal. apply (vup_vid [ι b]).
Qed.

(** *** Calcul de la traduction de lambda et de app *)

Lemma tr_app_eq {Γ a0 b0 c} (w0 : Arr a0 b0 c) (F : tm' Γ c) (u : tm' Γ a0) {Δ r} (w : vec Γ Δ)
  (sp : spine Δ b0 r) K :
  view _ (s_app w0) = vw_app w0 ->
  TR (tsym (xold (s_app w0)) (@acons _ XSym Γ (ι c) _ F (@acons _ XSym Γ (ι a0) _ u anil))) Δ r w sp K =
  TR u Δ a0 w snil (TR F (ι a0 :: Δ) r (vren w (wk [ι a0])) (scons w0 (var0 vz) (ren_sp sp (wk [ι a0])))
                      (ren_tm K (upr [ι r] (wk [ι a0])))).
Proof. intros Ev. cbn [tr]. rewrite Ev. reflexivity. Qed.

Lemma tr_lam_eq {Γ a0 b0 c} (w0 : Arr a0 b0 c) (t : tm' (ι a0 :: Γ) b0) {Δ r} (w : vec Γ Δ)
  (sp : spine Δ c r) K :
  view _ (s_lam w0) = vw_lam w0 ->
  TR (tsym (xold (s_lam w0)) (@acons _ XSym Γ (Spec [ι a0] b0) _ t anil)) Δ r w sp K =
  trlam Sdec (fun Δ r w sp K => TR t Δ r w sp K) w sp K.
Proof. intros Ev. cbn [tr]. rewrite Ev. reflexivity. Qed.

Lemma tr_oth_eq {Γ σ} (c0 : Sym σ) (a : args' Γ (dom σ)) {Δ r} (w : vec Γ Δ) (sp : spine Δ (cod σ) r) K :
  view σ c0 = vw_oth c0 ->
  TR (tsym (xold c0) a) Δ r w sp K = TRA a Δ w (plug (dom σ) (spK sp K) (tsym c0 (holes (dom σ) Δ))).
Proof. intros Ev. cbn [tr]. rewrite Ev. reflexivity. Qed.

Lemma vren_acons1 {Γ Δ Δ' a} (v : tm Δ a) (w : vec Γ Δ) (ρ : ren Δ Δ') :
  vren (@acons _ Sym Δ (ι a) Γ v w) ρ = @acons _ Sym Δ' (ι a) Γ (ren_tm v ρ) (vren w ρ).
Proof.
  change (vren (@acons _ Sym Δ (ι a) Γ v w) ρ) with (@acons _ Sym Δ' (ι a) Γ (ren_tms (σ := ι a) v ρ) (vren w ρ)).
  rewrite ren_tms_nil. reflexivity.
Qed.

(** La tête de pile, après substitution de la variable fraîche. *)
Lemma tr_scons_inst {Γ s a0 b0 r} (F : tm' Γ s) (w0 : Arr a0 b0 s) {Δ} (W : vec Γ Δ) (S : spine Δ b0 r)
  (K : form (ι r :: Δ)) (X : tm Δ a0) :
  vsubst (TR F (ι a0 :: Δ) r (vren W (wk [ι a0])) (scons w0 (var0 vz) (ren_sp S (wk [ι a0])))
            (ren_tm K (upr [ι r] (wk [ι a0])))) (inst1 X)
  = TR F Δ r W (scons w0 X S) K.
Proof.
  rewrite tr_vsubst. f_equal.
  - exact (vcomp_vren_wk_inst1 W X).
  - cbn [vsubst_sp]. f_equal; [apply vsubst_var0|].
    exact (eq_trans (vsubst_sp_wk_cat [ι a0] S (@acons _ Sym Δ (ι a0) [] X anil) (vid Δ)) (vsubst_sp_vid S)).
  - etransitivity; [exact (vsubst_ren_upr_wk_cat [ι r] [ι a0] K (@acons _ Sym Δ (ι a0) [] X anil) (vid Δ))|].
    rewrite vup_vid. apply vsubst_vid.
Qed.

Lemma spK_nil {Δ c} (K : form (ι c :: Δ)) : spK snil K = K.
Proof.
  unfold spK, plug. cbn [ren_sp apps]. rewrite <- (vsubst_vid K) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vid. revert σ x. refine (var_inv _ _ _); [reflexivity|].
  intros σ y. cbn [aget atl]. rewrite aget_wkv. reflexivity.
Qed.

(** *** Conditions sur les positions *)

Definition fpos (θ : spec Srt) : Prop := dom θ = [] /\ cod θ <> P.
(** Une position de terme : sans lieur, de sorte autre que P et non flèche. *)
Definition gpos (θ : spec Srt) : Prop := fpos θ /\ noarr (cod θ).
Definition spos (θ : spec Srt) : Prop := gpos θ \/ (cod θ = P /\ Forall gpos (dom θ)).
Definition vspec (σ : spec Srt) : Prop := Forall gpos (dom σ).
Definition vctx (Γ : ctx Srt) : Prop := forall σ, var Γ σ -> vspec σ.

(** *** Valeurs déterminées *)

Section Open.
Hypothesis Htot : forall Δ (Ξ : list (form Δ)) (a : Terms.args Sym Δ Df),
  Ξ ⊢ Ex b (phi (ren_args a (wk [ι b])) (var0 vz)).
Hypothesis Huniq : forall Δ (Ξ : list (form Δ)) (a : Terms.args Sym Δ Df) (y y' : tm Δ b),
  Ξ ⊢ phi a y -> Ξ ⊢ phi a y' -> Ξ ⊢ Eq b y y'.
Hypothesis Hsym : forall σ (c : Sym σ), view_ok P (view σ c).
Hypothesis HDf : Forall (okpos P) Df.
Hypothesis Hb : b <> P.
Hypothesis Harr_inj : forall a b c a' b' (w : Arr a b c) (w' : Arr a' b' c), a = a' /\ b = b'.
Hypothesis Harr_dom : forall a b c (w : Arr a b c), a <> P /\ noarr a.
Hypothesis Harr_cod : forall a b c (w : Arr a b c), b <> P.
Hypothesis Hnoarr_P : noarr P.

Lemma vctx_cons {Δ} τ0 : vspec τ0 -> vctx Δ -> vctx (τ0 :: Δ).
Proof. intros H0 HΔ σ x. revert σ x. refine (var_inv _ _ _); [exact H0|intros σ y; apply HΔ, y]. Qed.

Lemma vspec_ι c : vspec (ι c).
Proof. constructor. Qed.

(** Sous l'hypothèse φ(a, y₀), ∃y. φ(a, y) ∧ K[y] équivaut à K[y₀]. *)
Lemma ex_det {Δ} (Ξ : list (form Δ)) (a : Terms.args Sym Δ Df) (y0 : tm Δ b) (K : form (ι b :: Δ)) :
  Ξ ⊢ phi a y0 -> eqv Ξ (Ex b (And (phi (ren_args a (wk [ι b])) (var0 vz)) K)) (vsubst K (inst1 y0)).
Proof.
  intros Hf. split.
  - apply (ex_E C P R b _ (And (phi (ren_args a (wk [ι b])) (var0 vz)) K)); [apply d_ax; left; reflexivity|].
    match goal with |- deriv _ _ _ _ ?L _ => set (Ξ0 := L) end.
    assert (HK : Ξ0 ⊢ K) by (apply (and_E2 C P R _ (phi (ren_args a (wk [ι b])) (var0 vz))), d_ax; left; reflexivity).
    assert (Hq : Ξ0 ⊢ Eq b (var0 vz) (ren_tm y0 (wk [ι b]))).
    { apply (Huniq _ _ (ren_args a (wk [ι b]))).
      - apply (and_E1 C P R _ _ K), d_ax; left; reflexivity.
      - rewrite <- phi_ren. eapply deriv_mono; [exact (deriv_ren P C R _ (wk [ι b]) Hf)|].
        intros χ Hχ; right; right; exact Hχ. }
    pose (χ := ren_tm K (upr [ι b] (wk [ι b]))).
    assert (E1 : vsubst χ (inst1 (var0 vz)) = K) by apply vsubst_cancel1.
    assert (E2 : vsubst χ (inst1 (ren_tm y0 (wk [ι b]))) = ren_tm (vsubst K (inst1 y0)) (wk [ι b])).
    { unfold χ. rewrite vsubst_ren, ren_vsubst. f_equal. apply vec_ext; intros σ x; unfold vget.
      rewrite aget_vpre. unfold vren. rewrite aget_vmap. revert σ x. refine (var_inv _ _ _).
      - cbn [aget ahd inst1]. rewrite ren_tms_nil. reflexivity.
      - intros σ y. cbn [aget atl inst1]. rewrite aget_vid, eta_ren.
        change (upr [ι b] (wk [ι b]) σ (vs y)) with (upr [ι b] (wk [ι b]) σ (vr [ι b] y)).
        rewrite upr_vr. unfold wk. cbn [vr aget atl inst1].
        change (aget (vs y) (vid (Sym := Sym) (ι b :: Δ)) = eta σ (vs y)). apply aget_vid. }
    rewrite <- E2. apply (eq_subst C P R b _ χ (var0 vz)); [exact Hq|].
    apply (deriv_rw P C R _ K); [symmetry; exact E1|exact HK].
  - apply (ex_I C P R b _ _ y0). unfold And at 1. rewrite vsubst_Bin, phi_inst. fold (And (phi a y0) (vsubst K (inst1 y0))).
    apply (and_I C P R).
    + eapply deriv_mono; [exact Hf|]. intros χ Hχ; right; exact Hχ.
    + apply d_ax; left; reflexivity.
Qed.

(** La valeur d'une application t·sp (une seule pile). *)
Definition DetS {Γ s Δ r} (Ξ : list (form Δ)) (t : tm' Γ s) (w : vec Γ Δ) (sp : spine Δ s r) (τ : tm Δ r) : Prop :=
  forall Δ' (ρ : ren Δ Δ') (Ξ' : list (form Δ')), incl (ren_list Ξ ρ) Ξ' ->
  forall K, eqv Ξ' (TR t Δ' r (vren w ρ) (ren_sp sp ρ) K) (vsubst K (inst1 (ren_tm τ ρ))).

(** La valeur d'un terme (pile vide). *)
Definition DetT {Γ s Δ} (Ξ : list (form Δ)) (t : tm' Γ s) (w : vec Γ Δ) (τ : tm Δ s) : Prop :=
  DetS Ξ t w snil τ.

Definition DetA {Γ Θ Δ} (Ξ : list (form Δ)) (a : args' Γ Θ) (w : vec Γ Δ) (τs : Terms.args Sym Δ Θ) : Prop :=
  forall Δ' (ρ : ren Δ Δ') (Ξ' : list (form Δ')), incl (ren_list Ξ ρ) Ξ' ->
  forall K, eqv Ξ' (TRA a Δ' (vren w ρ) K) (vsubst K (vcat Θ (ren_args τs ρ) (vid Δ'))).

Lemma incl_ren_comp {Δ Δ1 Δ2} (Ξ : list (form Δ)) (Ξ1 : list (form Δ1)) (Ξ2 : list (form Δ2))
  (ρ1 : ren Δ Δ1) (ρ2 : ren Δ1 Δ2) :
  incl (ren_list Ξ ρ1) Ξ1 -> incl (ren_list Ξ1 ρ2) Ξ2 -> incl (ren_list Ξ (rcomp ρ1 ρ2)) Ξ2.
Proof.
  intros H1 H2. rewrite <- ren_list_ren. intros χ Hχ. apply H2. exact (incl_ren_list P _ _ ρ2 H1 χ Hχ).
Qed.

Lemma DetS_mono {Γ s Δ Δ1 r} (Ξ : list (form Δ)) (t : tm' Γ s) w (sp : spine Δ s r) τ (ρ : ren Δ Δ1)
  (Ξ1 : list (form Δ1)) :
  DetS Ξ t w sp τ -> incl (ren_list Ξ ρ) Ξ1 -> DetS Ξ1 t (vren w ρ) (ren_sp sp ρ) (ren_tm τ ρ).
Proof.
  intros Hd Hi Δ' ρ' Ξ' Hi' K. rewrite vren_vren, ren_ren, ren_sp_ren. apply Hd.
  exact (incl_ren_comp _ _ _ _ _ Hi Hi').
Qed.

Lemma DetT_mono {Γ s Δ Δ1} (Ξ : list (form Δ)) (t : tm' Γ s) w τ (ρ : ren Δ Δ1) (Ξ1 : list (form Δ1)) :
  DetT Ξ t w τ -> incl (ren_list Ξ ρ) Ξ1 -> DetT Ξ1 t (vren w ρ) (ren_tm τ ρ).
Proof. apply (DetS_mono _ _ _ snil). Qed.

Lemma DetA_mono {Γ Θ Δ Δ1} (Ξ : list (form Δ)) (a : args' Γ Θ) w τs (ρ : ren Δ Δ1) (Ξ1 : list (form Δ1)) :
  DetA Ξ a w τs -> incl (ren_list Ξ ρ) Ξ1 -> DetA Ξ1 a (vren w ρ) (ren_args τs ρ).
Proof.
  intros Hd Hi Δ' ρ' Ξ' Hi' K. rewrite vren_vren, ren_args_ren. apply Hd. exact (incl_ren_comp _ _ _ _ _ Hi Hi').
Qed.

Lemma incl_wk_cons {Δ Δ1} (Ξ : list (form Δ)) (Ξ1 : list (form Δ1)) (ρ : ren Δ Δ1) τ (A : form (τ :: Δ1)) :
  incl (ren_list Ξ ρ) Ξ1 -> incl (ren_list Ξ (rcomp ρ (wk [τ]))) (A :: wk_list [τ] Ξ1).
Proof.
  intros Hi. rewrite <- ren_list_ren. intros χ Hχ. right. exact (incl_ren_list P _ _ (wk [τ]) Hi χ Hχ).
Qed.

Lemma incl_wk_comp {Δ Δ1 Δ'} (Ξ : list (form Δ)) (Ξ1 : list (form Δ1)) (Ξ' : list (form Δ')) τ
  (ρ' : ren (τ :: Δ1) Δ') :
  incl (ren_list (wk_list [τ] Ξ1) ρ') Ξ' -> incl (ren_list Ξ1 (rcomp (wk [τ]) ρ')) Ξ'.
Proof. intros Hi'. rewrite <- ren_list_ren. exact Hi'. Qed.

(** **Ouverture** : pour dériver G, on peut supposer donnée une valeur
    déterminée de l'application t·sp, dans un contexte étendu. *)
Theorem open_mut :
  (forall Γ s (t : tm' Γ s), okctx P Γ -> forall Δ r (w : vec Γ Δ) (sp : spine Δ s r) (Ξ : list (form Δ))
      (G : form Δ), noarr r ->
      (forall Δ1 (ρ : ren Δ Δ1) Ξ1 τ, (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
         DetS Ξ1 t (vren w ρ) (ren_sp sp ρ) τ -> Ξ1 ⊢ ren_tm G ρ) ->
      Ξ ⊢ G) /\
  (forall Γ Θ (a : args' Γ Θ), okctx P Γ -> Forall (okpos P) Θ ->
      forall Δ (w : vec Γ Δ) (Ξ : list (form Δ)) (G : form Δ),
      (forall Δ1 (ρ : ren Δ Δ1) Ξ1 τs, (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
         DetA Ξ1 a (vren w ρ) τs -> Ξ1 ⊢ ren_tm G ρ) ->
      Ξ ⊢ G).
Proof.
  apply tm_args_ind2.
  - intros Γ σx x a IH _ HΓ Δ r w sp Ξ G Hr Hk. apply (IH HΓ (HΓ _ x) Δ w Ξ G).
    intros Δ1 ρ Ξ1 τs HV Hi Hd. apply (Hk Δ1 ρ Ξ1 (apps (happ σx (aget x (vren w ρ)) τs) (ren_sp sp ρ)) HV Hi).
    intros Δ' ρ' Ξ' Hi' K. cbn [tr]. eapply equiv_trans; [apply (Hd Δ' ρ' Ξ' Hi')|].
    rewrite plug_inst, spK_inst, ren_apps, happ_natural, happ_vsubst. unfold vren at 1. rewrite aget_vmap.
    apply equiv_refl.
  - intros Γ σx c a IH Hc HΓ Δ r w sp Ξ G Hr Hk. destruct c as [σ1 c0|].
    + pose proof (Hsym σ1 c0) as Hs. remember (view σ1 c0) as vv eqn:Ev.
      revert a IH Hc sp Hk Hs Ev. destruct vv as [a0 b0 c1 w0|a0 b0 c1 w0|σ2 c2]; intros a IH Hc sp Hk Hs Ev.
      * (* lambda *)
        pose proof (Hc _ vz) as Ht. cbn [aget] in Ht. revert Hk. rewrite (args1_inv a). intros Hk.
        change (cod (Spec [Spec [ι a0] b0] c1)) with c1 in *.
        revert Hk Hr. destruct sp as [s0|a1 b1 c2 r1 w1 v sp']; intros Hk Hr; [exfalso; exact (Hr _ _ w0)|].
        destruct (Harr_inj _ _ _ _ _ w1 w0) as [-> ->].
        apply (Ht (okctx_cons1 P a0 Γ HΓ) Δ r1 (@acons _ Sym Δ (ι a0) Γ v w) sp' Ξ G Hr).
        intros Δ1 ρ Ξ1 τ HV Hi Hd. apply (Hk Δ1 ρ Ξ1 τ HV Hi).
        intros Δ' ρ' Ξ' Hi' K. cbn [ren_sp]. rewrite (tr_lam_eq w0 (ahd a) (vren (vren w ρ) ρ')) by (symmetry; exact Ev). rewrite trlam_cons.
        pose proof (Hd Δ' ρ' Ξ' Hi' K) as H.
        assert (E : @vren _ Sym (dom (Spec [ι a0] b0) ++ Γ) Δ1 Δ' (@vren _ Sym (dom (Spec [ι a0] b0) ++ Γ) Δ Δ1
                      (@acons _ Sym Δ (ι a0) Γ v w) ρ) ρ'
                    = @acons _ Sym Δ' (ι a0) Γ (ren_tm (ren_tm v ρ) ρ') (vren (vren w ρ) ρ')).
        { etransitivity; [exact (f_equal (fun z => vren z ρ') (vren_acons1 v w ρ))|exact (vren_acons1 _ _ ρ')]. }
        rewrite E in H. exact H.
      * (* app *)
        pose proof (Hc _ vz) as HF. pose proof (Hc _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
        revert Hk. rewrite (args2_inv a). intros Hk.
        destruct (Harr_dom _ _ _ w0) as [_ Ha0].
        apply (Hu HΓ Δ a0 w snil Ξ G Ha0). intros Δ1 ρ1 Ξ1 τu HV1 Hi1 Hdu.
        apply (HF HΓ Δ1 r (vren w ρ1) (scons w0 τu (ren_sp sp ρ1)) Ξ1 (ren_tm G ρ1) Hr).
        intros Δ2 ρ2 Ξ2 τ HV2 Hi2 HdF. rewrite ren_ren.
        apply (Hk Δ2 (rcomp ρ1 ρ2) Ξ2 τ (fun H => HV2 (HV1 H)) (incl_ren_comp _ _ _ _ _ Hi1 Hi2)).
        intros Δ' ρ' Ξ' Hi' K. rewrite tr_app_eq by (symmetry; exact Ev).
        assert (Hi3 : incl (ren_list Ξ1 (rcomp ρ2 ρ')) Ξ') by exact (incl_ren_comp _ _ _ _ _ Hi2 Hi').
        pose proof (Hdu Δ' (rcomp ρ2 ρ') Ξ' Hi3) as Hu'. cbn [ren_sp] in Hu'.
        assert (HW : vren (vren w (rcomp ρ1 ρ2)) ρ' = vren (vren w ρ1) (rcomp ρ2 ρ'))
          by (rewrite !vren_vren; reflexivity).
        rewrite HW. eapply equiv_trans; [apply Hu'|]. rewrite tr_scons_inst.
        pose proof (HdF Δ' ρ' Ξ' Hi' K) as HF'. cbn [ren_sp] in HF'. rewrite !vren_vren, !ren_sp_ren, ren_ren in HF'.
        rewrite vren_vren, ren_sp_ren. exact HF'.
      * (* autre symbole *)
        cbn [view_ok] in Hs. apply (IH HΓ Hs Δ w Ξ G).
        intros Δ1 ρ Ξ1 τs HV Hi Hd. apply (Hk Δ1 ρ Ξ1 (apps (tsym c2 τs) (ren_sp sp ρ)) HV Hi).
        intros Δ' ρ' Ξ' Hi' K. rewrite tr_oth_eq by (symmetry; exact Ev).
        eapply equiv_trans; [apply (Hd Δ' ρ' Ξ' Hi')|].
        rewrite plug_inst, spK_inst, vsubst_tsym, holes_inst, ren_apps. apply equiv_refl.
    + apply (IH HΓ HDf Δ w Ξ G).
      intros Δ1 ρ Ξ1 τs HV Hi Hd.
      apply (ex_E C P R b _ (phi (ren_args τs (wk [ι b])) (var0 vz))); [apply Htot|].
      rewrite ren_ren. apply (Hk (ι b :: Δ1) (rcomp ρ (wk [ι b])) _ (apps (var0 vz) (ren_sp sp (rcomp ρ (wk [ι b])))));
        [intros HΔ; apply vctx_cons; [apply vspec_ι|apply HV, HΔ]|exact (incl_wk_cons _ _ _ _ _ Hi)|].
      intros Δ' ρ' Ξ' Hi' K. cbn [tr].
      pose proof (Hd Δ' (rcomp (wk [ι b]) ρ') Ξ' (incl_wk_comp Ξ Ξ1 Ξ' _ ρ' ltac:(intros χ Hχ; apply Hi';
        apply (incl_ren_list P (wk_list [ι b] Ξ1)); [intros χ' Hχ'; right; exact Hχ'|exact Hχ]))
        (fK Df b φ (spK (ren_sp (ren_sp sp ρ) (rcomp (wk [ι b]) ρ')) K))) as Hx.
      rewrite vren_vren in Hx. rewrite vren_vren, ren_sp_ren. rewrite ren_sp_ren in Hx.
      eapply equiv_trans; [exact Hx|].
      rewrite fK_inst, <- ren_args_ren. eapply equiv_trans; [apply ex_det|].
      * apply d_ax, Hi'. left. rewrite phi_ren. reflexivity.
      * rewrite spK_inst, ren_apps, ren_sp_ren. apply equiv_refl.
  - intros Γ HΓ _ Δ w Ξ G Hk. rewrite <- (ren_id G). apply (Hk Δ rid Ξ anil); [exact (fun H => H)|rewrite ren_list_id; apply incl_refl|].
    intros Δ' ρ' Ξ' Hi' K. cbn [tra vcat]. rewrite vsubst_vid. apply equiv_refl.
  - intros Γ σx Θ u IHu a IHa HΓ HΘ Δ w Ξ G Hk. inversion HΘ as [|? ? Hp HΘ']; subst.
    destruct σx as [Λ c]. destruct (Sdec c P) as [e|n].
    + subst c. apply (IHa HΓ HΘ' Δ w Ξ G). intros Δ1 ρ Ξ1 τs HV Hi Hd.
      apply (Hk Δ1 ρ Ξ1 (@acons _ Sym Δ1 (Spec Λ P) _ (TR u (Λ ++ Δ1) P (vup Λ (vren w ρ)) snil hole) τs) HV Hi).
      intros Δ' ρ' Ξ' Hi' K. cbn [tra]. rewrite Sdec_refl. cbn [castc castP eq_rect eq_sym].
      eapply equiv_trans; [apply (Hd Δ' ρ' Ξ' Hi')|]. rewrite sub0_inst.
      change (ren_args (@acons _ Sym Δ1 (Spec Λ P) _ (TR u (Λ ++ Δ1) P (vup Λ (vren w ρ)) snil hole) τs) ρ')
        with (@acons _ Sym Δ' (Spec Λ P) _ (ren_tm (TR u (Λ ++ Δ1) P (vup Λ (vren w ρ)) snil hole) (upr Λ ρ'))
                (ren_args τs ρ')).
      cbn [vcat]. rewrite tr_ren, vren_vup. apply equiv_refl.
    + destruct Λ as [|λ Λ].
      * assert (Hc : noarr c) by (destruct Hp as [[_ Hc]|[Hc _]]; [exact Hc|exact (False_ind _ (n Hc))]).
        apply (IHu HΓ Δ c w snil Ξ G Hc). intros Δ1 ρ1 Ξ1 τu HV1 Hi1 Hdu.
        apply (IHa HΓ HΘ' Δ1 (vren w ρ1) Ξ1 (ren_tm G ρ1)). intros Δ2 ρ2 Ξ2 τs HV2 Hi2 Hda.
        rewrite ren_ren, vren_vren in *.
        apply (Hk Δ2 (rcomp ρ1 ρ2) Ξ2 (@acons _ Sym Δ2 (ι c) _ (ren_tm τu ρ2) τs));
          [exact (fun H => HV2 (HV1 H))|exact (incl_ren_comp _ _ _ _ _ Hi1 Hi2)|].
        intros Δ' ρ' Ξ' Hi' K. cbn [tra]. destruct (Sdec c P) as [e'|n']; [contradiction|].
        assert (Hi3 : incl (ren_list Ξ1 (rcomp ρ2 ρ')) Ξ') by exact (incl_ren_comp _ _ _ _ _ Hi2 Hi').
        assert (HW : vren (vren w (rcomp ρ1 ρ2)) ρ' = vren (vren w ρ1) (rcomp ρ2 ρ'))
          by (rewrite !vren_vren; reflexivity).
        rewrite HW. eapply equiv_trans; [apply (Hdu Δ' (rcomp ρ2 ρ') Ξ' Hi3)|].
        rewrite tra_inst1, <- HW.
        eapply equiv_trans; [apply (Hda Δ' ρ' Ξ' Hi')|]. rewrite perm_inst2.
        change (ren_args (@acons _ Sym Δ2 (ι c) _ (ren_tm τu ρ2) τs) ρ')
          with (@acons _ Sym Δ' (ι c) _ (ren_tms (σ := ι c) (ren_tm τu ρ2) ρ') (ren_args τs ρ')).
        cbn [vcat]. rewrite ren_tms_nil, ren_ren. apply equiv_refl.
      * exfalso. destruct Hp as [[Hd _]|[Hc _]]; [discriminate Hd|exact (n Hc)].
Qed.



(** *** Remplacement des équivalents

    Dans le cœur du premier ordre, une position d'argument est soit un
    terme sans lieur de sorte autre que P ([fpos]), soit une formule liant
    de telles variables. Les variables des contextes n'ont que des
    positions du premier type ([vspec]) ; les symboles de sorte autre que P
    aussi. Les symboles de sorte P sont supposés compatibles avec
    l'équivalence à leurs positions de formules ([Hcong]). On en déduit
    qu'une formule quelconque de L respecte l'équivalence ([repl]). *)



(** Relation entre deux corps de même spécification : l'équivalence pour
    une formule, l'égalité sinon. *)
Definition comprel {Δ} (Ξ : list (form Δ)) (θ : spec Srt) : Terms.tms Sym Δ θ -> Terms.tms Sym Δ θ -> Prop :=
  match θ as θ0 return Terms.tms Sym Δ θ0 -> Terms.tms Sym Δ θ0 -> Prop with
  | Spec Λ c => fun u1 u2 =>
      match Sdec c P with
      | left e => eqv (wk_list Λ Ξ) (castP P e u1) (castP P e u2)
      | right _ => u1 = u2
      end
  end.

Definition argrel {Δ} (Ξ : list (form Δ)) (Θ : ctx Srt) (a1 a2 : Terms.args Sym Δ Θ) : Prop :=
  forall θ (z : var Θ θ), comprel Ξ θ (aget z a1) (aget z a2).

Lemma comprel_P {Δ} (Ξ : list (form Δ)) Λ (u1 u2 : tm (Λ ++ Δ) P) :
  comprel Ξ (Spec Λ P) u1 u2 <-> eqv (wk_list Λ Ξ) u1 u2.
Proof. cbn [comprel]. rewrite Sdec_refl. reflexivity. Qed.

Lemma comprel_nP {Δ} (Ξ : list (form Δ)) Λ c (u1 u2 : tm (Λ ++ Δ) c) :
  c <> P -> comprel Ξ (Spec Λ c) u1 u2 <-> u1 = u2.
Proof. intros n. cbn [comprel]. destruct (Sdec c P) as [e|n']; [contradiction|reflexivity]. Qed.

Lemma comprel_refl {Δ} (Ξ : list (form Δ)) θ (u : Terms.tms Sym Δ θ) : comprel Ξ θ u u.
Proof. destruct θ as [Λ c]. cbn [comprel]. destruct (Sdec c P); [apply equiv_refl|reflexivity]. Qed.

Lemma vsubst_list_wk_cat Λ {Δ} (Ξ : list (form Δ)) (a : Terms.args Sym Δ Λ) :
  vsubst_list (wk_list Λ Ξ) (vcat Λ a (vid Δ)) = Ξ.
Proof.
  unfold vsubst_list, wk_list. rewrite map_map. rewrite <- (map_id Ξ) at 2. apply map_ext; intros χ.
  rewrite vsubst_ren, vpre_wk, vsubst_vid. reflexivity.
Qed.

Lemma eqv_happ {Δ} (Ξ : list (form Δ)) Λ (A1 A2 : tm (Λ ++ Δ) P) (a : Terms.args Sym Δ Λ) :
  eqv (wk_list Λ Ξ) A1 A2 -> eqv Ξ (happ (Spec Λ P) A1 a) (happ (Spec Λ P) A2 a).
Proof.
  intros [H1 H2]. rewrite !happ_vsubst. cbn [dom].
  split; apply subst_imp with (Ξ := wk_list Λ Ξ); try assumption; apply vsubst_list_wk_cat.
Qed.

Lemma comprel_vup Λ {Δ} (Ξ : list (form Δ)) θ (u1 u2 : Terms.tms Sym Δ θ) :
  comprel Ξ θ u1 u2 -> comprel (wk_list Λ Ξ) θ (ren_tms u1 (wk Λ)) (ren_tms u2 (wk Λ)).
Proof.
  destruct θ as [Λθ c]. cbn [comprel]. destruct (Sdec c P) as [e|n].
  - subst c. cbn [castP eq_rect]. unfold ren_tms. cbn [dom]. intros Hq.
    rewrite <- wk_list_app_ren. apply equiv_ren, Hq.
  - intros ->. reflexivity.
Qed.

(** Conditions sur les symboles autres que lambda et app : leurs positions
    sont des termes non flèches ou des formules liant des termes ; un
    symbole de sorte autre que P n'a que des positions de termes. *)
Definition oth_ok (σ : spec Srt) : Prop := Forall spos (dom σ) /\ (cod σ <> P -> Forall gpos (dom σ)).
Hypothesis HsymV : forall σ (c : Sym σ), match view σ c with vw_oth _ => oth_ok σ | _ => True end.
Hypothesis Hcong : forall Θ (c : Sym (Spec Θ P)) Δ (Ξ : list (form Δ)) (a1 a2 : Terms.args Sym Δ Θ),
  argrel Ξ Θ a1 a2 -> eqv Ξ (tsym c a1) (tsym c a2).

Lemma vctx_app Λ Γ : Forall fpos Λ -> vctx Γ -> vctx (Λ ++ Γ).
Proof.
  intros HΛ HΓ σ x. vcase x; [|apply HΓ, z].
  clear HΓ. revert HΛ. induction z as [Λ0 σ0|Λ0 σ0 τ0 z IH]; intros HΛ.
  - inversion HΛ as [|? ? [Hd _]]; subst. unfold vspec. rewrite Hd. constructor.
  - inversion HΛ; subst. apply IH; assumption.
Qed.

Definition rpos (θ : spec Srt) : Prop := Forall fpos (dom θ).

Lemma noarr_neq a b0 c (w : Arr a b0 c) : c <> P.
Proof. intros ->. exact (Hnoarr_P _ _ w). Qed.

(** Les positions de tous les symboles de L ne lient que des termes, et un
    symbole de sorte autre que P n'a que des positions de sorte autre que P. *)
Lemma sym_rpos σ (c : Sym σ) : Forall rpos (dom σ) /\ (cod σ <> P -> Forall (fun θ => cod θ <> P) (dom σ)).
Proof.
  pose proof (HsymV σ c) as Hs. revert Hs. destruct (view σ c) as [a0 b0 c0 w0|a0 b0 c0 w0|σ0 c0]; intros Hs.
  - destruct (Harr_dom _ _ _ w0) as [Ha _]. split.
    + apply Forall_cons; [apply Forall_cons; [split; [reflexivity|exact Ha]|apply Forall_nil]|apply Forall_nil].
    + intros _. apply Forall_cons; [exact (Harr_cod _ _ _ w0)|apply Forall_nil].
  - destruct (Harr_dom _ _ _ w0) as [Ha _]. split.
    + repeat apply Forall_cons; try apply Forall_nil.
    + intros _. apply Forall_cons; [exact (noarr_neq _ _ _ w0)|apply Forall_cons; [exact Ha|apply Forall_nil]].
  - destruct Hs as [Hsp Hg]. split.
    + eapply Forall_impl; [|exact Hsp]. intros θ [[[Hd _] _]|[_ Hd]]; unfold rpos; [rewrite Hd; constructor|].
      eapply Forall_impl; [|exact Hd]. intros λ [Hl _]; exact Hl.
    + intros Hn. eapply Forall_impl; [|exact (Hg Hn)]. intros θ [[_ Hc] _]; exact Hc.
Qed.

Definition VR {Γ Δ} (Ξ : list (form Δ)) (v1 v2 : vec Γ Δ) : Prop :=
  forall σ (x : var Γ σ), comprel Ξ σ (aget x v1) (aget x v2).

Lemma VR_vup Λ {Γ Δ} (Ξ : list (form Δ)) (v1 v2 : vec Γ Δ) :
  VR Ξ v1 v2 -> VR (wk_list Λ Ξ) (vup Λ v1) (vup Λ v2).
Proof.
  intros Hv σ x. vcase x.
  - rewrite !aget_vup_l. apply comprel_refl.
  - rewrite !aget_vup_r'. apply comprel_vup, Hv.
Qed.

(** Des arguments liés par l'égalité aux positions de termes. *)
Lemma argrel_eq {Δ} (Ξ : list (form Δ)) Θ (a1 a2 : Terms.args Sym Δ Θ) :
  Forall (fun θ => cod θ <> P) Θ -> argrel Ξ Θ a1 a2 -> a1 = a2.
Proof.
  intros HΘ Ha. apply args_ext; intros θ z. specialize (Ha θ z).
  assert (Hf : cod θ <> P).
  { clear Ha a1 a2. revert HΘ. induction z as [Θ0 θ0|Θ0 θ0 τ0 z IH]; intros HΘ; inversion HΘ; subst;
      [assumption|apply IH; assumption]. }
  destruct θ as [Λ c]. cbn in Hf. exact (proj1 (comprel_nP Ξ Λ c _ _ Hf) Ha).
Qed.

Lemma gpos_cod Θ : Forall gpos Θ -> Forall (fun θ => cod θ <> P) Θ.
Proof. intros H. eapply Forall_impl; [|exact H]. intros θ [[_ Hc] _]; exact Hc. Qed.

Lemma gpos_rpos Θ : Forall gpos Θ -> Forall rpos Θ.
Proof. intros H. eapply Forall_impl; [|exact H]. intros θ [[Hd _] _]; unfold rpos; rewrite Hd; constructor. Qed.

Theorem repl_mut :
  (forall Γ s (t : tm Γ s), vctx Γ -> forall Δ (v1 v2 : vec Γ Δ) (Ξ : list (form Δ)),
      VR Ξ v1 v2 -> comprel Ξ (ι s) (vsubst t v1) (vsubst t v2)) /\
  (forall Γ Θ (a : Terms.args Sym Γ Θ), vctx Γ -> Forall rpos Θ -> forall Δ (v1 v2 : vec Γ Δ) (Ξ : list (form Δ)),
      VR Ξ v1 v2 -> argrel Ξ Θ (vsubst_args a v1) (vsubst_args a v2)).
Proof.
  apply tm_args_ind.
  - intros Γ σx x a IH HΓ Δ v1 v2 Ξ Hv.
    assert (Hf : Forall gpos (dom σx)) by apply (HΓ _ x).
    assert (Ha : vsubst_args a v1 = vsubst_args a v2).
    { apply (argrel_eq Ξ _ _ _ (gpos_cod _ Hf)). apply (IH HΓ (gpos_rpos _ Hf)). exact Hv. }
    change (comprel Ξ (ι (cod σx)) (happ σx (aget x v1) (vsubst_args a v1)) (happ σx (aget x v2) (vsubst_args a v2))).
    rewrite <- Ha. specialize (Hv σx x). destruct σx as [Λx c]. cbn [dom cod] in *.
    destruct (Sdec c P) as [e|n].
    + subst c. apply comprel_P. rewrite wk_list_nil. apply (proj1 (comprel_P Ξ Λx _ _)) in Hv.
      apply eqv_happ, Hv.
    + apply (comprel_nP Ξ [] c _ _ n). apply (proj1 (comprel_nP Ξ Λx c _ _ n)) in Hv. rewrite Hv. reflexivity.
  - intros Γ σx c a IH HΓ Δ v1 v2 Ξ Hv.
    change (comprel Ξ (ι (cod σx)) (tsym c (vsubst_args a v1)) (tsym c (vsubst_args a v2))).
    destruct (sym_rpos σx c) as [Hr Hn].
    pose proof (IH HΓ Hr Δ v1 v2 Ξ Hv) as Ha.
    destruct σx as [Θ c0]. cbn [dom cod] in *. destruct (Sdec c0 P) as [e|n].
    + subst c0. apply comprel_P. rewrite wk_list_nil. apply Hcong, Ha.
    + apply (comprel_nP Ξ [] c0 _ _ n). f_equal. apply (argrel_eq Ξ _ _ _ (Hn n) Ha).
  - intros Γ HΓ _ Δ v1 v2 Ξ Hv θ z. destruct (var_nil z).
  - intros Γ σx Θ u IHu a IHa HΓ HΘ Δ v1 v2 Ξ Hv. inversion HΘ as [|? ? Hp HΘ']; subst.
    intros θ z. revert θ z. refine (var_inv _ _ _).
    + change (comprel Ξ σx (vsubst_tms u v1) (vsubst_tms u v2)). rewrite !vsubst_tms_vup.
      destruct σx as [Λ c]. cbn [dom cod] in *.
      assert (HΛ : Forall fpos Λ) by exact Hp.
      pose proof (IHu (vctx_app Λ Γ HΛ HΓ) _ _ _ _ (VR_vup Λ Ξ v1 v2 Hv)) as Hu.
      destruct (Sdec c P) as [e|n].
      * subst c. apply comprel_P. apply (proj1 (comprel_P _ [] _ _)) in Hu. rewrite wk_list_nil in Hu. exact Hu.
      * apply (comprel_nP Ξ Λ c _ _ n). exact (proj1 (comprel_nP _ [] c _ _ n) Hu).
    + intros θ z. exact (IHa HΓ HΘ' Δ v1 v2 Ξ Hv θ z).
Qed.

(** Remplacer, dans une continuation, la formule de tête par une équivalente. *)
Lemma repl_sub0 {Δ} Λ (K : form (Spec Λ P :: Δ)) (A1 A2 : tm (Λ ++ Δ) P) (Ξ : list (form Δ)) :
  Forall gpos Λ -> vctx Δ -> eqv (wk_list Λ Ξ) A1 A2 ->
  eqv Ξ (sub0 (σ := Spec Λ P) K A1) (sub0 (σ := Spec Λ P) K A2).
Proof.
  intros HΛ HΔ HAq.
  assert (HK : vctx (Spec Λ P :: Δ)).
  { intros σ x. revert σ x. refine (var_inv _ _ _); [exact HΛ|intros σ y; apply HΔ, y]. }
  pose proof (proj1 repl_mut _ _ K HK Δ (@acons _ Sym Δ (Spec Λ P) _ A1 (vid Δ))
                (@acons _ Sym Δ (Spec Λ P) _ A2 (vid Δ)) Ξ) as H.
  unfold sub0. apply (proj1 (comprel_P Ξ [] _ _)) in H; [rewrite wk_list_nil in H; exact H|].
  intros σ x. revert σ x. refine (var_inv _ _ _).
  - apply comprel_P, HAq.
  - intros σ y. apply comprel_refl.
Qed.

(** Cas d'un trou propositionnel. *)
Lemma repl_hole {Δ} (K : form (ι P :: Δ)) (A1 A2 : form Δ) (Ξ : list (form Δ)) :
  vctx Δ -> eqv Ξ A1 A2 -> eqv Ξ (vsubst K (inst1 A1)) (vsubst K (inst1 A2)).
Proof.
  intros HΔ HAq. exact (repl_sub0 [] K A1 A2 Ξ (Forall_nil _) HΔ ltac:(rewrite wk_list_nil; exact HAq)).
Qed.


(** *** Renommage du terme source *)

Lemma vpre_vup Λ {Γ Δ Ω} (ρ : ren Γ Δ) (W : vec Δ Ω) : vpre (upr Λ ρ) (vup Λ W) = vup Λ (vpre ρ W).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre. vcase x.
  - rewrite upr_vl, !aget_vup_l. reflexivity.
  - rewrite upr_vr, !aget_vup_r', aget_vpre. reflexivity.
Qed.

Lemma vpre_vren {Γ Δ Ω Ω'} (ρ : ren Γ Δ) (W : vec Δ Ω) (ξ : ren Ω Ω') : vpre ρ (vren W ξ) = vren (vpre ρ W) ξ.
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre. unfold vren. rewrite !aget_vmap, aget_vpre.
  reflexivity.
Qed.

Lemma vpre_acons1 {Γ Γ' Δ a} (ρ : ren Γ Γ') (v : tm Δ a) (W : vec Γ' Δ) :
  vpre (upr [ι a] ρ) (@acons _ Sym Δ (ι a) Γ' v W) = @acons _ Sym Δ (ι a) Γ v (vpre ρ W).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre. revert σ x. refine (var_inv _ _ _); [reflexivity|].
  intros σ y. change (upr [ι a] ρ σ (vs y)) with (upr [ι a] ρ σ (vr [ι a] y)). rewrite upr_vr.
  cbn [aget atl vr]. rewrite aget_vpre. reflexivity.
Qed.

Theorem tr_sren_mut :
  (forall Γ s (t : tm' Γ s) Γ' (ρ : ren Γ Γ') Δ r (W : vec Γ' Δ) (sp : spine Δ s r) K,
      TR (ren_tm t ρ) Δ r W sp K = TR t Δ r (vpre ρ W) sp K) /\
  (forall Γ Θ (a : args' Γ Θ) Γ' (ρ : ren Γ Γ') Δ (W : vec Γ' Δ) K,
      TRA (ren_args a ρ) Δ W K = TRA a Δ (vpre ρ W) K).
Proof.
  apply tm_args_ind2.
  - intros Γ σx x a IH _ Γ' ρ Δ r W sp K. cbn [ren_tm tr]. rewrite IH, aget_vpre. reflexivity.
  - intros Γ σx c a IH Hc Γ' ρ Δ r W sp K. destruct c as [σ1 c0|]; cbn [ren_tm tr]; [|rewrite IH; reflexivity].
    revert a IH Hc sp. destruct (view σ1 c0) as [a0 b0 c1 w0|a0 b0 c1 w0|σ2 c2]; intros a IH Hc sp.
    + pose proof (Hc _ vz) as Ht. cbn [aget] in Ht. rewrite (args1_inv a). cbn [ren_args]. cbn beta iota zeta.
      change (cod (Spec [Spec [ι a0] b0] c1)) with c1 in *.
      revert K. destruct sp as [s0|a1 b1 c2 r1 w1 v sp']; intros K; [reflexivity|].
      unfold trlam. destruct (Sdec a1 a0) as [e1|]; [|reflexivity].
      destruct (Sdec b1 b0) as [e2|]; [|reflexivity]. subst a1 b1. cbn [eq_rect].
      unfold ren_tms. cbn [dom]. rewrite Ht. f_equal. apply vpre_acons1.
    + pose proof (Hc _ vz) as HF. pose proof (Hc _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
      rewrite (args2_inv a). cbn [ren_args]. cbn beta iota zeta. cbn [fst snd].
      unfold ren_tms. cbn [dom]. rewrite Hu, HF, vpre_vren. reflexivity.
    + rewrite IH. reflexivity.
  - reflexivity.
  - intros Γ σx Θ u IHu a IHa Γ' ρ Δ W K. destruct σx as [Λ c]. cbn [ren_args tra].
    destruct (Sdec c P) as [e|n].
    + rewrite IHa, IHu, vpre_vup. reflexivity.
    + destruct Λ as [|λ Λ]; [|reflexivity]. rewrite IHu, IHa, vpre_vren. reflexivity.
Qed.

Lemma tr_sren {Γ s} (t : tm' Γ s) {Γ'} (ρ : ren Γ Γ') {Δ r} (W : vec Γ' Δ) (sp : spine Δ s r) K :
  TR (ren_tm t ρ) Δ r W sp K = TR t Δ r (vpre ρ W) sp K.
Proof. apply (proj1 tr_sren_mut). Qed.

Lemma wkv_nil {Δ} : wkv (Sym := Sym) [] Δ = vid Δ.
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_wkv, aget_vid. reflexivity.
Qed.

Lemma vsubst_tvar {Γ Δ σ} (x : var Γ σ) (a : Terms.args XSym Γ (dom σ)) (v : Vectors.vec XSym Γ Δ) :
  vsubst (tvar x a) v = happ σ (aget x v) (vsubst_args a v).
Proof. reflexivity. Qed.

Lemma vsubst_args_one {Γ Δ σ} (u : Terms.tms XSym Γ σ) (v : Vectors.vec XSym Γ Δ) :
  vsubst_args (@acons _ XSym Γ σ [] u anil) v = @acons _ XSym Δ σ [] (vsubst_tms u v) anil.
Proof. rewrite vsubst_args_acons. f_equal. Qed.

Lemma vsubst_args_two {Γ Δ σ1 σ2} (u1 : Terms.tms XSym Γ σ1) (u2 : Terms.tms XSym Γ σ2) (v : Vectors.vec XSym Γ Δ) :
  vsubst_args (@acons _ XSym Γ σ1 _ u1 (@acons _ XSym Γ σ2 [] u2 anil)) v
  = @acons _ XSym Δ σ1 _ (vsubst_tms u1 v) (@acons _ XSym Δ σ2 [] (vsubst_tms u2 v) anil).
Proof. rewrite !vsubst_args_acons. reflexivity. Qed.

(** *** Le lemme de substitution, pour des composantes termes *)

(** Une composante terme : un terme sans lieur, de sorte autre que P et
    non flèche, de valeur déterminée. *)
Definition cdet {Γ0 Δ} (Ξ : list (form Δ)) (θ : spec Srt) (w0 : vec Γ0 Δ) :
  Terms.tms XSym Γ0 θ -> Terms.tms Sym Δ θ -> Prop :=
  match θ as θ0 return Terms.tms XSym Γ0 θ0 -> Terms.tms Sym Δ θ0 -> Prop with
  | Spec [] c => fun u τ => c <> P /\ noarr c /\ DetT Ξ u w0 τ
  | _ => fun _ _ => False
  end.

(** Relation entre la substitution v (dans L'), l'environnement w0 de la
    cible et l'environnement w de la source : chaque composante est soit
    une variable (lue de la même façon des deux côtés), soit un terme sans
    lieur de valeur déterminée. *)
Definition CRA {Γ1 Γ0 Δ} (Ξ : list (form Δ)) (v : Vectors.vec XSym Γ1 Γ0) (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) : Prop :=
  forall σ (x : var Γ1 σ),
    (exists y : var Γ0 σ, aget x v = eta σ y /\ aget x w = aget y w0) \/ cdet Ξ σ w0 (aget x v) (aget x w).

Lemma DetT_sren {Γ Γ' s Δ} (Ξ : list (form Δ)) (u : tm' Γ s) (ρ : ren Γ Γ') (W : vec Γ' Δ) τ :
  DetT Ξ u (vpre ρ W) τ -> DetT Ξ (ren_tm u ρ) W τ.
Proof. intros Hd Δ' ρ' Ξ' Hi K. rewrite tr_sren, vpre_vren. apply Hd, Hi. Qed.

Lemma DetT_rid {Γ s Δ} (Ξ : list (form Δ)) (t : tm' Γ s) (W : vec Γ Δ) τ K :
  DetT Ξ t W τ -> eqv Ξ (TR t Δ s W snil K) (vsubst K (inst1 τ)).
Proof.
  intros Hd. pose proof (Hd Δ rid Ξ ltac:(rewrite ren_list_id; apply incl_refl) K) as H.
  rewrite vren_id, ren_id in H. exact H.
Qed.

Lemma cdet_ren {Γ0 Δ Δ'} (Ξ : list (form Δ)) (Ξ' : list (form Δ')) θ (w0 : vec Γ0 Δ) u τ (ρ : ren Δ Δ') :
  cdet Ξ θ w0 u τ -> incl (ren_list Ξ ρ) Ξ' -> cdet Ξ' θ (vren w0 ρ) u (ren_tms τ ρ).
Proof.
  destruct θ as [[|λ Λ] c]; [|intros []]. cbn [cdet]. intros [n [Hna Hd]] Hi. split; [exact n|split; [exact Hna|]].
  rewrite ren_tms_nil. exact (DetT_mono _ _ _ _ _ _ Hd Hi).
Qed.

Lemma cdet_vup Λ' {Γ0 Δ} (Ξ : list (form Δ)) θ (w0 : vec Γ0 Δ) u τ :
  cdet Ξ θ w0 u τ -> cdet (wk_list Λ' Ξ) θ (vup Λ' w0) (ren_tms u (wk Λ')) (ren_tms τ (wk Λ')).
Proof.
  destruct θ as [[|λ Λ] c]; [|intros []]. cbn [cdet]. intros [n [Hna Hd]]. split; [exact n|split; [exact Hna|]].
  rewrite !ren_tms_nil. apply DetT_sren.
  assert (E : vren w0 (wk Λ') = vpre (wk Λ') (vup Λ' w0)) by (symmetry; apply vpre_wk_vup).
  pose proof (DetT_mono _ _ _ _ (wk Λ') (wk_list Λ' Ξ) Hd (incl_refl _)) as Hd'.
  cbn [dom cod app] in Hd' |- *. rewrite E in Hd'. exact Hd'.
Qed.

(** Sous un lambda : la variable liée reçoit la même valeur des deux côtés. *)
Lemma cdet_cons1 a {Γ0 Δ} (Ξ : list (form Δ)) θ (w0 : vec Γ0 Δ) (val : tm Δ a) u τ :
  cdet Ξ θ w0 u τ -> cdet Ξ θ (@acons _ Sym Δ (ι a) Γ0 val w0) (ren_tms u (wk [ι a])) τ.
Proof.
  destruct θ as [[|λ Λ] c]; [|intros []]. cbn [cdet]. intros [n [Hna Hd]]. split; [exact n|split; [exact Hna|]].
  rewrite ren_tms_nil. apply DetT_sren.
  refine (eq_rect _ (fun W => DetT Ξ u W τ) Hd _ _). symmetry. apply vpre_wk1.
Qed.

Lemma CRA_ren {Γ1 Γ0 Δ Δ'} (Ξ : list (form Δ)) (Ξ' : list (form Δ')) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ)
  (ρ : ren Δ Δ') :
  CRA Ξ v w0 w -> incl (ren_list Ξ ρ) Ξ' -> CRA Ξ' v (vren w0 ρ) (vren w ρ).
Proof.
  intros Hc Hi σ x. assert (E : aget x (vren w ρ) = ren_tms (aget x w) ρ) by (unfold vren; rewrite aget_vmap; reflexivity).
  rewrite E. destruct (Hc σ x) as [[y [Hv Hw]]|Ht].
  - left. exists y. split; [exact Hv|]. unfold vren. rewrite aget_vmap, Hw. reflexivity.
  - right. exact (cdet_ren _ _ _ _ _ _ _ Ht Hi).
Qed.

Lemma CRA_vup Λ {Γ1 Γ0 Δ} (Ξ : list (form Δ)) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) :
  CRA Ξ v w0 w -> CRA (wk_list Λ Ξ) (vup Λ v) (vup Λ w0) (vup Λ w).
Proof.
  intros Hc σ x. vcase x.
  - left. exists (vl Γ0 z). rewrite !aget_vup_l. split; reflexivity.
  - rewrite !aget_vup_r'. destruct (Hc σ z) as [[y [Hv Hw]]|Ht].
    + left. exists (vr Λ y). rewrite aget_vup_r', Hv, Hw, eta_ren. split; reflexivity.
    + right. exact (cdet_vup Λ _ _ _ _ _ Ht).
Qed.

Lemma aget_vup1_vz {Γ Δ a} (v : Vectors.vec XSym Γ Δ) :
  aget vz (vup [ι a] v) = eta (ι a) (Γ := ι a :: Δ) vz.
Proof. exact (aget_vup_l [ι a] v vz). Qed.

Lemma aget_vup1_vs {Γ Δ a σ} (v : Vectors.vec XSym Γ Δ) (z : var Γ σ) :
  aget (vs z) (vup [ι a] v) = ren_tms (aget z v) (wk [ι a]).
Proof. exact (aget_vup_r' [ι a] v z). Qed.

Lemma CRA_cons1 a {Γ1 Γ0 Δ} (Ξ : list (form Δ)) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) (val : tm Δ a) :
  CRA Ξ v w0 w ->
  CRA Ξ (vup [ι a] v) (@acons _ Sym Δ (ι a) Γ0 val w0) (@acons _ Sym Δ (ι a) Γ1 val w).
Proof.
  intros Hc σ x. revert σ x. refine (var_inv _ _ _).
  - left. exists vz. split; [apply aget_vup1_vz|reflexivity].
  - intros σ z. change (aget (vs z) (vup [ι a] v)) with (aget (vr [ι a] z) (vup [ι a] v)).
    rewrite aget_vup_r'. cbn [aget atl]. destruct (Hc σ z) as [[y [Hv Hw]]|Ht].
    + left. exists (vs y). rewrite Hv, eta_ren. split; [reflexivity|exact Hw].
    + right. exact (cdet_cons1 a _ _ _ val _ _ Ht).
Qed.

Lemma vctx_app' Θ {Δ} : Forall spos Θ -> vctx Δ -> vctx (Θ ++ Δ).
Proof.
  intros HΘ HΔ σ x. vcase x; [|apply HΔ, z].
  clear HΔ. revert HΘ. induction z as [Λ0 σ0|Λ0 σ0 τ0 z IH]; intros HΘ.
  - inversion HΘ as [|? ? [[[Hd _] _]|[_ Hd]]]; subst; unfold vspec; [rewrite Hd; constructor|exact Hd].
  - inversion HΘ; subst. apply IH; assumption.
Qed.

Lemma vspec_spos σ : vspec σ -> Forall spos (dom σ).
Proof. intros Hv. eapply Forall_impl; [|exact Hv]. intros θ Hθ; left; exact Hθ. Qed.

Hypothesis HDfs : Forall spos Df.

Lemma vctx_cons1 {Δ} a : vctx Δ -> vctx (ι a :: Δ).
Proof. apply vctx_cons, vspec_ι. Qed.

(** Une pile vide en une sorte non flèche. *)
Lemma spine_noarr {Δ c r} (sp : spine Δ c r) (Q : forall r, spine Δ c r -> form (ι r :: Δ) -> Prop) :
  noarr c -> (forall K, Q c snil K) -> forall K, Q r sp K.
Proof.
  intros Hn Hq K. destruct (noarr_snil sp Hn) as [e Hsp]. subst r. cbn in Hsp. subst sp. apply Hq.
Qed.

Theorem hoistA_mut :
  (forall Γ1 s (χ : tm' Γ1 s), vctx Γ1 -> forall Γ0 (v : Vectors.vec XSym Γ1 Γ0) Δ r (w0 : vec Γ0 Δ) (w : vec Γ1 Δ)
      (sp : spine Δ s r) (Ξ : list (form Δ)), vctx Δ -> CRA Ξ v w0 w -> noarr r ->
      forall K, eqv Ξ (TR (vsubst χ v) Δ r w0 sp K) (TR χ Δ r w sp K)) /\
  (forall Γ1 Θ (a : args' Γ1 Θ), vctx Γ1 -> Forall spos Θ -> forall Γ0 (v : Vectors.vec XSym Γ1 Γ0) Δ
      (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) (Ξ : list (form Δ)), vctx Δ -> CRA Ξ v w0 w ->
      forall K, eqv Ξ (TRA (vsubst_args a v) Δ w0 K) (TRA a Δ w K)).
Proof.
  apply tm_args_ind2.
  - intros Γ1 σx x a IH _ HΓ1 Γ0 v Δ r w0 w sp Ξ HΔ Hc Hr K. rewrite vsubst_tvar.
    destruct (Hc σx x) as [[y [Hv Hw]]|Ht].
    + rewrite Hv, happ_eta. cbn [tr]. rewrite Hw. apply (IH HΓ1 (vspec_spos _ (HΓ1 _ x)) Γ0 v Δ w0 w Ξ HΔ Hc).
    + destruct σx as [[|λ Λ] c]; [|destruct Ht]. destruct Ht as [Hn [Hna Hd]]. cbn [cod] in sp |- *.
      revert K. apply (spine_noarr sp (fun r sp K => eqv Ξ (TR (happ (ι c) (aget x v) (vsubst_args a v)) Δ r w0 sp K)
                                        (TR (tvar x a) Δ r w sp K)) Hna). intros K.
      rewrite (args_nil a). change (vsubst_args (@anil _ XSym Γ1) v) with (@anil _ XSym Γ0).
      rewrite happ_nil. cbn [tr tra]. rewrite spK_nil. unfold plug. rewrite wkv_nil.
      exact (DetT_rid _ _ _ _ _ Hd).
  - intros Γ1 σx c a IH Hcomp HΓ1 Γ0 v Δ r w0 w sp Ξ HΔ Hc Hr K.
    change (vsubst (tsym c a) v) with (tsym c (vsubst_args a v)).
    destruct c as [σ1 c0|]; cbn [tr]; [|apply (IH HΓ1 HDfs Γ0 v Δ w0 w Ξ HΔ Hc)].
    pose proof (HsymV σ1 c0) as Hs. revert a IH Hcomp sp Hs K.
    destruct (view σ1 c0) as [a0 b0 c1 w1|a0 b0 c1 w1|σ2 c2]; intros a IH Hcomp sp Hs K.
    + pose proof (Hcomp _ vz) as Ht. cbn [aget] in Ht. cbn [dom cod] in *. rewrite (args1_inv a), vsubst_args_one.
      cbn beta iota zeta.
      revert K Hr. destruct sp as [s0|a1 b1 c2 r1 w2 val sp']; intros K Hr; [exfalso; exact (Hr _ _ w1)|].
      destruct (Harr_inj _ _ _ _ _ w2 w1) as [-> ->]. rewrite !trlam_cons.
      rewrite vsubst_tms_vup. cbn [dom].
      exact (Ht (vctx_cons1 a0 HΓ1) _ _ _ _ _ _ sp' Ξ HΔ (CRA_cons1 a0 Ξ v w0 w val Hc) Hr K).
    + pose proof (Hcomp _ vz) as HF. pose proof (Hcomp _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
      cbn [dom cod] in *. rewrite (args2_inv a), vsubst_args_two. cbn beta iota zeta. cbn [fst snd]. rewrite !vsubst_tms_nil.
      destruct (Harr_dom _ _ _ w1) as [_ Ha0].
      eapply equiv_trans; [apply (Hu HΓ1 Γ0 v Δ a0 w0 w snil Ξ HΔ Hc Ha0)|]. apply tr_cong.
      apply (HF HΓ1 Γ0 v (ι a0 :: Δ) r _ _ _ _ (vctx_cons1 a0 HΔ)); [|exact Hr].
      apply (CRA_ren Ξ _ v w0 w (wk [ι a0]) Hc). apply incl_refl.
    + destruct Hs as [Hs _]. apply (IH HΓ1 Hs Γ0 v Δ w0 w Ξ HΔ Hc).
  - intros Γ1 HΓ1 _ Γ0 v Δ w0 w Ξ HΔ Hc K. apply equiv_refl.
  - intros Γ1 σx Θ u IHu a IHa HΓ1 HΘ Γ0 v Δ w0 w Ξ HΔ Hc K. inversion HΘ as [|? ? Hp HΘ']; subst.
    rewrite vsubst_args_acons. destruct σx as [Λ c]. cbn [tra].
    assert (HΘΔ : vctx (Θ ++ Δ)) by exact (vctx_app' Θ HΘ' HΔ).
    destruct (Sdec c P) as [e|n].
    + subst c. cbn [castc castP eq_rect eq_sym]. rewrite vsubst_tms_vup. cbn [dom].
      assert (HΛ : Forall gpos Λ) by (destruct Hp as [[[Hd _] _]|[_ Hd]]; [cbn in Hd; subst; constructor|exact Hd]).
      assert (HΛf : Forall fpos Λ) by (eapply Forall_impl; [|exact HΛ]; intros θ [Hθ _]; exact Hθ).
      pose proof (IHu (vctx_app Λ Γ1 HΛf HΓ1) _ _ _ _ _ _ snil _ (vctx_app Λ Δ HΛf HΔ) (CRA_vup Λ Ξ v w0 w Hc)
                    Hnoarr_P hole) as Hu.
      eapply equiv_trans; [apply tra_cong|apply (IHa HΓ1 HΘ' Γ0 v Δ w0 w Ξ HΔ Hc)].
      apply repl_sub0; [exact HΛ|exact HΘΔ|].
      rewrite <- wk_list_app_ren. apply equiv_ren, Hu.
    + destruct Λ as [|λ Λ]; [|apply equiv_refl].
      assert (Hna : noarr c) by (destruct Hp as [[_ Hna]|[Hc' _]]; [exact Hna|exact (False_ind _ (n Hc'))]).
      rewrite vsubst_tms_nil. cbn [app].
      eapply equiv_trans; [apply (IHu HΓ1 Γ0 v Δ c w0 w snil Ξ HΔ Hc Hna)|]. apply tr_cong.
      apply (IHa HΓ1 HΘ' Γ0 v (ι c :: Δ) _ _ _ (vctx_cons1 c HΔ)).
      apply (CRA_ren Ξ _ v w0 w (wk [ι c]) Hc). apply incl_refl.
Qed.


(** *** Valeurs des arguments termes *)

Lemma DetA_nil {Γ Δ} (Ξ : list (form Δ)) (w : vec Γ Δ) : DetA Ξ (@anil _ XSym Γ) w anil.
Proof. intros Δ' ρ' Ξ' Hi' K. cbn [tra vcat ren_args]. rewrite vsubst_vid. apply equiv_refl. Qed.

Lemma DetA_cons {Γ Θ Δ c} (Ξ : list (form Δ)) (u : tm' Γ c) (a : args' Γ Θ) (w : vec Γ Δ) τ τs :
  c <> P -> DetT Ξ u w τ -> DetA Ξ a w τs ->
  DetA Ξ (@acons _ XSym Γ (ι c) Θ u a) w (@acons _ Sym Δ (ι c) Θ τ τs).
Proof.
  intros n Hu Ha Δ' ρ' Ξ' Hi' K. cbn [tra]. destruct (Sdec c P) as [e|n']; [contradiction|].
  eapply equiv_trans; [apply (Hu Δ' ρ' Ξ' Hi')|]. rewrite tra_inst1.
  eapply equiv_trans; [apply (Ha Δ' ρ' Ξ' Hi')|]. rewrite perm_inst2.
  change (ren_args (@acons _ Sym Δ (ι c) _ τ τs) ρ')
    with (@acons _ Sym Δ' (ι c) _ (ren_tms (σ := ι c) τ ρ') (ren_args τs ρ')).
  cbn [vcat]. rewrite ren_tms_nil. apply equiv_refl.
Qed.

Lemma DetA_of_cdet {Γ Θ Δ} (Ξ : list (form Δ)) (a : args' Γ Θ) (w : vec Γ Δ) τs :
  (forall θ (z : var Θ θ), cdet Ξ θ w (aget z a) (aget z τs)) -> DetA Ξ a w τs.
Proof.
  induction Θ as [|θ Θ IH].
  - intros _. rewrite (args_nil a), (args_nil τs). apply DetA_nil.
  - intros H. rewrite (args_eta a), (args_eta τs). specialize (H θ vz) as H0. cbn [aget] in H0.
    destruct θ as [[|λ Λ] c]; [|destruct H0]. destruct H0 as [n [_ Hd]].
    apply (DetA_cons Ξ (ahd a) (atl a) w (ahd τs) (atl τs) n Hd).
    apply IH. intros θ' z. exact (H θ' (vs z)).
Qed.

Lemma vctx_okctx Γ : vctx Γ -> okctx P Γ.
Proof.
  intros H σ x. specialize (H σ x). unfold okhd. eapply Forall_impl; [|exact H].
  intros θ [[Hd _] Hn]; left; split; assumption.
Qed.

(** Ouverture d'une suite d'arguments termes : chacun reçoit une valeur. *)
Lemma open_fargs {Γ Θ} (a : args' Γ Θ) : okctx P Γ -> Forall gpos Θ ->
  forall Δ (w : vec Γ Δ) (Ξ : list (form Δ)) (G : form Δ),
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 (τs : Terms.args Sym Δ1 Θ), (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     (forall θ (z : var Θ θ), cdet Ξ1 θ (vren w ρ) (aget z a) (aget z τs)) -> Ξ1 ⊢ ren_tm G ρ) ->
  Ξ ⊢ G.
Proof.
  intros HΓ. induction a as [Γ0|Γ0 σ Θ0 u a IH]; intros HΘ Δ w Ξ G Hk.
  - rewrite <- (ren_id G). apply (Hk Δ rid Ξ anil); [exact (fun H => H)|rewrite ren_list_id; apply incl_refl|].
    intros θ z; destruct (var_nil z).
  - inversion HΘ as [|? ? [[Hd Hc] Hna] HΘ']; subst. destruct σ as [Λ c]. cbn in Hd, Hc, Hna. subst Λ.
    apply (proj1 open_mut _ _ u HΓ Δ c w snil Ξ G Hna). intros Δ1 ρ1 Ξ1 τu HV1 Hi1 Hdu.
    apply (IH HΓ HΘ' Δ1 (vren w ρ1) Ξ1 (ren_tm G ρ1)). intros Δ2 ρ2 Ξ2 τs HV2 Hi2 Hda.
    rewrite ren_ren, vren_vren in *.
    apply (Hk Δ2 (rcomp ρ1 ρ2) Ξ2 (@acons _ Sym Δ2 (ι c) _ (ren_tm τu ρ2) τs));
      [exact (fun H => HV2 (HV1 H))|exact (incl_ren_comp _ _ _ _ _ Hi1 Hi2)|].
    intros θ z. revert θ z. refine (var_inv _ _ _).
    + cbn [aget ahd cdet]. split; [exact Hc|split; [exact Hna|]]. rewrite <- vren_vren.
      exact (DetT_mono _ _ _ _ _ _ Hdu Hi2).
    + intros θ z. exact (Hda θ z).
Qed.

(** Ouverture pour une équivalence. *)
Lemma eqv_open_tm {Γ s} (t : tm' Γ s) : okctx P Γ -> noarr s ->
  forall Δ (W : vec Γ Δ) (Ξ : list (form Δ)) (A B : form Δ),
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 τ, (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     DetT Ξ1 t (vren W ρ) τ -> eqv Ξ1 (ren_tm A ρ) (ren_tm B ρ)) ->
  eqv Ξ A B.
Proof.
  intros HΓ Hs Δ W Ξ A B Hk. split.
  - apply (proj1 open_mut _ _ t HΓ Δ s W snil _ _ Hs). intros Δ1 ρ Ξ1 τ HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (Hk Δ1 ρ Ξ1 τ HV Hi' Hd)). apply d_ax, Hi; left; reflexivity.
  - apply (proj1 open_mut _ _ t HΓ Δ s W snil _ _ Hs). intros Δ1 ρ Ξ1 τ HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (equiv_sym P C R _ _ _ (Hk Δ1 ρ Ξ1 τ HV Hi' Hd))). apply d_ax, Hi; left; reflexivity.
Qed.

Lemma eqv_open_fargs {Γ Θ} (a : args' Γ Θ) : okctx P Γ -> Forall gpos Θ ->
  forall Δ (W : vec Γ Δ) (Ξ : list (form Δ)) (A B : form Δ),
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 (τs : Terms.args Sym Δ1 Θ), (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     (forall θ (z : var Θ θ), cdet Ξ1 θ (vren W ρ) (aget z a) (aget z τs)) -> eqv Ξ1 (ren_tm A ρ) (ren_tm B ρ)) ->
  eqv Ξ A B.
Proof.
  intros HΓ HΘ Δ W Ξ A B Hk. split.
  - apply (open_fargs a HΓ HΘ Δ W _ _). intros Δ1 ρ Ξ1 τs HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (Hk Δ1 ρ Ξ1 τs HV Hi' Hd)). apply d_ax, Hi; left; reflexivity.
  - apply (open_fargs a HΓ HΘ Δ W _ _). intros Δ1 ρ Ξ1 τs HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (equiv_sym P C R _ _ _ (Hk Δ1 ρ Ξ1 τs HV Hi' Hd))). apply d_ax, Hi; left; reflexivity.
Qed.

Lemma ren_inst1 {Δ Δ' s} (K : form (ι s :: Δ)) (X : tm Δ s) (ρ : ren Δ Δ') :
  ren_tm (vsubst K (inst1 X)) ρ = vsubst (ren_tm K (upr [ι s] ρ)) (inst1 (ren_tm X ρ)).
Proof.
  rewrite ren_vsubst, vsubst_ren. f_equal. apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
  unfold vren. rewrite aget_vmap. revert σ x. refine (var_inv _ _ _).
  - cbn [aget ahd inst1]. apply ren_tms_nil.
  - intros σ y. change (upr [ι s] ρ σ (vs y)) with (upr [ι s] ρ σ (vr [ι s] y)). rewrite upr_vr.
    cbn [aget atl inst1 vr]. rewrite !aget_vid, eta_ren. reflexivity.
Qed.

(** Une formule de L' envoie sa valeur dans la continuation. *)
Lemma prop_hoist {Γ} (ψ : tm' Γ P) : okctx P Γ -> forall Δ (W : vec Γ Δ) (Ξ : list (form Δ)) K,
  vctx Δ -> eqv Ξ (TR ψ Δ P W snil K) (vsubst K (inst1 (TR ψ Δ P W snil hole))).
Proof.
  intros HΓ Δ W Ξ K HΔ. apply (eqv_open_tm ψ HΓ Hnoarr_P Δ W). intros Δ1 ρ Ξ1 τ HV Hi Hd.
  rewrite ren_inst1, !tr_ren. cbn [ren_sp].
  change (ren_tm (hole (Sym := Sym) (P := P) (Δ := Δ)) (upr [ι P] ρ)) with (hole (Sym := Sym) (P := P) (Δ := Δ1)).
  eapply equiv_trans; [apply DetT_rid, Hd|]. apply equiv_sym.
  apply repl_hole; [apply HV, HΔ|]. pose proof (DetT_rid Ξ1 ψ (vren W ρ) τ hole Hd) as H.
  unfold hole at 2 in H. rewrite vsubst_var0 in H. exact H.
Qed.


(** *** Le lemme de substitution général *)

Lemma vup_cat Λ {Δ Γ Γ'} (w : vec Δ Γ) (a : Terms.args Sym Γ' Λ) (w' : vec Γ Γ') :
  vcomp (vup Λ w) (vcat Λ a w') = vcat Λ a (vcomp w w').
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. vcase x.
  - rewrite aget_vup_l, !aget_vcat_l, vsubst_eta, aget_vcat_l. reflexivity.
  - rewrite aget_vup_r', !aget_vcat_r, vsubst_tms_ren', vpre_wk, aget_vcomp. reflexivity.
Qed.

Lemma tr_vcat {Γ Λ} (u : tm' (Λ ++ Γ) P) {Δ1} (W : vec Γ Δ1) (τs : Terms.args Sym Δ1 Λ) :
  TR u Δ1 P (vcat Λ τs W) snil hole = vsubst (TR u (Λ ++ Δ1) P (vup Λ W) snil hole) (vcat Λ τs (vid Δ1)).
Proof. rewrite tr_vsubst, vup_cat, vcomp_vid_r. reflexivity. Qed.

Lemma tra_ren {Γ Θ} (a : args' Γ Θ) {Δ Δ'} (w : vec Γ Δ) K (ρ : ren Δ Δ') :
  ren_tm (TRA a Δ w K) ρ = TRA a Δ' (vren w ρ) (ren_tm K (upr Θ ρ)).
Proof. rewrite ren_as_vsubst, tra_vsubst, vcomp_vpre_vid. f_equal. apply (vsubst_vup_vpre Θ K ρ). Qed.

Lemma plug_ren {Δ Δ' s} Θ (K : form (ι s :: Δ)) (τ : tm (Θ ++ Δ) s) (ρ : ren Δ Δ') :
  ren_tm (plug Θ K τ) (upr Θ ρ) = plug Θ (ren_tm K (upr [ι s] ρ)) (ren_tm τ (upr Θ ρ)).
Proof.
  rewrite !ren_as_vsubst. rewrite <- (vup_vpre Θ ρ). rewrite plug_vsubst. f_equal. f_equal.
  apply (vup_vpre [ι s] ρ).
Qed.

Lemma DetA_rid {Γ Θ Δ} (Ξ : list (form Δ)) (a : args' Γ Θ) (W : vec Γ Δ) τs K :
  DetA Ξ a W τs -> eqv Ξ (TRA a Δ W K) (vsubst K (vcat Θ τs (vid Δ))).
Proof.
  intros Hd. pose proof (Hd Δ rid Ξ ltac:(rewrite ren_list_id; apply incl_refl) K) as H.
  rewrite vren_id, ren_args_id in H. exact H.
Qed.

Lemma ren_list_wk_upr Λ {Δ Δ'} (Ξ : list (form Δ)) (ρ : ren Δ Δ') :
  ren_list (wk_list Λ Ξ) (upr Λ ρ) = wk_list Λ (ren_list Ξ ρ).
Proof.
  unfold wk_list. fold (ren_list Ξ (wk Λ)). fold (ren_list (ren_list Ξ ρ) (wk Λ)).
  rewrite !ren_list_ren. apply ren_list_ext. intros σ y. unfold rcomp. change (wk Λ σ y) with (vr Λ y).
  rewrite upr_vr. reflexivity.
Qed.

(** Composantes formules : le corps de L est équivalent à la traduction. *)
Definition cform {Γ0 Δ} (Ξ : list (form Δ)) (θ : spec Srt) (w0 : vec Γ0 Δ) :
  Terms.tms XSym Γ0 θ -> Terms.tms Sym Δ θ -> Prop :=
  match θ as θ0 return Terms.tms XSym Γ0 θ0 -> Terms.tms Sym Δ θ0 -> Prop with
  | Spec Λ c => fun u A =>
      match Sdec c P with
      | left e => Forall gpos Λ /\
                  eqv (wk_list Λ Ξ) (castP P e A) (TR u (Λ ++ Δ) c (vup Λ w0) snil (castP P e (var0 vz)))
      | right _ => False
      end
  end.

Definition CRF {Γ1 Γ0 Δ} (Ξ : list (form Δ)) (v : Vectors.vec XSym Γ1 Γ0) (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) : Prop :=
  forall σ (x : var Γ1 σ),
    (exists y : var Γ0 σ, aget x v = eta σ y /\ aget x w = aget y w0) \/
    cdet Ξ σ w0 (aget x v) (aget x w) \/ cform Ξ σ w0 (aget x v) (aget x w).

Lemma cform_ren {Γ0 Δ Δ'} (Ξ : list (form Δ)) (Ξ' : list (form Δ')) θ (w0 : vec Γ0 Δ) u A (ρ : ren Δ Δ') :
  cform Ξ θ w0 u A -> incl (ren_list Ξ ρ) Ξ' -> cform Ξ' θ (vren w0 ρ) u (ren_tms A ρ).
Proof.
  destruct θ as [Λ c]. cbn [cform]. destruct (Sdec c P) as [e|n]; [|intros []].
  subst c. cbn [castP eq_rect]. intros [HΛ Hq] Hi. split; [exact HΛ|].
  apply (equiv_ren P C R _ _ _ (upr Λ ρ)) in Hq. rewrite ren_list_wk_upr, tr_ren, vren_vup in Hq.
  cbn [ren_sp] in Hq. eapply equiv_mono; [exact Hq|]. apply incl_map, Hi.
Qed.

Lemma cform_vup Λ' {Γ0 Δ} (Ξ : list (form Δ)) θ (w0 : vec Γ0 Δ) u A :
  cform Ξ θ w0 u A -> cform (wk_list Λ' Ξ) θ (vup Λ' w0) (ren_tms u (wk Λ')) (ren_tms A (wk Λ')).
Proof.
  intros Hf. pose proof (cform_ren Ξ (wk_list Λ' Ξ) θ w0 u A (wk Λ') Hf (incl_refl _)) as H.
  destruct θ as [Λ c]. cbn [cform] in *. destruct (Sdec c P) as [e|n]; [|destruct H].
  subst c. cbn [castP eq_rect] in *. destruct H as [HΛ Hq]. split; [exact HΛ|].
  unfold ren_tms. cbn [dom]. rewrite tr_sren, vpre_vup, vpre_wk_vup. exact Hq.
Qed.

Lemma cform_cons1 a {Γ0 Δ} (Ξ : list (form Δ)) θ (w0 : vec Γ0 Δ) (val : tm Δ a) u A :
  cform Ξ θ w0 u A -> cform Ξ θ (@acons _ Sym Δ (ι a) Γ0 val w0) (ren_tms u (wk [ι a])) A.
Proof.
  destruct θ as [Λ c]. cbn [cform]. destruct (Sdec c P) as [e|n]; [|intros []].
  subst c. cbn [castP eq_rect]. intros [HΛ Hq]. split; [exact HΛ|].
  unfold ren_tms. cbn [dom]. rewrite tr_sren, vpre_vup.
  refine (eq_rect _ (fun W => eqv (wk_list Λ Ξ) A (TR u (Λ ++ Δ) P (vup Λ W) snil (var0 vz))) Hq _ _).
  symmetry. apply vpre_wk1.
Qed.

Lemma CRF_ren {Γ1 Γ0 Δ Δ'} (Ξ : list (form Δ)) (Ξ' : list (form Δ')) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ)
  (ρ : ren Δ Δ') :
  CRF Ξ v w0 w -> incl (ren_list Ξ ρ) Ξ' -> CRF Ξ' v (vren w0 ρ) (vren w ρ).
Proof.
  intros Hc Hi σ x. assert (E : aget x (vren w ρ) = ren_tms (aget x w) ρ) by (unfold vren; rewrite aget_vmap; reflexivity).
  rewrite E. destruct (Hc σ x) as [[y [Hv Hw]]|[Ht|Ht]].
  - left. exists y. split; [exact Hv|]. unfold vren. rewrite aget_vmap, Hw. reflexivity.
  - right; left. exact (cdet_ren _ _ _ _ _ _ _ Ht Hi).
  - right; right. exact (cform_ren _ _ _ _ _ _ _ Ht Hi).
Qed.

Lemma CRF_vup Λ {Γ1 Γ0 Δ} (Ξ : list (form Δ)) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) :
  CRF Ξ v w0 w -> CRF (wk_list Λ Ξ) (vup Λ v) (vup Λ w0) (vup Λ w).
Proof.
  intros Hc σ x. vcase x.
  - left. exists (vl Γ0 z). rewrite !aget_vup_l. split; reflexivity.
  - rewrite !aget_vup_r'. destruct (Hc σ z) as [[y [Hv Hw]]|[Ht|Ht]].
    + left. exists (vr Λ y). rewrite aget_vup_r', Hv, Hw, eta_ren. split; reflexivity.
    + right; left. exact (cdet_vup Λ _ _ _ _ _ Ht).
    + right; right. exact (cform_vup Λ _ _ _ _ _ Ht).
Qed.

Lemma CRF_cons1 a {Γ1 Γ0 Δ} (Ξ : list (form Δ)) v (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) (val : tm Δ a) :
  CRF Ξ v w0 w ->
  CRF Ξ (vup [ι a] v) (@acons _ Sym Δ (ι a) Γ0 val w0) (@acons _ Sym Δ (ι a) Γ1 val w).
Proof.
  intros Hc σ x. revert σ x. refine (var_inv _ _ _).
  - left. exists vz. split; [apply aget_vup1_vz|reflexivity].
  - intros σ z. change (aget (vs z) (vup [ι a] v)) with (aget (vr [ι a] z) (vup [ι a] v)).
    rewrite aget_vup_r'. cbn [aget atl]. destruct (Hc σ z) as [[y [Hv Hw]]|[Ht|Ht]].
    + left. exists (vs y). rewrite Hv, eta_ren. split; [reflexivity|exact Hw].
    + right; left. exact (cdet_cons1 a _ _ _ val _ _ Ht).
    + right; right. exact (cform_cons1 a _ _ _ val _ _ Ht).
Qed.

Lemma CRA_of_cat {Γ0 Λ Δ1} (Ξ1 : list (form Δ1)) (a : args' Γ0 Λ) (W : vec Γ0 Δ1) τs :
  (forall θ (z : var Λ θ), cdet Ξ1 θ W (aget z a) (aget z τs)) ->
  CRA Ξ1 (vcat Λ a (vid Γ0)) W (vcat Λ τs W).
Proof.
  intros Hcd σ x. vcase x.
  - right. rewrite !aget_vcat_l. exact (Hcd σ z).
  - left. exists z. rewrite !aget_vcat_r, aget_vid. split; reflexivity.
Qed.

Lemma gpos_fpos Λ : Forall gpos Λ -> Forall fpos Λ.
Proof. intros H. eapply Forall_impl; [|exact H]. intros θ [Hθ _]; exact Hθ. Qed.

Theorem hoistF_mut :
  (forall Γ1 s (χ : tm' Γ1 s), vctx Γ1 -> forall Γ0 (v : Vectors.vec XSym Γ1 Γ0) Δ r (w0 : vec Γ0 Δ) (w : vec Γ1 Δ)
      (sp : spine Δ s r) (Ξ : list (form Δ)), vctx Γ0 -> vctx Δ -> CRF Ξ v w0 w -> noarr r ->
      forall K, eqv Ξ (TR (vsubst χ v) Δ r w0 sp K) (TR χ Δ r w sp K)) /\
  (forall Γ1 Θ (a : args' Γ1 Θ), vctx Γ1 -> Forall spos Θ -> forall Γ0 (v : Vectors.vec XSym Γ1 Γ0) Δ
      (w0 : vec Γ0 Δ) (w : vec Γ1 Δ) (Ξ : list (form Δ)), vctx Γ0 -> vctx Δ -> CRF Ξ v w0 w ->
      forall K, eqv Ξ (TRA (vsubst_args a v) Δ w0 K) (TRA a Δ w K)).
Proof.
  apply tm_args_ind2.
  - intros Γ1 σx x a IH _ HΓ1 Γ0 v Δ r w0 w sp Ξ HΓ0 HΔ Hc Hr K. rewrite vsubst_tvar.
    destruct (Hc σx x) as [[y [Hv Hw]]|[Ht|Ht]].
    + rewrite Hv, happ_eta. cbn [tr]. rewrite Hw.
      apply (IH HΓ1 (vspec_spos _ (HΓ1 _ x)) Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc).
    + destruct σx as [[|λ Λ] c]; [|destruct Ht]. destruct Ht as [Hn [Hna Hd]]. cbn [cod] in sp |- *.
      revert K. apply (spine_noarr sp (fun r sp K => eqv Ξ (TR (happ (ι c) (aget x v) (vsubst_args a v)) Δ r w0 sp K)
                                        (TR (tvar x a) Δ r w sp K)) Hna). intros K.
      rewrite (args_nil a). change (vsubst_args (@anil _ XSym Γ1) v) with (@anil _ XSym Γ0).
      rewrite happ_nil. cbn [tr tra]. rewrite spK_nil. unfold plug. rewrite wkv_nil.
      exact (DetT_rid _ _ _ _ _ Hd).
    + destruct σx as [Λ c]. cbn [cform] in Ht. destruct (Sdec c P) as [e|n]; [|destruct Ht].
      subst c. cbn [castP eq_rect] in Ht. destruct Ht as [HΛ Hq]. cbn [dom cod] in *.
      revert K. apply (spine_noarr sp (fun r sp K => eqv Ξ (TR (happ (Spec Λ P) (aget x v) (vsubst_args a v)) Δ r w0 sp K)
                                        (TR (tvar x a) Δ r w sp K)) Hnoarr_P). intros K.
      rewrite happ_vsubst. cbn [dom].
      apply (eqv_open_fargs (vsubst_args a v) (vctx_okctx Γ0 HΓ0) HΛ Δ w0 Ξ). intros Δ1 ρ Ξ1 τs HV Hi Hcd.
      pose proof (HV HΔ) as HΔ1.
      (* Le côté gauche. *)
      rewrite !tr_ren. cbn [ren_sp]. eapply equiv_trans.
      { apply (proj1 hoistA_mut _ _ (aget x v) (vctx_app Λ Γ0 (gpos_fpos _ HΛ) HΓ0) Γ0 _ Δ1 P _
                 (vcat Λ τs (vren w0 ρ)) snil Ξ1 HΔ1); [apply CRA_of_cat, Hcd|exact Hnoarr_P]. }
      eapply equiv_trans; [apply prop_hoist; [apply vctx_okctx, vctx_app; [apply gpos_fpos|]; assumption|exact HΔ1]|].
      eapply equiv_trans; [apply repl_hole; [exact HΔ1|]|].
      { rewrite tr_vcat. apply equiv_sym.
        pose proof (equiv_ren P C R _ _ _ (upr Λ ρ) Hq) as Hq'. rewrite ren_list_wk_upr, tr_ren, vren_vup in Hq'.
        cbn [ren_sp] in Hq'.
        pose proof (eqv_happ Ξ1 Λ _ _ τs (equiv_mono P C R _ _ _ _ Hq' ltac:(apply incl_map, Hi))) as H.
        rewrite !happ_vsubst in H. cbn [dom] in H. exact H. }
      (* Le côté droit. *)
      cbn [tr]. rewrite spK_nil. apply equiv_sym. eapply equiv_trans.
      { apply equiv_sym. apply (IH HΓ1 (vspec_spos _ (HΓ1 _ x)) Γ0 v Δ1 (vren w0 ρ) (vren w ρ) Ξ1 HΓ0 HΔ1).
        exact (CRF_ren _ _ _ _ _ _ Hc Hi). }
      eapply equiv_trans; [apply DetA_rid, DetA_of_cdet, Hcd|].
      rewrite plug_inst. unfold vren. rewrite aget_vmap. apply equiv_refl.
  - intros Γ1 σx c a IH Hcomp HΓ1 Γ0 v Δ r w0 w sp Ξ HΓ0 HΔ Hc Hr K.
    change (vsubst (tsym c a) v) with (tsym c (vsubst_args a v)).
    destruct c as [σ1 c0|]; cbn [tr]; [|apply (IH HΓ1 HDfs Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc)].
    pose proof (HsymV σ1 c0) as Hs. revert a IH Hcomp sp Hs K.
    destruct (view σ1 c0) as [a0 b0 c1 w1|a0 b0 c1 w1|σ2 c2]; intros a IH Hcomp sp Hs K.
    + pose proof (Hcomp _ vz) as Ht. cbn [aget] in Ht. cbn [dom cod] in *. rewrite (args1_inv a), vsubst_args_one.
      cbn beta iota zeta.
      revert K Hr. destruct sp as [s0|a1 b1 c2 r1 w2 val sp']; intros K Hr; [exfalso; exact (Hr _ _ w1)|].
      destruct (Harr_inj _ _ _ _ _ w2 w1) as [-> ->]. rewrite !trlam_cons.
      rewrite vsubst_tms_vup. cbn [dom].
      exact (Ht (vctx_cons1 a0 HΓ1) _ _ _ _ _ _ sp' Ξ (vctx_cons1 a0 HΓ0) HΔ (CRF_cons1 a0 Ξ v w0 w val Hc) Hr K).
    + pose proof (Hcomp _ vz) as HF. pose proof (Hcomp _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
      cbn [dom cod] in *. rewrite (args2_inv a), vsubst_args_two. cbn beta iota zeta. cbn [fst snd]. rewrite !vsubst_tms_nil.
      destruct (Harr_dom _ _ _ w1) as [_ Ha0].
      eapply equiv_trans; [apply (Hu HΓ1 Γ0 v Δ a0 w0 w snil Ξ HΓ0 HΔ Hc Ha0)|]. apply tr_cong.
      apply (HF HΓ1 Γ0 v (ι a0 :: Δ) r _ _ _ _ HΓ0 (vctx_cons1 a0 HΔ)); [|exact Hr].
      apply (CRF_ren Ξ _ v w0 w (wk [ι a0]) Hc). apply incl_refl.
    + destruct Hs as [Hs _]. apply (IH HΓ1 Hs Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc).
  - intros Γ1 HΓ1 _ Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc K. apply equiv_refl.
  - intros Γ1 σx Θ u IHu a IHa HΓ1 HΘ Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc K. inversion HΘ as [|? ? Hp HΘ']; subst.
    rewrite vsubst_args_acons. destruct σx as [Λ c]. cbn [tra].
    assert (HΘΔ : vctx (Θ ++ Δ)) by exact (vctx_app' Θ HΘ' HΔ).
    destruct (Sdec c P) as [e|n].
    + subst c. cbn [castc castP eq_rect eq_sym]. rewrite vsubst_tms_vup. cbn [dom].
      assert (HΛ : Forall gpos Λ) by (destruct Hp as [[[Hd _] _]|[_ Hd]]; [cbn in Hd; subst; constructor|exact Hd]).
      pose proof (gpos_fpos _ HΛ) as HΛf.
      pose proof (IHu (vctx_app Λ Γ1 HΛf HΓ1) _ _ _ _ _ _ snil _ (vctx_app Λ Γ0 HΛf HΓ0) (vctx_app Λ Δ HΛf HΔ)
                    (CRF_vup Λ Ξ v w0 w Hc) Hnoarr_P hole) as Hu.
      eapply equiv_trans; [apply tra_cong|apply (IHa HΓ1 HΘ' Γ0 v Δ w0 w Ξ HΓ0 HΔ Hc)].
      apply repl_sub0; [exact HΛ|exact HΘΔ|].
      rewrite <- wk_list_app_ren. apply equiv_ren, Hu.
    + destruct Λ as [|λ Λ]; [|apply equiv_refl].
      assert (Hna : noarr c) by (destruct Hp as [[_ Hna]|[Hc' _]]; [exact Hna|exact (False_ind _ (n Hc'))]).
      rewrite vsubst_tms_nil. cbn [app].
      eapply equiv_trans; [apply (IHu HΓ1 Γ0 v Δ c w0 w snil Ξ HΓ0 HΔ Hc Hna)|]. apply tr_cong.
      apply (IHa HΓ1 HΘ' Γ0 v (ι c :: Δ) _ _ _ HΓ0 (vctx_cons1 c HΔ)).
      apply (CRF_ren Ξ _ v w0 w (wk [ι c]) Hc). apply incl_refl.
Qed.


(** *** Ouverture des métavariables termes d'une règle *)

(** Une spécification de métavariable de règle : un terme sans lieur de
    sorte autre que P et non flèche, ou une formule dont les arguments sont
    de tels termes. *)
Definition mspec (σ : spec Srt) : Prop := gpos σ \/ (cod σ = P /\ Forall gpos (dom σ)).

Lemma mspec_vspec σ : mspec σ -> vspec σ.
Proof. intros [[[Hd _] _]|[_ Hd]]; unfold vspec; [rewrite Hd; constructor|exact Hd]. Qed.

Lemma open_vec {Θ Γ0} (v : Vectors.vec XSym Θ Γ0) : Forall mspec Θ -> okctx P Γ0 ->
  forall Δ (w0 : vec Γ0 Δ) (Ξ : list (form Δ)) (G : form Δ),
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 (w : vec Θ Δ1), (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     CRF Ξ1 v (vren w0 ρ) w -> Ξ1 ⊢ ren_tm G ρ) ->
  Ξ ⊢ G.
Proof.
  revert v; induction Θ as [|σ Θ IH]; intros v HΘ HΓ0 Δ w0 Ξ G Hk.
  - rewrite <- (ren_id G). apply (Hk Δ rid Ξ anil); [exact (fun H => H)|rewrite ren_list_id; apply incl_refl|].
    intros σ x; destruct (var_nil x).
  - inversion HΘ as [|? ? Hm HΘ']; subst.
    destruct Hm as [[[Hd Hc] Hna]|[Hc Hd]].
    + destruct σ as [Λ c]. cbn in Hd, Hc, Hna. subst Λ.
      apply (proj1 open_mut _ _ (ahd v) HΓ0 Δ c w0 snil Ξ G Hna). intros Δ1 ρ1 Ξ1 τ HV1 Hi1 Hdu.
      apply (IH (atl v) HΘ' HΓ0 Δ1 (vren w0 ρ1) Ξ1 (ren_tm G ρ1)). intros Δ2 ρ2 Ξ2 w HV2 Hi2 Hc2.
      rewrite ren_ren, vren_vren in *.
      apply (Hk Δ2 (rcomp ρ1 ρ2) Ξ2 (@acons _ Sym Δ2 (ι c) _ (ren_tm τ ρ2) w));
        [exact (fun H => HV2 (HV1 H))|exact (incl_ren_comp _ _ _ _ _ Hi1 Hi2)|].
      intros σ x. revert σ x. refine (var_inv _ _ _).
      * right; left. cbn [aget ahd cdet]. split; [exact Hc|split; [exact Hna|]]. rewrite <- vren_vren.
        exact (DetT_mono _ _ _ _ _ _ Hdu Hi2).
      * intros σ y. exact (Hc2 σ y).
    + destruct σ as [Λ c]. cbn in Hd, Hc. subst c.
      apply (IH (atl v) HΘ' HΓ0 Δ w0 Ξ G). intros Δ1 ρ Ξ1 w HV Hi Hc1.
      apply (Hk Δ1 ρ Ξ1 (@acons _ Sym Δ1 (Spec Λ P) _ (TR (ahd v) (Λ ++ Δ1) P (vup Λ (vren w0 ρ)) snil hole) w) HV Hi).
      intros σ x. revert σ x. refine (var_inv _ _ _).
      * right; right. cbn [aget ahd cform]. rewrite Sdec_refl. cbn [castP eq_rect]. split; [exact Hd|].
        apply equiv_refl.
      * intros σ y. exact (Hc1 σ y).
Qed.

(** *** Transport d'une dérivation le long d'équivalences *)

Lemma deriv_transfer {Γ X} (hs : list X) (f g : X -> form Γ) (B1 B2 : list (form Γ)) G1 G2 :
  (map f hs ++ B1) ⊢ G1 -> incl B1 B2 ->
  (forall h, In h hs -> eqv B2 (f h) (g h)) -> eqv B2 G1 G2 ->
  (map g hs ++ B2) ⊢ G2.
Proof.
  intros Hd Hi Hh [HG _].
  assert (Hw : forall χ, In χ (map f hs ++ B1) -> (map g hs ++ B2) ⊢ χ).
  { intros χ Hχ. apply in_app_or in Hχ as [Hχ|Hχ].
    - apply in_map_iff in Hχ as (h & <- & Hin). destruct (Hh h Hin) as [_ H2].
      apply (deriv_cut' P C R _ (g h)); [apply d_ax, in_or_app; left; apply in_map, Hin|].
      eapply deriv_mono; [exact H2|]. intros χ' [<-|Hχ']; [left; reflexivity|right; apply in_or_app; right; exact Hχ'].
    - apply d_ax, in_or_app; right; apply Hi, Hχ. }
  pose proof (deriv_cut_gen C P R Hd _ Hw) as H1.
  apply (deriv_cut' P C R _ G1); [exact H1|].
  eapply deriv_mono; [exact HG|]. intros χ' [<-|Hχ']; [left; reflexivity|right; apply in_or_app; right; exact Hχ'].
Qed.

(** Deux formules convertibles sont équivalentes. *)
Lemma eqv_conv {Γ} (Ξ : list (form Γ)) A B : conv C A B -> eqv Ξ A B.
Proof.
  intros Hc. split.
  - eapply d_conv; [exact Hc|apply d_ax; left; reflexivity].
  - eapply d_conv; [apply conv_sym, Hc|apply d_ax; left; reflexivity].
Qed.

(** ** La logique étendue L' et la correction de la traduction *)

Lemma Forall_var {Q : spec Srt -> Prop} {Θ σ} (x : var Θ σ) : Forall Q Θ -> Q σ.
Proof.
  induction x as [Θ0 σ0|Θ0 σ0 τ0 x IH]; intros H0; inversion H0; subst; [assumption|apply IH; assumption].
Qed.

Local Notation EL := (el Sdec Df b view φ).

Definition emb_prem {Θ} (p : premise Sym P Θ) : premise XSym P Θ :=
  {| p_ext := p_ext p; p_hyps := map (emb Df b) (p_hyps p); p_goal := emb Df b (p_goal p) |}.

Definition emb_rule (r : drule Sym P) : drule XSym P :=
  {| d_ctx := d_ctx r; d_prems := map emb_prem (d_prems r); d_concl := emb Df b (d_concl r) |}.

(** L'axiome de définition : φ(x⃗, f(x⃗)). *)
Definition def_rule : drule XSym P :=
  {| d_ctx := Df; d_prems := [];
     d_concl := vsubst (emb Df b φ) (@acons _ XSym Df (ι b) Df (tsym xf (vid Df)) (vid Df)) |}.

Definition xrules (k : I + unit) : drule XSym P :=
  match k with inl i => emb_rule (R i) | inr _ => def_rule end.

Lemma el_ren {Γ Δ} (χ : tm' Γ P) (ρ : ren Γ Δ) : EL (ren_tm χ ρ) = ren_tm (EL χ) ρ.
Proof.
  unfold el. rewrite tr_sren, tr_ren. cbn [ren_sp]. f_equal. apply vec_ext; intros σ x; unfold vget.
  rewrite aget_vpre, aget_vid. unfold vren. rewrite aget_vmap, aget_vid, eta_ren. reflexivity.
Qed.

Lemma vren_vid_upr Λ {Γ Δ} (ρ : ren Γ Δ) :
  vren (vid (Sym := Sym) (Λ ++ Γ)) (upr Λ ρ) = vup Λ (vren (vid Γ) ρ).
Proof. rewrite <- vup_vid. apply vren_vup. Qed.

Hypothesis HDff : Forall gpos Df.
Hypothesis Hbn : noarr b.
Hypothesis Harr_uniq : forall a b c (w w' : Arr a b c), w = w'.
Hypothesis Hbeta : forall a b c (w : Arr a b c) Γ (t : tm (ι a :: Γ) b) (u : tm Γ a),
  conv C (App w (Lam w t) u) (vsubst t (inst1 u)).

Lemma Hnoarr_dom a b' c (w : Arr a b' c) : noarr a.
Proof. exact (proj2 (Harr_dom a b' c w)). Qed.

(** Une formule de L est traduite en une formule convertible. *)
Lemma tr_emb_hole {Γ Δ} (χ : form Γ) (w : vec Γ Δ) : okctx P Γ ->
  conv C (TR (emb Df b χ) Δ P w snil hole) (vsubst χ w).
Proof.
  intros Hok. eapply conv_trans;
    [exact (tr_emb P Sdec Df b view φ C Hsym Harr_inj Harr_uniq Hnoarr_dom Hnoarr_P Hbeta χ Hok _ _ w snil hole Hnoarr_P)|].
  cbn [apps]. unfold hole. rewrite vsubst_var0. apply conv_refl.
Qed.

(** Le cœur du traitement d'une règle : sous les valeurs w des
    métavariables, la traduction d'une instance est l'instance de L. *)
Lemma key_rule {Θ Γ Δ1} Λ (χ0 : form (Λ ++ Θ)) (v : Vectors.vec XSym Θ Γ) (ρ : ren Γ Δ1) (w : vec Θ Δ1)
  (Ξ1 : list (form Δ1)) :
  Forall mspec Θ -> Forall fpos Λ -> vctx Γ -> vctx Δ1 -> CRF Ξ1 v (vren (vid Γ) ρ) w ->
  eqv (wk_list Λ Ξ1) (ren_tm (EL (vsubst (emb Df b χ0) (vup Λ v))) (upr Λ ρ)) (vsubst χ0 (vup Λ w)).
Proof.
  intros HΘ HΛ HΓ HΔ1 Hc.
  assert (HΘv : vctx Θ) by (intros σ x; apply mspec_vspec, (Forall_var x HΘ)).
  unfold el. rewrite tr_ren. cbn [ren_sp]. change (ren_tm (hole (Sym := Sym) (P := P) (Δ := Λ ++ Γ)) (upr [ι P] (upr Λ ρ)))
    with (hole (Sym := Sym) (P := P) (Δ := Λ ++ Δ1)).
  rewrite vren_vid_upr. eapply equiv_trans.
  - apply (proj1 hoistF_mut _ _ (emb Df b χ0) (vctx_app Λ Θ HΛ HΘv) _ (vup Λ v) _ _ _ (vup Λ w) snil _
             (vctx_app Λ Γ HΛ HΓ) (vctx_app Λ Δ1 HΛ HΔ1) (CRF_vup Λ Ξ1 v _ w Hc) Hnoarr_P).
  - apply eqv_conv, tr_emb_hole, vctx_okctx, vctx_app; assumption.
Qed.

Section Sound.
Context (C' : system XSym).
Hypothesis HC' : forall Γ (φ1 φ2 : tm' Γ P), conv C' φ1 φ2 -> vctx Γ ->
  forall Ξ, eqv Ξ (EL φ1) (EL φ2).
Hypothesis Hrules : forall i, Forall mspec (d_ctx (R i)) /\
  (forall p, In p (d_prems (R i)) -> Forall fpos (p_ext p)).

Lemma vsubst_def_rule {Γ} (v : Vectors.vec XSym Df Γ) :
  vsubst (d_concl def_rule) v = vsubst (emb Df b φ) (@acons _ XSym Γ (ι b) Df (tsym xf v) v).
Proof.
  cbn [d_concl def_rule]. rewrite vsubst_vsubst. f_equal.
  change (vcomp (@acons _ XSym Df (ι b) Df (@tsym _ XSym Df (Spec Df b) xf (vid Df)) (vid Df)) v)
    with (@acons _ XSym Γ (ι b) Df (vsubst_tms (σ := ι b) (@tsym _ XSym Df (Spec Df b) xf (vid Df)) v) (vcomp (vid Df) v)).
  rewrite vcomp_vid_l, vsubst_tms_nil. f_equal. change (vsubst (@tsym _ XSym Df (Spec Df b) xf (vid Df)) v) with (@tsym _ XSym Γ (Spec Df b) xf (vsubst_args (vid Df) v)).
  f_equal. apply vec_ext; intros σ z; unfold vget, vsubst_args. rewrite aget_subst_args, aget_vid.
  apply vsubst_eta.
Qed.

(** L'axiome de définition est valide une fois traduit. *)
Lemma def_sound {Γ} (v : Vectors.vec XSym Df Γ) (Ξ : list (form Γ)) :
  vctx Γ -> Ξ ⊢ EL (vsubst (d_concl def_rule) v).
Proof.
  intros HΓ. rewrite vsubst_def_rule.
  apply (open_fargs v (vctx_okctx _ HΓ) HDff Γ (vid Γ) Ξ _). intros Δ1 ρ1 Ξ1 τs HV1 Hi1 Hcd.
  apply (proj1 open_mut _ _ (tsym xf v) (vctx_okctx _ HΓ) Δ1 b (vren (vid Γ) ρ1) snil Ξ1 _ Hbn).
  intros Δ2 ρ2 Ξ2 y HV2 Hi2 Hdy. cbn [ren_sp] in Hdy.
  set (W := vren (vren (vid (Sym := Sym) Γ) ρ1) ρ2). set (τs' := ren_args τs ρ2).
  assert (Hcd' : forall θ (z : var Df θ), cdet Ξ2 θ W (aget z v) (aget z τs')).
  { intros θ z. unfold τs'. rewrite aget_ren. exact (cdet_ren _ _ _ _ _ _ _ (Hcd θ z) Hi2). }
  rewrite ren_ren. unfold el. rewrite tr_ren. cbn [ren_sp].
  change (ren_tm (hole (Sym := Sym) (P := P) (Δ := Γ)) (upr [ι P] (rcomp ρ1 ρ2)))
    with (hole (Sym := Sym) (P := P) (Δ := Δ2)).
  assert (EW : vren (vid (Sym := Sym) Γ) (rcomp ρ1 ρ2) = W) by (unfold W; rewrite vren_vren; reflexivity).
  rewrite EW.
  assert (HCA : CRA Ξ2 (@acons _ XSym Γ (ι b) Df (tsym xf v) v) W (@acons _ Sym Δ2 (ι b) Df y τs')).
  { intros σ x. revert σ x. refine (var_inv _ _ _).
    - right. cbn [aget ahd cdet]. split; [exact Hb|split; [exact Hbn|exact Hdy]].
    - intros σ z. right. exact (Hcd' σ z). }
  assert (HΔ2 : vctx Δ2) by exact (HV2 (HV1 HΓ)).
  assert (HΘ : vctx (ι b :: Df)).
  { apply vctx_cons; [apply vspec_ι|]. intros σ x. destruct (Forall_var x HDff) as [[Hd _] _].
    unfold vspec; rewrite Hd; constructor. }
  eapply equiv_mp; [apply equiv_sym, (proj1 hoistA_mut _ _ (emb Df b φ) HΘ _ _ _ _ _ _ snil _ HΔ2 HCA Hnoarr_P hole)|].
  eapply equiv_mp; [apply equiv_sym, eqv_conv, tr_emb_hole, vctx_okctx, HΘ|].
  fold (phi τs' y).
  (* φ(τ⃗, y) : la valeur de f(v) est y. *)
  pose (K := phi (ren_args τs' (wk [ι b])) (var0 vz)).
  pose proof (DetT_rid _ _ _ _ K Hdy) as H1.
  assert (EK : @vsubst _ Sym (ι b :: Δ2) P K Δ2 (@inst1 _ Sym Δ2 b y) = phi τs' y) by (unfold K; apply phi_inst).
  rewrite EK in H1.
  apply (equiv_mp P C R _ _ _ H1). cbn [tr]. rewrite spK_nil.
  eapply equiv_mp; [apply equiv_sym, DetA_rid, DetA_of_cdet, Hcd'|].
  rewrite fK_inst. apply (deriv_cut' P C R _ (Ex b K)); [apply Htot|].
  apply (ex_mono P C R b). apply (and_I C P R); apply d_ax; left; reflexivity.
Qed.

(** **Correction** : la traduction envoie les dérivations de L' sur des
    dérivations de L, dans les contextes du premier ordre. *)
Theorem el_sound Γ (Ξ' : list (tm' Γ P)) ψ :
  deriv C' P xrules Γ Ξ' ψ -> vctx Γ -> map EL Ξ' ⊢ EL ψ.
Proof.
  induction 1 as [Γ Ξ' ψ Hin|Γ Ξ' ψ1 ψ2 Hc H IH|Γ Ξ' k v Hp IH]; intros HΓ.
  - apply d_ax, in_map, Hin.
  - exact (equiv_mp P C R _ _ _ (HC' Γ ψ1 ψ2 Hc HΓ _) (IH HΓ)).
  - destruct k as [i|[]]; [|apply def_sound, HΓ].
    destruct (Hrules i) as [HΘ Hext]. cbn [xrules emb_rule d_concl d_ctx] in *.
    apply (open_vec v HΘ (vctx_okctx _ HΓ) Γ (vid Γ) (map EL Ξ') _). intros Δ1 ρ Ξ1 w HV Hi Hc.
    pose proof (HV HΓ) as HΔ1.
    eapply equiv_mp.
    { apply equiv_sym. pose proof (key_rule [] (d_concl (R i)) v ρ w Ξ1 HΘ (Forall_nil _) HΓ HΔ1 Hc) as Hk.
      rewrite wk_list_nil in Hk. rewrite vup_nil in Hk. exact Hk. }
    rewrite vup_nil. apply (d_rule C P R Δ1 Ξ1 i w). intros p Hin.
    pose proof (Hext p Hin) as HΛ.
    assert (Hin' : In (emb_prem p) (map emb_prem (d_prems (R i)))) by (apply in_map, Hin).
    pose proof (IH (emb_prem p) Hin' (vctx_app _ _ HΛ HΓ)) as Hd.
    apply (deriv_ren P C R _ (upr (p_ext p) ρ)) in Hd.
    unfold inst_hyps, inst_goal, vsubst_list in Hd |- *. cbn [emb_prem p_ext p_hyps p_goal] in Hd.
    rewrite map_map, !map_app, map_map in Hd. unfold ren_list in Hd. rewrite map_app, map_map in Hd.
    eapply (deriv_transfer (p_hyps p) _ (fun h => vsubst h (vup (p_ext p) w))); [exact Hd| | |].
    + intros χ Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply in_map_iff in Hχ0 as (χ1 & <- & Hχ1).
      apply in_map_iff in Hχ1 as (χ2 & <- & Hχ2).
      rewrite el_ren, ren_ren. apply in_map_iff. exists (ren_tm (EL χ2) ρ). split.
      * rewrite ren_ren. apply ren_ext. intros σ y. unfold rcomp, wk. rewrite upr_vr. reflexivity.
      * apply Hi. unfold ren_list. apply (in_map (fun χ => ren_tm χ ρ)), in_map, Hχ2.
    + intros h Hh. cbn beta. apply (key_rule (p_ext p) h v ρ w Ξ1 HΘ HΛ HΓ HΔ1 Hc).
    + apply (key_rule (p_ext p) (p_goal p) v ρ w Ξ1 HΘ HΛ HΓ HΔ1 Hc).
Qed.

(** **Conservativité** : un jugement de L dérivable dans L' l'est dans L. *)
Theorem def_conservative Γ (Ξ : list (form Γ)) (ψ : form Γ) :
  vctx Γ -> deriv C' P xrules Γ (map (emb Df b) Ξ) (emb Df b ψ) -> Ξ ⊢ ψ.
Proof.
  intros HΓ Hd. pose proof (el_sound Γ _ _ Hd HΓ) as H. rewrite map_map in H.
  pose proof (vctx_okctx _ HΓ) as Hok.
  assert (Hel : forall χ : form Γ, conv C (EL (emb Df b χ)) χ).
  { intros χ. pose proof (tr_emb_hole χ (vid Γ) Hok) as Hc. rewrite vsubst_vid in Hc. exact Hc. }
  eapply d_conv; [apply Hel|]. apply (deriv_cut_gen C P R H). intros χ Hχ.
  apply in_map_iff in Hχ as (χ0 & <- & Hin).
  eapply d_conv; [apply conv_sym, Hel|]. apply d_ax, Hin.
Qed.

End Sound.


(** *** Le calcul de L' : réécriture en contexte

    On montre que la traduction respecte les conversions de L' obtenues par
    réécriture en contexte : une instance de β, de η, ou d'une règle de
    calcul de L (à métavariables du premier ordre), à une position
    quelconque d'une formule. *)

(** La couche fonctionnelle de L' : celle de L, par le plongement. *)
Definition xFS : Functional XSym :=
  {| Arr := @Arr _ Sym FS; s_lam := fun a b c w => xold (s_lam w); s_app := fun a b c w => xold (s_app w) |}.

Section Compat.
Hypothesis Hview_lam : forall a b c (w : Arr a b c), view _ (s_lam w) = vw_lam w.
Hypothesis Hview_app : forall a b c (w : Arr a b c), view _ (s_app w) = vw_app w.

Context {J : Type} (R' : J -> rule XSym).

Inductive cstep : forall Γ s, tm' Γ s -> tm' Γ s -> Prop :=
| cs_rule (j : J) Γ (v : Vectors.vec XSym (r_ctx (R' j)) Γ) :
    cstep Γ _ (vsubst (r_lhs (R' j)) v) (vsubst (r_rhs (R' j)) v)
| cs_sym Γ σ (c : XSym σ) (a a' : args' Γ (dom σ)) : astep Γ _ a a' -> cstep Γ _ (tsym c a) (tsym c a')
| cs_var Γ σ (x : var Γ σ) (a a' : args' Γ (dom σ)) : astep Γ _ a a' -> cstep Γ _ (tvar x a) (tvar x a')
with astep : forall Γ Θ, args' Γ Θ -> args' Γ Θ -> Prop :=
| as_hd Γ σ Θ (u u' : Terms.tms XSym Γ σ) (a : args' Γ Θ) :
    cstep _ _ u u' -> astep Γ (σ :: Θ) (acons u a) (acons u' a)
| as_tl Γ σ Θ (u : Terms.tms XSym Γ σ) (a a' : args' Γ Θ) :
    astep Γ Θ a a' -> astep Γ (σ :: Θ) (acons u a) (acons u a').

Scheme cstep_ind' := Induction for cstep Sort Prop
  with astep_ind' := Induction for astep Sort Prop.
Combined Scheme cstep_astep_ind from cstep_ind', astep_ind'.

(** La clôture réflexive, symétrique et transitive. *)
Inductive cconv {Γ s} : tm' Γ s -> tm' Γ s -> Prop :=
| cc_refl t : cconv t t
| cc_fwd t u w : cstep Γ s t u -> cconv u w -> cconv t w
| cc_bwd t u w : cstep Γ s u t -> cconv u w -> cconv t w.

(** La réécriture en contexte est contenue dans le calcul engendré. *)
Lemma cstep_generated :
  (forall Γ s (t t' : tm' Γ s), cstep Γ s t t' -> conv (generated R') t t') /\
  (forall Γ Θ (a a' : args' Γ Θ), astep Γ Θ a a' -> arel (conv (generated R')) a a').
Proof.
  apply cstep_astep_ind.
  - intros j Γ v. apply generated_instance.
  - intros Γ σ c a a' _ IH. apply (conv_tsym (generated R')), IH.
  - intros Γ σ x a a' _ IH. apply (conv_tvar (generated R')), IH.
  - intros Γ σ Θ u u' a _ IH. split; [exact IH|apply (arel_refl (generated R'))].
  - intros Γ σ Θ u a a' _ IH. split; [apply conv_refl|exact IH].
Qed.

Lemma cconv_generated {Γ s} (t t' : tm' Γ s) : cconv t t' -> conv (generated R') t t'.
Proof.
  induction 1 as [t|t u w Hs _ IH|t u w Hs _ IH].
  - apply conv_refl.
  - eapply conv_trans; [exact (proj1 cstep_generated _ _ _ _ Hs)|exact IH].
  - eapply conv_trans; [apply conv_sym; exact (proj1 cstep_generated _ _ _ _ Hs)|exact IH].
Qed.

(** La relation induite par la traduction. *)
Definition TRel {Γ s} (t t' : tm' Γ s) : Prop :=
  forall Δ r (w : vec Γ Δ) (sp : spine Δ s r) K (Ξ : list (form Δ)), vctx Δ -> noarr r ->
  eqv Ξ (TR t Δ r w sp K) (TR t' Δ r w sp K).

Lemma TRel_refl {Γ s} (t : tm' Γ s) : TRel t t.
Proof. intros Δ r w sp K Ξ _ _. apply equiv_refl. Qed.

Lemma TRel_sym {Γ s} (t t' : tm' Γ s) : TRel t t' -> TRel t' t.
Proof. intros H Δ r w sp K Ξ HΔ Hr. apply equiv_sym, H; assumption. Qed.

Lemma TRel_eq_r {Γ s} (t u u' : tm' Γ s) : u' = u -> TRel t u' -> TRel t u.
Proof. intros <-; exact (fun H => H). Qed.

Lemma TRel_trans {Γ s} (t t' t'' : tm' Γ s) : TRel t t' -> TRel t' t'' -> TRel t t''.
Proof. intros H1 H2 Δ r w sp K Ξ HΔ Hr. eapply equiv_trans; [apply H1|apply H2]; assumption. Qed.

(** Composantes reliées : la relation, quand le contexte de la composante
    est du premier ordre. *)
Definition ARel {Γ Θ} (a a' : args' Γ Θ) : Prop :=
  forall θ (z : var Θ θ), vctx (dom θ ++ Γ) -> TRel (aget z a) (aget z a').

Lemma tra_ARel {Γ Θ} (a a' : args' Γ Θ) : ARel a a' -> Forall spos Θ ->
  forall Δ (w : vec Γ Δ) K (Ξ : list (form Δ)), vctx Γ -> vctx Δ -> eqv Ξ (TRA a Δ w K) (TRA a' Δ w K).
Proof.
  revert a'. induction a as [Γ0|Γ0 σ Θ0 u a IH]; intros a' Ha HΘ Δ w K Ξ HΓ HΔ.
  - rewrite (args_nil a'). apply equiv_refl.
  - rewrite (args_eta a') in *. inversion HΘ as [|? ? Hp HΘ']; subst.
    assert (Hu : vctx (dom σ ++ Γ0) -> TRel u (ahd a')) by exact (Ha σ vz).
    assert (Ha' : ARel a (atl a')) by (intros θ z; exact (Ha θ (vs z))).
    destruct σ as [Λ c]. cbn [tra]. cbn [dom cod] in *. destruct (Sdec c P) as [e|n].
    + subst c. cbn [castc castP eq_rect eq_sym].
      assert (HΛ : Forall gpos Λ) by (destruct Hp as [[[Hd _] _]|[_ Hd]]; [cbn in Hd; subst; constructor|exact Hd]).
      pose proof (gpos_fpos _ HΛ) as HΛf.
      eapply equiv_trans; [apply (IH (atl a') Ha' HΘ' Δ w _ Ξ HΓ HΔ)|]. apply tra_cong.
      apply repl_sub0; [exact HΛ|exact (vctx_app' Θ0 HΘ' HΔ)|].
      rewrite <- wk_list_app_ren. apply equiv_ren.
      apply (Hu (vctx_app Λ Γ0 HΛf HΓ)); [exact (vctx_app Λ Δ HΛf HΔ)|exact Hnoarr_P].
    + destruct Λ as [|λ Λ]; [|apply equiv_refl].
      assert (Hna : noarr c) by (destruct Hp as [[_ Hna]|[Hc' _]]; [exact Hna|exact (False_ind _ (n Hc'))]).
      cbn [app] in *. eapply equiv_trans; [apply (Hu HΓ); assumption|]. apply tr_cong.
      apply (IH (atl a') Ha' HΘ' (ι c :: Δ) _ _ _ HΓ (vctx_cons1 c HΔ)).
Qed.

Lemma ARel_refl {Γ Θ} (a : args' Γ Θ) : ARel a a.
Proof. intros θ z _. apply TRel_refl. Qed.

(** **Congruence** : un symbole ou une variable dont les arguments sont
    reliés. *)
Lemma TRel_tsym {Γ σ} (c : XSym σ) (a a' : args' Γ (dom σ)) :
  vctx Γ -> ARel a a' -> TRel (tsym c a) (tsym c a').
Proof.
  intros HΓ Ha Δ r w sp K Ξ HΔ Hr. destruct c as [σ1 c0|]; cbn [tr].
  - pose proof (HsymV σ1 c0) as Hs. revert a a' Ha sp Hs K.
    destruct (view σ1 c0) as [a0 b0 c1 w1|a0 b0 c1 w1|σ2 c2]; intros a a' Ha sp Hs K; cbn [dom cod] in *.
    + pose proof (Ha _ vz (vctx_cons1 a0 HΓ)) as Ht. cbn [aget] in Ht.
      rewrite (args1_inv a), (args1_inv a'). cbn beta iota zeta.
      revert K Hr. destruct sp as [s0|a2 b2 c2 r1 w2 val sp']; intros K Hr; [exfalso; exact (Hr _ _ w1)|].
      destruct (Harr_inj _ _ _ _ _ w2 w1) as [-> ->]. rewrite !trlam_cons. apply Ht; assumption.
    + pose proof (Ha _ vz HΓ) as HF. pose proof (Ha _ (vs vz) HΓ) as Hu. cbn [aget] in HF, Hu.
      rewrite (args2_inv a), (args2_inv a'). cbn beta iota zeta. cbn [fst snd].
      destruct (Harr_dom _ _ _ w1) as [_ Ha0].
      eapply equiv_trans; [apply tr_cong|apply Hu; assumption].
      apply HF; [apply vctx_cons1, HΔ|exact Hr].
    + destruct Hs as [Hs _]. apply (tra_ARel a a' Ha Hs Δ w _ Ξ HΓ HΔ).
  - apply (tra_ARel a a' Ha HDfs Δ w _ Ξ HΓ HΔ).
Qed.

Lemma TRel_tvar {Γ σ} (x : var Γ σ) (a a' : args' Γ (dom σ)) :
  vctx Γ -> ARel a a' -> TRel (tvar x a) (tvar x a').
Proof.
  intros HΓ Ha Δ r w sp K Ξ HΔ Hr. cbn [tr]. apply (tra_ARel a a' Ha (vspec_spos _ (HΓ _ x)) Δ w _ Ξ HΓ HΔ).
Qed.

(** Ouverture d'un terme dont la valeur est passée à une continuation. *)
Lemma open_eqv_cont {Γ a} (U : tm' Γ a) : okctx P Γ -> noarr a ->
  forall Δ (W : vec Γ Δ) (Ξ : list (form Δ)) (Kb : form (ι a :: Δ)) B,
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 τ, (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     DetT Ξ1 U (vren W ρ) τ -> eqv Ξ1 (vsubst (ren_tm Kb (upr [ι a] ρ)) (inst1 τ)) (ren_tm B ρ)) ->
  eqv Ξ (TR U Δ a W snil Kb) B.
Proof.
  intros HΓ Ha Δ W Ξ Kb B Hk. apply (eqv_open_tm U HΓ Ha Δ W). intros Δ1 ρ Ξ1 τ HV Hi Hd.
  rewrite tr_ren. cbn [ren_sp]. eapply equiv_trans; [apply DetT_rid, Hd|]. apply (Hk Δ1 ρ Ξ1 τ HV Hi Hd).
Qed.

(** Le corps d'un lambda, sa variable liée remplacée par une valeur. *)
Lemma lam_body_inst {Γ a s r} (T : tm' (ι a :: Γ) s) {Δ Δ1} (W : vec Γ Δ) (sp : spine Δ s r)
  (K : form (ι r :: Δ)) (ρ : ren Δ Δ1) (τ : tm Δ1 a) :
  vsubst (ren_tm (TR T (ι a :: Δ) r (vup [ι a] W) (ren_sp sp (wk [ι a])) (ren_tm K (upr [ι r] (wk [ι a]))))
                 (upr [ι a] ρ)) (inst1 τ)
  = TR T Δ1 r (@acons _ Sym Δ1 (ι a) Γ τ (vren W ρ)) (ren_sp sp ρ) (ren_tm K (upr [ι r] ρ)).
Proof.
  rewrite ren_as_vsubst, <- (vup_vpre [ι a] ρ), vsubst_vsubst.
  match goal with |- vsubst ?X _ = _ =>
    transitivity (vsubst X (@acons _ Sym Δ1 (ι a) Δ τ (vpre ρ (vid Δ1)))); [f_equal; apply vcomp_vup1_inst1|] end.
  rewrite tr_vsubst. f_equal.
  - exact (eq_trans (vup_cat [ι a] W (@acons _ Sym Δ1 (ι a) [] τ anil) (vpre ρ (vid Δ1)))
             (f_equal (@acons _ Sym Δ1 (ι a) Γ τ) (vcomp_vpre_vid W ρ))).
  - etransitivity; [exact (vsubst_sp_wk_cat [ι a] sp (@acons _ Sym Δ1 (ι a) [] τ anil) (vpre ρ (vid Δ1)))|].
    symmetry. apply ren_sp_as_vsubst.
  - exact (eq_trans (vsubst_ren_upr_wk_cat [ι r] [ι a] K (@acons _ Sym Δ1 (ι a) [] τ anil) (vpre ρ (vid Δ1)))
             (vsubst_vup_vpre [ι r] K ρ)).
Qed.

Lemma equiv_eq {Γ} (Ξ : list (form Γ)) A B : A = B -> eqv Ξ A B.
Proof. intros ->. apply equiv_refl. Qed.

(** **β** : app(λx. T, U) et T[U/x] ont des traductions équivalentes. *)
Lemma beta_TRel {Γ a b0 c} (w0 : Arr a b0 c) (T : tm' (ι a :: Γ) b0) (U : tm' Γ a) : vctx Γ ->
  TRel (tsym (xold (s_app w0)) (@acons _ XSym Γ (ι c) _
          (tsym (xold (s_lam w0)) (@acons _ XSym Γ (Spec [ι a] b0) _ T anil)) (@acons _ XSym Γ (ι a) _ U anil)))
       (vsubst T (@acons _ XSym Γ (ι a) Γ U (vid Γ))).
Proof.
  intros HΓ Δ r W sp K Ξ HΔ Hr.
  rewrite tr_app_eq by apply Hview_app. rewrite (tr_lam_eq w0 T (vren W (wk [ι a]))) by apply Hview_lam.
  rewrite trlam_cons.
  destruct (Harr_dom _ _ _ w0) as [Han Ha].
  apply (open_eqv_cont U (vctx_okctx _ HΓ) Ha Δ W Ξ). intros Δ1 ρ Ξ1 τ HV Hi Hd.
  eapply equiv_trans; [apply equiv_eq; exact (lam_body_inst T W sp K ρ τ)|].
  rewrite tr_ren. apply equiv_sym.
  apply (proj1 hoistA_mut _ _ T (vctx_cons1 a HΓ) Γ _ Δ1 r (vren W ρ) (@acons _ Sym Δ1 (ι a) Γ τ (vren W ρ))
           (ren_sp sp ρ) Ξ1 (HV HΔ)); [|exact Hr].
  intros σ x. revert σ x. refine (var_inv _ _ _).
  - right. cbn [aget ahd cdet]. split; [exact Han|split; [exact Ha|exact Hd]].
  - intros σ y. left. exists y. cbn [aget atl]. split; [apply aget_vid|reflexivity].
Qed.

(** **η** : λx. app(F, x) et F ont la même traduction. *)
Lemma eta_TRel {Γ a b0 c} (w0 : Arr a b0 c) (F : tm' Γ c) :
  TRel (tsym (xold (s_lam w0)) (@acons _ XSym Γ (Spec [ι a] b0) _
          (tsym (xold (s_app w0)) (@acons _ XSym (ι a :: Γ) (ι c) _ (ren_tms (σ := ι c) F (wk [ι a]))
             (@acons _ XSym (ι a :: Γ) (ι a) _ (var0 vz) anil))) anil))
       F.
Proof.
  intros Δ r W sp K Ξ HΔ Hr. rewrite tr_lam_eq by apply Hview_lam. cbn [cod] in sp |- *.
  revert K Hr. destruct sp as [s0|a1 b1 c1 r1 w1 v sp']; intros K Hr; [exfalso; exact (Hr _ _ w0)|].
  destruct (Harr_inj _ _ _ _ _ w1 w0) as [-> ->]. rewrite (Harr_uniq _ _ _ w1 w0), trlam_cons.
  rewrite (tr_app_eq w0 (ren_tms (σ := ι c1) F (wk [ι a])) (var0 vz) (@acons _ Sym Δ (ι a) Γ v W)) by apply Hview_app.
  unfold var0 at 1. cbn [tr tra]. rewrite spK_nil. unfold plug. rewrite wkv_nil.
  cbn [aget ahd]. apply equiv_eq.
  etransitivity; [exact (tr_scons_inst (ren_tms (σ := ι c1) F (wk [ι a])) w0 (@acons _ Sym Δ (ι a) Γ v W) sp' K v)|].
  unfold ren_tms. cbn [dom]. rewrite tr_sren. f_equal. exact (vpre_wk1 (τ := ι a) v W).
Qed.

Lemma eqv_open_vec {Θ Γ0} (v : Vectors.vec XSym Θ Γ0) : Forall mspec Θ -> okctx P Γ0 ->
  forall Δ (w0 : vec Γ0 Δ) (Ξ : list (form Δ)) (A B : form Δ),
  (forall Δ1 (ρ : ren Δ Δ1) Ξ1 (w : vec Θ Δ1), (vctx Δ -> vctx Δ1) -> incl (ren_list Ξ ρ) Ξ1 ->
     CRF Ξ1 v (vren w0 ρ) w -> eqv Ξ1 (ren_tm A ρ) (ren_tm B ρ)) ->
  eqv Ξ A B.
Proof.
  intros HΘ HΓ Δ W Ξ A B Hk. split.
  - apply (open_vec v HΘ HΓ Δ W _ _). intros Δ1 ρ Ξ1 w HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (Hk Δ1 ρ Ξ1 w HV Hi' Hd)). apply d_ax, Hi; left; reflexivity.
  - apply (open_vec v HΘ HΓ Δ W _ _). intros Δ1 ρ Ξ1 w HV Hi Hd.
    assert (Hi' : incl (ren_list Ξ ρ) Ξ1) by (intros χ Hχ; apply Hi; right; exact Hχ).
    apply (equiv_mp P C R _ _ _ (equiv_sym P C R _ _ _ (Hk Δ1 ρ Ξ1 w HV Hi' Hd))). apply d_ax, Hi; left; reflexivity.
Qed.

(** Une règle de calcul de L, à métavariables du premier ordre. *)
Lemma rule_TRel (r0 : rule Sym) {Γ} (v : Vectors.vec XSym (r_ctx r0) Γ) :
  Forall mspec (r_ctx r0) -> conv C (r_lhs r0) (r_rhs r0) -> vctx Γ ->
  TRel (vsubst (emb Df b (r_lhs r0)) v) (vsubst (emb Df b (r_rhs r0)) v).
Proof.
  intros HΘ Hc HΓ Δ r W sp K Ξ HΔ Hr.
  assert (HΘv : vctx (r_ctx r0)) by (intros σ x; apply mspec_vspec, (Forall_var x HΘ)).
  apply (eqv_open_vec v HΘ (vctx_okctx _ HΓ) Δ W Ξ). intros Δ1 ρ Ξ1 wv HV Hi Hcr.
  rewrite !tr_ren. pose proof (HV HΔ) as HΔ1.
  eapply equiv_trans; [apply (proj1 hoistF_mut _ _ _ HΘv _ v Δ1 r (vren W ρ) wv _ Ξ1 HΓ HΔ1 Hcr Hr)|].
  eapply equiv_trans; [|apply equiv_sym, (proj1 hoistF_mut _ _ _ HΘv _ v Δ1 r (vren W ρ) wv _ Ξ1 HΓ HΔ1 Hcr Hr)].
  apply eqv_conv.
  eapply conv_trans; [exact (tr_emb P Sdec Df b view φ C Hsym Harr_inj Harr_uniq Hnoarr_dom Hnoarr_P Hbeta
                               (r_lhs r0) (vctx_okctx _ HΘv) _ _ wv _ _ Hr)|].
  eapply conv_trans; [|apply conv_sym; exact (tr_emb P Sdec Df b view φ C Hsym Harr_inj Harr_uniq Hnoarr_dom
                               Hnoarr_P Hbeta (r_rhs r0) (vctx_okctx _ HΘv) _ _ wv _ _ Hr)].
  apply (conv_K_inst P C), (conv_apps C), (conv_vsubst C); [exact Hc|apply (arel_refl C)].
Qed.

(** Les règles de calcul de L' : β, η, ou une règle de L à métavariables du
    premier ordre. *)
Hypothesis HR' : forall j,
  (exists a0 b0 c0 (w0 : Arr a0 b0 c0), R' j = @beta_rule _ XSym xFS _ _ _ w0) \/
  (exists a0 b0 c0 (w0 : Arr a0 b0 c0), R' j = @eta_rule _ XSym xFS _ _ _ w0) \/
  (exists r0 : rule Sym, R' j = {| r_ctx := r_ctx r0; r_sort := r_sort r0;
                                   r_lhs := emb Df b (r_lhs r0); r_rhs := emb Df b (r_rhs r0) |} /\
                         Forall mspec (r_ctx r0) /\ conv C (r_lhs r0) (r_rhs r0)).

Theorem cstep_TRel :
  (forall Γ s (t t' : tm' Γ s), cstep Γ s t t' -> vctx Γ -> TRel t t') /\
  (forall Γ Θ (a a' : args' Γ Θ), astep Γ Θ a a' -> vctx Γ -> ARel a a').
Proof.
  apply cstep_astep_ind.
  - intros j Γ v HΓ. destruct (HR' j) as [[a0 [b0 [c0 [w0 E]]]]|[[a0 [b0 [c0 [w0 E]]]]|[r0 [E [HΘ Hc]]]]];
      revert v; rewrite E; intros v.
    + rewrite (args2_inv v). cbn [beta_rule r_lhs r_rhs r_ctx beta_ctx r_sort].
      rewrite (@vsubst_App _ XSym xFS), (@vsubst_Lam _ XSym xFS), vsubst_var0, vsubst_eta. cbn [aget ahd atl].
      apply (TRel_eq_r _ _ (vsubst (ahd v) (@acons _ XSym Γ (ι a0) Γ (ahd (atl v)) (vid Γ)))).
      * symmetry. etransitivity;
          [exact (vsubst_tvar vz _ (@acons _ XSym Γ _ _ (ahd v) (@acons _ XSym Γ (ι a0) _ (ahd (atl v)) anil)))|].
        cbn [dom cod aget ahd atl]. rewrite vsubst_args_one, vsubst_tms_nil, vsubst_var0, happ_vsubst. reflexivity.
      * exact (beta_TRel w0 _ _ HΓ).
    + rewrite (args1_inv v). cbn [eta_rule r_lhs r_rhs r_ctx eta_ctx r_sort].
      rewrite (@vsubst_Lam _ XSym xFS), vsubst_tms_vup. cbn [dom]. rewrite (@vsubst_App _ XSym xFS), !vsubst_var0.
      change (aget vz (vup [ι a0] (@acons _ XSym Γ (ι c0) [] (ahd v) anil))) with (@var0 _ XSym (ι a0 :: Γ) a0 vz).
      change (aget (vs vz) (vup [ι a0] (@acons _ XSym Γ (ι c0) [] (ahd v) anil)))
        with (aget (vr [ι a0] vz) (vup [ι a0] (@acons _ XSym Γ (ι c0) [] (ahd v) anil))).
      rewrite aget_vup_r'. cbn [aget ahd]. exact (eta_TRel w0 (ahd v)).
    + cbn [r_lhs r_rhs r_ctx] in *. apply rule_TRel; assumption.
  - intros Γ σ c a a' Ha IH HΓ. apply TRel_tsym; [exact HΓ|apply IH, HΓ].
  - intros Γ σ x a a' Ha IH HΓ. apply TRel_tvar; [exact HΓ|apply IH, HΓ].
  - intros Γ σ Θ u u' a Hu IH HΓ θ z. revert θ z. refine (var_inv _ _ _); [exact IH|].
    intros θ z _. apply TRel_refl.
  - intros Γ σ Θ u a a' Ha IH HΓ θ z. revert θ z. refine (var_inv _ _ _); [intros _; apply TRel_refl|].
    intros θ z Hz. exact (IH HΓ θ z Hz).
Qed.

Lemma cconv_TRel {Γ s} (t t' : tm' Γ s) : cconv t t' -> vctx Γ -> TRel t t'.
Proof.
  induction 1 as [t|t u w Hs H IH|t u w Hs H IH]; intros HΓ.
  - apply TRel_refl.
  - eapply TRel_trans; [apply (proj1 cstep_TRel _ _ _ _ Hs HΓ)|apply IH, HΓ].
  - eapply TRel_trans; [apply TRel_sym, (proj1 cstep_TRel _ _ _ _ Hs HΓ)|apply IH, HΓ].
Qed.

(** La traduction respecte la réécriture en contexte. *)
Theorem cconv_eqv {Γ} (φ1 φ2 : tm' Γ P) : cconv φ1 φ2 -> vctx Γ -> forall Ξ, eqv Ξ (EL φ1) (EL φ2).
Proof.
  intros Hc HΓ Ξ. unfold el. apply (cconv_TRel φ1 φ2 Hc HΓ Γ P (vid Γ) snil hole Ξ HΓ Hnoarr_P).
Qed.

End Compat.

End Open.



(** ** Congruence des connecteurs usuels

    L'hypothèse [Hcong] porte sur chaque symbole de sorte P. Elle est
    immédiate pour un symbole sans position de formule (un prédicat), et se
    démontre pour ∧ et ∃ à partir de leurs règles. *)

Lemma cong_atom {Θ} (c : Sym (Spec Θ P)) {Δ} (Ξ : list (form Δ)) (a1 a2 : Terms.args Sym Δ Θ) :
  Forall fpos Θ -> argrel Ξ Θ a1 a2 -> eqv Ξ (tsym c a1) (tsym c a2).
Proof.
  intros HΘ Ha. rewrite (argrel_eq Ξ Θ a1 a2 ltac:(eapply Forall_impl; [|exact HΘ]; intros θ [_ Hc]; exact Hc) Ha).
  apply equiv_refl.
Qed.

Lemma cong_and {Δ} (Ξ : list (form Δ)) (a1 a2 : Terms.args Sym Δ [ι P; ι P]) :
  argrel Ξ [ι P; ι P] a1 a2 -> eqv Ξ (tsym c_and a1) (tsym c_and a2).
Proof.
  intros Ha. pose proof (Ha _ vz) as H1. pose proof (Ha _ (vs vz)) as H2. cbn [aget] in H1, H2.
  apply comprel_P in H1, H2. rewrite wk_list_nil in H1, H2.
  rewrite (args_eta a1), (args_eta (atl a1)), (args_nil (atl (atl a1))),
    (args_eta a2), (args_eta (atl a2)), (args_nil (atl (atl a2))) in *.
  cbn [ahd atl] in *. fold (Bin c_and (ahd a1) (ahd (atl a1))). fold (Bin c_and (ahd a2) (ahd (atl a2))).
  fold (And (ahd a1) (ahd (atl a1))). fold (And (ahd a2) (ahd (atl a2))).
  destruct H1 as [H11 H12], H2 as [H21 H22]. split; apply (and_mono P C R); assumption.
Qed.

Lemma cong_ex {Δ} (Ξ : list (form Δ)) (a1 a2 : Terms.args Sym Δ [Spec [ι b] P]) :
  argrel Ξ [Spec [ι b] P] a1 a2 -> eqv Ξ (tsym c_ex a1) (tsym c_ex a2).
Proof.
  intros Ha. pose proof (Ha _ vz) as H1. cbn [aget] in H1. apply comprel_P in H1.
  rewrite (args_eta a1), (args_nil (atl a1)), (args_eta a2), (args_nil (atl a2)) in *.
  cbn [ahd atl] in *. fold (Qnt (P := P) (s := b) c_ex (ahd a1)). fold (Qnt (P := P) (s := b) c_ex (ahd a2)).
  fold (Ex b (ahd a1)). fold (Ex b (ahd a2)).
  destruct H1 as [H11 H12]. split; apply (ex_mono P C R b); assumption.
Qed.

(** ** Énoncé final

    Les hypothèses sont celles de la section précédente, sous une forme
    directement vérifiable :
    - la totalité et l'unicité sont deux jugements de L : Df ⊢ ∃y φ(x⃗, y)
      et φ(x⃗, y), φ(x⃗, y') ⊢ y = y' ;
    - les arguments de f et b sont des termes non flèches (sortes autres
      que P) ;
    - les symboles autres que lambda et app ont des positions de termes non
      flèches, ou de formules liant de tels termes (seulement des termes
      pour un symbole de sorte autre que P), et ceux de sorte P respectent
      l'équivalence à leurs positions de formules ([Hcong]) ;
    - une sorte flèche c détermine son domaine a, son codomaine b et le
      témoin de Arr a b c ; a n'est pas une sorte flèche, a, b ≠ P, et P
      n'est pas une sorte flèche ;
    - le calcul de L contient β ;
    - les métavariables des règles de L sont des termes non flèches ou des
      formules à arguments de tels termes, et leurs prémisses ne lient que
      des termes.
    La conclusion porte sur les jugements dont le contexte est du premier
    ordre ([vctx]). Le premier énoncé ([definitional_conservative]) suppose
    que la traduction respecte le calcul de L' ([HC']) ; le second
    ([definitional_conservative_cc]) le démontre quand les conversions de
    L' s'obtiennent par réécriture en contexte avec β, η et des règles de
    calcul de L. *)

Section Final.
Local Notation EL := (el Sdec Df b view φ).
Hypothesis Htot0 : deriv C P R Df [] (Ex b φ).
Hypothesis Huniq0 : deriv C P R (ι b :: ι b :: Df)
  [ren_tm φ (upr [ι b] (wk [ι b])); ren_tm φ (wk [ι b])] (Eq b (var0 vz) (var0 (vs vz))).
Hypothesis HsymV : forall σ (c : Sym σ), match view σ c with vw_oth _ => oth_ok σ | _ => True end.
Hypothesis Hcong : forall Θ (c : Sym (Spec Θ P)) Δ (Ξ : list (form Δ)) (a1 a2 : Terms.args Sym Δ Θ),
  argrel Ξ Θ a1 a2 -> eqv Ξ (tsym c a1) (tsym c a2).
Hypothesis HDff : Forall gpos Df.
Hypothesis Hb : b <> P.
Hypothesis Hbn : noarr b.
Hypothesis Harr_inj : forall a b c a' b' (w : Arr a b c) (w' : Arr a' b' c), a = a' /\ b = b'.
Hypothesis Harr_uniq : forall a b c (w w' : Arr a b c), w = w'.
Hypothesis Harr_dom : forall a b c (w : Arr a b c), a <> P /\ noarr a.
Hypothesis Harr_cod : forall a b c (w : Arr a b c), b <> P.
Hypothesis Hnoarr_P : noarr P.
Hypothesis Hbeta : forall a b c (w : Arr a b c) Γ (t : tm (ι a :: Γ) b) (u : tm Γ a),
  conv C (App w (Lam w t) u) (vsubst t (inst1 u)).

Lemma Htot_inst Δ (Ξ : list (form Δ)) (a : Terms.args Sym Δ Df) :
  Ξ ⊢ Ex b (phi (ren_args a (wk [ι b])) (var0 vz)).
Proof.
  pose proof (deriv_subst C P R Htot0 _ a) as H. cbn [vsubst_list map] in H.
  apply (deriv_mono P C R []); [|intros χ []]. unfold Ex in H |- *. rewrite vsubst_Qnt, vsubst_tms_vup in H.
  unfold phi. eapply deriv_rw; [|exact H]. f_equal. f_equal. f_equal.
  apply vec_ext; intros σ x; unfold vget. revert σ x. refine (var_inv _ _ _); [reflexivity|].
  intros σ z. cbn [dom]. exact (eq_trans (aget_vup_r' [ι b] a z) (eq_sym (aget_ren z a (wk [ι b])))).
Qed.

Lemma Huniq_inst Δ (Ξ : list (form Δ)) (a : Terms.args Sym Δ Df) (y y' : tm Δ b) :
  Ξ ⊢ phi a y -> Ξ ⊢ phi a y' -> Ξ ⊢ Eq b y y'.
Proof.
  intros H1 H2.
  pose (v := @acons _ Sym Δ (ι b) _ y (@acons _ Sym Δ (ι b) _ y' a)).
  pose proof (deriv_subst C P R Huniq0 _ v) as H. cbn [vsubst_list map] in H.
  rewrite vsubst_Eq, !vsubst_var0 in H. cbn [aget ahd atl v] in H.
  assert (E1 : vsubst (ren_tm φ (upr [ι b] (wk [ι b]))) v = phi a y).
  { unfold phi. rewrite vsubst_ren. f_equal. apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
    revert σ x. refine (var_inv _ _ _); [reflexivity|intros σ z; reflexivity]. }
  assert (E2 : vsubst (ren_tm φ (wk [ι b])) v = phi a y').
  { unfold phi. rewrite vsubst_ren. f_equal. apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
    revert σ x. refine (var_inv _ _ _); [reflexivity|intros σ z; reflexivity]. }
  apply (deriv_cut_gen C P R H). intros χ [<-|[<-|[]]].
  - apply (deriv_rw P C R _ (phi a y)); [symmetry; exact E1|exact H1].
  - apply (deriv_rw P C R _ (phi a y')); [symmetry; exact E2|exact H2].
Qed.

Lemma HsymV_ok σ (c : Sym σ) : view_ok P (view σ c).
Proof.
  pose proof (HsymV σ c) as Hs. revert Hs. destruct (view σ c); intros Hs; cbn [view_ok]; [exact Logic.I|exact Logic.I|].
  destruct Hs as [Hs _]. unfold okhd. eapply Forall_impl; [|exact Hs].
  intros θ [[[Hd _] Hn]|[Hc Hd]]; [left; split; assumption|right; split; [exact Hc|]].
  eapply Forall_impl; [|exact Hd]. intros λ [[Hl _] _]; exact Hl.
Qed.

Lemma HDf_okpos : Forall (okpos P) Df.
Proof. eapply Forall_impl; [|exact HDff]. intros θ [[Hd _] Hn]; left; split; assumption. Qed.

Lemma HDf_spos : Forall spos Df.
Proof. eapply Forall_impl; [|exact HDff]. intros θ Hθ; left; exact Hθ. Qed.

Context (C' : system XSym).
Hypothesis HC' : forall Γ (φ1 φ2 : tm' Γ P), conv C' φ1 φ2 -> vctx Γ ->
  forall Ξ, eqv Ξ (EL φ1) (EL φ2).
Hypothesis Hrules : forall i, Forall mspec (d_ctx (R i)) /\
  (forall p, In p (d_prems (R i)) -> Forall fpos (p_ext p)).

(** **Théorème.** L' = L + f + φ(x⃗, f(x⃗)) est conservative sur L pour les
    jugements de contexte du premier ordre. *)
Theorem definitional_conservative Γ (Ξ : list (form Γ)) (ψ : form Γ) :
  vctx Γ -> deriv C' P xrules Γ (map (emb Df b) Ξ) (emb Df b ψ) -> Ξ ⊢ ψ.
Proof.
  exact (def_conservative Htot_inst Huniq_inst HsymV_ok HDf_okpos Hb Harr_inj Harr_dom Harr_cod Hnoarr_P
           HsymV Hcong HDf_spos HDff Hbn Harr_uniq Hbeta C' HC' Hrules Γ Ξ ψ).
Qed.

(** **Théorème, sans hypothèse sur la traduction.** Si les conversions
    de L' (entre formules de contexte du premier ordre) s'obtiennent par
    réécriture en contexte avec β, η et des règles de calcul de L à
    métavariables du premier ordre, L' est conservative sur L. *)
Section CC.
Hypothesis Hview_lam : forall a b c (w : Arr a b c), view _ (s_lam w) = vw_lam w.
Hypothesis Hview_app : forall a b c (w : Arr a b c), view _ (s_app w) = vw_app w.
Context {J : Type} (R' : J -> rule XSym).
Hypothesis HR' : forall j,
  (exists a0 b0 c0 (w0 : Arr a0 b0 c0), R' j = @beta_rule _ XSym xFS _ _ _ w0) \/
  (exists a0 b0 c0 (w0 : Arr a0 b0 c0), R' j = @eta_rule _ XSym xFS _ _ _ w0) \/
  (exists r0 : rule Sym, R' j = {| r_ctx := r_ctx r0; r_sort := r_sort r0;
                                   r_lhs := emb Df b (r_lhs r0); r_rhs := emb Df b (r_rhs r0) |} /\
                         Forall mspec (r_ctx r0) /\ conv C (r_lhs r0) (r_rhs r0)).
Hypothesis HCC : forall Γ (φ1 φ2 : tm' Γ P), conv C' φ1 φ2 -> vctx Γ -> cconv R' φ1 φ2.

Theorem definitional_conservative_cc Γ (Ξ : list (form Γ)) (ψ : form Γ) :
  vctx Γ -> deriv C' P xrules Γ (map (emb Df b) Ξ) (emb Df b ψ) -> Ξ ⊢ ψ.
Proof.
  exact (def_conservative Htot_inst Huniq_inst HsymV_ok HDf_okpos Hb Harr_inj Harr_dom Harr_cod Hnoarr_P
           HsymV Hcong HDf_spos HDff Hbn Harr_uniq Hbeta C'
           (fun Γ φ1 φ2 Hc HΓ => cconv_eqv Htot_inst Huniq_inst HsymV_ok HDf_okpos Harr_inj Harr_dom Harr_cod
              Hnoarr_P HsymV Hcong HDf_spos Harr_uniq Hbeta Hview_lam Hview_app R' HR' φ1 φ2 (HCC Γ φ1 φ2 Hc HΓ) HΓ)
           Hrules Γ Ξ ψ).
Qed.

End CC.

End Final.

End Trans.

(** ** Le cas d'un calcul trivial

    Pour une logique du premier ordre sans conversion, L' n'a pas non plus
    de conversion : l'hypothèse [HC'] est alors immédiate. *)

Lemma triv_conv_mut {Srt : Type} {Sym : spec Srt -> Type} :
  (forall Γ s (t u : Terms.tm Sym Γ s), gconv (fun e : Empty_set => match e with end) Γ s t u -> t = u) /\
  (forall Γ Θ (a a' : Terms.args Sym Γ Θ), gargs (fun e : Empty_set => match e with end) Γ Θ a a' -> a = a').
Proof.
  apply gconv_gargs_ind; intros; subst; try reflexivity; try destruct i; try (symmetry; assumption);
    try (etransitivity; eassumption).
Qed.

Lemma triv_conv {Srt : Type} {Sym : spec Srt -> Type} Γ s (t u : Terms.tm Sym Γ s) :
  conv (generated (fun e : Empty_set => match e with end)) t u -> t = u.
Proof. apply (proj1 triv_conv_mut). Qed.
