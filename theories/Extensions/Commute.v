(** * Commutation de la traduction avec la substitution

    Pour une interprétation F de Σ₁ dans Σ₂, on montre

      ⟦t[v]⟧ = ⟦t⟧[⟦v⟧]                       ([tr_vsubst])
      ⟦happ σ u b⟧ = happ ⟦σ⟧ ⟦u⟧ ⟦b⟧          ([itm_happ])

    La preuve suit celle de [happ_commutes] (dans [Composition.v]). On
    établit d'abord, pour deux kits *reliés par la traduction* ([ktr]), que
    traduire puis traverser revient à traverser puis traduire
    ([itm_trav_mut]). Pour une variable substituée, ce lemme utilise la
    commutation avec [happ] à une spécification de profondeur plus petite.
    Celle-ci découle à son tour du lemme de traversée, appliqué au kit
    d'instanciation. On conclut par récurrence sur la profondeur
    ([itm_happ_all]).

    Le cas des symboles utilise que la traversée commute avec la
    substitution d'un terme clos de signature Σ₂ ([trav_vsubst]), conséquence
    de [trav_comp]. *)

From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Extensions Require Import Interpretation.

(** ** Traversée d'une substitution (dans une seule signature) *)

Lemma trav_vsubst {Srt} {Sym : spec Srt -> Type} n {Θ Δ s} (w : Terms.tm Sym Θ s) (b : args Sym Δ Θ)
  {Δ'} (K : kit Sym Δ Δ') :
  bounded n K -> trav (vsubst w b) K = vsubst w (trav_args b K).
Proof.
  intros HK. unfold vsubst, subst.
  rewrite (trav_comp w _ K n); [|exact (sub_kit_commutes (vget b) n)|exact HK].
  apply trav_ext; intros σ x. unfold kcomp, sub_kit, vget. rewrite aget_trav. reflexivity.
Qed.

Lemma ren_args_vren {Srt} {Sym : spec Srt -> Type} {Γ Θ} (b : args Sym Γ Θ) {Δ} (ξ : ren Γ Δ) :
  ren_args b ξ = vren b ξ.
Proof.
  apply vec_ext; intros σ x; unfold vget, vren. rewrite aget_vmap, aget_ren. reflexivity.
Qed.

Lemma trav_tvar {Srt} {Sym : spec Srt -> Type} {Γ σ} (x : var Γ σ) (a : args Sym Γ (dom σ)) {Δ} (K : kit Sym Γ Δ) :
  trav (tvar x a) K = match K σ x with
                      | inl y => tvar y (trav_args a K)
                      | inr (u, f) => f Δ u (trav_args a K)
                      end.
Proof. reflexivity. Qed.

Lemma trav_tsym {Srt} {Sym : spec Srt -> Type} {Γ σ} (c : Sym σ) (a : args Sym Γ (dom σ)) {Δ} (K : kit Sym Γ Δ) :
  trav (tsym c a) K = tsym c (trav_args a K).
Proof. reflexivity. Qed.

Lemma trav_args_acons {Srt} {Sym : spec Srt -> Type} {Γ σ Θ} (u : tms Sym Γ σ) (a : args Sym Γ Θ)
  {Δ} (K : kit Sym Γ Δ) :
  trav_args (acons u a) K = acons (trav u (kup (dom σ) K)) (trav_args a K).
Proof. reflexivity. Qed.

Lemma ren_tvar {Srt} {Sym : spec Srt -> Type} {Γ σ} (x : var Γ σ) (a : args Sym Γ (dom σ)) {Δ} (ξ : ren Γ Δ) :
  ren_tm (tvar x a) ξ = tvar (ξ σ x) (ren_args a ξ).
Proof. reflexivity. Qed.

Lemma ren_tsym {Srt} {Sym : spec Srt -> Type} {Γ σ} (c : Sym σ) (a : args Sym Γ (dom σ)) {Δ} (ξ : ren Γ Δ) :
  ren_tm (tsym c a) ξ = tsym c (ren_args a ξ).
Proof. reflexivity. Qed.

Lemma ren_args_acons {Srt} {Sym : spec Srt -> Type} {Γ σ Θ} (u : tms Sym Γ σ) (a : args Sym Γ Θ)
  {Δ} (ξ : ren Γ Δ) :
  ren_args (acons u a) ξ = acons (ren_tm u (upr (dom σ) ξ)) (ren_args a ξ).
Proof. reflexivity. Qed.

Section Commute.

Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type} (F : interp Sym1 Sym2).

Local Notation fs := (i_srt F).
Local Notation sm := (smap fs).
Local Notation cm := (cmap fs).
Local Notation tm1 := (Terms.tm Sym1).
Local Notation tm2 := (Terms.tm Sym2).
Local Notation vmap1 Γ Γ' := (forall σ, var Γ σ -> var Γ' (sm σ)).

(** ** Traduction des corps de spécification *)

Definition itms {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ : vmap1 Γ Γ') : tms Sym2 Γ' (sm σ) :=
  match σ as σ0 return tms Sym1 Γ σ0 -> tms Sym2 Γ' (sm σ0) with
  | Spec D c => fun u => itm F u (cm D ++ Γ') (vlift fs D ρ)
  end u.

Lemma itms_Spec {Γ D c} (u : tms Sym1 Γ (Spec D c)) Γ' (ρ : vmap1 Γ Γ') :
  itms u Γ' ρ = itm F u (cm D ++ Γ') (vlift fs D ρ).
Proof. reflexivity. Qed.

Lemma itm_tvar {Γ D c} (x : var Γ (Spec D c)) (a : args Sym1 Γ D) Γ' (ρ : vmap1 Γ Γ') :
  itm F (tvar x a) Γ' ρ = @tvar _ Sym2 Γ' (sm (Spec D c)) (ρ _ x) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma itm_tsym {Γ σ} (c : Sym1 σ) (a : args Sym1 Γ (dom σ)) Γ' (ρ : vmap1 Γ Γ') :
  itm F (tsym c a) Γ' ρ = vsubst (i_sym F c) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma iargs_acons {Γ σ Θ} (u : tms Sym1 Γ σ) (a : args Sym1 Γ Θ) Γ' (ρ : vmap1 Γ Γ') :
  iargs F (acons u a) Γ' ρ = @acons _ Sym2 Γ' (sm σ) _ (itms u Γ' ρ) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma vlift_vl D {Γ Γ'} (ρ : vmap1 Γ Γ') {σ} (z : var D σ) :
  vlift fs D ρ σ (vl Γ z) = vl Γ' (cvar fs z).
Proof. unfold vlift; rewrite vsplit_vl; reflexivity. Qed.

Lemma vlift_vr D {Γ Γ'} (ρ : vmap1 Γ Γ') {σ} (y : var Γ σ) :
  vlift fs D ρ σ (vr D y) = vr (cm D) (ρ σ y).
Proof. unfold vlift; rewrite vsplit_vr; reflexivity. Qed.

#[local] Hint Rewrite @vlift_vl @vlift_vr : vsimpl.

Lemma aget_iargs {Θ σ} (z : var Θ σ) {Γ} (b : args Sym1 Γ Θ) Γ' (ρ : vmap1 Γ Γ') :
  aget (cvar fs z) (iargs F b Γ' ρ) = itms (aget z b) Γ' ρ.
Proof.
  revert b; induction z as [Θ0 σ0|Θ0 σ0 τ0 z IH]; intros b;
    rewrite (args_eta b), iargs_acons; cbn [cvar aget ahd atl]; [reflexivity|apply IH].
Qed.

(** ** Extensionnalité *)

Lemma vlift_ext D {Γ Γ'} (ρ ρ' : vmap1 Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> forall σ x, vlift fs D ρ σ x = vlift fs D ρ' σ x.
Proof. intros H σ x; unfold vlift; destruct (vsplit D x); [reflexivity|rewrite H; reflexivity]. Qed.

Lemma itm_ext_mut :
  (forall Γ s (t : tm1 Γ s) Γ' (ρ ρ' : vmap1 Γ Γ'),
      (forall σ x, ρ σ x = ρ' σ x) -> itm F t Γ' ρ = itm F t Γ' ρ') /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Γ' (ρ ρ' : vmap1 Γ Γ'),
      (forall σ x, ρ σ x = ρ' σ x) -> iargs F a Γ' ρ = iargs F a Γ' ρ').
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Γ' ρ ρ' H. destruct σ as [D c]. rewrite !itm_tvar, H. f_equal. apply IH, H.
  - intros Γ σ c a IH Γ' ρ ρ' H. rewrite !itm_tsym. f_equal. apply IH, H.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Γ' ρ ρ' H. rewrite !iargs_acons. f_equal; [|apply IHa, H].
    destruct σ as [D c]. rewrite !itms_Spec. apply IHu, vlift_ext, H.
Qed.

Lemma itm_ext {Γ s} (t : tm1 Γ s) Γ' (ρ ρ' : vmap1 Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> itm F t Γ' ρ = itm F t Γ' ρ'.
Proof. apply itm_ext_mut. Qed.

Lemma itms_ext {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ ρ' : vmap1 Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> itms u Γ' ρ = itms u Γ' ρ'.
Proof. intros H; destruct σ as [D c]; rewrite !itms_Spec; apply itm_ext, vlift_ext, H. Qed.

(** ** Renommages *)

(** Renommer puis traduire. *)
Lemma itm_ren_mut :
  (forall Γ s (t : tm1 Γ s) Δ (ξ : ren Γ Δ) Γ' (ρ : vmap1 Δ Γ'),
      itm F (ren_tm t ξ) Γ' ρ = itm F t Γ' (fun σ x => ρ σ (ξ σ x))) /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Δ (ξ : ren Γ Δ) Γ' (ρ : vmap1 Δ Γ'),
      iargs F (ren_args a ξ) Γ' ρ = iargs F a Γ' (fun σ x => ρ σ (ξ σ x))).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Δ ξ Γ' ρ. destruct σ as [D c].
    rewrite ren_tvar, !itm_tvar. f_equal. apply IH.
  - intros Γ σ c a IH Δ ξ Γ' ρ. rewrite ren_tsym, !itm_tsym. f_equal. apply IH.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ ξ Γ' ρ. rewrite ren_args_acons, !iargs_acons. f_equal; [|apply IHa].
    destruct σ as [D c]. rewrite !itms_Spec. cbn [dom]. rewrite IHu.
    apply itm_ext; intros τ x. vcase x; vsimp; reflexivity.
Qed.

(** Traduire puis renommer. *)
Lemma ren_itm_mut :
  (forall Γ s (t : tm1 Γ s) Γ' (ρ : vmap1 Γ Γ') Δ' (ξ : ren Γ' Δ'),
      ren_tm (itm F t Γ' ρ) ξ = itm F t Δ' (fun σ x => ξ (sm σ) (ρ σ x))) /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Γ' (ρ : vmap1 Γ Γ') Δ' (ξ : ren Γ' Δ'),
      ren_args (iargs F a Γ' ρ) ξ = iargs F a Δ' (fun σ x => ξ (sm σ) (ρ σ x))).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Γ' ρ Δ' ξ. destruct σ as [D c].
    rewrite !itm_tvar.
    transitivity (@tvar _ Sym2 Δ' (sm (Spec D c)) (ξ _ (ρ _ x)) (ren_args (iargs F a Γ' ρ) ξ));
      [reflexivity|]. f_equal. apply IH.
  - intros Γ σ c a IH Γ' ρ Δ' ξ. rewrite !itm_tsym, ren_vsubst, <- ren_args_vren. f_equal. apply IH.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Γ' ρ Δ' ξ. rewrite !iargs_acons.
    etransitivity; [exact (ren_args_acons (itms u Γ' ρ) (iargs F a Γ' ρ) ξ)|].
    f_equal; [|apply IHa].
    destruct σ as [D c]. rewrite !itms_Spec. cbn [dom smap]. rewrite IHu.
    apply itm_ext; intros τ x. vcase x; vsimp; reflexivity.
Qed.

Lemma itms_ren {Γ σ} (u : tms Sym1 Γ σ) {Δ} (ξ : ren Γ Δ) Γ' (ρ : vmap1 Δ Γ') :
  itms (ren_tms u ξ) Γ' ρ = itms u Γ' (fun σ x => ρ σ (ξ σ x)).
Proof.
  destruct σ as [D c]. unfold ren_tms. rewrite !itms_Spec. cbn [dom].
  rewrite (proj1 itm_ren_mut). apply itm_ext; intros τ x. vcase x; vsimp; reflexivity.
Qed.

Lemma ren_itms {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ : vmap1 Γ Γ') {Δ'} (ξ : ren Γ' Δ') :
  ren_tms (itms u Γ' ρ) ξ = itms u Δ' (fun σ x => ξ (sm σ) (ρ σ x)).
Proof.
  destruct σ as [D c]. unfold ren_tms. rewrite !itms_Spec.
  transitivity (itm F u (cm D ++ Δ') (fun τ x => upr (cm D) ξ (sm τ) (vlift fs D ρ τ x)));
    [exact (proj1 ren_itm_mut _ _ u _ (vlift fs D ρ) _ (upr (cm D) ξ))|].
  apply itm_ext; intros τ x. vcase x; vsimp; reflexivity.
Qed.

(** Affaiblir sous un lieur, de part et d'autre de la traduction. *)
Lemma itms_wk D {Δ σ} (u : tms Sym1 Δ σ) Δ' (ρ : vmap1 Δ Δ') :
  itms (ren_tms u (wk D)) (cm D ++ Δ') (vlift fs D ρ) = ren_tms (itms u Δ' ρ) (wk (cm D)).
Proof.
  rewrite itms_ren, ren_itms. apply itms_ext; intros τ x. unfold wk. vsimp. reflexivity.
Qed.

(** ** Kits reliés par la traduction *)

(** [ktr m ρΓ ρΔ K K'] : pour chaque variable x de Γ, l'entrée de K' en
    ⟦x⟧ est la traduction de l'entrée de K en x. Les entrées substituées
    sont des [happ] de profondeur < m. *)
Definition ktr (m : nat) {Γ Δ Γ' Δ'} (ρΓ : vmap1 Γ Γ') (ρΔ : vmap1 Δ Δ')
  (K : kit Sym1 Γ Δ) (K' : kit Sym2 Γ' Δ') : Prop :=
  forall σ x,
    match K σ x with
    | inl y => K' (sm σ) (ρΓ σ x) = inl (ρΔ σ y)
    | inr (u, f) => f = happ σ /\ depth σ < m /\
                    K' (sm σ) (ρΓ σ x) = inr (itms u Δ' ρΔ, happ (sm σ))
    end.

Lemma ktr_kup m D {Γ Δ Γ' Δ'} (ρΓ : vmap1 Γ Γ') (ρΔ : vmap1 Δ Δ') K K' :
  ktr m ρΓ ρΔ K K' -> ktr m (vlift fs D ρΓ) (vlift fs D ρΔ) (kup D K) (kup (cm D) K').
Proof.
  intros H σ x. vcase x; vsimp; [reflexivity|].
  specialize (H σ z). destruct (K σ z) as [w|[u f]]; cbn [eshift]; vsimp.
  - rewrite H; cbn [eshift]. reflexivity.
  - destruct H as (-> & Hd & H). split; [reflexivity|split; [exact Hd|]].
    rewrite H; cbn [eshift]. rewrite itms_wk. reflexivity.
Qed.

(** La commutation avec [happ] jusqu'à la profondeur d. *)
Definition happ_tr (d : nat) : Prop :=
  forall D c, depth (Spec D c) < d ->
  forall Δ Δ' (ρ : vmap1 Δ Δ') (u : tm1 (D ++ Δ) c) (b : args Sym1 Δ D),
    itm F (happ (Spec D c) u b) Δ' ρ
    = happ (Spec (cm D) (fs c)) (itm F u (cm D ++ Δ') (vlift fs D ρ)) (iargs F b Δ' ρ).

(** ** Le lemme de traversée *)

Lemma itm_trav_mut m (HC : happ_tr m) :
  (forall Γ s (t : tm1 Γ s) Δ Γ' Δ' (ρΓ : vmap1 Γ Γ') (ρΔ : vmap1 Δ Δ') K K' n,
      ktr m ρΓ ρΔ K K' -> bounded n K' ->
      itm F (trav t K) Δ' ρΔ = trav (itm F t Γ' ρΓ) K') /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Δ Γ' Δ' (ρΓ : vmap1 Γ Γ') (ρΔ : vmap1 Δ Δ') K K' n,
      ktr m ρΓ ρΔ K K' -> bounded n K' ->
      iargs F (trav_args a K) Δ' ρΔ = trav_args (iargs F a Γ' ρΓ) K').
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn. destruct σ as [D c].
    pose proof (HK _ x) as Hx.
    assert (E : trav (itm F (tvar x a) Γ' ρΓ) K'
                = match K' (sm (Spec D c)) (ρΓ _ x) with
                  | inl y => @tvar _ Sym2 Δ' (sm (Spec D c)) y (trav_args (iargs F a Γ' ρΓ) K')
                  | inr (u, f) => f Δ' u (trav_args (iargs F a Γ' ρΓ) K')
                  end) by reflexivity.
    rewrite E, trav_tvar. clear E.
    destruct (K _ x) as [y|[u f]].
    + rewrite Hx, itm_tvar. f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
    + destruct Hx as (-> & Hd & Hx). rewrite Hx.
      rewrite (HC D c Hd). f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
  - intros Γ σ c a IH Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn.
    rewrite trav_tsym, !itm_tsym, (trav_vsubst n _ _ K' Hn). f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn.
    rewrite trav_args_acons, !iargs_acons.
    etransitivity; [|symmetry; exact (trav_args_acons (itms u Γ' ρΓ) (iargs F a Γ' ρΓ) K')].
    f_equal; [|apply (IHa _ _ _ _ _ _ _ _ HK Hn)].
    destruct σ as [D c]. rewrite !itms_Spec. cbn [dom smap].
    apply (IHu _ _ _ _ _ (kup D K) (kup (cm D) K') n); [apply ktr_kup, HK|apply bounded_kup, Hn].
Qed.

(** ** La commutation avec l'application héréditaire *)

Theorem itm_happ_all d : happ_tr d.
Proof.
  induction d as [|d IHd]; intros D c Hd; [lia|].
  intros Δ Δ' ρ u b. rewrite !happ_Spec.
  assert (HC : happ_tr (depth (Spec D c))) by (intros D' c' H'; apply IHd; lia).
  apply (proj1 (itm_trav_mut _ HC) _ _ u Δ (cm D ++ Δ') Δ' (vlift fs D ρ) ρ _ _
                 (depth (Spec (cm D) (fs c)))).
  - intros σ x. vcase x; vsimp.
    + rewrite !all_get_happs, aget_iargs. split; [reflexivity|split; [exact (depth_dom c z)|reflexivity]].
    + reflexivity.
  - intros σ' x u' f E. unfold inst_kit in E. destruct (vsplit (cm D) x) as [z|y]; [|discriminate].
    injection E as <- <-. split; [apply all_get_happs|exact (depth_dom (fs c) z)].
Qed.

Corollary itm_happ {D c Δ} (u : tm1 (D ++ Δ) c) (b : args Sym1 Δ D) Δ' (ρ : vmap1 Δ Δ') :
  itm F (happ (Spec D c) u b) Δ' ρ
  = happ (Spec (cm D) (fs c)) (itm F u (cm D ++ Δ') (vlift fs D ρ)) (iargs F b Δ' ρ).
Proof. apply (itm_happ_all (S (depth (Spec D c)))); lia. Qed.

(** ** La commutation avec la substitution par un vecteur *)

(** Traduction d'un vecteur Θ → Γ en un vecteur ⟦Θ⟧ → ⟦Γ⟧. *)
Definition trv {Θ Γ} (v : vec Sym1 Θ Γ) : vec Sym2 (cm Θ) (cm Γ) :=
  iargs F v (cm Γ) (fun σ x => cvar fs x).

Theorem itm_vsubst {Θ Γ s} (t : tm1 Θ s) (v : vec Sym1 Θ Γ) Γ' (ρ : vmap1 Γ Γ') Θ' (ρΘ : vmap1 Θ Θ')
  (v' : vec Sym2 Θ' Γ') :
  (forall σ x, aget (ρΘ σ x) v' = itms (aget x v) Γ' ρ) ->
  itm F (vsubst t v) Γ' ρ = vsubst (itm F t Θ' ρΘ) v'.
Proof.
  intros Hv. unfold vsubst at 1, subst.
  apply (proj1 (itm_trav_mut (S (depths Θ)) (itm_happ_all _)) _ _ t Γ Θ' Γ' ρΘ ρ _ _ (S (depths Θ'))).
  - intros σ x. cbn [sub_kit]. unfold vget, sub_kit. rewrite Hv.
    split; [reflexivity|split; [pose proof (depth_var x); lia|reflexivity]].
  - apply bounded_sub_kit.
Qed.

Theorem tr_vsubst {Θ Γ s} (t : tm1 Θ s) (v : vec Sym1 Θ Γ) :
  tr F (vsubst t v) = vsubst (tr F t) (trv v).
Proof. apply itm_vsubst; intros σ x; unfold trv; apply aget_iargs. Qed.

End Commute.

Arguments itms {S1 S2 Sym1 Sym2} F {Γ σ} u Γ' ρ.
Arguments trv {S1 S2 Sym1 Sym2} F {Θ Γ} v.
