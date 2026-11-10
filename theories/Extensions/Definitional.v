(** * Extensions par définition d'un symbole de fonction : la traduction

    On part d'une logique L sur la signature [Sym], de sorte des
    propositions P, et d'une formule φ(x⃗, y), de contexte [ι b :: Df],
    telle que L ⊢ ∀x⃗ ∃!y φ(x⃗, y). L'extension L' ajoute un symbole
    f : Df → b et l'axiome φ(x⃗, f(x⃗)). On montre que L' est conservative
    sur L (fichier [DefSound.v]) en éliminant f par une traduction des
    formules de L' dans L.

    ** La traduction

    Elle est écrite en style « par continuation » : [tr t Δ w K] traduit le
    terme t de L' sous l'environnement w (un vecteur de L vers Δ), et passe
    sa valeur à la continuation K, une formule de L avec un trou de la sorte
    de t. Pour f(u⃗), on obtient ∃y. φ(u⃗*, y) ∧ K[y] : seule f introduit un
    quantificateur, et la traduction d'un terme sans f est
    [K[t[w]]] ([tr_emb]).

    Les positions d'arguments sont de deux sortes :
    - une position « flottante » (sans lieur, de sorte autre que P) :
      l'existentielle produite par l'argument remonte au-dessus du symbole ;
    - une position « locale » (de sorte P, avec ou sans lieurs) : l'argument
      est une formule, traduite sur place, avec la continuation triviale.
    Les autres positions (un terme de sorte autre que P sous des lieurs)
    sont traduites par ⊤, ce qui ne sert jamais sous les conditions de
    [DefSound.v].

    ** La couche du bord : lambda et app

    Une vue ([symview]) reconnaît les symboles lambda et app de la couche
    fonctionnelle. La traduction reçoit en plus une **pile** des valeurs
    des arguments en attente ([spine]) : pour app(F, u), on évalue u, puis
    on traduit F avec la valeur de u en tête de pile ; un lambda qui trouve
    une pile non vide lie sa variable à la valeur de tête, ce qui contracte
    le β-redex à la traduction ; toute autre tête reçoit la pile appliquée
    par app ([spK]). Comme les arguments de app sont de sorte non flèche, la
    valeur substituée ne crée jamais de nouveau redex : la traduction reste
    structurelle. Une formule de L est donc traduite en sa forme β-réduite,
    convertible à elle-même dès que le calcul de L contient β ([el_emb]).

    La traduction des formules est [el ψ := tr ψ Γ P id [] □], où □ est la
    continuation triviale (le trou propositionnel). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant.

Local Notation ι a := (Spec [] a).

(** ** La signature étendue *)

Inductive xsym {Srt : Type} (Sym : spec Srt -> Type) (Df : ctx Srt) (b : Srt) : spec Srt -> Type :=
| xold {σ} : Sym σ -> xsym Sym Df b σ
| xf : xsym Sym Df b (Spec Df b).

Arguments xold {Srt Sym Df b σ} c.
Arguments xf {Srt Sym Df b}.

(** ** Opérations sur les continuations *)

Section Cont.
Context {Srt : Type} {Sym : spec Srt -> Type}.

Local Notation tm := (Terms.tm Sym).
Local Notation vec := (vec Sym).

(** Les variables de Θ, vues dans Θ ++ Δ. *)
Definition holes (Θ : ctx Srt) (Δ : ctx Srt) : Terms.args Sym (Θ ++ Δ) Θ :=
  etas Θ (fun _ z => vl Δ z).

(** L'affaiblissement de Δ dans Θ ++ Δ, comme vecteur. *)
Definition wkv (Θ : ctx Srt) (Δ : ctx Srt) : vec Δ (Θ ++ Δ) := vren (vid Δ) (wk Θ).

(** Brancher la valeur τ (dans Θ ++ Δ) dans le trou d'une continuation. *)
Definition plug {Δ s P} (Θ : ctx Srt) (K : tm (ι s :: Δ) P) (τ : tm (Θ ++ Δ) s) : tm (Θ ++ Δ) P :=
  vsubst K (@acons _ Sym (Θ ++ Δ) (ι s) Δ τ (wkv Θ Δ)).

(** Substituer la position 0 (de spécification σ) par un corps A. *)
Definition sub0 {Δ σ P} (K : tm (σ :: Δ) P) (A : Terms.tms Sym Δ σ) : tm Δ P :=
  vsubst K (@acons _ Sym Δ σ Δ A (vid Δ)).

(** Échanger le trou de tête avec les variables de Θ. *)
Definition perm (Θ : ctx Srt) {Δ} (τ : spec Srt) : ren (τ :: Θ ++ Δ) (Θ ++ τ :: Δ) :=
  fun σ x => var_inv (fun σ' _ => var (Θ ++ τ :: Δ) σ')
               (vr Θ vz)
               (fun σ' y => match vsplit Θ y with
                            | inl z => vl (τ :: Δ) z
                            | inr y' => vr Θ (vs y')
                            end) σ x.

End Cont.


(** ** Algèbre des vecteurs utilisée par la traduction *)

Section Alg.
Context {Srt : Type} {Sym : spec Srt -> Type}.

Local Notation tm := (Terms.tm Sym).
Local Notation tms := (Terms.tms Sym).
Local Notation vec := (vec Sym).

Lemma aget_vup_l Λ {Γ Δ σ} (v : vec Γ Δ) (z : var Λ σ) :
  aget (vl Γ z) (vup Λ v) = eta σ (vl Δ z).
Proof. unfold vup. rewrite aget_vcat_l, aget_etas. reflexivity. Qed.

Lemma aget_vup_r' Λ {Γ Δ σ} (v : vec Γ Δ) (y : var Γ σ) :
  aget (vr Λ y) (vup Λ v) = ren_tms (aget y v) (wk Λ).
Proof. unfold vup, vren. rewrite aget_vcat_r, aget_vmap. reflexivity. Qed.

Lemma aget_wkv Θ {Δ σ} (y : var Δ σ) : aget y (wkv (Sym := Sym) Θ Δ) = eta σ (vr Θ y).
Proof. unfold wkv, vren. rewrite aget_vmap, aget_vid, eta_ren. reflexivity. Qed.

Lemma aget_holes Θ Δ {σ} (z : var Θ σ) : aget z (holes (Sym := Sym) Θ Δ) = eta σ (vl Δ z).
Proof. unfold holes. exact (aget_etas z _). Qed.

Lemma vsubst_tms_ren' {Γ σ} (u : tms Γ σ) {Δ Ξ} (ρ : ren Γ Δ) (w : vec Δ Ξ) :
  vsubst_tms (ren_tms u ρ) w = vsubst_tms u (vpre ρ w).
Proof.
  unfold vsubst_tms. rewrite subst_tms_ren. apply subst_tms_ext; intros τ x.
  unfold rs_comp, vget. rewrite aget_vpre. reflexivity.
Qed.

Lemma vpre_wk1 {τ Δ Ξ} (t : tms Ξ τ) (w : vec Δ Ξ) :
  vpre (wk [τ]) (@acons _ Sym Ξ τ Δ t w) = w.
Proof. apply vec_ext; intros ρ y; unfold vget. rewrite aget_vpre. reflexivity. Qed.

Lemma vpre_wk {Θ Δ Ξ} (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) : vpre (wk Θ) (vcat Θ a w) = w.
Proof. apply vec_ext; intros ρ y; unfold vget. rewrite aget_vpre. unfold wk. apply aget_vcat_r. Qed.

Lemma vup_cons τ Λ {Γ Δ} (v : vec Γ Δ) : vup [τ] (vup Λ v) = vup (τ :: Λ) v.
Proof.
  apply vec_ext; intros σ x; unfold vget. revert σ x. refine (var_inv _ _ _); [reflexivity|].
  intros σ y. unfold vup at 1. cbn [vcat app aget atl ahd etas]. unfold vren at 1. rewrite aget_vmap.
  unfold vup. vcase y.
  - rewrite aget_vcat_l, aget_etas, eta_ren.
    change (vs (vl Γ z)) with (vl Γ (vs (σ := σ) (τ := τ) z)).
    etransitivity; [|symmetry; exact (aget_vcat_l (Θ := τ :: Λ) (vs z) _ _)]. rewrite aget_etas. reflexivity.
  - rewrite aget_vcat_r. unfold vren. rewrite aget_vmap, ren_tms_ren.
    change (vs (vr Λ z)) with (vr (τ :: Λ) z).
    etransitivity; [|symmetry; exact (aget_vcat_r (τ :: Λ) z _ _)]. rewrite aget_vmap.
    apply ren_tms_ext; intros; reflexivity.
Qed.

(** Brancher puis substituer. *)
Lemma plug_vsubst {Δ Δ0 s P} Θ (K : tm (ι s :: Δ) P) (τ : tm (Θ ++ Δ) s) (σ : vec Δ Δ0) :
  vsubst (plug Θ K τ) (vup Θ σ) = plug Θ (vsubst K (vup [ι s] σ)) (vsubst τ (vup Θ σ)).
Proof.
  unfold plug. rewrite !vsubst_vsubst. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite !aget_vcomp. revert ρ x. refine (var_inv _ _ _).
  - cbn [aget ahd]. rewrite vsubst_tms_nil. unfold vup at 2. cbn [vcat aget ahd etas].
    rewrite (vsubst_eta (Γ := ι s :: Δ0) vz). reflexivity.
  - intros ρ y. cbn [aget atl]. rewrite aget_wkv, vsubst_eta, aget_vup_r'.
    change (atl (vup [ι s] σ)) with (vren σ (wk [ι s])). unfold vren. rewrite aget_vmap.
    rewrite vsubst_tms_ren', vpre_wk1.
    unfold wkv. rewrite <- ren_vsubst_tms, vsubst_tms_vid. reflexivity.
Qed.

Lemma holes_vsubst Θ {Δ Δ0} (σ : vec Δ Δ0) :
  vsubst_args (holes (Sym := Sym) Θ Δ) (vup Θ σ) = holes Θ Δ0.
Proof.
  apply vec_ext; intros ρ z; unfold vget. unfold vsubst_args.
  rewrite aget_subst_args, !aget_holes. fold (vsubst_tms (eta ρ (vl Δ z)) (vup Θ σ)).
  rewrite vsubst_eta, aget_vup_l. reflexivity.
Qed.


Lemma sub0_vsubst {Δ Δ0 σ0 P} (K : tm (σ0 :: Δ) P) (A : tms Δ σ0) (τ : vec Δ Δ0) :
  vsubst (sub0 K A) τ = sub0 (vsubst K (vup [σ0] τ)) (vsubst_tms A τ).
Proof.
  unfold sub0. rewrite !vsubst_vsubst. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite !aget_vcomp. revert ρ x. refine (var_inv _ _ _).
  - cbn [aget ahd]. unfold vup. cbn [vcat aget ahd etas]. rewrite vsubst_eta. reflexivity.
  - intros ρ y. cbn [aget atl]. rewrite aget_vid, vsubst_eta.
    change (atl (vup [σ0] τ)) with (vren τ (wk [σ0])). unfold vren. rewrite aget_vmap.
    rewrite vsubst_tms_ren', vpre_wk1, vsubst_tms_vid. reflexivity.
Qed.

Lemma vcomp_vren_wk1 τ0 {Γ Δ Δ0} (w : vec Γ Δ) (σ : vec Δ Δ0) :
  vcomp (Δ := τ0 :: Δ) (Ξ := τ0 :: Δ0) (vren (Ξ := τ0 :: Δ) w (wk [τ0])) (vup [τ0] σ)
  = vren (Ξ := τ0 :: Δ0) (vcomp w σ) (wk [τ0]).
Proof.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vcomp. unfold vren. rewrite !aget_vmap, !aget_vcomp.
  rewrite vsubst_tms_ren'. rewrite ren_vsubst_tms. f_equal.
  apply vec_ext; intros ρ' y; unfold vget. rewrite aget_vpre. unfold wk; cbn [vr].
  unfold vup. cbn [vcat aget atl]. unfold vren. rewrite !aget_vmap. reflexivity.
Qed.

Lemma vsubst_ren_upr_wk Λ Θ {Δ Δ0 s} (X : tm (Λ ++ Δ) s) (σ : vec Δ Δ0) :
  vsubst (ren_tm X (upr Λ (wk Θ))) (vup Λ (vup Θ σ)) = ren_tm (vsubst X (vup Λ σ)) (upr Λ (wk Θ)).
Proof.
  rewrite vsubst_ren, ren_vsubst. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre. unfold vren. rewrite aget_vmap. vcase x.
  - rewrite upr_vl, !aget_vup_l, eta_ren, upr_vl. reflexivity.
  - rewrite upr_vr. unfold wk at 1. rewrite !aget_vup_r'. rewrite ren_tms_ren, ren_tms_ren.
    apply ren_tms_ext; intros ρ' y. unfold rcomp, wk. rewrite upr_vr. reflexivity.
Qed.

Lemma perm_vs_vl (Θ Δ : ctx Srt) (τ0 σ : spec Srt) (z : var Θ σ) :
  perm Θ (Δ := Δ) τ0 σ (vs (vl Δ z)) = vl (τ0 :: Δ) z.
Proof. unfold perm. cbn. rewrite vsplit_vl. reflexivity. Qed.

Lemma perm_vs_vr (Θ Δ : ctx Srt) (τ0 σ : spec Srt) (y : var Δ σ) :
  perm Θ (Δ := Δ) τ0 σ (vs (vr Θ y)) = vr Θ (vs y).
Proof. unfold perm. cbn. rewrite vsplit_vr. reflexivity. Qed.

Lemma perm_vz (Θ Δ : ctx Srt) (τ0 : spec Srt) : perm Θ (Δ := Δ) τ0 τ0 vz = vr Θ vz.
Proof. reflexivity. Qed.

Lemma perm_vsubst Θ τ0 {Δ Δ0 P} (K : tm (τ0 :: Θ ++ Δ) P) (σ : vec Δ Δ0) :
  vsubst (Δ := Θ ++ τ0 :: Δ0) (ren_tm K (perm Θ τ0)) (vup Θ (Γ := τ0 :: Δ) (Δ := τ0 :: Δ0) (vup [τ0] σ))
  = ren_tm (vsubst K (vup (τ0 :: Θ) σ)) (perm Θ τ0).
Proof.
  rewrite vsubst_ren, ren_vsubst. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre. unfold vren. rewrite aget_vmap.
  revert ρ x. refine (var_inv _ _ _).
  - rewrite perm_vz, aget_vup_r'.
    change (aget vz (vup [τ0] σ)) with (aget (vl (Θ := [τ0]) Δ vz) (vup [τ0] σ)).
    change (aget vz (vup (τ0 :: Θ) σ)) with (aget (vl (Θ := τ0 :: Θ) Δ vz) (vup (τ0 :: Θ) σ)).
    rewrite !aget_vup_l, !eta_ren. reflexivity.
  - intros ρ y. vcase y.
    + rewrite perm_vs_vl, aget_vup_l.
      change (aget (vs (vl Δ z)) (vup (τ0 :: Θ) σ)) with (aget (vl (Θ := τ0 :: Θ) Δ (vs z)) (vup (τ0 :: Θ) σ)).
      rewrite aget_vup_l, eta_ren. cbn [vl]. rewrite perm_vs_vl. reflexivity.
    + rewrite perm_vs_vr, aget_vup_r'.
      change (aget (vs (vr Θ z)) (vup (τ0 :: Θ) σ)) with (aget (vr (τ0 :: Θ) z) (vup (τ0 :: Θ) σ)).
      rewrite aget_vup_r'. change (aget (vs z) (vup [τ0] σ)) with (aget (vr [τ0] z) (vup [τ0] σ)).
      rewrite aget_vup_r', !ren_tms_ren. apply ren_tms_ext; intros ρ' y. unfold rcomp, wk.
      cbn [vr]. rewrite perm_vs_vr. reflexivity.
Qed.

Lemma vup_vcons_split σ0 Θ {Δ Δ0} (σ : vec Δ Δ0) : vup [σ0] (vup Θ σ) = vup (σ0 :: Θ) σ.
Proof. apply vup_cons. Qed.

Lemma vcomp_wkv_vcat Θ {Δ Ξ} (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) : vcomp (wkv Θ Δ) (vcat Θ a w) = w.
Proof.
  apply vec_ext; intros ρ y; unfold vget. rewrite aget_vcomp, aget_wkv, vsubst_eta, aget_vcat_r. reflexivity.
Qed.

Lemma plug_inst {Δ s P} Θ (K : tm (ι s :: Δ) P) (τ : tm (Θ ++ Δ) s) (a : Terms.args Sym Δ Θ) :
  vsubst (plug Θ K τ) (vcat Θ a (vid Δ)) = vsubst K (inst1 (vsubst τ (vcat Θ a (vid Δ)))).
Proof.
  unfold plug. rewrite vsubst_vsubst. f_equal.
  change (vcomp (@acons _ Sym (Θ ++ Δ) (ι s) Δ τ (wkv Θ Δ)) (vcat Θ a (vid Δ)))
    with (@acons _ Sym Δ (ι s) Δ (vsubst_tms (σ := ι s) τ (vcat Θ a (vid Δ))) (vcomp (wkv Θ Δ) (vcat Θ a (vid Δ)))).
  rewrite vsubst_tms_nil, vcomp_wkv_vcat. reflexivity.
Qed.

Lemma holes_inst Θ {Δ Ξ} (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) :
  vsubst_args (holes Θ Δ) (vcat Θ a w) = a.
Proof.
  apply vec_ext; intros ρ z; unfold vget, vsubst_args. rewrite aget_subst_args, aget_holes.
  fold (vsubst_tms (eta ρ (vl Δ z)) (vcat Θ a w)). rewrite vsubst_eta, aget_vcat_l. reflexivity.
Qed.

Lemma vup_vid Λ {Δ} : vup Λ (vid (Sym := Sym) Δ) = vid (Λ ++ Δ).
Proof.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vid. vcase x.
  - rewrite aget_vup_l. reflexivity.
  - rewrite aget_vup_r', aget_vid, eta_ren. reflexivity.
Qed.

Lemma vsubst_ren_upr_wk_cat Λ Θ {Δ Ξ s} (X : tm (Λ ++ Δ) s) (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) :
  vsubst (ren_tm X (upr Λ (wk Θ))) (vup Λ (vcat Θ a w)) = vsubst X (vup Λ w).
Proof.
  rewrite vsubst_ren. f_equal. apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre. vcase x.
  - rewrite upr_vl, !aget_vup_l. reflexivity.
  - rewrite upr_vr, !aget_vup_r'. unfold wk. rewrite aget_vcat_r. reflexivity.
Qed.

Lemma vcomp_vren_wk_inst1 {Γ Δ c} (w : vec Γ Δ) (X : tm Δ c) :
  vcomp (Δ := ι c :: Δ) (vren (Ξ := ι c :: Δ) w (wk [ι c])) (inst1 X) = w.
Proof.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vcomp. unfold vren. rewrite aget_vmap.
  rewrite vsubst_tms_ren'. rewrite <- (vsubst_tms_vid (aget x w)) at 2. f_equal.
  apply vec_ext; intros ρ' y; unfold vget. rewrite aget_vpre. reflexivity.
Qed.

Lemma perm_inst Θ {Δ c P} (K : tm (ι c :: Θ ++ Δ) P) (a : Terms.args Sym (ι c :: Δ) Θ) (X : tm Δ c) :
  vsubst (vsubst (ren_tm K (perm Θ (ι c))) (vcat Θ a (vid (ι c :: Δ)))) (inst1 X)
  = vsubst K (@acons _ Sym Δ (ι c) _ X (vcat Θ (vsubst_args a (inst1 X)) (vid Δ))).
Proof.
  rewrite vsubst_vsubst, vsubst_ren. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre. revert ρ x. refine (var_inv _ _ _).
  - rewrite perm_vz, aget_vcomp, aget_vcat_r, aget_vid, vsubst_eta. reflexivity.
  - intros ρ y. vcase y.
    + rewrite perm_vs_vl, aget_vcomp, aget_vcat_l. cbn [aget atl]. rewrite aget_vcat_l.
      unfold vsubst_args. rewrite aget_subst_args. reflexivity.
    + rewrite perm_vs_vr, aget_vcomp, aget_vcat_r, aget_vid, vsubst_eta. cbn [aget atl].
      rewrite aget_vcat_r. reflexivity.
Qed.

Lemma vup_vpre Λ {Δ Δ'} (ρ : ren Δ Δ') : vup Λ (vpre ρ (vid (Sym := Sym) Δ')) = vpre (upr Λ ρ) (vid (Λ ++ Δ')).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre, aget_vid. vcase x.
  - rewrite aget_vup_l, upr_vl. reflexivity.
  - rewrite aget_vup_r', aget_vpre, aget_vid, eta_ren, upr_vr. reflexivity.
Qed.

Lemma ren_tms_as_vsubst {Γ σ} (u : tms Γ σ) {Δ} (ρ : ren Γ Δ) : ren_tms u ρ = vsubst_tms u (vpre ρ (vid Δ)).
Proof. rewrite vsubst_tms_vup, vup_vpre. unfold ren_tms. apply ren_as_vsubst. Qed.

Lemma vcomp_vpre_vid {Γ Δ Δ'} (w : vec Γ Δ) (ρ : ren Δ Δ') : vcomp w (vpre ρ (vid Δ')) = vren w ρ.
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. unfold vren. rewrite aget_vmap.
  symmetry; apply ren_tms_as_vsubst.
Qed.

Lemma vsubst_vup_vpre Λ {Δ Δ' P} (K : tm (Λ ++ Δ) P) (ρ : ren Δ Δ') :
  vsubst K (vup Λ (vpre ρ (vid Δ'))) = ren_tm K (upr Λ ρ).
Proof. rewrite vup_vpre. symmetry; apply ren_as_vsubst. Qed.

Lemma perm_inst2 Θ {Δ c P} (K : tm (ι c :: Θ ++ Δ) P) (X : tm Δ c) (a : Terms.args Sym Δ Θ) :
  vsubst (vsubst (ren_tm K (perm Θ (ι c))) (vup Θ (Γ := ι c :: Δ) (inst1 X))) (vcat Θ a (vid Δ))
  = vsubst K (@acons _ Sym Δ (ι c) _ X (vcat Θ a (vid Δ))).
Proof.
  rewrite !vsubst_vsubst, vsubst_ren. f_equal.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vpre, aget_vcomp. revert ρ x. refine (var_inv _ _ _).
  - rewrite perm_vz, aget_vup_r'. cbn [aget ahd inst1].
    rewrite vsubst_tms_ren', vpre_wk, vsubst_tms_vid. reflexivity.
  - intros ρ y. vcase y.
    + rewrite perm_vs_vl, aget_vup_l, vsubst_eta, aget_vcat_l. cbn [aget atl]. rewrite aget_vcat_l. reflexivity.
    + rewrite perm_vs_vr, aget_vup_r'. cbn [aget atl inst1]. rewrite aget_vid, eta_ren, vsubst_eta.
      reflexivity.
Qed.

Lemma sub0_inst Λ Θ {Δ P} (K : tm (Spec Λ P :: Θ ++ Δ) P) (A : tm (Λ ++ Δ) P) (a : Terms.args Sym Δ Θ) :
  vsubst (sub0 (σ := Spec Λ P) K (ren_tm A (upr Λ (wk Θ)))) (vcat Θ a (vid Δ))
  = vsubst K (@acons _ Sym Δ (Spec Λ P) _ A (vcat Θ a (vid Δ))).
Proof.
  unfold sub0. rewrite vsubst_vsubst.
  match goal with |- vsubst K (vcomp (@acons _ _ _ _ _ ?A0 _) ?V) = _ =>
    change (vcomp (@acons _ Sym (Θ ++ Δ) (Spec Λ P) _ A0 (vid _)) V)
      with (@acons _ Sym Δ (Spec Λ P) _ (vsubst_tms (σ := Spec Λ P) A0 V) (vcomp (vid _) V)) end.
  rewrite vcomp_vid_l. f_equal. f_equal.
  rewrite vsubst_tms_vup. cbn [dom]. rewrite vsubst_ren_upr_wk_cat, vup_vid, vsubst_vid. reflexivity.
Qed.

End Alg.


(** ** Le plongement de L dans L' *)

Section Emb.
Context {Srt : Type} {Sym : spec Srt -> Type} (Df : ctx Srt) (b : Srt).

Fixpoint emb {Γ s} (t : Terms.tm Sym Γ s) : Terms.tm (xsym Sym Df b) Γ s :=
  match t with
  | tvar x a => tvar x (emba a)
  | tsym c a => tsym (xold c) (emba a)
  end
with emba {Γ Θ} (a : Terms.args Sym Γ Θ) : Terms.args (xsym Sym Df b) Γ Θ :=
  match a with
  | anil => anil
  | acons u a' => acons (emb u) (emba a')
  end.

End Emb.

Arguments emb {Srt Sym} Df b {Γ s} t.
Arguments emba {Srt Sym} Df b {Γ Θ} a.

(** ** Une récurrence sur les termes avec les composantes des arguments

    Dans le cas d'un symbole ou d'une variable, on dispose, en plus de la
    propriété de la liste d'arguments, de la propriété de chacune de ses
    composantes (dont on a besoin pour app et lambda). *)

Section Ind2.
Context {Srt : Type} {Sym : spec Srt -> Type}.

Lemma tm_args_ind2 (Pt : forall Γ s, Terms.tm Sym Γ s -> Prop) (Pa : forall Γ Θ, Terms.args Sym Γ Θ -> Prop) :
  (forall Γ σ (x : var Γ σ) a, Pa Γ (dom σ) a -> (forall θ (z : var (dom σ) θ), Pt _ _ (aget z a)) ->
     Pt Γ (cod σ) (tvar x a)) ->
  (forall Γ σ (c : Sym σ) a, Pa Γ (dom σ) a -> (forall θ (z : var (dom σ) θ), Pt _ _ (aget z a)) ->
     Pt Γ (cod σ) (tsym c a)) ->
  (forall Γ, Pa Γ [] anil) ->
  (forall Γ σ Θ (u : Terms.tms Sym Γ σ), Pt _ _ u -> forall a, Pa Γ Θ a -> Pa Γ (σ :: Θ) (acons u a)) ->
  (forall Γ s t, Pt Γ s t) /\ (forall Γ Θ a, Pa Γ Θ a).
Proof.
  intros Hv Hs Hn Hc.
  assert (H : (forall Γ s t, Pt Γ s t) /\
              (forall Γ Θ a, Pa Γ Θ a /\ forall θ (z : var Θ θ), Pt _ _ (aget z a))).
  { apply tm_args_ind.
    - intros Γ σ x a [Ha Hz]. apply Hv; assumption.
    - intros Γ σ c a [Ha Hz]. apply Hs; assumption.
    - intros Γ. split; [apply Hn|]. intros θ z. destruct (var_nil z).
    - intros Γ σ Θ u Hu a [Ha Hz]. split; [apply Hc; assumption|].
      refine (var_inv _ _ _); [exact Hu|intros θ z; exact (Hz θ z)]. }
  split; [exact (proj1 H)|intros Γ Θ a; exact (proj1 (proj2 H Γ Θ a))].
Qed.

Lemma args1_inv {Γ σ} (a : Terms.args Sym Γ [σ]) : a = acons (ahd a) anil.
Proof. rewrite (args_eta a) at 1. rewrite (args_nil (atl a)). reflexivity. Qed.

Lemma args2_inv {Γ σ1 σ2} (a : Terms.args Sym Γ [σ1; σ2]) : a = acons (ahd a) (acons (ahd (atl a)) anil).
Proof. rewrite (args_eta a) at 1. rewrite (args_eta (atl a)), (args_nil (atl (atl a))). reflexivity. Qed.

End Ind2.


(** ** Vue des symboles, piles d'arguments

    La couche du bord traite les symboles lambda et app de la couche
    fonctionnelle. Une **vue** classe chaque symbole de L : lambda, app ou
    autre. La traduction d'un terme reçoit, en plus de l'environnement et
    de la continuation, une **pile** des valeurs des arguments en attente :
    pour app(F, u), on évalue u, puis on traduit F avec la valeur de u en
    tête de pile ; un lambda qui trouve une pile non vide lie sa variable à
    la valeur en tête (ce qui contracte le β-redex) ; toute autre tête
    reçoit la pile appliquée par app ([apps]). *)

Section Spine.
Context {Srt : Type} {Sym : spec Srt -> Type} `{FS : Functional Srt Sym}.

Local Notation tm := (Terms.tm Sym).
Local Notation vec := (vec Sym).

Inductive symview : forall σ, Sym σ -> Type :=
| vw_lam {a b c} (w : Arr a b c) : symview _ (s_lam w)
| vw_app {a b c} (w : Arr a b c) : symview _ (s_app w)
| vw_oth {σ} (c : Sym σ) : symview σ c.

(** Une sorte qui n'est pas une sorte flèche. *)
Definition noarr (s : Srt) : Prop := forall a b, Arr a b s -> False.

(** Une pile de valeurs (termes de L dans Δ) attendues par un terme de
    sorte c, dont l'application est de sorte r. *)
Inductive spine (Δ : ctx Srt) : Srt -> Srt -> Type :=
| snil {s} : spine Δ s s
| scons {a b c r} : Arr a b c -> tm Δ a -> spine Δ b r -> spine Δ c r.

Arguments snil {Δ s}.
Arguments scons {Δ a b c r} w v sp.

Fixpoint ren_sp {Δ Δ' c r} (sp : spine Δ c r) (ρ : ren Δ Δ') {struct sp} : spine Δ' c r :=
  match sp with
  | snil => snil
  | scons w v sp' => scons w (ren_tm v ρ) (ren_sp sp' ρ)
  end.

Fixpoint vsubst_sp {Δ Δ0 c r} (sp : spine Δ c r) (σ : vec Δ Δ0) {struct sp} : spine Δ0 c r :=
  match sp with
  | snil => snil
  | scons w v sp' => scons w (vsubst v σ) (vsubst_sp sp' σ)
  end.

(** L'application d'une tête à la pile. *)
Fixpoint apps {Δ c r} (h : tm Δ c) (sp : spine Δ c r) {struct sp} : tm Δ r :=
  match sp in spine _ c0 r0 return tm Δ c0 -> tm Δ r0 with
  | snil => fun h => h
  | scons w v sp' => fun h => apps (App w h v) sp'
  end h.

(** La continuation d'une tête : la pile appliquée au trou, puis K. *)
Definition spK {Δ c r Q} (sp : spine Δ c r) (K : tm (ι r :: Δ) Q) : tm (ι c :: Δ) Q :=
  plug [ι c] K (apps (var0 (Sym := Sym) vz) (ren_sp sp (wk [ι c]))).

Lemma vsubst_apps {Δ Δ0 c r} (h : tm Δ c) (sp : spine Δ c r) (σ : vec Δ Δ0) :
  vsubst (apps h sp) σ = apps (vsubst h σ) (vsubst_sp sp σ).
Proof.
  revert h. induction sp as [s|a b c r w v sp IH]; intros h; [reflexivity|].
  cbn [apps vsubst_sp]. rewrite IH, vsubst_App. reflexivity.
Qed.

Lemma ren_apps {Δ Δ' c r} (h : tm Δ c) (sp : spine Δ c r) (ρ : ren Δ Δ') :
  ren_tm (apps h sp) ρ = apps (ren_tm h ρ) (ren_sp sp ρ).
Proof.
  revert h. induction sp as [s|a b c r w v sp IH]; intros h; [reflexivity|].
  cbn [apps ren_sp]. rewrite IH. reflexivity.
Qed.

Lemma ren_sp_ren {Δ Δ' Δ'' c r} (sp : spine Δ c r) (ρ : ren Δ Δ') (ξ : ren Δ' Δ'') :
  ren_sp (ren_sp sp ρ) ξ = ren_sp sp (rcomp ρ ξ).
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, ren_ren. reflexivity. Qed.

Lemma ren_sp_id {Δ c r} (sp : spine Δ c r) : ren_sp sp rid = sp.
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, ren_id. reflexivity. Qed.

Lemma ren_sp_ext {Δ Δ' c r} (sp : spine Δ c r) (ρ ρ' : ren Δ Δ') :
  (forall σ x, ρ σ x = ρ' σ x) -> ren_sp sp ρ = ren_sp sp ρ'.
Proof. intros H. induction sp; cbn; [reflexivity|]. rewrite IHsp, (ren_ext _ _ _ H). reflexivity. Qed.

Lemma vsubst_sp_ren {Δ Δ' Δ0 c r} (sp : spine Δ c r) (ρ : ren Δ Δ') (σ : vec Δ' Δ0) :
  vsubst_sp (ren_sp sp ρ) σ = vsubst_sp sp (vpre ρ σ).
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, vsubst_ren. reflexivity. Qed.

Lemma ren_sp_vsubst {Δ Δ0 Δ1 c r} (sp : spine Δ c r) (σ : vec Δ Δ0) (ρ : ren Δ0 Δ1) :
  ren_sp (vsubst_sp sp σ) ρ = vsubst_sp sp (vren σ ρ).
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, ren_vsubst. reflexivity. Qed.

Lemma vsubst_sp_vsubst {Δ Δ0 Δ1 c r} (sp : spine Δ c r) (σ : vec Δ Δ0) (τ : vec Δ0 Δ1) :
  vsubst_sp (vsubst_sp sp σ) τ = vsubst_sp sp (vcomp σ τ).
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, vsubst_vsubst. reflexivity. Qed.

Lemma vsubst_sp_vid {Δ c r} (sp : spine Δ c r) : vsubst_sp sp (vid Δ) = sp.
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, vsubst_vid. reflexivity. Qed.

Lemma vsubst_sp_ext {Δ Δ0 c r} (sp : spine Δ c r) (σ σ' : vec Δ Δ0) :
  σ = σ' -> vsubst_sp sp σ = vsubst_sp sp σ'.
Proof. intros ->; reflexivity. Qed.

Lemma ren_sp_as_vsubst {Δ Δ' c r} (sp : spine Δ c r) (ρ : ren Δ Δ') :
  ren_sp sp ρ = vsubst_sp sp (vpre ρ (vid Δ')).
Proof. induction sp; cbn; [reflexivity|]. rewrite IHsp, ren_as_vsubst. reflexivity. Qed.

Lemma vpre_wk_vup Λ {Γ Δ} (W : vec Γ Δ) : vpre (wk Λ) (vup Λ W) = vren W (wk Λ).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre. unfold wk at 1. rewrite aget_vup_r'.
  unfold vren. rewrite aget_vmap. reflexivity.
Qed.

Lemma vsubst_ren_wk Λ {Δ Δ0 s} (X : tm Δ s) (σ : vec Δ Δ0) :
  vsubst (ren_tm X (wk Λ)) (vup Λ σ) = ren_tm (vsubst X σ) (wk Λ).
Proof. rewrite vsubst_ren, vpre_wk_vup, ren_vsubst. reflexivity. Qed.

Lemma vsubst_sp_wk Λ {Δ Δ0 c r} (sp : spine Δ c r) (σ : vec Δ Δ0) :
  vsubst_sp (ren_sp sp (wk Λ)) (vup Λ σ) = ren_sp (vsubst_sp sp σ) (wk Λ).
Proof. rewrite vsubst_sp_ren, vpre_wk_vup, ren_sp_vsubst. reflexivity. Qed.

Lemma vsubst_ren_wk_cat Θ {Δ Ξ s} (X : tm Δ s) (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) :
  vsubst (ren_tm X (wk Θ)) (vcat Θ a w) = vsubst X w.
Proof. rewrite vsubst_ren, vpre_wk. reflexivity. Qed.

Lemma vsubst_sp_wk_cat Θ {Δ Ξ c r} (sp : spine Δ c r) (a : Terms.args Sym Ξ Θ) (w : vec Δ Ξ) :
  vsubst_sp (ren_sp sp (wk Θ)) (vcat Θ a w) = vsubst_sp sp w.
Proof. rewrite vsubst_sp_ren, vpre_wk. reflexivity. Qed.

Lemma spK_vsubst {Δ Δ0 c r Q} (sp : spine Δ c r) (K : tm (ι r :: Δ) Q) (σ : vec Δ Δ0) :
  vsubst (spK sp K) (vup [ι c] σ) = spK (vsubst_sp sp σ) (vsubst K (vup [ι r] σ)).
Proof.
  unfold spK. etransitivity; [exact (plug_vsubst [ι c] K _ σ)|]. f_equal.
  rewrite vsubst_apps, vsubst_sp_wk. reflexivity.
Qed.

Lemma spK_inst {Δ c r Q} (sp : spine Δ c r) (K : tm (ι r :: Δ) Q) (h : tm Δ c) :
  vsubst (spK sp K) (inst1 h) = vsubst K (inst1 (apps h sp)).
Proof.
  unfold spK. etransitivity; [exact (plug_inst [ι c] K _ (@acons _ Sym Δ (ι c) [] h anil))|].
  f_equal. f_equal. rewrite vsubst_apps. cbn [vcat]. rewrite vsubst_var0.
  f_equal. etransitivity; [exact (vsubst_sp_wk_cat [ι c] sp (@acons _ Sym Δ (ι c) [] h anil) (vid Δ))|].
  apply vsubst_sp_vid.
Qed.

End Spine.

Arguments symview {Srt Sym FS} σ c.
Arguments vw_lam {Srt Sym FS a b c} w.
Arguments vw_app {Srt Sym FS a b c} w.
Arguments vw_oth {Srt Sym FS σ} c.
Arguments noarr {Srt Sym FS} s.
Arguments spine {Srt Sym FS} Δ c r.
Arguments snil {Srt Sym FS Δ s}.
Arguments scons {Srt Sym FS Δ a b c r} w v sp.


(** ** La traduction *)

Section Trans.
Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).
Context (Sdec : forall s s' : Srt, {s = s'} + {s <> s'}).
Context (Df : ctx Srt) (b : Srt).
Context `{HasAnd Srt Sym P} `{HasTop Srt Sym P} {HE : HasExists Sym P b}.
Context `{FS : Functional Srt Sym} (view : forall σ (c : Sym σ), symview σ c).
Context (φ : form Sym P (ι b :: Df)).

Local Notation tm := (Terms.tm Sym).
Local Notation XSym := (xsym Sym Df b).
Local Notation tm' := (Terms.tm XSym).
Local Notation args' := (Terms.args XSym).
Local Notation form := (form Sym P).
Local Notation vec := (vec Sym).

(** La continuation de f : ∃y. φ(x⃗, y) ∧ K[y], les x⃗ étant les trous. *)
Definition fK {Δ} (K : form (ι b :: Δ)) : form (Df ++ Δ) :=
  Ex b (And (ren_tm φ (fun _ x => vl Δ x)) (ren_tm K (upr [ι b] (wk Df)))).

Definition castP {Γ c} (e : c = P) (t : tm Γ c) : tm Γ P := eq_rect c (tm Γ) t P e.
Definition castc {Γ c} (e : c = P) (t : tm Γ P) : tm Γ c := eq_rect P (tm Γ) t c (eq_sym e).

(** Les traductions (partielles) des composantes de app et de lambda. *)
Definition TrT Γ c : Type := forall Δ r, vec Γ Δ -> spine Δ c r -> form (ι r :: Δ) -> form Δ.

Definition RTapp Γ (L : ctx Srt) : Type :=
  match L with
  | [Spec [] cF; Spec [] cu] => TrT Γ cF * TrT Γ cu
  | _ => unit
  end.

Definition RTlam Γ (L : ctx Srt) : Type :=
  match L with
  | [Spec [Spec [] a] b'] => TrT (ι a :: Γ) b'
  | _ => unit
  end.

(** Un lambda devant sa pile : la tête de pile est la valeur de la
    variable liée. Pile vide (ou sortes incompatibles) : ⊤, ce qui
    n'arrive pas sous les conditions de [DefSound.v]. *)
Definition trlam {Γ a0 b0 c Δ r} (B : TrT (ι a0 :: Γ) b0) (w : vec Γ Δ) (sp : spine Δ c r)
  (K : form (ι r :: Δ)) : form Δ :=
  match sp in spine _ c1 r1 return form (ι r1 :: Δ) -> form Δ with
  | snil => fun _ => Top
  | @scons _ _ _ _ a1 b1 c1 r1 w1 v sp' => fun K =>
      match Sdec a1 a0, Sdec b1 b0 with
      | left e1, left e2 =>
          B Δ r1 (@acons _ Sym Δ (ι a0) Γ (eq_rect a1 (tm Δ) v a0 e1) w)
            (eq_rect b1 (fun x => spine Δ x r1) sp' b0 e2) K
      | _, _ => Top
      end
  end K.

Fixpoint tr {Γ s} (t : tm' Γ s) {struct t} : TrT Γ s :=
  match t in Terms.tm _ Γ0 s0 return TrT Γ0 s0 with
  | @tvar _ _ Γ0 σ x a => fun Δ r w sp K => tra a Δ w (plug (dom σ) (spK sp K) (aget x w))
  | @tsym _ _ Γ0 σ c a => fun Δ r w sp K =>
      match c in xsym _ _ _ σ0 return args' Γ0 (dom σ0) -> spine Δ (cod σ0) r -> form Δ with
      | @xold _ _ _ _ σ1 c0 => fun a sp =>
          match view σ1 c0 in symview σ2 c2 return args' Γ0 (dom σ2) -> spine Δ (cod σ2) r -> form Δ with
          | @vw_lam _ _ _ a0 b0 c1 w0 => fun a sp =>
              let B := match a in Terms.args _ Γ1 L return RTlam Γ1 L with
                | anil => tt
                | @acons _ _ Γ1 σt Θ t a' =>
                    match σt as σ0 return tm' (dom σ0 ++ Γ1) (cod σ0) -> RTlam Γ1 (σ0 :: Θ) with
                    | Spec [Spec [] a1] b1 => fun t =>
                        match Θ as Θ3 return RTlam Γ1 (Spec [ι a1] b1 :: Θ3) with
                        | [] => fun Δ r w sp K => tr t Δ r w sp K
                        | _ :: _ => tt
                        end
                    | _ => fun _ => tt
                    end t
                end in
              trlam B w sp K
          | @vw_app _ _ _ a0 b0 c1 w0 => fun a sp =>
              let p := match a in Terms.args _ Γ1 L return RTapp Γ1 L with
                | anil => tt
                | @acons _ _ Γ1 σF Θ F a' =>
                    match σF as σ0 return tm' (dom σ0 ++ Γ1) (cod σ0) -> RTapp Γ1 (σ0 :: Θ) with
                    | Spec [] cF => fun F =>
                        match a' in Terms.args _ Γ2 L2 return tm' Γ2 cF -> RTapp Γ2 (ι cF :: L2) with
                        | anil => fun _ => tt
                        | @acons _ _ Γ2 σu Θ2 u a'' => fun F =>
                            match σu as σ0 return tm' (dom σ0 ++ Γ2) (cod σ0) -> RTapp Γ2 (ι cF :: σ0 :: Θ2) with
                            | Spec [] cu => fun u =>
                                match Θ2 as Θ3 return RTapp Γ2 (ι cF :: ι cu :: Θ3) with
                                | [] => (fun Δ r w sp K => tr F Δ r w sp K, fun Δ r w sp K => tr u Δ r w sp K)
                                | _ :: _ => tt
                                end
                            | _ => fun _ => tt
                            end u
                        end F
                    | _ => fun _ => tt
                    end F
                end in
              snd p Δ a0 w snil
                (fst p (ι a0 :: Δ) r (vren w (wk [ι a0])) (scons w0 (var0 vz) (ren_sp sp (wk [ι a0])))
                   (ren_tm K (upr [ι r] (wk [ι a0]))))
          | @vw_oth _ _ _ σ2 c2 => fun a sp =>
              tra a Δ w (plug (dom σ2) (spK sp K) (tsym c2 (holes (dom σ2) Δ)))
          end a sp
      | xf => fun a sp => tra a Δ w (fK (spK sp K))
      end a sp
  end
with tra {Γ Θ} (a : args' Γ Θ) {struct a} : forall Δ, vec Γ Δ -> form (Θ ++ Δ) -> form Δ :=
  match a in Terms.args _ Γ0 Θ0 return forall Δ, vec Γ0 Δ -> form (Θ0 ++ Δ) -> form Δ with
  | anil => fun Δ w K => K
  | @acons _ _ Γ0 σ Θ0 u a' => fun Δ w K =>
      match σ as σ0 return tm' (dom σ0 ++ Γ0) (cod σ0) -> form (σ0 :: Θ0 ++ Δ) -> form Δ with
      | Spec Λ c => fun u K =>
          match Sdec c P with
          | left e =>
              tra a' Δ w
                (sub0 (σ := Spec Λ c) K
                   (castc e (ren_tm (tr u (Λ ++ Δ) c (vup Λ w) snil (castP e (var0 vz))) (upr Λ (wk Θ0)))))
          | right _ =>
              match Λ as Λ0 return tm' (Λ0 ++ Γ0) c -> form (Spec Λ0 c :: Θ0 ++ Δ) -> form Δ with
              | [] => fun u K => tr u Δ c w snil (tra a' (ι c :: Δ) (vren w (wk [ι c])) (ren_tm K (perm Θ0 (ι c))))
              | _ :: _ => fun _ _ => Top
              end u K
          end
      end u K
  end.

(** Le trou propositionnel. *)
Definition hole {Δ} : form (ι P :: Δ) := var0 vz.

(** La traduction des formules. *)
Definition el {Γ} (ψ : tm' Γ P) : form Γ := tr ψ Γ P (vid Γ) snil hole.


(** ** Commutation avec la substitution de l'environnement *)

Lemma fK_vsubst {Δ Δ0} (K : form (ι b :: Δ)) (σ : vec Δ Δ0) :
  vsubst (fK K) (vup Df σ) = fK (vsubst K (vup [ι b] σ)).
Proof.
  unfold fK, Ex. rewrite vsubst_Qnt, vsubst_tms_vup. cbn [dom]. unfold And. rewrite vsubst_Bin. f_equal. f_equal.
  - rewrite vsubst_ren, ren_as_vsubst. f_equal.
    apply vec_ext; intros ρ x; unfold vget. rewrite !aget_vpre, aget_vid. revert ρ x. refine (var_inv _ _ _).
    + reflexivity.
    + intros ρ y. cbn [vl]. change (aget (vs (vl Δ y)) (vup [ι b] (vup Df σ)))
        with (aget (vl Δ y) (vren (vup Df σ) (wk [ι b]))).
      unfold vren. rewrite aget_vmap, aget_vup_l, eta_ren. reflexivity.
  - exact (vsubst_ren_upr_wk [ι b] Df K σ).
Qed.

Lemma vsubst_hole {Γ Δ} (v : vec Γ Δ) : vsubst (hole (Δ := Γ)) (vup [ι P] v) = hole.
Proof. reflexivity. Qed.

Lemma vsubst_Top {Γ Δ} (v : vec Γ Δ) : vsubst (Top (Γ := Γ)) v = Top.
Proof. reflexivity. Qed.

Lemma vcomp_acons1 {Γ Δ Δ0 a} (v : tm Δ a) (w : vec Γ Δ) (σ : vec Δ Δ0) :
  vcomp (@acons _ Sym Δ (ι a) Γ v w) σ = @acons _ Sym Δ0 (ι a) Γ (vsubst v σ) (vcomp w σ).
Proof.
  change (vcomp (@acons _ Sym Δ (ι a) Γ v w) σ)
    with (@acons _ Sym Δ0 (ι a) Γ (vsubst_tms (σ := ι a) v σ) (vcomp w σ)).
  rewrite vsubst_tms_nil. reflexivity.
Qed.

Lemma vsubst_sp_cons {Δ Δ0 a b' c r} (w0 : Arr a b' c) (v : tm Δ a) (sp : spine Δ b' r) (σ : vec Δ Δ0) :
  vsubst_sp (scons w0 v sp) σ = scons w0 (vsubst v σ) (vsubst_sp sp σ).
Proof. reflexivity. Qed.

Theorem tr_vsubst_mut :
  (forall Γ s (t : tm' Γ s) Δ r (w : vec Γ Δ) (sp : spine Δ s r) K Δ0 (σ : vec Δ Δ0),
      vsubst (tr t Δ r w sp K) σ = tr t Δ0 r (vcomp w σ) (vsubst_sp sp σ) (vsubst K (vup [ι r] σ))) /\
  (forall Γ Θ (a : args' Γ Θ) Δ (w : vec Γ Δ) K Δ0 (σ : vec Δ Δ0),
      vsubst (tra a Δ w K) σ = tra a Δ0 (vcomp w σ) (vsubst K (vup Θ σ))).
Proof.
  apply tm_args_ind2.
  - intros Γ σx x a IH _ Δ r w sp K Δ0 σ. cbn [tr].
    rewrite IH, plug_vsubst, aget_vcomp, vsubst_tms_vup, spK_vsubst. reflexivity.
  - intros Γ σx c a IH Hc Δ r w sp K Δ0 σ. destruct c as [σ1 c0|]; cbn [tr].
    + revert a IH Hc sp. destruct (view σ1 c0) as [a0 b0 c1 w0|a0 b0 c1 w0|σ2 c2]; intros a IH Hc sp.
      * pose proof (Hc _ vz) as Ht. cbn [aget] in Ht. rewrite (args1_inv a). cbn beta iota zeta.
        revert K. destruct sp as [s0|a1 b1 c2 r1 w1 v sp']; intros K; [reflexivity|].
        unfold trlam. cbn [vsubst_sp]. destruct (Sdec a1 a0) as [e1|]; [|reflexivity].
        destruct (Sdec b1 b0) as [e2|]; [|reflexivity]. subst a1 b1. cbn [eq_rect].
        rewrite Ht. f_equal. apply vcomp_acons1.
      * pose proof (Hc _ vz) as HF. pose proof (Hc _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
        rewrite (args2_inv a). cbn beta iota zeta. cbn [fst snd].
        rewrite Hu, HF. f_equal. f_equal.
        -- exact (vcomp_vren_wk1 (ι a0) w σ).
        -- cbn [vsubst_sp]. f_equal. exact (vsubst_sp_wk [ι a0] sp σ).
        -- exact (vsubst_ren_upr_wk [ι r] [ι a0] K σ).
      * rewrite IH, plug_vsubst, vsubst_tsym, holes_vsubst, spK_vsubst. reflexivity.
    + rewrite IH, fK_vsubst, spK_vsubst. reflexivity.
  - intros Γ Δ w K Δ0 σ. cbn [tra]. rewrite vup_nil. reflexivity.
  - intros Γ σx Θ u IHu a IHa Δ w K Δ0 σ. destruct σx as [Λ c]. cbn [tra].
    destruct (Sdec c P) as [e|n].
    + subst c. cbn [castc castP eq_rect eq_sym]. rewrite IHa, sub0_vsubst, vup_cons. f_equal. f_equal.
      rewrite vsubst_tms_vup. cbn [dom]. rewrite vsubst_ren_upr_wk. f_equal.
      etransitivity; [apply IHu|]. cbn [vsubst_sp]. rewrite vup_vcomp. reflexivity.
    + destruct Λ as [|λ Λ]; [|reflexivity].
      etransitivity; [apply IHu|]. cbn [vsubst_sp]. rewrite IHa. cbn [cod app]. rewrite vcomp_vren_wk1, perm_vsubst. reflexivity.
Qed.

Lemma tr_vsubst {Γ s} (t : tm' Γ s) {Δ r} (w : vec Γ Δ) sp K {Δ0} (σ : vec Δ Δ0) :
  vsubst (tr t Δ r w sp K) σ = tr t Δ0 r (vcomp w σ) (vsubst_sp sp σ) (vsubst K (vup [ι r] σ)).
Proof. apply (proj1 tr_vsubst_mut). Qed.

Lemma tra_vsubst {Γ Θ} (a : args' Γ Θ) {Δ} (w : vec Γ Δ) K {Δ0} (σ : vec Δ Δ0) :
  vsubst (tra a Δ w K) σ = tra a Δ0 (vcomp w σ) (vsubst K (vup Θ σ)).
Proof. apply (proj2 tr_vsubst_mut). Qed.

(** ** Traduction des termes de L

    Une formule de L n'est plus traduite en elle-même, mais en sa forme
    β-réduite (les β-redex sont contractés à la traduction) : l'égalité
    devient une conversion, dès que le calcul de L contient β. *)

(** Une position d'argument est acceptable si elle est sans lieur et de
    sorte non flèche, ou de sorte P et ne liant que des variables sans
    argument. Les positions des symboles autres que lambda et app, et des
    variables du contexte, sont supposées acceptables. *)
Definition okpos (θ : spec Srt) : Prop :=
  (dom θ = [] /\ noarr (cod θ)) \/ (cod θ = P /\ Forall (fun λ => dom λ = []) (dom θ)).
Definition okhd (σ : spec Srt) : Prop := Forall okpos (dom σ).
Definition okctx (Γ : ctx Srt) : Prop := forall σ, var Γ σ -> okhd σ.
Definition view_ok {σ c} (v : symview σ c) : Prop :=
  match v with vw_oth _ => okhd σ | _ => True end.

Lemma okctx_app Λ Γ : Forall (fun λ => dom λ = []) Λ -> okctx Γ -> okctx (Λ ++ Γ).
Proof.
  intros HΛ HΓ σ x. vcase x; [|apply HΓ, z].
  induction z as [Λ0 σ0|Λ0 σ0 τ0 z IH].
  - inversion HΛ as [|? ? Hd]; subst. unfold okhd. rewrite Hd. constructor.
  - inversion HΛ; subst. apply IH; assumption.
Qed.

Lemma okctx_cons1 a Γ : okctx Γ -> okctx (ι a :: Γ).
Proof. intros HΓ. apply (okctx_app [ι a] Γ); [repeat constructor|exact HΓ]. Qed.

Section EmbTr.
Context (C : system Sym).
Hypothesis Hsym : forall σ (c : Sym σ), view_ok (view σ c).
Hypothesis Harr_inj : forall a b c a' b' (w : Arr a b c) (w' : Arr a' b' c), a = a' /\ b = b'.
Hypothesis Harr_uniq : forall a b c (w w' : Arr a b c), w = w'.
Hypothesis Hnoarr_dom : forall a b c (w : Arr a b c), noarr a.
Hypothesis Hnoarr_P : noarr P.
Hypothesis Hbeta : forall a b c (w : Arr a b c) Γ (t : tm (ι a :: Γ) b) (u : tm Γ a),
  conv C (App w (Lam w t) u) (vsubst t (inst1 u)).

Lemma conv_eq {Γ s} (t u : tm Γ s) : t = u -> conv C t u.
Proof. intros ->. apply conv_refl. Qed.

Lemma conv_inst1 {Γ a} (u u' : tm Γ a) : conv C u u' -> arel (conv C) (inst1 u) (inst1 u').
Proof. intros Hu. split; [exact Hu|apply (arel_refl C)]. Qed.

Lemma arel_cons {Γ σ Θ} (u u' : Terms.tms Sym Γ σ) (a a' : Terms.args Sym Γ Θ) :
  conv C u u' -> arel (conv C) a a' -> arel (conv C) (acons u a) (acons u' a').
Proof. intros H1 H2. split; assumption. Qed.

Lemma conv_apps {Δ c r} (h h' : tm Δ c) (sp : spine Δ c r) : conv C h h' -> conv C (apps h sp) (apps h' sp).
Proof.
  revert h h'. induction sp as [s|a0 b0 c0 r0 w0 v sp IH]; intros h h' Hh; [exact Hh|].
  cbn [apps]. apply IH. unfold App. apply (conv_tsym C (Γ := Δ) (σ := Spec [ι c0; ι a0] b0)). split; [exact Hh|split; [apply conv_refl|exact I]].
Qed.

Lemma conv_K_inst {Δ r} (K : form (ι r :: Δ)) (X Y : tm Δ r) :
  conv C X Y -> conv C (vsubst K (inst1 X)) (vsubst K (inst1 Y)).
Proof. intros HXY. apply (conv_vsubst C); [apply conv_refl|apply conv_inst1, HXY]. Qed.

Lemma vcomp_vup1_inst1 {Γ Δ a} (w : vec Γ Δ) (v : tm Δ a) :
  vcomp (vup [ι a] w) (inst1 v) = @acons _ Sym Δ (ι a) Γ v w.
Proof.
  apply vec_ext; intros ρ x; unfold vget. rewrite aget_vcomp. revert ρ x. refine (var_inv _ _ _).
  - unfold vup. cbn [vcat aget ahd etas]. rewrite (vsubst_eta (Γ := ι a :: Δ) vz). reflexivity.
  - intros ρ y. change (aget (vs y) (vup [ι a] w)) with (aget (vr [ι a] y) (vup [ι a] w)).
    rewrite aget_vup_r', vsubst_tms_ren'. unfold inst1. rewrite vpre_wk1, vsubst_tms_vid. reflexivity.
Qed.

Lemma noarr_snil {Δ c r} (sp : spine Δ c r) : noarr c ->
  { e : c = r & sp = eq_rect c (fun x => spine Δ c x) snil r e }.
Proof.
  destruct sp as [s|a0 b0 c0 r0 w0 v sp]; intros Hn; [exists eq_refl; reflexivity|].
  exfalso; exact (Hn _ _ w0).
Qed.

Theorem tr_emb_mut :
  (forall Γ s (t : tm Γ s), okctx Γ -> forall Δ r (w : vec Γ Δ) (sp : spine Δ s r) K, noarr r ->
      conv C (tr (emb Df b t) Δ r w sp K) (vsubst K (inst1 (apps (vsubst t w) sp)))) /\
  (forall Γ Θ (a : Terms.args Sym Γ Θ), okctx Γ -> Forall okpos Θ -> forall Δ (w : vec Γ Δ) K,
      conv C (tra (emba Df b a) Δ w K) (vsubst K (vcat Θ (vsubst_args a w) (vid Δ)))).
Proof.
  apply tm_args_ind2.
  - intros Γ σx x a IH _ HΓ Δ r w sp K Hr. cbn [emb tr].
    eapply conv_trans; [apply (IH HΓ (HΓ _ x))|]. apply conv_eq.
    rewrite plug_inst, spK_inst, <- happ_vsubst. reflexivity.
  - intros Γ σx c a IH Hc HΓ Δ r w sp K Hr. cbn [emb tr]. pose proof (Hsym σx c) as Hs.
    revert a IH Hc sp Hs. destruct (view σx c) as [a0 b0 c1 w0|a0 b0 c1 w0|σ2 c2]; intros a IH Hc sp Hs.
    + pose proof (Hc _ vz) as Ht. cbn [aget] in Ht. rewrite (args1_inv a). cbn [emba]. cbn beta iota zeta.
      change (cod (Spec [Spec [ι a0] b0] c1)) with c1 in *.
      revert K Hr. destruct sp as [s0|a1 b1 c2 r1 w1 v sp']; intros K Hr; [exfalso; exact (Hr _ _ w0)|].
      destruct (Harr_inj _ _ _ _ _ w1 w0) as [-> ->]. rewrite (Harr_uniq _ _ _ w1 w0).
      unfold trlam. destruct (Sdec a0 a0) as [e1|n]; [|contradiction].
      destruct (Sdec b0 b0) as [e2|n]; [|contradiction].
      rewrite (Eqdep_dec.UIP_dec Sdec e1 eq_refl), (Eqdep_dec.UIP_dec Sdec e2 eq_refl). cbn [eq_rect].
      eapply conv_trans; [apply (Ht (okctx_cons1 a0 Γ HΓ) _ _ _ _ _ Hr)|]. apply conv_K_inst.
      cbn [apps]. apply conv_apps. apply conv_sym.
      change (vsubst (tsym (s_lam w0) (@acons _ Sym Γ (Spec [ι a0] b0) [] (ahd a) anil)) w)
        with (Lam w0 (vsubst_tms (σ := Spec [ι a0] b0) (ahd a) w)).
      eapply conv_trans; [apply Hbeta|]. apply conv_eq.
      rewrite vsubst_tms_vup, vsubst_vsubst. f_equal. exact (vcomp_vup1_inst1 w v).
    + pose proof (Hc _ vz) as HF. pose proof (Hc _ (vs vz)) as Hu. cbn [aget] in HF, Hu.
      rewrite (args2_inv a). cbn [emba]. cbn beta iota zeta. cbn [fst snd].
      eapply conv_trans; [apply (Hu HΓ _ _ _ _ _ (Hnoarr_dom _ _ _ w0))|]. cbn [apps].
      rewrite tr_vsubst, vsubst_sp_cons, vsubst_var0. cbn [aget ahd inst1].
      match goal with |- conv C (tr _ _ _ ?W' (scons _ _ ?S) ?K') _ =>
        assert (EW : W' = w); [|assert (ES : S = sp); [|assert (EK : K' = K)]] end.
      { exact (vcomp_vren_wk_inst1 w _). }
      { exact (eq_trans (vsubst_sp_wk_cat [ι a0] sp (@acons _ Sym Δ (ι a0) [] _ anil) (vid Δ)) (vsubst_sp_vid sp)). }
      { etransitivity; [exact (vsubst_ren_upr_wk_cat [ι r] [ι a0] K (@acons _ Sym Δ (ι a0) [] _ anil) (vid Δ))|].
        rewrite vup_vid. apply vsubst_vid. }
      rewrite EW, ES, EK. eapply conv_trans; [apply (HF HΓ _ _ _ _ _ Hr)|]. apply conv_eq.
      cbn [apps]. do 3 f_equal.
      change (tsym (s_app w0) (@acons _ Sym Γ (ι c1) _ (ahd a) (@acons _ Sym Γ (ι a0) _ (ahd (atl a)) anil)))
        with (App w0 (ahd a) (ahd (atl a))).
      rewrite vsubst_App. reflexivity.
    + cbn [view_ok] in Hs. eapply conv_trans; [apply (IH HΓ Hs)|]. apply conv_eq.
      rewrite plug_inst, spK_inst, vsubst_tsym, holes_inst. reflexivity.
  - intros Γ HΓ _ Δ w K. cbn [emba tra vcat]. rewrite vsubst_vid. apply conv_refl.
  - intros Γ σx Θ u IHu a IHa HΓ HΘ Δ w K. inversion HΘ as [|? ? Hp HΘ']; subst.
    destruct σx as [Λ c]. cbn [emba tra].
    assert (HΛ : Forall (fun λ => dom λ = []) Λ).
    { destruct Hp as [[Hd _]|[_ Hd]]; [cbn in Hd; subst; constructor|exact Hd]. }
    destruct (Sdec c P) as [e|n].
    + subst c. cbn [castc castP eq_rect eq_sym].
      eapply conv_trans; [apply (IHa HΓ HΘ')|].
      pose proof (IHu (okctx_app Λ Γ HΛ HΓ) (Λ ++ Δ) P (vup Λ w) snil (var0 vz) Hnoarr_P) as HX.
      cbn [apps] in HX. rewrite vsubst_var0 in HX. cbn [aget ahd inst1] in HX.
      unfold sub0. eapply conv_trans.
      { apply (conv_vsubst C); [|apply (arel_refl C)]. apply (conv_vsubst C); [apply conv_refl|].
        apply arel_cons; [apply (conv_ren C), HX|apply (arel_refl C)]. }
      rewrite vsubst_vsubst.
      apply conv_eq. f_equal. rewrite vsubst_args_acons.
      match goal with |- vcomp (acons ?A0 (vid _)) ?V = _ =>
        change (vcomp (@acons _ Sym (Θ ++ Δ) (Spec Λ P) _ A0 (vid _)) V)
          with (@acons _ Sym Δ (Spec Λ P) _ (vsubst_tms (σ := Spec Λ P) A0 V) (vcomp (vid _) V)) end.
      rewrite vcomp_vid_l. cbn [vcat]. f_equal.
      rewrite !vsubst_tms_vup. cbn [dom]. rewrite vsubst_ren_upr_wk_cat, vup_vid, vsubst_vid. reflexivity.
    + destruct Λ as [|λ Λ].
      * assert (Hc : noarr c) by (destruct Hp as [[_ Hc]|[Hc _]]; [exact Hc|exact (False_ind _ (n Hc))]).
        eapply conv_trans; [apply (IHu HΓ _ _ _ snil _ Hc)|]. cbn [apps app].
        eapply conv_trans; [apply (conv_vsubst C); [apply (IHa HΓ HΘ')|apply (arel_refl C)]|]. apply conv_eq.
        rewrite perm_inst. rewrite vsubst_args_vsubst, vcomp_vren_wk_inst1.
        change (vsubst_args (acons u a) w) with (@acons _ Sym Δ (ι c) _ (vsubst_tms (σ := ι c) u w) (vsubst_args a w)).
        cbn [vcat]. rewrite vsubst_tms_nil. reflexivity.
      * exfalso. destruct Hp as [[Hd _]|[Hc _]]; [discriminate Hd|exact (n Hc)].
Qed.

Lemma tr_emb {Γ s} (t : tm Γ s) : okctx Γ -> forall Δ r (w : vec Γ Δ) (sp : spine Δ s r) K, noarr r ->
  conv C (tr (emb Df b t) Δ r w sp K) (vsubst K (inst1 (apps (vsubst t w) sp))).
Proof. apply (proj1 tr_emb_mut). Qed.

(** La traduction d'une formule de L est convertible à elle-même. *)
Lemma el_emb {Γ} (ψ : form Γ) : okctx Γ -> conv C (el (emb Df b ψ)) ψ.
Proof.
  intros HΓ. unfold el. eapply conv_trans; [apply (tr_emb ψ HΓ _ _ _ snil _ Hnoarr_P)|].
  apply conv_eq. cbn [apps]. rewrite vsubst_vid. unfold hole. apply vsubst_var0.
Qed.

End EmbTr.

End Trans.

Arguments fK {Srt Sym P} Df b {_ HE} φ {Δ} K.
Arguments trlam {Srt Sym P} Sdec {_ FS Γ a0 b0 c Δ r} B w sp K.
Arguments tr {Srt Sym P} Sdec Df b {_ _ HE FS} view φ {Γ s} t Δ r w sp K.
Arguments tra {Srt Sym P} Sdec Df b {_ _ HE FS} view φ {Γ Θ} a Δ w K.
Arguments el {Srt Sym P} Sdec Df b {_ _ HE FS} view φ {Γ} ψ.
Arguments hole {Srt Sym P Δ}.
Arguments okpos {Srt Sym} P {FS} θ.
Arguments okhd {Srt Sym} P {FS} σ.
Arguments okctx {Srt Sym} P {FS} Γ.
Arguments view_ok {Srt Sym} P {FS σ c} v.
