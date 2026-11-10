(** * Sémantique des termes dans une catégorie cartésienne fermée

    Données concrètes : une catégorie cartésienne fermée C, un objet ⟦b⟧
    pour chaque sorte, et pour chaque symbole f : σ un morphisme
    ⟦f⟧ : ⟦dom σ⟧ ~> ⟦cod σ⟧. On interprète :
    - une spécification σ = Θ → b par l'exponentielle ⟦b⟧^⟦Θ⟧ ([ispec]) ;
    - un contexte Θ = [σ₁; …; σₙ] par le produit (…(1 × ⟦σₙ⟧) …) × ⟦σ₁⟧
      ([ictx]), dans l'ordre du produit de [SynConv] : τ :: Θ = Θ × [τ] ;
    - un terme t : tm Γ b, relativement à un *environnement*
      ρ : ∀ σ, var Γ σ → X ~> ⟦σ⟧, par un morphisme ⟦t⟧ρ : X ~> ⟦b⟧
      ([stm]) : une variable appliquée est une évaluation, un argument
      (un corps sous les lieurs de sa spécification) est un curryfié.

    Résultats : extensionnalité, naturalité en l'objet X, renommage,
    η-expansion, et surtout le **lemme de substitution**
    ⟦t[v]⟧ρ ≈ ⟦t⟧(⟦v⟧ρ) ([stm_vsubst]). La substitution étant héréditaire,
    la preuve suit celle de [Commute.v] : un lemme de traversée pour les
    kits dont les fonctions d'application sont « correctes », puis la
    correction de [happ σ] par récurrence sur la profondeur de σ. *)

From Category Require Import Lib Theory.Category
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors Syn.

Generalizable All Variables.

Scheme tm_rectT := Induction for Terms.tm Sort Type
  with args_rectT := Induction for Terms.args Sort Type.
Combined Scheme tm_args_rectT from tm_rectT, args_rectT.

Section Semantics.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (So : Srt -> obj[C]).

Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).
Local Notation tms := (Terms.tms Sym).

(** ** Interprétation des spécifications et des contextes *)

Fixpoint ispec (σ : spec Srt) : obj[C] :=
  match σ with
  | Spec Θ b => So b ^ ((fix go (Θ0 : list (spec Srt)) : obj[C] :=
                          match Θ0 with
                          | [] => 1
                          | τ :: Θ1 => go Θ1 × ispec τ
                          end) Θ)
  end.

Fixpoint ictx (Θ : ctx Srt) : obj[C] :=
  match Θ with
  | [] => 1
  | τ :: Θ1 => ictx Θ1 × ispec τ
  end.

Lemma ispec_Spec Θ b : ispec (Spec Θ b) = So b ^ ictx Θ.
Proof. reflexivity. Qed.

(** Abstraction et application, pour une spécification quelconque. *)
Definition lam {X σ} : X × ictx (dom σ) ~> So (cod σ) -> X ~> ispec σ :=
  match σ with Spec Θ b => fun g => curry g end.

Definition app {X σ} : X ~> ispec σ -> X ~> ictx (dom σ) -> X ~> So (cod σ) :=
  match σ with Spec Θ b => fun f a => eval ∘ (f △ a) end.

#[export] Instance lam_respects X σ : Proper (equiv ==> equiv) (@lam X σ).
Proof. destruct σ; intros f g E; simpl; rewrite E; reflexivity. Qed.

#[export] Instance app_respects X σ : Proper (equiv ==> equiv ==> equiv) (@app X σ).
Proof. destruct σ; intros f g E a b E'; simpl; rewrite E, E'; reflexivity. Qed.

Lemma app_lam {X σ} (g : X × ictx (dom σ) ~> So (cod σ)) (a : X ~> ictx (dom σ)) :
  app (lam g) a ≈ g ∘ (id △ a).
Proof. destruct σ; simpl. rewrite <- (id_right (curry g)). rewrite eval_curry. reflexivity. Qed.

Lemma lam_comp {X Y σ} (g : X × ictx (dom σ) ~> So (cod σ)) (h : Y ~> X) :
  lam g ∘ h ≈ lam (g ∘ first h).
Proof. destruct σ; simpl. apply curry_comp_l. Qed.

Lemma app_comp {X Y σ} (f : X ~> ispec σ) (a : X ~> ictx (dom σ)) (h : Y ~> X) :
  app f a ∘ h ≈ app (f ∘ h) (a ∘ h).
Proof. destruct σ; simpl. rewrite <- comp_assoc, fork_comp. reflexivity. Qed.

Lemma lam_inj {X σ} (g g' : X × ictx (dom σ) ~> So (cod σ)) : lam g ≈ lam g' -> g ≈ g'.
Proof. destruct σ; simpl. apply curry_inj. Qed.

(** η : toute flèche vers [ispec σ] est une abstraction. *)
Lemma lam_eta {X σ} (f : X ~> ispec σ) : lam (app (f ∘ exl) exr) ≈ f.
Proof.
  destruct σ; simpl. transitivity (curry (eval ∘ first f)).
  - reflexivity.
  - rewrite eval_first. apply curry_uncurry.
Qed.

(** ** Projections et n-uplets *)

Fixpoint proj {Θ τ} (z : var Θ τ) : ictx Θ ~> ispec τ :=
  match z in var Θ0 τ0 return ictx Θ0 ~> ispec τ0 with
  | vz => exr
  | vs z' => proj z' ∘ exl
  end.

Definition env Γ X : Type := forall σ, var Γ σ -> X ~> ispec σ.

Definition env_eq {Γ X} (ρ ρ' : env Γ X) : Type := forall σ (x : var Γ σ), ρ σ x ≈ ρ' σ x.

Fixpoint tuple {X} Θ : env Θ X -> X ~> ictx Θ :=
  match Θ return env Θ X -> X ~> ictx Θ with
  | [] => fun _ => one
  | τ :: Θ1 => fun f => tuple Θ1 (fun σ y => f σ (vs y)) △ f τ vz
  end.

Arguments tuple {X} Θ f.

Lemma proj_tuple {X Θ τ} (z : var Θ τ) (f : env Θ X) : proj z ∘ tuple Θ f ≈ f τ z.
Proof.
  induction z as [Θ τ|Θ τ τ' z IH]; cbn [proj tuple ictx].
  - apply exr_fork.
  - rewrite <- (comp_assoc (proj z)), exl_fork. apply (IH (fun σ y => f σ (vs y))).
Qed.

Lemma tuple_ext {X Θ} (f g : env Θ X) : env_eq f g -> tuple Θ f ≈ tuple Θ g.
Proof.
  induction Θ as [|τ Θ IH]; intros E; cbn [tuple]; [reflexivity|].
  apply fork_respects; [apply IH; intros σ y; apply E|apply E].
Qed.

(** Les projections sont conjointement monomorphes. *)
Lemma proj_ext {X Θ} (h k : X ~> ictx Θ) :
  (forall τ (z : var Θ τ), proj z ∘ h ≈ proj z ∘ k) -> h ≈ k.
Proof.
  induction Θ as [|τ Θ IH]; intros E; [apply one_unique|].
  cbn [ictx] in h, k |- *.
  transitivity ((exl ∘ k) △ (exr ∘ k));
    [|symmetry; apply (snd (ump_products _ _ _)); split; reflexivity].
  apply (snd (ump_products _ _ _)); split.
  - apply IH; intros σ y. rewrite !comp_assoc. exact (E σ (vs y)).
  - exact (E τ vz).
Qed.

Lemma tuple_comp {X Y Θ} (f : env Θ X) (h : Y ~> X) :
  tuple Θ f ∘ h ≈ tuple Θ (fun σ z => f σ z ∘ h).
Proof. apply proj_ext; intros τ z. rewrite comp_assoc, !proj_tuple. reflexivity. Qed.

Lemma tuple_proj {Θ} : tuple Θ (fun σ z => proj z) ≈ id.
Proof. apply proj_ext; intros τ z. rewrite proj_tuple, id_right. reflexivity. Qed.

Lemma tuple_proj_comp {X Θ} (h : X ~> ictx Θ) : tuple Θ (fun σ z => proj z ∘ h) ≈ h.
Proof. apply proj_ext; intros τ z. rewrite proj_tuple. reflexivity. Qed.

(** L'environnement canonique d'un contexte. *)
Definition penv Γ : env Γ (ictx Γ) := fun σ z => proj z.

(** ** Environnement relevé sous des lieurs *)

Definition ext D {Γ X} (ρ : env Γ X) : env (D ++ Γ) (X × ictx D) :=
  fun σ x => match vsplit D x with
             | inl z => proj z ∘ exr
             | inr y => ρ σ y ∘ exl
             end.

Lemma ext_vl D {Γ X} (ρ : env Γ X) {σ} (z : var D σ) : ext D ρ σ (vl Γ z) = proj z ∘ exr.
Proof. unfold ext; rewrite vsplit_vl; reflexivity. Qed.

Lemma ext_vr D {Γ X} (ρ : env Γ X) {σ} (y : var Γ σ) : ext D ρ σ (vr D y) = ρ σ y ∘ exl.
Proof. unfold ext; rewrite vsplit_vr; reflexivity. Qed.

Lemma ext_respects D {Γ X} (ρ ρ' : env Γ X) : env_eq ρ ρ' -> env_eq (ext D ρ) (ext D ρ').
Proof.
  intros E σ x. vcase x; rewrite ?ext_vl, ?ext_vr; [reflexivity|]. rewrite (E σ z). reflexivity.
Qed.

Context (Iy : forall σ, Sym σ -> ictx (dom σ) ~> So (cod σ)).

(** ** Interprétation des termes *)

Fixpoint stm {Γ s} (t : tm Γ s) : forall X, env Γ X -> X ~> So s :=
  match t with
  | tvar x a => fun X ρ => app (ρ _ x) (sargs a X ρ)
  | tsym c a => fun X ρ => Iy _ c ∘ sargs a X ρ
  end
with sargs {Γ Θ} (a : args Γ Θ) : forall X, env Γ X -> X ~> ictx Θ :=
  match a with
  | anil => fun X ρ => one
  | @acons _ _ _ σ _ u a' => fun X ρ => sargs a' X ρ △ lam (stm u _ (ext (dom σ) ρ))
  end.

Arguments stm {Γ s} t {X} ρ.
Arguments sargs {Γ Θ} a {X} ρ.

(** Un corps de spécification σ, interprété comme élément de ⟦σ⟧. *)
Definition stms {Γ σ} (u : tms Γ σ) {X} (ρ : env Γ X) : X ~> ispec σ :=
  lam (stm u (ext (dom σ) ρ)).

Lemma sargs_acons {Γ σ Θ} (u : tms Γ σ) (a : args Γ Θ) {X} (ρ : env Γ X) :
  sargs (acons u a) ρ = sargs a ρ △ stms u ρ.
Proof. reflexivity. Qed.

Lemma proj_sargs {Γ Θ τ} (z : var Θ τ) (a : args Γ Θ) {X} (ρ : env Γ X) :
  proj z ∘ sargs a ρ ≈ stms (aget z a) ρ.
Proof.
  revert a; induction z as [Θ τ|Θ τ τ' z IH]; intros a; rewrite (args_eta a); cbn [proj aget ahd atl ictx sargs].
  - apply exr_fork.
  - rewrite <- (comp_assoc (proj z)), exl_fork. apply IH.
Qed.

(** *** Extensionnalité *)

Lemma stm_ext_mut :
  (forall Γ s (t : tm Γ s) X (ρ ρ' : env Γ X), env_eq ρ ρ' -> stm t ρ ≈ stm t ρ') *
  (forall Γ Θ (a : args Γ Θ) X (ρ ρ' : env Γ X), env_eq ρ ρ' -> sargs a ρ ≈ sargs a ρ').
Proof.
  apply tm_args_rectT.
  - intros Γ σ x a IH X ρ ρ' E. cbn [stm]. apply app_respects; [apply E|apply IH, E].
  - intros Γ σ c a IH X ρ ρ' E. cbn [stm]. apply compose_respects; [reflexivity|apply IH, E].
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa X ρ ρ' E. cbn [sargs].
    apply fork_respects; [apply IHa, E|apply lam_respects, IHu, ext_respects, E].
Qed.

Lemma stm_ext {Γ s} (t : tm Γ s) {X} (ρ ρ' : env Γ X) : env_eq ρ ρ' -> stm t ρ ≈ stm t ρ'.
Proof. apply stm_ext_mut. Qed.

Lemma sargs_ext {Γ Θ} (a : args Γ Θ) {X} (ρ ρ' : env Γ X) : env_eq ρ ρ' -> sargs a ρ ≈ sargs a ρ'.
Proof. apply stm_ext_mut. Qed.

Lemma stms_ext {Γ σ} (u : tms Γ σ) {X} (ρ ρ' : env Γ X) : env_eq ρ ρ' -> stms u ρ ≈ stms u ρ'.
Proof. intros E; unfold stms; rewrite (stm_ext u _ _ (ext_respects _ _ _ E)). reflexivity. Qed.

(** *** Naturalité en X *)

Definition env_comp {Γ X Y} (ρ : env Γ X) (h : Y ~> X) : env Γ Y := fun σ x => ρ σ x ∘ h.

Lemma ext_comp D {Γ X Y} (ρ : env Γ X) (h : Y ~> X) :
  env_eq (env_comp (ext D ρ) (first h)) (ext D (env_comp ρ h)).
Proof.
  intros σ x; unfold env_comp. vcase x; rewrite ?ext_vl, ?ext_vr.
  - rewrite <- comp_assoc, exr_first. reflexivity.
  - rewrite <- !comp_assoc, exl_first. reflexivity.
Qed.

Lemma stm_nat_mut :
  (forall Γ s (t : tm Γ s) X Y (ρ : env Γ X) (h : Y ~> X), stm t ρ ∘ h ≈ stm t (env_comp ρ h)) *
  (forall Γ Θ (a : args Γ Θ) X Y (ρ : env Γ X) (h : Y ~> X), sargs a ρ ∘ h ≈ sargs a (env_comp ρ h)).
Proof.
  apply tm_args_rectT.
  - intros Γ σ x a IH X Y ρ h. cbn [stm]. rewrite app_comp, IH. reflexivity.
  - intros Γ σ c a IH X Y ρ h. cbn [stm]. rewrite <- comp_assoc, IH. reflexivity.
  - intros; apply one_unique.
  - intros Γ σ Θ u IHu a IHa X Y ρ h. cbn [sargs ictx]. rewrite <- fork_comp, IHa.
    apply fork_respects; [reflexivity|]. rewrite lam_comp, IHu.
    apply lam_respects, stm_ext, ext_comp.
Qed.

Lemma stm_nat {Γ s} (t : tm Γ s) {X Y} (ρ : env Γ X) (h : Y ~> X) :
  stm t ρ ∘ h ≈ stm t (env_comp ρ h).
Proof. apply stm_nat_mut. Qed.

Lemma sargs_nat {Γ Θ} (a : args Γ Θ) {X Y} (ρ : env Γ X) (h : Y ~> X) :
  sargs a ρ ∘ h ≈ sargs a (env_comp ρ h).
Proof. apply stm_nat_mut. Qed.

Lemma stms_nat {Γ σ} (u : tms Γ σ) {X Y} (ρ : env Γ X) (h : Y ~> X) :
  stms u ρ ∘ h ≈ stms u (env_comp ρ h).
Proof. unfold stms. rewrite lam_comp, stm_nat. apply lam_respects, stm_ext, ext_comp. Qed.

(** Tout environnement se factorise par l'environnement canonique. *)
Lemma env_penv {Γ X} (ρ : env Γ X) : env_eq ρ (env_comp (penv Γ) (tuple Γ ρ)).
Proof. intros σ x; unfold env_comp, penv. rewrite proj_tuple. reflexivity. Qed.

Lemma stm_penv {Γ s} (t : tm Γ s) {X} (ρ : env Γ X) : stm t ρ ≈ stm t (penv Γ) ∘ tuple Γ ρ.
Proof. rewrite stm_nat. apply stm_ext, env_penv. Qed.

Lemma sargs_penv {Γ Θ} (a : args Γ Θ) {X} (ρ : env Γ X) : sargs a ρ ≈ sargs a (penv Γ) ∘ tuple Γ ρ.
Proof. rewrite sargs_nat. apply sargs_ext, env_penv. Qed.

(** *** Renommage *)

Definition env_ren {Γ Δ X} (ξ : ren Γ Δ) (ρ : env Δ X) : env Γ X := fun σ x => ρ σ (ξ σ x).

Lemma ext_ren D {Γ Δ X} (ξ : ren Γ Δ) (ρ : env Δ X) :
  env_eq (env_ren (upr D ξ) (ext D ρ)) (ext D (env_ren ξ ρ)).
Proof.
  intros σ x; unfold env_ren. vcase x; rewrite ?upr_vl, ?upr_vr, ?ext_vl, ?ext_vr; reflexivity.
Qed.

Lemma stm_ren_mut :
  (forall Γ s (t : tm Γ s) Δ (ξ : ren Γ Δ) X (ρ : env Δ X), stm (ren_tm t ξ) ρ ≈ stm t (env_ren ξ ρ)) *
  (forall Γ Θ (a : args Γ Θ) Δ (ξ : ren Γ Δ) X (ρ : env Δ X),
      sargs (ren_args a ξ) ρ ≈ sargs a (env_ren ξ ρ)).
Proof.
  apply tm_args_rectT.
  - intros Γ σ x a IH Δ ξ X ρ. cbn [ren_tm stm]. rewrite IH. reflexivity.
  - intros Γ σ c a IH Δ ξ X ρ. cbn [ren_tm stm]. rewrite IH. reflexivity.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ ξ X ρ. cbn [ren_args sargs]. rewrite IHa.
    apply fork_respects; [reflexivity|]. apply lam_respects. rewrite IHu. apply stm_ext, ext_ren.
Qed.

Lemma stm_ren {Γ s} (t : tm Γ s) {Δ} (ξ : ren Γ Δ) {X} (ρ : env Δ X) :
  stm (ren_tm t ξ) ρ ≈ stm t (env_ren ξ ρ).
Proof. apply stm_ren_mut. Qed.

Lemma stms_ren {Γ σ} (u : tms Γ σ) {Δ} (ξ : ren Γ Δ) {X} (ρ : env Δ X) :
  stms (ren_tms u ξ) ρ ≈ stms u (env_ren ξ ρ).
Proof. unfold stms, ren_tms. rewrite stm_ren. apply lam_respects, stm_ext, ext_ren. Qed.

(** Affaiblir sous un lieur. *)
Lemma stms_wk D {Γ σ} (u : tms Γ σ) {X} (ρ : env Γ X) :
  stms (ren_tms u (wk D)) (ext D ρ) ≈ stms u ρ ∘ exl.
Proof.
  rewrite stms_ren, stms_nat. apply stms_ext. intros τ y; unfold env_ren, env_comp, wk.
  rewrite ext_vr. reflexivity.
Qed.

(** ** Kits et application héréditaire *)

(** L'environnement décrit par un kit : une variable renommée en y vaut ρ y,
    une variable substituée par u vaut ⟦u⟧ρ. *)
Definition kenv {Γ Δ X} (K : kit Sym Γ Δ) (ρ : env Δ X) : env Γ X :=
  fun σ x => match K σ x with
             | inl y => ρ σ y
             | inr (u, _) => stms u ρ
             end.

(** Une fonction d'application est correcte si elle interprète l'application. *)
Definition good σ (f : applier Sym σ) : Type :=
  forall Ξ (u : tms Ξ σ) (a : args Ξ (dom σ)) X (ρ : env Ξ X),
    stm (f Ξ u a) ρ ≈ app (stms u ρ) (sargs a ρ).

Definition kgood {Γ Δ} (K : kit Sym Γ Δ) : Type :=
  forall σ x u f, K σ x = inr (u, f) -> good σ f.

Lemma kenv_kup D {Γ Δ X} (K : kit Sym Γ Δ) (ρ : env Δ X) :
  env_eq (kenv (kup D K) (ext D ρ)) (ext D (kenv K ρ)).
Proof.
  intros σ x. unfold kenv at 1. vcase x.
  - rewrite kup_vl, !ext_vl. reflexivity.
  - rewrite kup_vr, ext_vr. unfold kenv. destruct (K σ z) as [w|[u f]]; cbn [eshift].
    + rewrite ext_vr. reflexivity.
    + apply stms_wk.
Qed.

Lemma kgood_kup D {Γ Δ} (K : kit Sym Γ Δ) : kgood K -> kgood (kup D K).
Proof.
  intros HK σ x u f E. vcase x.
  - rewrite kup_vl in E. discriminate.
  - rewrite kup_vr in E. destruct (K σ z) as [w|[u' f']] eqn:E'; cbn [eshift] in E; [discriminate|].
    injection E as _ <-. exact (HK σ z u' f' E').
Qed.

Lemma stm_trav_mut :
  (forall Γ s (t : tm Γ s) Δ (K : kit Sym Γ Δ) X (ρ : env Δ X),
      kgood K -> stm (trav t K) ρ ≈ stm t (kenv K ρ)) *
  (forall Γ Θ (a : args Γ Θ) Δ (K : kit Sym Γ Δ) X (ρ : env Δ X),
      kgood K -> sargs (trav_args a K) ρ ≈ sargs a (kenv K ρ)).
Proof.
  apply tm_args_rectT.
  - intros Γ σ x a IH Δ K X ρ HK.
    change (stm (match K σ x with
                 | inl y => tvar y (trav_args a K)
                 | inr (u, f) => f Δ u (trav_args a K)
                 end) ρ ≈ app (kenv K ρ σ x) (sargs a (kenv K ρ))).
    pose proof (IH Δ K X ρ HK) as IH'.
    unfold kenv at 1. destruct (K σ x) as [y|[u f]] eqn:E.
    + cbn [stm]. apply app_respects; [reflexivity|exact IH'].
    + rewrite (HK σ x u f E). apply app_respects; [reflexivity|exact IH'].
  - intros Γ σ c a IH Δ K X ρ HK. cbn [trav stm]. apply compose_respects; [reflexivity|apply IH, HK].
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ K X ρ HK. cbn [trav_args sargs].
    apply fork_respects; [apply IHa, HK|]. apply lam_respects.
    rewrite (IHu _ _ _ _ (kgood_kup _ _ HK)). apply stm_ext, kenv_kup.
Qed.

Lemma stm_trav {Γ s} (t : tm Γ s) {Δ} (K : kit Sym Γ Δ) {X} (ρ : env Δ X) :
  kgood K -> stm (trav t K) ρ ≈ stm t (kenv K ρ).
Proof. apply stm_trav_mut. Qed.

Lemma sargs_trav {Γ Θ} (a : args Γ Θ) {Δ} (K : kit Sym Γ Δ) {X} (ρ : env Δ X) :
  kgood K -> sargs (trav_args a K) ρ ≈ sargs a (kenv K ρ).
Proof. apply stm_trav_mut. Qed.

(** La correction de [happ σ], par récurrence sur la profondeur de σ. *)
Lemma good_happ_all n : forall σ, (depth σ < n)%nat -> good σ (happ σ).
Proof.
  induction n as [|n IHn]; intros σ Hd; [exfalso; lia|].
  destruct σ as [Θ b]. intros Ξ u a X ρ. rewrite happ_Spec.
  assert (HK : kgood (inst_kit Θ a (happs Θ))).
  { intros τ x u' f E. unfold inst_kit in E. destruct (vsplit Θ x) as [z|y]; [|discriminate].
    injection E as _ <-. rewrite all_get_happs. apply IHn.
    pose proof (depth_dom b z). lia. }
  rewrite (stm_trav u _ ρ HK). unfold stms. cbn [dom].
  rewrite app_lam, stm_nat. apply stm_ext. intros τ x. unfold env_comp. vcase x.
  - unfold kenv. rewrite inst_kit_vl, ext_vl, <- comp_assoc, exr_fork, proj_sargs. reflexivity.
  - unfold kenv. rewrite inst_kit_vr, ext_vr, <- comp_assoc, exl_fork, id_right. reflexivity.
Qed.

Corollary good_happ σ : good σ (happ σ).
Proof. apply (good_happ_all (S (depth σ))). lia. Qed.

Lemma kgood_sub {Γ Δ} (τ : sub Sym Γ Δ) : kgood (sub_kit τ).
Proof. intros σ x u f E. unfold sub_kit in E. injection E as _ <-. apply good_happ. Qed.

(** ** Le lemme de substitution *)

Lemma stm_subst {Γ s} (t : tm Γ s) {Δ} (τ : sub Sym Γ Δ) {X} (ρ : env Δ X) :
  stm (subst t τ) ρ ≈ stm t (fun σ x => stms (τ σ x) ρ).
Proof. unfold subst. rewrite (stm_trav t _ ρ (kgood_sub τ)). reflexivity. Qed.

(** L'environnement « ⟦v⟧ρ » : la variable x reçoit ⟦v_x⟧ρ. *)
Lemma env_vget {Γ Δ X} (v : vec Sym Γ Δ) (ρ : env Δ X) :
  env_eq (fun σ x => stms (vget v σ x) ρ) (env_comp (penv Γ) (sargs v ρ)).
Proof. intros σ x. unfold env_comp, penv, vget. rewrite proj_sargs. reflexivity. Qed.

Theorem stm_vsubst {Γ s} (t : tm Γ s) {Δ} (v : vec Sym Γ Δ) {X} (ρ : env Δ X) :
  stm (vsubst t v) ρ ≈ stm t (penv Γ) ∘ sargs v ρ.
Proof. unfold vsubst. rewrite stm_subst, stm_nat. apply stm_ext, env_vget. Qed.

Theorem stms_vsubst {Γ σ} (u : tms Γ σ) {Δ} (v : vec Sym Γ Δ) {X} (ρ : env Δ X) :
  stms (vsubst_tms u v) ρ ≈ stms u (penv Γ) ∘ sargs v ρ.
Proof.
  unfold vsubst_tms, subst_tms, stms.
  rewrite (stm_trav u _ _ (kgood_kup _ _ (kgood_sub _))), lam_comp, stm_nat.
  apply lam_respects, stm_ext. intros τ x. rewrite (kenv_kup _ _ _ τ x).
  rewrite (ext_comp _ (penv Γ) (sargs v ρ) τ x).
  apply ext_respects, env_vget.
Qed.

Theorem sargs_vsubst {Γ Θ} (a : args Γ Θ) {Δ} (v : vec Sym Γ Δ) {X} (ρ : env Δ X) :
  sargs (vsubst_args a v) ρ ≈ sargs a (penv Γ) ∘ sargs v ρ.
Proof.
  unfold vsubst_args, subst_args. rewrite (sargs_trav a _ ρ (kgood_sub _)), sargs_nat.
  apply sargs_ext, env_vget.
Qed.

(** ** η-expansion *)

Lemma sargs_etas Θ :
  (forall τ (z : var Θ τ) Γ (x : var Γ τ) X (ρ : env Γ X), stms (eta τ x) ρ ≈ ρ τ x) ->
  forall Ξ (f : forall τ, var Θ τ -> var Ξ τ) X (ρ : env Ξ X),
    sargs (etas Θ f) ρ ≈ tuple Θ (fun τ z => ρ τ (f τ z)).
Proof.
  induction Θ as [|τ Θ IH]; intros He Ξ f X ρ; cbn [etas sargs tuple]; [reflexivity|].
  apply fork_respects.
  - apply IH. intros τ' z. apply (He τ' (vs z)).
  - apply (He τ vz).
Qed.

Lemma stms_eta_all n : forall σ, (depth σ < n)%nat ->
  forall Γ (x : var Γ σ) X (ρ : env Γ X), stms (eta σ x) ρ ≈ ρ σ x.
Proof.
  induction n as [|n IHn]; intros σ Hd; [exfalso; lia|].
  destruct σ as [Θ b]. intros Γ x X ρ. rewrite eta_Spec. unfold stms. cbn [dom stm].
  rewrite ext_vr, sargs_etas.
  - rewrite (tuple_ext _ (fun τ z => proj z ∘ exr)), tuple_proj_comp; [exact (lam_eta (σ := Spec Θ b) (ρ _ x))|].
    intros τ z. rewrite ext_vl. reflexivity.
  - intros τ z. apply IHn. pose proof (depth_dom b z). lia.
Qed.

Corollary stms_eta {Γ σ} (x : var Γ σ) {X} (ρ : env Γ X) : stms (eta σ x) ρ ≈ ρ σ x.
Proof. apply (stms_eta_all (S (depth σ))). lia. Qed.

Corollary sargs_etas' Θ {Ξ} (f : forall τ, var Θ τ -> var Ξ τ) {X} (ρ : env Ξ X) :
  sargs (etas Θ f) ρ ≈ tuple Θ (fun τ z => ρ τ (f τ z)).
Proof. apply sargs_etas. intros; apply stms_eta. Qed.

Corollary sargs_vid {Γ X} (ρ : env Γ X) : sargs (vid Γ) ρ ≈ tuple Γ ρ.
Proof. apply sargs_etas'. Qed.

Corollary sargs_vid_penv Γ : sargs (vid Γ) (penv Γ) ≈ id.
Proof. rewrite sargs_vid. apply tuple_proj. Qed.

End Semantics.

Arguments stm {Srt Sym} C {CT CC CL} So Iy {Γ s} t {X} ρ.
Arguments sargs {Srt Sym} C {CT CC CL} So Iy {Γ Θ} a {X} ρ.
