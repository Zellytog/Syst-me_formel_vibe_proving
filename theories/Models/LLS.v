(** * Le théorème de Lawvere–Lambek–Scott : des données concrètes au modèle

    Soit C une catégorie cartésienne fermée, un objet ⟦b⟧ pour chaque sorte
    et un morphisme ⟦f⟧ : ⟦dom σ⟧ ~> ⟦cod σ⟧ pour chaque symbole f : σ.
    Si ces données **valident le calcul** — deux termes convertibles ont la
    même interprétation ([Hc]) —, alors elles s'étendent en un morphisme de
    CCC [SynConv] → C, c'est-à-dire en un modèle du calcul au sens de
    [Calculus.v] ([lls_model]) :
    - le foncteur envoie Γ sur ⟦Γ⟧ et un vecteur v : Γ → Δ sur le n-uplet
      des interprétations de ses composantes ([lls_fun]) ; la composition
      est respectée grâce au lemme de substitution ;
    - il préserve l'objet terminal, les produits ([sp_iso] :
      ⟦Δ ++ Γ⟧ ≅ ⟦Γ⟧ × ⟦Δ⟧) et les exponentielles
      ([eiso] : ⟦Γ^Δ⟧ ≅ ⟦Γ⟧^⟦Δ⟧), avec les cohérences demandées par
      [CartesianFunctor] et [ClosedFunctor].

    Et le modèle obtenu étend bien les données ([lls_sem], [lls_sym]) :
    à l'isomorphisme canonique M[ι b] ≅ ⟦b⟧ près, un terme s'interprète
    par sa sémantique [stm] et un symbole par ⟦f⟧. *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Models Require Import Semantics Calculus.

Local Notation ι a := (Spec [] a).

Section Split.

Context {Srt : Type}.
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (So : Srt -> obj[C]).

Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ : spec Srt).

Local Notation ictx := (ictx C So).
Local Notation ispec := (ispec C So).
Local Notation proj := (proj C So).
Local Notation tuple := (tuple C So).
Local Notation penv := (penv C So).
Local Notation ext := (ext C So).
Local Notation env := (env C So).

(** ** L'isomorphisme ⟦D ++ Γ⟧ ≅ ⟦Γ⟧ × ⟦D⟧ *)

Definition sp_to D Γ : ictx (D ++ Γ) ~> ictx Γ × ictx D :=
  tuple Γ (fun σ z => proj (vr D z)) △ tuple D (fun σ z => proj (vl Γ z)).

Definition sp_from D Γ : ictx Γ × ictx D ~> ictx (D ++ Γ) := tuple (D ++ Γ) (ext D (penv Γ)).

Lemma sp_to_from D Γ : sp_to D Γ ∘ sp_from D Γ ≈ id.
Proof.
  unfold sp_to. rewrite <- fork_comp, <- fork_exl_exr. apply fork_respects.
  - rewrite tuple_comp. etransitivity; [|apply (tuple_proj_comp C So exl)].
    apply tuple_ext. intros σ z. unfold sp_from. rewrite proj_tuple, ext_vr. reflexivity.
  - rewrite tuple_comp. etransitivity; [|apply (tuple_proj_comp C So exr)].
    apply tuple_ext. intros σ z. unfold sp_from. rewrite proj_tuple, ext_vl. reflexivity.
Qed.

Lemma sp_from_to D Γ : sp_from D Γ ∘ sp_to D Γ ≈ id.
Proof.
  apply proj_ext. intros τ x. rewrite id_right, comp_assoc. unfold sp_from. rewrite proj_tuple.
  unfold sp_to. vcase x.
  - rewrite ext_vl, <- comp_assoc, exr_fork, proj_tuple. reflexivity.
  - rewrite ext_vr. unfold penv. rewrite <- comp_assoc, exl_fork, proj_tuple. reflexivity.
Qed.

Definition sp_iso D Γ : ictx (D ++ Γ) ≅ ictx Γ × ictx D :=
  {| to := sp_to D Γ; from := sp_from D Γ;
     iso_to_from := sp_to_from D Γ; iso_from_to := sp_from_to D Γ |}.

(** Un environnement relevé, vu à travers [sp_from]. *)
Lemma ext_penv D Γ : env_eq C So (ext D (penv Γ)) (env_comp C So (penv (D ++ Γ)) (sp_from D Γ)).
Proof. intros σ x. unfold env_comp, penv at 2, sp_from. rewrite proj_tuple. reflexivity. Qed.

(** ** L'isomorphisme ⟦Γ^Δ⟧ ≅ ⟦Γ⟧^⟦Δ⟧

    Pour une spécification σ = D → b : ⟦b⟧^⟦D ++ Δ⟧ ≅ (⟦b⟧^⟦D⟧)^⟦Δ⟧
    ([phi1], [psi1]) ; puis composante par composante sur Γ ([eiso]). *)

Definition Kphi D Δ b : (So b ^ ictx (D ++ Δ) × ictx Δ) × ictx D ~> So b :=
  eval ∘ ((exl ∘ exl) △ (sp_from D Δ ∘ first exr)).
Definition phi1 D Δ b : So b ^ ictx (D ++ Δ) ~> (So b ^ ictx D) ^ ictx Δ := curry (curry (Kphi D Δ b)).
Definition Kpsi D Δ b : (So b ^ ictx D) ^ ictx Δ × ictx (D ++ Δ) ~> So b :=
  eval ∘ ((eval ∘ (exl △ (exl ∘ (sp_to D Δ ∘ exr)))) △ (exr ∘ (sp_to D Δ ∘ exr))).
Definition psi1 D Δ b : (So b ^ ictx D) ^ ictx Δ ~> So b ^ ictx (D ++ Δ) := curry (Kpsi D Δ b).

Lemma psi_phi D Δ b : psi1 D Δ b ∘ phi1 D Δ b ≈ id.
Proof.
  apply uncurry_inj. rewrite uncurry_comp. unfold psi1. rewrite uncurry_curry. unfold Kpsi.
  rewrite <- comp_assoc, <- fork_comp.
  rewrite <- !comp_assoc, !exr_first, <- fork_comp, exl_first, <- !comp_assoc, exr_first.
  unfold phi1. rewrite eval_curry, eval_curry. unfold Kphi.
  rewrite <- comp_assoc, <- fork_comp, <- comp_assoc, exl_fork, exl_fork.
  unfold first. rewrite <- comp_assoc, <- fork_comp, <- comp_assoc, exl_fork, exr_fork, exr_fork.
  rewrite fork_comp, fork_exl_exr, id_left, comp_assoc, sp_from_to, id_left, fork_exl_exr, id_right.
  reflexivity.
Qed.

Lemma phi_psi D Δ b : phi1 D Δ b ∘ psi1 D Δ b ≈ id.
Proof.
  apply uncurry_inj. rewrite uncurry_comp. unfold phi1. rewrite uncurry_curry, curry_comp_l.
  apply uncurry_inj. rewrite uncurry_curry.
  transitivity (eval (x := ictx D) (y := So b) ∘ first (eval (x := ictx Δ) (y := So b ^ ictx D))); [|rewrite eval_first; reflexivity].
  unfold Kphi. rewrite <- comp_assoc, <- fork_comp.
  rewrite <- !comp_assoc, exl_first, (comp_assoc exl), exl_first, <- comp_assoc.
  rewrite <- first_comp, exr_first.
  unfold psi1. rewrite eval_curry. unfold Kpsi.
  rewrite <- comp_assoc, <- fork_comp, <- comp_assoc, <- fork_comp.
  rewrite exl_fork, <- !comp_assoc, exr_fork, (comp_assoc (sp_to D Δ)), sp_to_from, id_left.
  unfold first. rewrite exl_fork, exr_fork, fork_comp, fork_exl_exr, id_left.
  reflexivity.
Qed.

Lemma Kphi_first D Δ b {Y Z} (g : Y × ictx (D ++ Δ) ~> So b) (T : Z ~> Y × ictx Δ) :
  Kphi D Δ b ∘ first (first (curry g) ∘ T)
  ≈ g ∘ ((exl ∘ T ∘ exl) △ (sp_from D Δ ∘ first (exr ∘ T))).
Proof.
  unfold Kphi.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc. rewrite (exl_first (first (curry g) ∘ T)), <- first_comp.
  rewrite !comp_assoc, exl_first, exr_first, <- !comp_assoc, eval_curry. reflexivity.
Qed.

Definition phis σ Δ : ispec (Spec (dom σ ++ Δ) (cod σ)) ~> ispec σ ^ ictx Δ :=
  match σ as σ0 return ispec (Spec (dom σ0 ++ Δ) (cod σ0)) ~> ispec σ0 ^ ictx Δ with
  | Spec D b => phi1 D Δ b
  end.
Definition psis σ Δ : ispec σ ^ ictx Δ ~> ispec (Spec (dom σ ++ Δ) (cod σ)) :=
  match σ as σ0 return ispec σ0 ^ ictx Δ ~> ispec (Spec (dom σ0 ++ Δ) (cod σ0)) with
  | Spec D b => psi1 D Δ b
  end.
Lemma psis_phis σ Δ : psis σ Δ ∘ phis σ Δ ≈ id.
Proof. destruct σ; apply psi_phi. Qed.
Lemma phis_psis σ Δ : phis σ Δ ∘ psis σ Δ ≈ id.
Proof. destruct σ; apply phi_psi. Qed.

Fixpoint eto Δ Γ : ictx (expo Δ Γ) ~> ictx Γ ^ ictx Δ :=
  match Γ as Γ0 return ictx (expo Δ Γ0) ~> ictx Γ0 ^ ictx Δ with
  | [] => curry one
  | σ :: Γ' => curry (uncurry (eto Δ Γ' ∘ exl) △ uncurry (phis σ Δ ∘ exr))
  end.
Fixpoint efrom Δ Γ : ictx Γ ^ ictx Δ ~> ictx (expo Δ Γ) :=
  match Γ as Γ0 return ictx Γ0 ^ ictx Δ ~> ictx (expo Δ Γ0) with
  | [] => one
  | σ :: Γ' => (efrom Δ Γ' ∘ curry (exl ∘ eval)) △ (psis σ Δ ∘ curry (exr ∘ eval))
  end.

Lemma efrom_eto Δ Γ : efrom Δ Γ ∘ eto Δ Γ ≈ id.
Proof.
  induction Γ as [|σ Γ IH]; cbn [efrom eto expo Semantics.ictx]; [apply one_unique|].
  rewrite <- fork_comp, <- fork_exl_exr. apply fork_respects.
  - rewrite <- comp_assoc, <- curry_comp, exl_fork, curry_uncurry, comp_assoc, IH, id_left. reflexivity.
  - rewrite <- comp_assoc, <- curry_comp, exr_fork, curry_uncurry, comp_assoc, psis_phis, id_left.
    reflexivity.
Qed.

Lemma eto_efrom Δ Γ : eto Δ Γ ∘ efrom Δ Γ ≈ id.
Proof.
  induction Γ as [|σ Γ IH]; cbn [efrom eto expo Semantics.ictx]; apply uncurry_inj; [apply one_unique|].
  rewrite uncurry_comp, uncurry_curry, <- fork_comp, <- !uncurry_comp, <- !comp_assoc, exl_fork, exr_fork.
  rewrite !comp_assoc, IH, phis_psis, !id_left, !uncurry_curry, fork_comp, fork_exl_exr, id_left.
  reflexivity.
Qed.

Definition eiso Δ Γ : ictx (expo Δ Γ) ≅ ictx Γ ^ ictx Δ :=
  {| to := eto Δ Γ; from := efrom Δ Γ; iso_to_from := eto_efrom Δ Γ; iso_from_to := efrom_eto Δ Γ |}.

End Split.

Set Default Proof Using "All".

Section LLS.

Context {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (So : Srt -> obj[C]).
Context (Iy : forall σ, Sym σ -> ictx C So (dom σ) ~> So (cod σ)).

Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation ictx := (ictx C So).
Local Notation ispec := (ispec C So).
Local Notation proj := (proj C So).
Local Notation tuple := (tuple C So).
Local Notation penv := (penv C So).
Local Notation ext := (ext C So).
Local Notation env := (env C So).
Local Notation stm := (stm C So Iy).
Local Notation sargs := (sargs C So Iy).
Local Notation stms := (stms C So Iy).
Local Notation sp_to := (sp_to C So).
Local Notation sp_from := (sp_from C So).
Local Notation sp_iso := (sp_iso C So).
Local Notation sp_from_to := (sp_from_to C So).
Local Notation sp_to_from := (sp_to_from C So).

Lemma sargs_sexl Γ Δ : sargs (sexl Sym Γ Δ) (penv (Δ ++ Γ)) ≈ tuple Γ (fun σ z => proj (vr Δ z)).
Proof. unfold sexl. apply sargs_etas'. Qed.

Lemma sargs_sexr Γ Δ : sargs (sexr Sym Γ Δ) (penv (Δ ++ Γ)) ≈ tuple Δ (fun σ z => proj (vl Γ z)).
Proof. unfold sexr. apply sargs_etas'. Qed.

(** ** Validation du calcul *)

Context (Hc : forall Γ s (t u : tm Γ s), conv S t u -> stm t (penv Γ) ≈ stm u (penv Γ)).

Lemma conv_stm {Γ s} (t u : tm Γ s) {X} (ρ : env Γ X) : conv S t u -> stm t ρ ≈ stm u ρ.
Proof.
  intros H. rewrite (stm_penv C So Iy t ρ), (stm_penv C So Iy u ρ), (Hc _ _ _ _ H). reflexivity.
Qed.

Lemma conv_sargs {Γ Θ} (a a' : args Sym Γ Θ) {X} (ρ : env Γ X) :
  arel (conv S) a a' -> sargs a ρ ≈ sargs a' ρ.
Proof.
  revert a a'; induction Θ as [|σ Θ IH]; intros a a' H.
  - rewrite (args_nil a), (args_nil a'). reflexivity.
  - destruct H as [H1 H2]. rewrite (args_eta a), (args_eta a'). cbn [Semantics.sargs].
    apply fork_respects; [apply IH, H2|]. apply lam_respects, conv_stm, H1.
Qed.

(** ** Le foncteur *)

Lemma sargs_vcomp {Γ Δ Ξ} (f : args Sym Δ Ξ) (g : args Sym Γ Δ) :
  sargs (vcomp f g) (penv Γ) ≈ sargs f (penv Δ) ∘ sargs g (penv Γ).
Proof.
  apply proj_ext. intros τ z. rewrite comp_assoc, !proj_sargs, aget_vcomp. apply stms_vsubst.
Qed.

Program Definition lls_fun : SynConv S ⟶ C := {|
  fobj := fun Γ => ictx Γ;
  fmap := fun Γ Δ (v : args Sym Γ Δ) => sargs v (penv Γ)
|}.
Next Obligation. repeat intro. simpl in *. apply conv_sargs. assumption. Qed.
Next Obligation. apply sargs_vid_penv. Qed.
Next Obligation. apply sargs_vcomp. Qed.

Lemma lls_exl x y : fmap[lls_fun] (@exl (SynConv S) _ x y) ≈ exl ∘ sp_to y x.
Proof. unfold sp_to. rewrite exl_fork. apply sargs_sexl. Qed.

Lemma lls_exr x y : fmap[lls_fun] (@exr (SynConv S) _ x y) ≈ exr ∘ sp_to y x.
Proof. unfold sp_to. rewrite exr_fork. apply sargs_sexr. Qed.

Lemma lls_fork {x y z : SynConv S} (f : x ~> y) (g : x ~> z) :
  fmap[lls_fun] (f △ g) ≈ sp_from z y ∘ (fmap[lls_fun] f △ fmap[lls_fun] g).
Proof.
  transitivity (sp_from z y ∘ sp_to z y ∘ fmap[lls_fun] (f △ g)).
  { symmetry. etransitivity; [apply compose_respects; [apply sp_from_to|reflexivity]|]. apply id_left. }
  rewrite <- comp_assoc.
  apply compose_respects; [reflexivity|].
  apply (snd (ump_products _ _ _)); split.
  - rewrite comp_assoc.
    etransitivity; [apply compose_respects; [symmetry; apply lls_exl|reflexivity]|].
    rewrite <- fmap_comp. exact (@fmap_respects _ _ lls_fun _ _ _ _ (exl_fork f g)).
  - rewrite comp_assoc.
    etransitivity; [apply compose_respects; [symmetry; apply lls_exr|reflexivity]|].
    rewrite <- fmap_comp. exact (@fmap_respects _ _ lls_fun _ _ _ _ (exr_fork f g)).
Qed.

#[local] Program Instance lls_cartesian :
  @CartesianFunctor (SynConv S) C lls_fun (SynConv_Cartesian S) CC := {
  fobj_prod_iso := fun x y => sp_iso y x
}.
Next Obligation. apply lls_exl. Qed.
Next Obligation. apply lls_exr. Qed.
Next Obligation. apply lls_fork. Qed.


(** ** Préservation des exponentielles *)

Local Notation eto := (eto C So).
Local Notation efrom := (efrom C So).
Local Notation phis := (phis C So).
Local Notation eiso := (eiso C So).

Lemma uncurry_core σ Δ Ξ (u : Terms.tms Sym Ξ (Spec (dom σ ++ Δ) (cod σ))) :
  stms (ren_tm (s := cod σ) (Γ := (dom σ ++ Δ) ++ Ξ) u (assoc_r (dom σ) Δ Ξ) : Terms.tms Sym (Δ ++ Ξ) σ) (penv (Δ ++ Ξ))
  ≈ uncurry (phis σ Δ ∘ stms u (penv Ξ)) ∘ sp_to Δ Ξ.
Proof.
  destruct σ as [D b]. cbn [dom cod phis]. unfold stms. cbn [dom cod lam]. unfold phi1.
  rewrite uncurry_comp, uncurry_curry, <- comp_assoc.
  etransitivity; [|symmetry; exact (curry_comp_l (Kphi C So D Δ b) _)]. apply curry_respects.
  transitivity (stm u (ext (D ++ Δ) (penv Ξ)) ∘
                ((exl ∘ sp_to Δ Ξ ∘ exl) △ (sp_from D Δ ∘ first (exr ∘ sp_to Δ Ξ)))).
  2:{ symmetry. apply Kphi_first. }
  rewrite stm_ren, stm_nat. apply stm_ext. intros τ x. unfold env_ren, env_comp.
  vcase x; [vcase z|].
  - rewrite assoc_r_D, !ext_vl, <- comp_assoc, exr_fork, comp_assoc. unfold sp_from.
    rewrite proj_tuple, ext_vl, <- comp_assoc, exr_first. reflexivity.
  - rewrite assoc_r_M, ext_vr, ext_vl, <- comp_assoc, exr_fork, comp_assoc. unfold sp_from.
    rewrite proj_tuple, ext_vr. unfold penv. rewrite <- comp_assoc, exl_first, !comp_assoc.
    unfold sp_to. rewrite <- (comp_assoc (proj z0)), exr_fork, proj_tuple. reflexivity.
  - rewrite assoc_r_X, !ext_vr. unfold penv. unfold sp_to.
    rewrite <- (comp_assoc (proj z)), exl_fork, exl_fork, comp_assoc, proj_tuple. reflexivity.
Qed.

Lemma sargs_vuncurry Δ Ξ Γ (g : args Sym Ξ (expo Δ Γ)) :
  sargs (vuncurry Sym Δ Ξ Γ g) (penv (Δ ++ Ξ)) ≈ uncurry (eto Δ Γ ∘ sargs g (penv Ξ)) ∘ sp_to Δ Ξ.
Proof.
  induction Γ as [|σ Γ IH]; cbn [vuncurry Semantics.sargs LLS.eto expo Semantics.ictx].
  - apply one_unique.
  - assert (Eg : sargs g (penv Ξ) ≈ sargs (atl g) (penv Ξ) △ stms (ahd g) (penv Ξ))
      by exact (eq_rect _ (fun h : args Sym Ξ (expo Δ (σ :: Γ)) => sargs h (penv Ξ) ≈ sargs (atl g) (penv Ξ) △ stms (ahd g) (penv Ξ))
                  (reflexivity _) g (eq_sym (args_eta g))).
    rewrite Eg, uncurry_comp, uncurry_curry, <- fork_comp, <- fork_comp.
    apply fork_respects.
    + rewrite IH. apply compose_respects; [|reflexivity].
      rewrite <- uncurry_comp, <- comp_assoc, exl_fork. reflexivity.
    + rewrite <- uncurry_comp, <- comp_assoc, exr_fork. apply uncurry_core.
Qed.

Lemma lls_curry {x y z : SynConv S} (f : x × y ~> z) :
  fmap[lls_fun] (curry f) ≈ efrom y z ∘ curry (fmap[lls_fun] f ∘ sp_from y x).
Proof.
  transitivity (efrom y z ∘ eto y z ∘ fmap[lls_fun] (curry f)).
  { symmetry. etransitivity; [apply compose_respects; [apply efrom_eto|reflexivity]|]. apply id_left. }
  rewrite <- comp_assoc. apply compose_respects; [reflexivity|].
  apply uncurry_inj. rewrite uncurry_curry.
  pose proof (sargs_vuncurry y x z (vcurry Sym y x z f)) as H.
  rewrite vuncurry_vcurry in H.
  etransitivity; [|apply compose_respects; [symmetry; exact H|reflexivity]].
  rewrite <- comp_assoc.
  etransitivity; [|apply compose_respects; [reflexivity|symmetry; apply sp_to_from]].
  symmetry. etransitivity; [apply id_right|]. reflexivity.
Qed.

#[local] Program Instance lls_closed :
  @ClosedFunctor (SynConv S) C lls_fun (SynConv_Cartesian S) CC lls_cartesian
    (SynConv_Closed S) CL := {
  fobj_exp_iso := fun x y => eiso x y
}.
Next Obligation. apply lls_curry. Qed.
Next Obligation. apply sargs_vuncurry. Qed.

(** ** Le modèle *)

Definition lls_model : cmodel S C := {|
  cm_fun := lls_fun;
  cm_terminal := iso_id;
  cm_cartesian := lls_cartesian;
  cm_closed := lls_closed
|}.

(** L'isomorphisme canonique M[ι b] = 1 × ⟦b⟧^1 ≅ ⟦b⟧. *)
Definition sort_iso b : sort_obj lls_model b ≅ So b := iso_compose exp_one prod_one_l.

(** Le modèle étend les données : les termes s'interprètent par [stm]... *)
Theorem lls_sem {Γ b} (t : tm Γ b) : to (sort_iso b) ∘ sem lls_model t ≈ stm t (penv Γ).
Proof.
  unfold sem, sort_iso, hat. simpl. cbn [Semantics.ictx Semantics.ispec].
  rewrite <- !comp_assoc.
  etransitivity; [apply compose_respects; [reflexivity|apply compose_respects; [reflexivity|apply exr_fork]]|].
  etransitivity; [apply compose_respects; [reflexivity|symmetry; apply fork_comp]|].
  etransitivity.
  { apply compose_respects; [reflexivity|].
    apply fork_respects; [rewrite id_left; symmetry; apply id_right|apply (one_unique _ one)]. }
  etransitivity; [apply eval_curry|]. rewrite stm_nat. apply stm_ext. intros τ x. unfold env_comp.
  change (ext [] (penv Γ) τ x) with (ext [] (penv Γ) τ (vr [] x)).
  rewrite ext_vr, <- comp_assoc, exl_fork, id_right. reflexivity.
Qed.

(** ... et les symboles par les morphismes donnés. *)
Corollary lls_sym {σ} (c : Sym σ) : to (sort_iso (cod σ)) ∘ sym_mor lls_model c ≈ Iy σ c.
Proof.
  unfold sym_mor. rewrite lls_sem. cbn [Semantics.stm].
  rewrite (sargs_vid_penv C So Iy), id_right. reflexivity.
Qed.

(** Et les contextes par les produits des données : M Γ = ⟦Γ⟧. *)
Lemma lls_ctx Γ : ctx_obj lls_model Γ = ictx Γ.
Proof. reflexivity. Qed.

End LLS.
