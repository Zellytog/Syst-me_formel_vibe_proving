(** * Correction de la traduction : les schémas de IZF⁻ε

    Séparation, collection et ∈-induction. On se ramène, par clôture
    universelle, au cas où les métavariables d'ensembles sont des
    variables ; la métavariable de formule n'est alors appliquée qu'à des
    variables, et la traduction commute exactement avec ces
    substitutions, qui sont des renommages ([tr_inst_var]). Chaque schéma
    traduit est l'instance d'un gabarit de IZF, prouvé une fois pour
    toutes. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFTrSem IZFSound.

Local Notation ι a := (Spec [] a).

(** ** La traduction commute avec les substitutions de variables *)

Lemma tr_vsubst_rv {Θ Γ} (ψ : form Θ) (ρ : ren Θ Γ) :
  tr (vsubst ψ (vpre ρ (vid Γ))) = vsubst (tr ψ) (vpre ρ (vid Γ)).
Proof. rewrite <- !ren_as_vsubst. apply tr_ren. Qed.

Definition rz {Γ} (z : var Γ (ι V)) : ren (ι V :: Γ) Γ :=
  fun σ x => var_inv (fun σ _ => var Γ σ) z (fun σ' y => y) σ x.

Lemma inst1_rv {Sg : spec isort -> Type} {Γ} (z : var Γ (ι V)) :
  inst1 (Sym := Sg) (var0 z) = vpre (rz z) (vid Γ).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
  refine (var_inv (fun σ x => aget x (inst1 (Sym := Sg) (var0 z)) = aget (rz z σ x) (vid Γ)) _ _ σ x).
  - cbn. rewrite aget_vid. reflexivity.
  - intros τ y. cbn. reflexivity.
Qed.

Lemma tr_inst_var {Γ} (ψ : form (ι V :: Γ)) (z : var Γ (ι V)) :
  tr (vsubst ψ (inst1 (var0 z))) = vsubst (tr ψ) (inst1 (var0 z)).
Proof. rewrite !inst1_rv. apply tr_vsubst_rv. Qed.

Definition rz2 {Γ} (z1 z2 : var Γ (ι V)) : ren (ι V :: ι V :: Γ) Γ :=
  fun σ x => var_inv (fun σ _ => var Γ σ) z1 (fun σ' y => var_inv (fun σ _ => var Γ σ) z2 (fun σ'' w => w) σ' y) σ x.

Lemma inst2_rv {Sg : spec isort -> Type} {Γ} (z1 z2 : var Γ (ι V)) :
  inst2 (Sg := Sg) (var0 z1) (var0 z2) = vpre (rz2 z1 z2) (vid Γ).
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre.
  refine (var_inv (fun σ x => aget x (inst2 (Sg := Sg) (var0 z1) (var0 z2)) = aget (rz2 z1 z2 σ x) (vid Γ)) _ _ σ x).
  - cbn. rewrite aget_vid. reflexivity.
  - intros τ y.
    refine (var_inv (fun τ y => aget (vs y) (inst2 (Sg := Sg) (var0 z1) (var0 z2)) = aget (rz2 z1 z2 τ (vs y)) (vid Γ)) _ _ τ y).
    + cbn. rewrite aget_vid. reflexivity.
    + intros τ' w. cbn. reflexivity.
Qed.

Lemma tr_inst2_var {Γ} (ψ : form (ι V :: ι V :: Γ)) (z1 z2 : var Γ (ι V)) :
  tr (vsubst ψ (inst2 (var0 z1) (var0 z2))) = vsubst (tr ψ) (inst2 (var0 z1) (var0 z2)).
Proof. rewrite !inst2_rv. apply tr_vsubst_rv. Qed.

(** ** Les gabarits de schémas *)

(** Une relation entre une formule de IZF⁻ε et son gabarit dans IZF : les
    métavariables d'ensembles sont des variables, les métavariables de
    formule ne sont appliquées qu'à des variables. *)
Inductive schV : forall Θ, tm Θ V -> zform (ι V :: Θ) -> Prop :=
| sc_var {Θ} (x : var Θ (ι V)) : schV Θ (var0 x) (DV x)
| sc_sep {Θ} t φ D P : schV Θ t D -> schP (ι V :: Θ) φ P -> schV Θ (Sep t φ) (vsubst Fsep (vup [ι V] (v2 D P)))
| sc_power {Θ} t D : schV Θ t D -> schV Θ (Power t) (vsubst Fpower (vup [ι V] (v1 D)))
| sc_repl {Θ} t ψ D P : schV Θ t D -> schP (ι V :: ι V :: Θ) ψ P ->
    schV Θ (Repl t ψ) (vsubst Frepl (vup [ι V] (vPR D P)))
| sc_rec {Θ} φ ψ t P R D : schP (ι V :: Θ) φ P -> schP (ι V :: ι V :: Θ) ψ R -> schV Θ t D ->
    schV Θ (Rec φ ψ t) (vsubst Frec (vup [ι V] (vrec P R D)))
with schP : forall Θ, form Θ -> zform Θ -> Prop :=
| sc_rel {Θ} (c : isym (Spec [ι V; ι V] Pr)) (R : zform [ι V; ι V; σP; σP]) t u D1 D2 :
    (forall Γ' (A B : zform (ι V :: Γ')), tsymT c (A, (B, tt)) = vsubst (Frel R) (v2 A B)) ->
    schV Θ t D1 -> schV Θ u D2 -> schP Θ (rel2 c t u) (vsubst (Frel R) (v2 D1 D2))
| sc_top {Θ} : schP Θ Top Top
| sc_bot {Θ} : schP Θ Bot Bot
| sc_imp {Θ} A B A' B' : schP Θ A A' -> schP Θ B B' -> schP Θ (Imp A B) (Imp A' B')
| sc_and {Θ} A B A' B' : schP Θ A A' -> schP Θ B B' -> schP Θ (And A B) (And A' B')
| sc_or {Θ} A B A' B' : schP Θ A A' -> schP Θ B B' -> schP Θ (Or A B) (Or A' B')
| sc_all {Θ} A A' : schP (ι V :: Θ) A A' -> schP Θ (All A) (zAll A')
| sc_ex {Θ} A A' : schP (ι V :: Θ) A A' -> schP Θ (Ex A) (zEx A')
| sc_app1 {Θ} (X : var Θ σP) (y : var Θ (ι V)) : schP Θ (app1 (s := V) X (var0 y)) (zap1 X (var0 y))
| sc_app2 {Θ} (X : var Θ σR) (y1 y2 : var Θ (ι V)) :
    schP Θ (app2 X (var0 y1) (var0 y2)) (zapp2 X (var0 y1) (var0 y2)).

Scheme schV_ind' := Induction for schV Sort Prop
with schP_ind' := Induction for schP Sort Prop.
Combined Scheme sch_mut_ind from schV_ind', schP_ind'.

(** Deux instanciations reliées : mêmes variables pour les ensembles,
    traductions pour les formules. *)
Definition Wrel {Θ Γ} (W : vec isym Θ Γ) (Wz : vec zsym Θ Γ) : Prop :=
  (forall x : var Θ (ι V), exists z, aget x W = var0 z /\ aget x Wz = var0 z) /\
  (forall x : var Θ σP, tr (aget x W) = aget x Wz) /\
  (forall x : var Θ σR, tr (aget x W) = aget x Wz).

Lemma aget_vup_vs {Sg : spec isort -> Type} {Θ Γ σ} (y : var Θ σ) (W : vec Sg Θ Γ) :
  aget (vs y) (vup [ι V] W) = ren_tms (aget y W) (wk [ι V]).
Proof.
  change (aget (vr [ι V] y) (vup [ι V] W) = ren_tms (aget y W) (wk [ι V])).
  unfold vup, vren. rewrite aget_vcat_r, aget_vmap. reflexivity.
Qed.

Lemma Wrel_up {Θ Γ} (W : vec isym Θ Γ) (Wz : vec zsym Θ Γ) :
  Wrel W Wz -> Wrel (vup [ι V] W) (vup [ι V] Wz).
Proof.
  intros [H1 [H2 H3]]. split; [|split].
  - intros x.
    set (P := fun σ (y : var (ι V :: Θ) σ) =>
      match σ as σ0 return var (ι V :: Θ) σ0 -> Prop with
      | Spec [] V => fun y => exists z, aget y (vup [ι V] W) = var0 z /\ aget y (vup [ι V] Wz) = var0 z
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ (ι V) x); unfold P.
    + exists vz. split; reflexivity.
    + intros [[|? ?] [|]] y; try exact I.
      destruct (H1 y) as [z [E1 E2]]. exists (vs z).
      rewrite !aget_vup_vs, E1, E2. split; reflexivity.
  - intros x.
    set (P := fun σ (y : var (ι V :: Θ) σ) =>
      match σ as σ0 return var (ι V :: Θ) σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => tr (aget y (vup [ι V] W)) = aget y (vup [ι V] Wz)
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σP x); unfold P.
    + exact I.
    + intros [[|[[|] [|]] [|]] [|]] y; try exact I.
      rewrite !aget_vup_vs. unfold ren_tms. cbn [dom]. unfold tr. rewrite <- (H2 y).
      exact (tr_ren (aget y W) _).
  - intros x.
    set (P := fun σ (y : var (ι V :: Θ) σ) =>
      match σ as σ0 return var (ι V :: Θ) σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => tr (aget y (vup [ι V] W)) = aget y (vup [ι V] Wz)
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σR x); unfold P.
    + exact I.
    + intros [[|[[|] [|]] [|[[|] [|]] [|]]] [|]] y; try exact I.
      rewrite !aget_vup_vs. unfold ren_tms. cbn [dom]. unfold tr. rewrite <- (H3 y).
      exact (tr_ren (aget y W) _).
Qed.

Lemma vsubst_Sep {Θ Γ} (t : tm Θ V) (φ : form (ι V :: Θ)) (W : vec isym Θ Γ) :
  vsubst (Sep t φ) W = Sep (vsubst t W) (vsubst φ (vup [ι V] W)).
Proof.
  change (@tsym _ isym Γ _ i_sep (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) t W)
            (@acons _ isym Γ σP _ (vsubst_tms (σ := σP) φ W) anil)) = Sep (vsubst t W) (vsubst φ (vup [ι V] W))).
  rewrite vsubst_tms_nil, (vsubst_tms_vup (σ := σP)). reflexivity.
Qed.

Lemma vcomp_v2 {Θ Γ} (A B : zform (ι V :: Θ)) (w : vec zsym Θ Γ) :
  vcomp (v2 A B) w = v2 (vsubst A (vup [ι V] w)) (vsubst B (vup [ι V] w)).
Proof.
  unfold vcomp, v2. cbn [vmap]. rewrite !(vsubst_tms_vup (σ := σP)). reflexivity.
Qed.

Lemma DV_vsubst {Θ Γ} (x : var Θ (ι V)) (z : var Γ (ι V)) (Wz : vec zsym Θ Γ) :
  aget x Wz = var0 z -> vsubst (DV x) (vup [ι V] Wz) = DV z.
Proof.
  intros E. unfold DV, zEq, Eq. rewrite vsubst_tsym2, !vsubst_var0, aget_vup_vs, E. reflexivity.
Qed.

Lemma vsubst_Power {Θ Γ} (t : tm Θ V) (W : vec isym Θ Γ) : vsubst (Power t) W = Power (vsubst t W).
Proof.
  change (@tsym _ isym Γ _ i_power (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) t W) anil) = Power (vsubst t W)).
  rewrite vsubst_tms_nil. reflexivity.
Qed.

Lemma vsubst_Repl {Θ Γ} (t : tm Θ V) (ψ : form (ι V :: ι V :: Θ)) (W : vec isym Θ Γ) :
  vsubst (Repl t ψ) W = Repl (vsubst t W) (vsubst ψ (vup [ι V; ι V] W)).
Proof.
  change (@tsym _ isym Γ _ i_repl (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) t W)
            (@acons _ isym Γ σR _ (vsubst_tms (σ := σR) ψ W) anil)) = Repl (vsubst t W) (vsubst ψ (vup [ι V; ι V] W))).
  rewrite vsubst_tms_nil, (vsubst_tms_vup (σ := σR)). reflexivity.
Qed.

Lemma vsubst_Rec {Θ Γ} (φ : form (ι V :: Θ)) (ψ : form (ι V :: ι V :: Θ)) (t : tm Θ V) (W : vec isym Θ Γ) :
  vsubst (Rec φ ψ t) W = Rec (vsubst φ (vup [ι V] W)) (vsubst ψ (vup [ι V; ι V] W)) (vsubst t W).
Proof.
  change (@tsym _ isym Γ _ i_rec (@acons _ isym Γ σP _ (vsubst_tms (σ := σP) φ W)
            (@acons _ isym Γ σR _ (vsubst_tms (σ := σR) ψ W)
              (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) t W) anil)))
          = Rec (vsubst φ (vup [ι V] W)) (vsubst ψ (vup [ι V; ι V] W)) (vsubst t W)).
  rewrite vsubst_tms_nil, (vsubst_tms_vup (σ := σP)), (vsubst_tms_vup (σ := σR)). reflexivity.
Qed.

Lemma vcomp_vrec {Θ Γ} (P : zform (ι V :: Θ)) (R : zform (ι V :: ι V :: Θ)) (D : zform (ι V :: Θ)) (w : vec zsym Θ Γ) :
  vcomp (vrec P R D) w = vrec (vsubst P (vup [ι V] w)) (vsubst R (vup [ι V; ι V] w)) (vsubst D (vup [ι V] w)).
Proof. unfold vcomp, vrec. cbn [vmap]. rewrite !(vsubst_tms_vup (σ := σP)), (vsubst_tms_vup (σ := σR)). reflexivity. Qed.

Lemma vcomp_v1 {Θ Γ} (A : zform (ι V :: Θ)) (w : vec zsym Θ Γ) :
  vcomp (v1 A) w = v1 (vsubst A (vup [ι V] w)).
Proof. unfold vcomp, v1. cbn [vmap]. rewrite !(vsubst_tms_vup (σ := σP)). reflexivity. Qed.

Lemma vcomp_vPR {Θ Γ} (A : zform (ι V :: Θ)) (B : zform (ι V :: ι V :: Θ)) (w : vec zsym Θ Γ) :
  vcomp (vPR A B) w = vPR (vsubst A (vup [ι V] w)) (vsubst B (vup [ι V; ι V] w)).
Proof. unfold vcomp, vPR. cbn [vmap]. rewrite (vsubst_tms_vup (σ := σP)), (vsubst_tms_vup (σ := σR)). reflexivity. Qed.

Lemma vup2_eq {Sg : spec isort -> Type} {Θ Γ} (W : vec Sg Θ Γ) : vup [ι V; ι V] W = vup [ι V] (vup [ι V] W).
Proof.
  apply vec_ext; intros σ x; unfold vget.
  refine (var_inv (fun σ x => aget x (vup [ι V; ι V] W) = aget x (vup [ι V] (vup [ι V] W))) _ _ σ x); [reflexivity|].
  intros τ y.
  refine (var_inv (fun τ y => aget (vs y) (vup [ι V; ι V] W) = aget (vs y) (vup [ι V] (vup [ι V] W))) _ _ τ y);
    [reflexivity|].
  intros τ' w. rewrite !aget_vup_vs.
  change (aget (vr [ι V; ι V] w) (vup [ι V; ι V] W) = ren_tms (ren_tms (aget w W) (wk [ι V])) (wk [ι V])).
  unfold vup at 1, vren. rewrite aget_vcat_r, aget_vmap, ren_tms_ren. apply ren_tms_ext. reflexivity.
Qed.

Lemma Wrel_up2 {Θ Γ} (W : vec isym Θ Γ) (Wz : vec zsym Θ Γ) :
  Wrel W Wz -> Wrel (vup [ι V; ι V] W) (vup [ι V; ι V] Wz).
Proof. intros H. rewrite !vup2_eq. exact (Wrel_up _ _ (Wrel_up _ _ H)). Qed.

Theorem sch_tr :
  (forall Θ t D, schV Θ t D -> forall Γ (W : vec isym Θ Γ) Wz, Wrel W Wz ->
     ttm (vsubst t W) = vsubst D (vup [ι V] Wz)) /\
  (forall Θ φ P, schP Θ φ P -> forall Γ (W : vec isym Θ Γ) Wz, Wrel W Wz ->
     tr (vsubst φ W) = vsubst P Wz).
Proof.
  apply sch_mut_ind.
  - intros Θ x Γ W Wz HW. destruct HW as [H1 _]. destruct (H1 x) as [z [E1 E2]].
    rewrite vsubst_var0, E1, (DV_vsubst _ _ _ E2). reflexivity.
  - intros Θ t φ D P _ IHt _ IHφ Γ W Wz HW. rewrite vsubst_Sep.
    transitivity (vsubst Fsep (vup [ι V] (v2 (ttm (vsubst t W)) (tr (vsubst φ (vup [ι V] W)))))); [reflexivity|].
    rewrite (IHt _ _ _ HW), (IHφ _ _ _ (Wrel_up _ _ HW)).
    rewrite vsubst_vsubst. f_equal. rewrite <- vcomp_v2. symmetry. exact (vup_vcomp [ι V] (v2 D P) Wz).
  - intros Θ t D _ IHt Γ W Wz HW. rewrite vsubst_Power.
    transitivity (vsubst Fpower (vup [ι V] (v1 (ttm (vsubst t W))))); [reflexivity|].
    rewrite (IHt _ _ _ HW).
    rewrite vsubst_vsubst. f_equal. rewrite <- vcomp_v1. symmetry. exact (vup_vcomp [ι V] (v1 D) Wz).
  - intros Θ t ψ D P _ IHt _ IHψ Γ W Wz HW. rewrite vsubst_Repl.
    transitivity (vsubst Frepl (vup [ι V] (vPR (ttm (vsubst t W)) (tr (vsubst ψ (vup [ι V; ι V] W)))))); [reflexivity|].
    rewrite (IHt _ _ _ HW), (IHψ _ _ _ (Wrel_up2 _ _ HW)).
    rewrite vsubst_vsubst. f_equal. rewrite <- vcomp_vPR. symmetry. exact (vup_vcomp [ι V] (vPR D P) Wz).
  - intros Θ φ ψ t P R D _ IHφ _ IHψ _ IHt Γ W Wz HW. rewrite vsubst_Rec.
    transitivity (vsubst Frec (vup [ι V] (vrec (tr (vsubst φ (vup [ι V] W))) (tr (vsubst ψ (vup [ι V; ι V] W)))
                                               (ttm (vsubst t W))))); [reflexivity|].
    rewrite (IHφ _ _ _ (Wrel_up _ _ HW)), (IHψ _ _ _ (Wrel_up2 _ _ HW)), (IHt _ _ _ HW).
    rewrite vsubst_vsubst. f_equal. rewrite <- vcomp_vrec. symmetry. exact (vup_vcomp [ι V] (vrec P R D) Wz).
  - intros Θ c R t u D1 D2 HR _ IH1 _ IH2 Γ W Wz HW. unfold rel2 at 1.
    rewrite vsubst_tsym2.
    transitivity (tsymT c (ttm (vsubst t W), (ttm (vsubst u W), tt))); [reflexivity|].
    rewrite HR, (IH1 _ _ _ HW), (IH2 _ _ _ HW), vsubst_vsubst, vcomp_v2. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Θ A B A' B' _ IHA _ IHB Γ W Wz HW. unfold Imp. rewrite !vsubst_Bin.
    transitivity (Imp (tr (vsubst A W)) (tr (vsubst B W))); [reflexivity|].
    rewrite (IHA _ _ _ HW), (IHB _ _ _ HW). reflexivity.
  - intros Θ A B A' B' _ IHA _ IHB Γ W Wz HW. unfold And. rewrite !vsubst_Bin.
    transitivity (And (tr (vsubst A W)) (tr (vsubst B W))); [reflexivity|].
    rewrite (IHA _ _ _ HW), (IHB _ _ _ HW). reflexivity.
  - intros Θ A B A' B' _ IHA _ IHB Γ W Wz HW. unfold Or. rewrite !vsubst_Bin.
    transitivity (Or (tr (vsubst A W)) (tr (vsubst B W))); [reflexivity|].
    rewrite (IHA _ _ _ HW), (IHB _ _ _ HW). reflexivity.
  - intros Θ A A' _ IH Γ W Wz HW. unfold Quant.All. rewrite !vsubst_Qnt, !(vsubst_tms_vup (σ := σP)).
    cbn [dom app].
    transitivity (zAll (tr (vsubst A (vup [ι V] W)))); [reflexivity|].
    rewrite (IH _ _ _ (Wrel_up _ _ HW)). reflexivity.
  - intros Θ A A' _ IH Γ W Wz HW. unfold Quant.Ex. rewrite !vsubst_Qnt, !(vsubst_tms_vup (σ := σP)).
    cbn [dom app].
    transitivity (zEx (tr (vsubst A (vup [ι V] W)))); [reflexivity|].
    rewrite (IH _ _ _ (Wrel_up _ _ HW)). reflexivity.
  - intros Θ X y Γ W Wz [H1 [H2 _]]. destruct (H1 y) as [z [E1 E2]].
    rewrite !vsubst_app1, E1, E2. etransitivity; [exact (tr_inst_var (aget X W) z)|]. rewrite H2. reflexivity.
  - intros Θ X y1 y2 Γ W Wz [H1 [_ H3]]. destruct (H1 y1) as [z1 [E1 E1']]. destruct (H1 y2) as [z2 [E2 E2']].
    unfold app2, zapp2. rewrite !vsubst_app2_gen, !vsubst_var0, E1, E1', E2, E2'.
    etransitivity; [exact (tr_inst2_var (aget X W) z1 z2)|]. rewrite H3. reflexivity.
Qed.

Lemma Wrel_P {Γ} (φ : form (ι V :: Γ)) :
  Wrel (@acons _ isym Γ σP _ φ anil) (@acons _ zsym Γ σP _ (tr φ) anil).
Proof.
  split; [|split].
  - intros x. exfalso.
    refine (var_inv (fun σ _ => σ = ι V -> False) _ _ (ι V) x eq_refl); [discriminate|intros ? y; destruct (var_nil y)].
  - intros x.
    refine (var_inv (fun σ y => match σ as σ0 return var [σP] σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σP _ φ anil)) = aget y (@acons _ zsym Γ σP _ (tr φ) anil)
      | _ => fun _ => True end y) _ _ σP x); [reflexivity|intros ? y; destruct (var_nil y)].
  - intros x. exfalso.
    refine (var_inv (fun σ _ => σ = σR -> False) _ _ σR x eq_refl); [discriminate|intros ? y; destruct (var_nil y)].
Qed.

Lemma Wrel_R {Γ} (ψ : form (ι V :: ι V :: Γ)) :
  Wrel (@acons _ isym Γ σR _ ψ anil) (@acons _ zsym Γ σR _ (tr ψ) anil).
Proof.
  split; [|split].
  - intros x. exfalso.
    refine (var_inv (fun σ _ => σ = ι V -> False) _ _ (ι V) x eq_refl); [discriminate|intros ? y; destruct (var_nil y)].
  - intros x. exfalso.
    refine (var_inv (fun σ _ => σ = σP -> False) _ _ σP x eq_refl); [discriminate|intros ? y; destruct (var_nil y)].
  - intros x.
    refine (var_inv (fun σ y => match σ as σ0 return var [σR] σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σR _ ψ anil)) = aget y (@acons _ zsym Γ σR _ (tr ψ) anil)
      | _ => fun _ => True end y) _ _ σR x); [reflexivity|intros ? y; destruct (var_nil y)].
Qed.

(** L'atome x ε y traduit. *)
Definition zE {Θ} (x y : var Θ (ι V)) : zform Θ := vsubst (Frel (zMem x1 x0)) (v2 (DV x) (DV y)).

Lemma zE_mem {Θ} (x y : var Θ (ι V)) Ξ : IZF Θ Ξ (zIff (zE x y) (zMem (var0 x) (var0 y))).
Proof. exact (pcanon_tr (Eps (var0 x) (var0 y)) _ (pc_eps x y) Ξ). Qed.

Lemma sc_eps {Θ} (x y : var Θ (ι V)) : schP Θ (Eps (var0 x) (var0 y)) (zE x y).
Proof. apply sc_rel; [reflexivity|constructor|constructor]. Qed.

(** ** ∈-induction *)

Definition Tind : zform [σP] :=
  Imp (zAll (Imp (zAll (Imp (zE vz (vs vz)) (zap1 φ2 x0))) (zap1 (vs vz) x0))) (zAll (zap1 (vs vz) x0)).

Lemma sch_ind : schP [σP] (d_concl (izfm_rules A_ind)) Tind.
Proof.
  cbn [d_concl izfm_rules ax]. unfold Tind.
  repeat first [apply sc_imp | apply sc_all | apply sc_eps | apply sc_app1].
Qed.

Lemma tmpl_ind : IZF [σP] [] Tind.
Proof.
  unfold Tind. zap zimp_I.
  zap (zimp_E _ (zAll (Imp (zAll (Imp (zMem x0 x1) (zap1 φ2 x0))) (zap1 (vs vz) x0)))).
  { exact (zaxm Z_ind _ (@acons _ zsym [σP] σP _ (eta σP (Γ := [σP]) vz) anil)). }
  zap zall_I. zap zimp_I.
  (* [a; P] *)
  zap (zimp_E _ (zAll (Imp (zE vz (vs vz)) (zap1 φ2 x0)))).
  { zinst (Imp (zAll (Imp (zE vz (vs vz)) (zap1 φ3 x0))) (zap1 φ2 x0)) x0. zhyp. }
  zap zall_I. zap zimp_I.
  (* [b; a; P] *)
  zap (zimp_E _ (zMem x0 x1)).
  { zinst (Imp (zMem x0 x2) (zap1 φ3 x0)) x0. zhyp. }
  apply (ziff_E1 _ (zE vz (vs vz))); [apply zE_mem|zhyp].
Qed.

(** ** Séparation *)

Definition Tsep : zform [σP] :=
  zAll (zAll (zIff (vsubst (Frel (zMem x1 x0)) (v2 (DV vz) (vsubst Fsep (vup [ι V] (v2 (DV (vs vz)) (zap1 φ3 x0))))))
                   (And (zE vz (vs vz)) (zap1 φ2 x0)))).

Lemma sch_sep : schP [σP] (Cl 2 (d_concl (izfm_rules A_sep))) Tsep.
Proof.
  cbn [Cl Vn d_concl izfm_rules ax]. unfold Tsep, Iff.
  apply sc_all, sc_all, sc_and; apply sc_imp; try apply sc_and; try apply sc_eps; try apply sc_app1.
  all: apply sc_rel; [reflexivity|constructor|].
  all: apply sc_sep; [constructor|apply sc_app1].
Qed.

Lemma tmpl_sep : IZF [σP] [] Tsep.
Proof.
  unfold Tsep. zap zall_I. zap zall_I.
  (* [α; a; P] *)
  apply ziff_I.
  - zexh. zexh2. zexh.
    (* [a'; s; u; α; a; P] *)
    apply (deriv_cut ZC Pr RIZF (φ := And (zMem x2 x0) (zap1 φ5 x2))).
    { apply (ziff_E1 _ (zMem x2 x1)); [|zhyp].
      zinst (zIff (zMem x0 x2) (And (zMem x0 x1) (zap1 φ6 x0))) x2. zhyp. }
    apply zand_L. zap zand_I.
    + zap (zex_I _ _ x2). zap zand_I; [zhyp|].
      zap (zex_I _ _ x0). zap zand_I; zhyp.
    + zap (zeq_subst _ (zap1 φ6 x0) x2 x3); zhyp.
  - apply zand_L.
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x1)).
    { apply (ziff_E1 _ (zE vz (vs vz))); [apply zE_mem|zhyp]. }
    zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x3) (zap1 φ4 x0))))).
    { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zap1 φ5 x0))))) x1.
      exact (zaxm Z_sep _ (v1 (zap1 φ3 x0))). }
    (* [s; α; a; P] *)
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). zap zand_I.
    + zap (zex_I _ _ x2). zap zand_I; [zap zeq_refl|zhyp].
    + apply (ziff_E2 _ _ (And (zMem x1 x2) (zap1 φ3 x1))).
      { zinst (zIff (zMem x0 x1) (And (zMem x0 x3) (zap1 φ4 x0))) x1. zhyp. }
      zap zand_I; zhyp.
Qed.

(** ** Collection *)

Definition Tcoll : zform [σR] :=
  zAll (Imp (zAll (Imp (zE vz (vs vz)) (zEx (zapp2 φ3 x1 x0))))
            (zEx (zAll (Imp (zE vz φ2) (zEx (And (zE vz φ2) (zapp2 φ4 x1 x0))))))).

Lemma sch_coll : schP [σR] (Cl 1 (d_concl (izfm_rules A_coll))) Tcoll.
Proof.
  cbn [Cl Vn d_concl izfm_rules ax]. unfold Tcoll.
  repeat first [apply sc_imp | apply sc_and | apply sc_all | apply sc_ex | apply sc_eps | apply sc_app2].
Qed.

Lemma tmpl_coll : IZF [σR] [] Tcoll.
Proof.
  unfold Tcoll. zap zall_I. zap zimp_I.
  (* [a; ψ] *)
  zap (zex_E _ (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (zapp2 φ4 x1 x0)))))).
  { zap (zimp_E _ (zAll (Imp (zMem x0 x1) (zEx (zapp2 φ3 x1 x0))))).
    - zinst (Imp (zAll (Imp (zMem x0 x1) (zEx (zapp2 φ4 x1 x0))))
                 (zEx (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (zapp2 φ5 x1 x0))))))) x0.
      exact (zaxm Z_coll _ (@acons _ zsym [ι V; σR] σR _ (eta σR (Γ := [ι V; σR]) (vs vz)) anil)).
    - zap zall_I. zap zimp_I.
      zap (zimp_E _ (zE vz (vs vz))).
      { zinst (Imp (zE vz φ2) (zEx (zapp2 φ4 x1 x0))) x0. zhyp. }
      apply (ziff_E2 _ _ (zMem x0 x1)); [apply zE_mem|zhyp]. }
  (* [c; a; ψ] *)
  zap (zex_I _ _ x0). zap zall_I. zap zimp_I.
  (* [α; c; a; ψ] *)
  zap (zex_E _ (And (zMem x0 x2) (zapp2 φ4 x1 x0))).
  { zap (zimp_E _ (zMem x0 x2)).
    - zinst (Imp (zMem x0 x3) (zEx (And (zMem x0 x3) (zapp2 φ5 x1 x0)))) x0. zhyp.
    - apply (ziff_E1 _ (zE vz φ2)); [apply zE_mem|zhyp]. }
  apply zand_L.
  zap (zex_I _ _ x0). zap zand_I; [|zhyp].
  apply (ziff_E2 _ _ (zMem x0 x2)); [apply zE_mem|zhyp].
Qed.

(** ** Correction des schémas *)

Lemma tmpl_inst {σ Γ} (T : zform [σ]) (A : tms zsym Γ σ) (Ξ : list (zform Γ)) :
  IZF [σ] [] T -> IZF Γ Ξ (vsubst T (@acons _ zsym Γ σ _ A anil)).
Proof. intros H. exact (deriv_weaken _ _ _ (deriv_subst _ _ _ H Γ _) _ (incl_nil_l _)). Qed.

Lemma sep_sound {Γ} (v : vec isym [ι V; ι V; σP] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfm_rules A_sep)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_eta (atl v)), (args_eta (atl (atl v))), (args_nil (atl (atl (atl v)))).
  set (φ := ahd (atl (atl v))).
  apply (closure_inst 2 (d_concl (izfm_rules A_sep)) (@acons _ isym Γ (ι V) _ (ahd v) (@acons _ isym Γ (ι V) _ (ahd (atl v)) anil))
           (@acons _ isym Γ σP _ φ anil) Ξ HΓ).
  rewrite (proj2 sch_tr _ _ _ sch_sep Γ _ _ (Wrel_P φ)). apply tmpl_inst, tmpl_sep.
Qed.

Lemma coll_sound {Γ} (v : vec isym [ι V; σR] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfm_rules A_coll)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
  set (ψ := ahd (atl v)).
  apply (closure_inst 1 (d_concl (izfm_rules A_coll)) (@acons _ isym Γ (ι V) _ (ahd v) anil)
           (@acons _ isym Γ σR _ ψ anil) Ξ HΓ).
  rewrite (proj2 sch_tr _ _ _ sch_coll Γ _ _ (Wrel_R ψ)). apply tmpl_inst, tmpl_coll.
Qed.

Lemma ind_sound {Γ} (v : vec isym [σP] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfm_rules A_ind)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_nil (atl v)).
  refine (eq_rect_r (fun f => IZF Γ Ξ f) _ (proj2 sch_tr _ _ _ sch_ind Γ _ _ (Wrel_P (ahd v)))).
  apply tmpl_inst, tmpl_ind.
Qed.
