(** * Conservativité, étape 2 : remplacement, partie séparée, parties

    IZF⁻ε plus les axiomes de IZFε autres que rec (remplacement, partie
    séparée {α ε a | φ} ε P(a), éléments de P(x) inclus dans x) est
    conservative sur IZF. Le remplacement est traduit par la construction
    totale de 1.5.11 ([Frepl] : y ≜ {z | Fn(a, R) ∧ ∃α ∈ a. R(α, z)}). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFTrSem IZFSound IZFSchema IZFCons.

Local Notation ι a := (Spec [] a).
Local Notation φ10 := (vs φ9).

(** ** Outils *)

Definition zEQ {Θ} (x y : var Θ (ι V)) : zform Θ := vsubst (Frel (zEq x1 x0)) (v2 (DV x) (DV y)).

Lemma zEQ_eq {Θ} (x y : var Θ (ι V)) Ξ : IZF Θ Ξ (zIff (zEQ x y) (zEq (var0 x) (var0 y))).
Proof. exact (pcanon_tr (EqV (var0 x) (var0 y)) _ (pc_eqV x y) Ξ). Qed.

Lemma sc_eqV {Θ} (x y : var Θ (ι V)) : schP Θ (EqV (var0 x) (var0 y)) (zEQ x y).
Proof. apply sc_rel; [reflexivity|constructor|constructor]. Qed.

Lemma tot_at {σs : list (spec isort)} {Γ} (T : zform (ι V :: σs)) (w : vec zsym σs Γ) (Ξ : list (zform Γ)) Ξ0 :
  IZF σs Ξ0 (Tot T) -> (forall χ, In χ Ξ0 -> IZF Γ Ξ (vsubst χ w)) -> IZF Γ Ξ (Tot (vsubst T (vup [ι V] w))).
Proof. intros H Hh. rewrite <- Tot_vsubst. exact (zuse H w Ξ Hh). Qed.

Lemma tot_DVw {Γ} (a : var Γ (ι V)) (Ξ : list (zform Γ)) : IZF Γ Ξ (Tot (DV a)).
Proof. exact (deriv_weaken _ _ _ (tot_DV a) _ (incl_nil_l _)). Qed.

Lemma tot_sep_at {Γ} (a : var Γ (ι V)) (P : zform (ι V :: Γ)) (Ξ : list (zform Γ)) :
  IZF Γ Ξ (Tot (vsubst Fsep (vup [ι V] (v2 (DV a) P)))).
Proof. apply (tot_at _ _ _ _ tot_sep). intros χ [<-|[]]. apply tot_eta, tot_DVw. Qed.

Lemma tot_power_at {Γ} (a : var Γ (ι V)) (Ξ : list (zform Γ)) :
  IZF Γ Ξ (Tot (vsubst Fpower (vup [ι V] (v1 (DV a))))).
Proof. apply (tot_at _ _ _ _ tot_power). intros χ [<-|[]]. apply tot_eta, tot_DVw. Qed.

Lemma tot_repl_at {Γ} (a : var Γ (ι V)) (R : zform (ι V :: ι V :: Γ)) (Ξ : list (zform Γ)) :
  IZF Γ Ξ (Tot (vsubst Frepl (vup [ι V] (vPR (DV a) R)))).
Proof. apply (tot_at _ _ _ _ tot_repl). intros χ [<-|[]]. apply tot_eta, tot_DVw. Qed.

(** ** Les éléments de P(x) sont inclus dans x *)

Lemma ax_power_sub0 : IZF [] [] (tr (Cl 2 (d_concl (izfe_extra A_power_sub)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfe_extra wk_list map].
  (* [x; a] *)
  zap zimp_I. zexh. zexh2. zexh.
  (* [x'; p; u; x; a] *)
  apply (deriv_cut ZC Pr RIZF (φ := zAll (Imp (zMem x0 x3) (zMem x0 x1)))).
  { apply (ziff_E1 _ (zMem x2 x1)); [|zhyp].
    zinst (zIff (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x2)))) x2. zhyp. }
  zap (zex_I _ _ x4). zap zall_I.
  (* [α; x'; p; u; x; a] *)
  refine (_ : IZF _ _ (tr (Iff (Eps x0 x5) (And (Eps x0 x4) (Eps x0 x5))))).
  apply (ziff_E2 _ _ (zIff (zMem x0 x5) (And (zMem x0 x4) (zMem x0 x5)))); [apply pcanon_tr; pcan|].
  apply ziff_I.
  - zap zand_I; [|zhyp].
    zap (zeq_subst _ (zMem x1 x0) x1 x4); [zhyp|].
    zap (zimp_E _ (zMem x0 x3)); [zinst (Imp (zMem x0 x4) (zMem x0 x2)) x0; zhyp|].
    zap (zeq_subst _ (zMem x1 x0) x5 x3); [zap zeq_sym; zhyp|zhyp].
  - zap (zand_E2 _ (zMem x0 x4)). zhyp.
Qed.

(** ** La partie séparée est une partie *)

Definition Tsp : zform [σP] :=
  zAll (vsubst (Frel (zMem x1 x0)) (v2 (vsubst Fsep (vup [ι V] (v2 (DV vz) (zap1 φ2 x0))))
                                       (vsubst Fpower (vup [ι V] (v1 (DV vz)))))).

Lemma sch_sp : schP [σP] (Cl 1 (d_concl (izfe_extra A_sep_power))) Tsp.
Proof.
  cbn [Cl Vn d_concl izfe_extra ax]. unfold Tsp.
  apply sc_all. apply sc_rel; [reflexivity| |].
  - apply sc_sep; [constructor|apply sc_app1].
  - apply sc_power. constructor.
Qed.

Lemma tmpl_sp : IZF [σP] [] Tsp.
Proof.
  unfold Tsp. zap zall_I.
  (* [a; P] *)
  zap (zex_E _ (vsubst Fsep (vup [ι V] (v2 (DV vz) (zap1 φ2 x0))))); [apply tot_sep_at|].
  zap (zex_E _ (vsubst Fpower (vup [ι V] (v1 (DV (vs vz)))))); [apply tot_power_at|].
  (* [p; s; a; P] *)
  zap (zex_I _ _ x1). zap zand_I; [zhyp|].
  zap (zex_I _ _ x0). zap zand_I; [zhyp|].
  zexh.
  (* [x'; p; s; a; P] *)
  zap (zex_E _ (And (zEq x0 x4) (zAll (zIff (zMem x0 x4) (And (zMem x0 x1) (zap1 φ6 x0)))))); [zhyp|].
  apply zand_L.
  (* [a''; x'; p; s; a; P] *)
  apply (ziff_E2 _ _ (zAll (Imp (zMem x0 x4) (zMem x0 x2)))).
  { zinst (zIff (zMem x0 x3) (zAll (Imp (zMem x0 x1) (zMem x0 x3)))) x3. zhyp. }
  zap zall_I. zap zimp_I.
  (* [w; a''; x'; p; s; a; P] *)
  zap (zeq_subst _ (zMem x1 x0) x5 x2); [zap zeq_sym; zhyp|].
  zap (zeq_subst _ (zMem x1 x0) x1 x5); [zhyp|].
  zap (zand_E1 _ _ (zap1 φ6 x0)). apply (ziff_E1 _ (zMem x0 x4)); [|zhyp].
  zinst (zIff (zMem x0 x5) (And (zMem x0 x2) (zap1 φ7 x0))) x0. zhyp.
Qed.

(** ** Remplacement *)

Definition Trepl : zform [σR] :=
  zAll (Imp (zAll (Imp (zE vz (vs vz)) (zEx (And (zapp2 φ3 x1 x0) (zAll (Imp (zapp2 φ4 x2 x0) (zEQ vz (vs vz))))))))
            (zAll (zIff (vsubst (Frel (zMem x1 x0)) (v2 (DV vz) (vsubst Frepl (vup [ι V] (vPR (DV (vs vz)) (zapp2 φ4 x0 x1))))))
                        (zEx (And (zE vz φ2) (zapp2 φ3 x0 x1)))))).

Lemma sch_repl : schP [σR] (Cl 1 (d_concl (izfe_extra A_repl))) Trepl.
Proof.
  cbn [Cl Vn d_concl izfe_extra ax]. unfold Trepl, ExU, Iff.
  apply sc_all, sc_imp.
  - apply sc_all, sc_imp; [apply sc_eps|].
    apply sc_ex, sc_and; [apply sc_app2|]. apply sc_all, sc_imp; [apply sc_app2|apply sc_eqV].
  - apply sc_all. apply sc_and; apply sc_imp.
    all: try (apply sc_ex, sc_and; [apply sc_eps|apply sc_app2]).
    all: apply sc_rel; [reflexivity|constructor|]; apply sc_repl; [constructor|apply sc_app2].
Qed.

Lemma tmpl_repl : IZF [σR] [] Trepl.
Proof.
  unfold Trepl. zap zall_I. zap zimp_I. zap zall_I.
  (* [β; a; R] : Fn(a, R) *)
  apply (deriv_cut ZC Pr RIZF (φ := FnAt (vs vz) φ2)).
  { unfold FnAt. zap zall_I. zap zimp_I.
    (* [α; β; a; R] *)
    zap (zex_E _ (And (zapp2 φ4 x1 x0) (zAll (Imp (zapp2 φ5 x2 x0) (zEQ vz (vs vz)))))).
    { zap (zimp_E _ (zE vz φ2)).
      - zinst (Imp (zE vz φ3) (zEx (And (zapp2 φ5 x1 x0) (zAll (Imp (zapp2 φ6 x2 x0) (zEQ vz (vs vz))))))) x0. zhyp.
      - apply (ziff_E2 _ _ (zMem x0 x2)); [apply zE_mem|zhyp]. }
    apply zand_L.
    zap (zex_I _ _ x0). zap zand_I; [zhyp|].
    zap zall_I. zap zimp_I.
    apply (ziff_E1 _ (zEQ vz (vs vz))); [apply zEQ_eq|].
    zap (zimp_E _ (zapp2 φ5 x2 x0)); [|zhyp]. zinst (Imp (zapp2 φ6 x3 x0) (zEQ vz φ2)) x0. zhyp. }
  apply ziff_I.
  - zexh. zexh2. zexh.
    (* [a'; r; u; β; a; R] *)
    apply (deriv_cut ZC Pr RIZF (φ := ExIn vz φ5 φ2)).
    { zap (zand_E2 _ (FnAt vz φ5)). apply (ziff_E1 _ (zMem x2 x1)); [|zhyp].
      zinst (zIff (zMem x0 x2) (And (FnAt (vs vz) φ6) (ExIn (vs vz) φ6 vz))) x2. zhyp. }
    zap (zex_E _ (And (zMem x0 x1) (zapp2 φ6 x0 x3))); [zhyp|]. apply zand_L.
    (* [α; a'; r; u; β; a; R] *)
    zap (zex_I _ _ x0). zap zand_I.
    + apply (ziff_E2 _ (zE vz φ5) (zMem x0 x5)); [apply zE_mem|].
      zap (zeq_subst _ (zMem x1 x0) x1 x5); zhyp.
    + zap (zeq_subst _ (zapp2 φ7 x1 x0) x3 x4); zhyp.
  - zap (zex_E _ (And (zE vz φ2) (zapp2 φ3 x0 x1))); [zhyp|]. apply zand_L.
    (* [α; β; a; R] *)
    zap (zex_E _ (vsubst Frepl (vup [ι V] (vPR (DV φ2) (zapp2 φ5 x0 x1))))); [apply tot_repl_at|].
    (* [r; α; β; a; R] *)
    zap (zex_I _ _ x2). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). zap zand_I; [zhyp|].
    zexh.
    (* [a'; r; α; β; a; R] *)
    apply (ziff_E2 _ _ (And (FnAt vz φ5) (ExIn vz φ5 φ3))).
    { zinst (zIff (zMem x0 x2) (And (FnAt (vs vz) φ6) (ExIn (vs vz) φ6 vz))) x3. zhyp. }
    zap zand_I.
    + zap (zeq_subst _ (FnAt vz φ6) x4 x0); [zap zeq_sym; zhyp|zhyp].
    + zap (zex_I _ _ x2). zap zand_I; [|zhyp].
      zap (zeq_subst _ (zMem x3 x0) x4 x0); [zap zeq_sym; zhyp|].
      apply (ziff_E1 _ (zE φ2 φ4)); [apply zE_mem|zhyp].
Qed.

(** ** Correction des trois axiomes *)

Lemma repl_sound {Γ} (v : vec isym [ι V; σR] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfe_extra A_repl)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
  set (ψ := ahd (atl v)).
  apply (closure_inst 1 (d_concl (izfe_extra A_repl)) (@acons _ isym Γ (ι V) _ (ahd v) anil)
           (@acons _ isym Γ σR _ ψ anil) Ξ HΓ).
  rewrite (proj2 sch_tr _ _ _ sch_repl Γ _ _ (Wrel_R ψ)). apply tmpl_inst, tmpl_repl.
Qed.

Lemma sp_sound {Γ} (v : vec isym [ι V; σP] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfe_extra A_sep_power)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
  set (φ := ahd (atl v)).
  apply (closure_inst 1 (d_concl (izfe_extra A_sep_power)) (@acons _ isym Γ (ι V) _ (ahd v) anil)
           (@acons _ isym Γ σP _ φ anil) Ξ HΓ).
  rewrite (proj2 sch_tr _ _ _ sch_sp Γ _ _ (Wrel_P φ)). apply tmpl_inst, tmpl_sp.
Qed.

(** ** La théorie : IZF⁻ε plus les axiomes de IZFε autres que rec *)

Inductive izfr_idx := R_repl | R_sep_power | R_power_sub.

Definition izfr_emb (j : izfr_idx) : izfe_idx :=
  match j with R_repl => A_repl | R_sep_power => A_sep_power | R_power_sub => A_power_sub end.

Definition RIZFr := rsum RIZFm (fun j => izfe_extra (izfr_emb j)).

Notation IZFr Γ Ξ φ := (deriv C Pr RIZFr Γ Ξ φ).

Theorem izfr_sound {Γ} (Ξ : list (form Γ)) (φ : form Γ) :
  IZFr Γ Ξ φ -> vctx Γ -> IZF Γ (map tr Ξ) (tr φ).
Proof.
  induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc _ IH|Γ Ξ i v _ IH]; intros HΓ.
  - apply d_ax, in_map, Hin.
  - pose proof (proj1 conv_C_eq _ _ _ _ Hc) as E. subst ψ. exact (IH HΓ).
  - destruct i as [[[i|i]|a]|j].
    + exact (ipc_sound HΓ Ξ i v IH).
    + exact (quant_sound HΓ Ξ i v IH).
    + apply ax_sound, HΓ.
    + clear IH. destruct j; cbn [RIZFr rsum izfr_emb izfe_extra ax d_ctx d_concl] in v |- *.
      * apply repl_sound, HΓ.
      * apply sp_sound, HΓ.
      * rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
        exact (closed_ax HΓ Ξ 2 _ _ ax_power_sub0).
Qed.

(** IZF⁻ε, avec remplacement, partie séparée et parties incluses, est
    conservative sur IZF. *)
Theorem izfr_conservative {Γ} (Ξ : list (form Γ)) (Ξ' : list (zform Γ)) (φ : form Γ) (φ' : zform Γ) :
  vctx Γ -> Forall2 (pcanon Γ) Ξ Ξ' -> pcanon Γ φ φ' -> IZFr Γ Ξ φ -> IZF Γ Ξ' φ'.
Proof.
  intros HΓ HΞ Hφ H. apply (ziff_E1 _ (tr φ)); [apply pcanon_tr, Hφ|].
  apply (deriv_cut_gen _ _ _ (izfr_sound Ξ φ H HΓ)). intros χ Hχ.
  apply in_map_iff in Hχ. destruct Hχ as [ψ [<- Hψ]]. exact (hyps_tr _ _ HΞ ψ Hψ).
Qed.

Corollary izfr_conservative_closed (φ : form []) (φ' : zform []) :
  pcanon [] φ φ' -> IZFr [] [] φ -> IZF [] [] φ'.
Proof. intros Hφ H. exact (izfr_conservative [] [] φ φ' vctx_nil (Forall2_nil _) Hφ H). Qed.
