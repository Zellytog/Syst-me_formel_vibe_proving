(** * Conservativité, étape 3 : rec

    IZFε tout entier est conservative sur IZF. rec_{φ,ψ}(a) est traduit
    par la construction totale des essais ([Frec], [IZFRecV.v],
    [IZFRecW.v]). Dans l'axiome de rec, ψ est appliquée au terme
    rec(α) ; on passe par une variante où ψ(rec α, β) devient
    ∃w. w = rec(α) ∧ ψ(w, β), équivalente en logique pure ([rec_var]),
    et dont la traduction est l'instance d'un gabarit de IZF
    ([tmpl_rec]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFRecV IZFRecW IZFTrSem
  IZFSound IZFSchema IZFCons IZFRepl IZFRecX.

Local Notation ι a := (Spec [] a).
Local Notation φ10 := (vs φ9).
Local Notation φ11 := (vs φ10).
Local Notation φ12 := (vs φ11).
Local Notation x9 := (var0 φ9).

(** ** La variante de l'axiome, dans IZFε *)

(** ∃w. w = rec(α) ∧ ψ(w, β)   (contextes [β; α; a; φ; ψ] et [α; β; a; φ; ψ]). *)
Definition chiV : form [ι V; ι V; ι V; σP; σR] := Ex (And (EqV x0 (RecM φ4 φ5 x2)) (app2 φ5 x0 x1)).
Definition chi2V : form [ι V; ι V; ι V; σP; σR] := Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2)).

Definition HV : form [σP; σR] :=
  All (Imp (app1 (s := V) (vs vz) x0) (All (Imp (Eps x0 x1) (And (app1 (s := V) φ2 x0) (ExU chiV))))).
Definition CV : form [σP; σR] :=
  All (Imp (app1 (s := V) (vs vz) x0) (All (Iff (Eps x0 (RecM φ2 φ3 x1)) (Ex (And (Eps x0 x2) chi2V))))).
Definition ArecV : form [σP; σR] := Imp HV CV.

Ltac ehyp := apply d_ax; cbn [In wk_list map app]; auto 20.
Tactic Notation "eap" uconstr(t) := eapply t; try typeclasses eauto.
Tactic Notation "einst" uconstr(φ) uconstr(t) :=
  match goal with |- IZFm ?G ?X _ =>
    refine (_ : IZFm G X (vsubst (Γ := ι V :: G) φ (inst1 t))); eap (qall_E C RIZFm V hV X _ t) end.
Tactic Notation "esubst" uconstr(φ) uconstr(t) uconstr(u) :=
  match goal with |- IZFm ?G ?X _ =>
    refine (_ : IZFm G X (vsubst (Γ := ι V :: G) φ (inst1 u))); eap (qeq_subst C RIZFm V hV X φ t u) end.

Lemma eand_L {Γ} (Ξ : list (form Γ)) A B D : IZFm Γ (A :: B :: Ξ) D -> IZFm Γ (And A B :: Ξ) D.
Proof.
  intros H. apply (deriv_cut_gen _ _ _ H). intros χ [<-|[<-|Hχ]].
  - eap (and_E1 C Pr RIZFm _ _ B). ehyp.
  - eap (and_E2 C Pr RIZFm _ A). ehyp.
  - ehyp.
Qed.

Lemma eiff_E1 {Γ} (Ξ : list (form Γ)) A B : IZFm Γ Ξ (Iff A B) -> IZFm Γ Ξ A -> IZFm Γ Ξ B.
Proof. intros H1 H2. eap (imp_E C Pr RIZFm _ A B); [eap (and_E1 C Pr RIZFm _ _ (Imp B A)); exact H1|exact H2]. Qed.
Lemma eiff_E2 {Γ} (Ξ : list (form Γ)) A B : IZFm Γ Ξ (Iff A B) -> IZFm Γ Ξ B -> IZFm Γ Ξ A.
Proof. intros H1 H2. eap (imp_E C Pr RIZFm _ B A); [eap (and_E2 C Pr RIZFm _ (Imp A B)); exact H1|exact H2]. Qed.

Lemma euse {Γ0 Ξ0 φ} (H : IZFm Γ0 Ξ0 φ) {Γ} (w : vec isym Γ0 Γ) (Ξ : list (form Γ)) :
  (forall χ, In χ Ξ0 -> IZFm Γ Ξ (vsubst χ w)) -> IZFm Γ Ξ (vsubst φ w).
Proof.
  intros Hh. apply (deriv_cut_gen _ _ _ (deriv_subst _ _ _ H Γ w)).
  intros χ Hχ. unfold vsubst_list in Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply Hh, Hχ0.
Qed.
Tactic Notation "euses" constr(H) uconstr(w) :=
  refine (euse H w _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

(** ψ(t, β) ↔ ∃w. w = t ∧ ψ(w, β)   (contexte [β; t; ψ]). *)
Lemma eqL : IZFm [ι V; ι V; σR] [] (Iff (app2 (vs (vs vz)) x1 x0) (Ex (And (EqV x0 x2) (app2 φ3 x0 x1)))).
Proof.
  eap (and_I C Pr RIZFm); eap (imp_I C Pr RIZFm).
  - eap (qex_I C RIZFm V hV _ _ x1).
    refine (_ : IZFm _ _ (And (EqV x1 x1) (app2 (vs (vs vz)) x1 x0))).
    eap (and_I C Pr RIZFm); [eap (qeq_refl C RIZFm V hV)|ehyp].
  - eap (qex_E C RIZFm V hV _ (And (EqV x0 x2) (app2 φ3 x0 x1))); [ehyp|].
    (* [w; β; t; ψ] *)
    refine (_ : IZFm _ _ (app2 φ3 x2 x1)). apply eand_L.
    esubst (app2 φ4 x0 x2) x0 x2; [ehyp|]. refine (_ : IZFm _ _ (app2 φ3 x0 x1)). ehyp.
Qed.

Definition wPP {Γ} (A B : form (ι V :: Γ)) : vec isym [σP; σP] Γ :=
  @acons _ isym Γ σP _ A (@acons _ isym Γ σP _ B anil).

(** ∃! est monotone   (contexte [X; Y]). *)
Lemma exu_mono : IZFm [σP; σP] [All (Iff (app1 (s := V) (vs vz) x0) (app1 (s := V) φ2 x0))]
                   (Imp (ExU (app1 (s := V) (vs vz) x0)) (ExU (app1 (s := V) φ2 x0))).
Proof.
  eap (imp_I C Pr RIZFm).
  eap (qex_E C RIZFm V hV _ (And (app1 (s := V) (vs vz) x0) (All (Imp (app1 (s := V) φ2 x0) (EqV x0 x1))))); [ehyp|].
  (* [β; X; Y] *)
  apply eand_L.
  refine (_ : IZFm _ _ (Ex (And (app1 (s := V) φ3 x0) (All (Imp (app1 (s := V) φ4 x0) (EqV x0 x1)))))).
  eap (qex_I C RIZFm V hV _ _ x0).
  refine (_ : IZFm _ _ (And (app1 (s := V) φ2 x0) (All (Imp (app1 (s := V) φ3 x0) (EqV x0 x1))))).
  eap (and_I C Pr RIZFm).
  - apply (eiff_E1 _ (app1 (s := V) (vs vz) x0)); [|ehyp].
    einst (Iff (app1 (s := V) φ2 x0) (app1 (s := V) φ3 x0)) x0. ehyp.
  - eap (qall_I C RIZFm V hV). eap (imp_I C Pr RIZFm).
    (* [β''; β; X; Y] *)
    eap (imp_E C Pr RIZFm _ (app1 (s := V) φ2 x0)).
    + einst (Imp (app1 (s := V) φ3 x0) (EqV x0 x2)) x0. ehyp.
    + apply (eiff_E2 _ _ (app1 (s := V) φ3 x0)); [|ehyp].
      einst (Iff (app1 (s := V) φ3 x0) (app1 (s := V) φ4 x0)) x0. ehyp.
Qed.

Definition wEq {Γ} (β t : tm Γ V) (ψ : var Γ σR) : vec isym [ι V; ι V; σR] Γ :=
  @acons _ isym Γ (ι V) _ β (@acons _ isym Γ (ι V) _ t (@acons _ isym Γ σR _ (eta σR ψ) anil)).

(** La variante entraîne l'axiome de rec, en logique pure. *)
Lemma rec_var : IZFm [σP; σR] [] (Imp ArecV (d_concl (izfe_extra A_rec))).
Proof.
  cbn [d_concl izfe_extra ax]. unfold ArecV.
  eap (imp_I C Pr RIZFm). eap (imp_I C Pr RIZFm).
  apply (deriv_cut C Pr RIZFm (φ := CV)).
  { eap (imp_E C Pr RIZFm _ HV); [ehyp|].
    unfold HV. eap (qall_I C RIZFm V hV). eap (imp_I C Pr RIZFm). eap (qall_I C RIZFm V hV). eap (imp_I C Pr RIZFm).
    (* [α; a; φ; ψ] *)
    apply (deriv_cut C Pr RIZFm (φ := And (app1 (s := V) φ2 x0) (ExU (app2 φ4 (RecM φ3 φ4 x1) x0)))).
    { eap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|ehyp].
      einst (Imp (Eps x0 x2) (And (app1 (s := V) φ3 x0) (ExU (app2 φ5 (RecM φ4 φ5 x1) x0)))) x0.
      eap (imp_E C Pr RIZFm _ (app1 (s := V) φ2 x1)); [|ehyp].
      einst (Imp (app1 (s := V) φ3 x0) (All (Imp (Eps x0 x1) (And (app1 (s := V) φ4 x0) (ExU (app2 φ6 (RecM φ5 φ6 x1) x0)))))) x1.
      ehyp. }
    apply eand_L. eap (and_I C Pr RIZFm); [ehyp|].
    eap (imp_E C Pr RIZFm _ (ExU (app2 φ4 (RecM φ3 φ4 x1) x0))); [|ehyp].
    euses exu_mono (wPP (app2 φ4 (RecM φ3 φ4 x1) x0) chiV).
    refine (_ : IZFm _ _ (All (Iff (app2 φ4 (RecM φ3 φ4 x1) x0) chiV))).
    eap (qall_I C RIZFm V hV). euses eqL (wEq x0 (RecM φ3 φ4 x1) φ4). }
  unfold CV. eap (qall_I C RIZFm V hV). eap (imp_I C Pr RIZFm). eap (qall_I C RIZFm V hV).
  (* [β; a; φ; ψ] *)
  apply (deriv_cut C Pr RIZFm (φ := Iff (Eps x0 (RecM φ2 φ3 x1)) (Ex (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2))))))).
  { einst (Iff (Eps x0 (RecM φ3 φ4 x2)) (Ex (And (Eps x0 x3) (Ex (And (EqV x0 (RecM φ5 φ6 x1)) (app2 φ6 x0 x2)))))) x0.
    eap (imp_E C Pr RIZFm _ (app1 (s := V) φ2 x1)); [|ehyp].
    einst (Imp (app1 (s := V) φ3 x0) (All (Iff (Eps x0 (RecM φ4 φ5 x1)) (Ex (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ6 φ7 x1)) (app2 φ7 x0 x2)))))))) x1.
    ehyp. }
  eap (and_I C Pr RIZFm); eap (imp_I C Pr RIZFm).
  - apply (deriv_cut C Pr RIZFm (φ := Ex (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2)))))).
    { apply (eiff_E1 _ (Eps x0 (RecM φ2 φ3 x1))); ehyp. }
    eap (qex_E C RIZFm V hV _ (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2))))); [ehyp|].
    (* [α; β; a; φ; ψ] *)
    apply eand_L.
    refine (_ : IZFm _ _ (Ex (And (Eps x0 x3) (app2 φ5 (RecM φ4 φ5 x0) x2)))).
    eap (qex_I C RIZFm V hV _ _ x0).
    refine (_ : IZFm _ _ (And (Eps x0 x2) (app2 φ4 (RecM φ3 φ4 x0) x1))). eap (and_I C Pr RIZFm); [ehyp|].
    apply (eiff_E2 _ _ (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2)))); [|ehyp].
    euses eqL (wEq x1 (RecM φ3 φ4 x0) φ4).
  - apply (eiff_E2 _ (Eps x0 (RecM φ2 φ3 x1)) (Ex (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2)))))); [ehyp|].
    eap (qex_E C RIZFm V hV _ (And (Eps x0 x2) (app2 φ4 (RecM φ3 φ4 x0) x1))); [ehyp|].
    (* [α; β; a; φ; ψ] *)
    apply eand_L.
    refine (_ : IZFm _ _ (Ex (And (Eps x0 x3) (Ex (And (EqV x0 (RecM φ5 φ6 x1)) (app2 φ6 x0 x3)))))).
    eap (qex_I C RIZFm V hV _ _ x0).
    refine (_ : IZFm _ _ (And (Eps x0 x2) (Ex (And (EqV x0 (RecM φ4 φ5 x1)) (app2 φ5 x0 x2))))).
    eap (and_I C Pr RIZFm); [ehyp|].
    apply (eiff_E1 _ (app2 φ4 (RecM φ3 φ4 x0) x1)); [|ehyp].
    euses eqL (wEq x1 (RecM φ3 φ4 x0) φ4).
Qed.

(** ** Le gabarit dans IZF *)

Definition Trec : zform [σP; σR] :=
  Imp (zAll (Imp (zap1 (vs vz) x0)
                 (zAll (Imp (zE vz (vs vz))
                            (And (zap1 φ2 x0)
                                 (zEx (And (zEx (And (EqR vz φ4 φ5 φ2) (zapp2 φ5 x0 x1)))
                                           (zAll (Imp (zEx (And (EqR vz φ5 φ6 φ3) (zapp2 φ6 x0 x1))) (zEQ vz (vs vz)))))))))))
      (zAll (Imp (zap1 (vs vz) x0)
                 (zAll (zIff (EpsR vz φ2 φ3 (vs vz))
                             (zEx (And (zE vz φ2) (zEx (And (EqR vz φ4 φ5 (vs vz)) (zapp2 φ5 x0 x2))))))))).

Lemma sch_rec : schP [σP; σR] ArecV Trec.
Proof.
  unfold ArecV, HV, CV, chiV, chi2V, Trec, ExU, Iff.
  apply sc_imp.
  - apply sc_all, sc_imp; [apply sc_app1|].
    apply sc_all, sc_imp; [apply sc_eps|].
    apply sc_and; [apply sc_app1|].
    apply sc_ex, sc_and.
    + apply sc_ex, sc_and; [|apply sc_app2].
      apply sc_rel; [reflexivity|constructor|]. apply sc_rec; [apply sc_app1|apply sc_app2|constructor].
    + apply sc_all, sc_imp; [|apply sc_eqV].
      apply sc_ex, sc_and; [|apply sc_app2].
      apply sc_rel; [reflexivity|constructor|]. apply sc_rec; [apply sc_app1|apply sc_app2|constructor].
  - apply sc_all, sc_imp; [apply sc_app1|].
    apply sc_all, sc_and; apply sc_imp.
    all: first [ apply sc_rel; [reflexivity|constructor|]; apply sc_rec; [apply sc_app1|apply sc_app2|constructor]
               | apply sc_ex, sc_and; [apply sc_eps|]; apply sc_ex, sc_and; [|apply sc_app2];
                 apply sc_rel; [reflexivity|constructor|]; apply sc_rec; [apply sc_app1|apply sc_app2|constructor] ].
Qed.

(** Obtenir u avec ⟨α, u⟩ ∈ f, pour α ∈ a, f essai défini en a
    (contexte [α; v; f; β; a; φ; ψ], hypothèse de tête α ∈ a). *)
Ltac dc_u :=
  zap (zex_E _ (InF φ3 (vs vz) vz));
  [ zap (zimp_E _ (zMem x0 x4)); [|zhyp];
    zinst (Imp (zMem x0 x5) (zEx (InF φ4 (vs vz) vz))) x0;
    zap (zimp_E _ (InF φ2 φ4 (vs vz))); [|zhyp];
    zinst (Imp (InF φ3 φ5 vz) (zAll (Imp (zMem x0 x6) (zEx (InF φ5 (vs vz) vz))))) x1;
    zinst (zAll (Imp (InF φ4 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ6 (vs vz) vz)))))) x4;
    zuses att_dc (wVR x2 φ6); zhyp
  | ].

Lemma tmpl_rec : IZF [σP; σR] [] Trec.
Proof.
  unfold Trec. zap zimp_I.
  zap zall_I. zap zimp_I. zap zall_I.
  (* [β; a; φ; ψ] : un essai défini en a *)
  apply (deriv_cut ZC Pr RIZF (φ := Pe (vs vz) φ3)).
  { zinst (Pe vz φ4) x1. zuses att_ex (@acons _ zsym _ σR _ (eta σR φ3) anil). }
  zdes. zdes2.
  (* [v; f; β; a; φ; ψ] : Fn(a, R_f), par l'hypothèse *)
  apply (deriv_cut ZC Pr RIZF (φ := FnR φ3 (vs vz) φ5)).
  { refine (_ : IZF _ _ (zAll (Imp (zMem x0 x4) (zEx (And (RF φ3 φ7 (vs vz) vz) (zAll (Imp (RF φ4 φ8 φ2 vz) (zEq x0 x1)))))))).
    zap zall_I. zap zimp_I.
    (* [α; v; f; β; a; φ; ψ] *)
    dc_u.
    (* [u; α; v; f; β; a; φ; ψ] *)
    apply (deriv_cut ZC Pr RIZF (φ := And (zap1 φ6 x1) (zEx (And (zEx (And (EqR vz φ8 φ9 φ3) (zapp2 φ9 x0 x1)))
                                       (zAll (Imp (zEx (And (EqR vz φ9 φ10 φ4) (zapp2 φ10 x0 x1))) (zEQ vz (vs vz)))))))).
    { zap (zimp_E _ (zE (vs vz) φ5)); [|apply (ziff_E2 _ _ (zMem x1 x5)); [apply zE_mem|zhyp]].
      zinst (Imp (zE vz φ6) (And (zap1 φ7 x0) (zEx (And (zEx (And (EqR vz φ9 φ10 φ2) (zapp2 φ10 x0 x1)))
                (zAll (Imp (zEx (And (EqR vz φ10 φ11 φ3) (zapp2 φ11 x0 x1))) (zEQ vz (vs vz)))))))) x1.
      zap (zimp_E _ (zap1 φ6 x5)); [|zhyp].
      zinst (Imp (zap1 φ7 x0) (zAll (Imp (zE vz (vs vz)) (And (zap1 φ8 x0) (zEx (And (zEx (And (EqR vz φ10 φ11 φ2) (zapp2 φ11 x0 x1)))
                (zAll (Imp (zEx (And (EqR vz φ11 φ12 φ3) (zapp2 φ12 x0 x1))) (zEQ vz (vs vz)))))))))) x5.
      zhyp. }
    apply zand_L. zdes2.
    (* [β'; u; α; v; f; β; a; φ; ψ] *)
    refine (_ : IZF _ _ (zEx (And (RF φ5 φ9 φ3 vz) (zAll (Imp (RF φ6 φ10 φ4 vz) (zEq x0 x1)))))).
    zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (And (RF φ4 φ8 φ2 vz) (zAll (Imp (RF φ5 φ9 φ3 vz) (zEq x0 x1))))).
    zap zand_I.
    + apply (ziff_E1 _ (zEx (And (EqR vz φ8 φ9 φ3) (zapp2 φ9 x0 x1)))); [zuses chi_rf (wDR x0 x1 x4 x2 φ7 φ8); zhyp|zhyp].
    + zap zall_I. zap zimp_I.
      (* [β''; β'; u; α; v; f; β; a; φ; ψ] *)
      apply (ziff_E1 _ (zEQ vz (vs vz))); [apply zEQ_eq|].
      zap (zimp_E _ (zEx (And (EqR vz φ9 φ10 φ4) (zapp2 φ10 x0 x1)))).
      { zinst (Imp (zEx (And (EqR vz φ10 φ11 φ5) (zapp2 φ11 x0 x1))) (zEQ vz φ2)) x0. zhyp. }
      apply (ziff_E2 _ _ (RF φ5 φ9 φ3 vz)); [zuses chi_rf (wDR x0 x2 x5 x3 φ8 φ9); zhyp|zhyp]. }
  refine (_ : IZF _ _ (zIff (EpsR φ2 φ4 φ5 φ3) (zEx (And (zE vz φ4) (zEx (And (EqR vz φ6 φ7 (vs vz)) (zapp2 φ7 x0 x4))))))).
  (* β ε rec(a) ↔ β ∈ v ↔ Fn ∧ ∃α ∈ a. R_f(α, β) *)
  apply (ziff_trans _ _ (zMem x2 x0)).
  { zuses epsr_iff (wDR x2 x0 x1 x3 φ4 φ5); zhyp. }
  apply (ziff_trans _ _ (And (FnR φ3 (vs vz) φ5) (ExR φ3 (vs vz) φ5 φ2))).
  { zinst (zIff (zMem x0 x1) (And (FnR φ4 φ2 φ6) (ExR φ4 φ2 φ6 vz))) x2.
    zap (zimp_E _ (InF (vs vz) φ3 vz)); [|zhyp].
    zinst (Imp (InF φ2 φ4 vz) (StepEq vz φ4 φ2 φ6)) x0.
    zinst (zAll (Imp (InF φ3 (vs vz) vz) (StepEq vz (vs vz) φ3 φ7))) x3.
    zuses att_cr (wVR x1 φ5). zhyp. }
  apply ziff_I.
  - apply zand_L. zdes2.
    (* [α; v; f; β; a; φ; ψ] *)
    refine (_ : IZF _ _ (zEx (And (zE vz φ5) (zEx (And (EqR vz φ7 φ8 (vs vz)) (zapp2 φ8 x0 x5)))))).
    zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (And (zE vz φ4) (zEx (And (EqR vz φ6 φ7 (vs vz)) (zapp2 φ7 x0 x4))))).
    zap zand_I; [apply (ziff_E2 _ (zE vz φ4) (zMem x0 x4)); [apply zE_mem|zhyp]|].
    dc_u.
    (* [u; α; v; f; β; a; φ; ψ] *)
    refine (_ : IZF _ _ (zEx (And (EqR vz φ7 φ8 φ2) (zapp2 φ8 x0 x5)))).
    apply (ziff_E2 _ _ (RF φ3 φ7 (vs vz) φ4)); [zuses chi_rf (wDR x4 x0 x3 x1 φ6 φ7); zhyp|zhyp].
  - zdes.
    (* [α; v; f; β; a; φ; ψ] *)
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x4)); [apply (ziff_E1 _ (zE vz φ4)); [apply zE_mem|zhyp]|].
    refine (_ : IZF _ _ (And (FnR φ4 φ2 φ6) (ExR φ4 φ2 φ6 φ3))). zap zand_I; [zhyp|].
    refine (_ : IZF _ _ (zEx (And (zMem x0 x5) (RF φ3 φ7 vz φ4)))). zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (And (zMem x0 x4) (RF φ2 φ6 vz φ3))). zap zand_I; [zhyp|].
    dc_u.
    (* [u; α; v; f; β; a; φ; ψ] *)
    refine (_ : IZF _ _ (RF φ3 φ7 (vs vz) φ4)).
    apply (ziff_E1 _ (zEx (And (EqR vz φ7 φ8 φ2) (zapp2 φ8 x0 x5)))); [zuses chi_rf (wDR x4 x0 x3 x1 φ6 φ7); zhyp|zhyp].
Qed.

(** ** Correction de l'axiome de rec *)

Lemma Wrel_PR {Γ} (φ : form (ι V :: Γ)) (ψ : form (ι V :: ι V :: Γ)) :
  Wrel (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil)) (@acons _ zsym Γ σP _ (tr φ) (@acons _ zsym Γ σR _ (tr ψ) anil)).
Proof.
  split; [|split].
  - intros x. exfalso.
    refine (var_inv (fun σ _ => σ = ι V -> False) _ _ (ι V) x eq_refl); [discriminate|intros ? y].
    refine (var_inv (fun σ _ => σ = ι V -> False) _ _ _ y); [discriminate|intros ? y'; destruct (var_nil y')].
  - intros x.
    refine (var_inv (fun σ y => match σ as σ0 return var [σP; σR] σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil)))
                                         = aget y (@acons _ zsym Γ σP _ (tr φ) (@acons _ zsym Γ σR _ (tr ψ) anil))
      | _ => fun _ => True end y) _ _ σP x); [reflexivity|intros ? y].
    refine (var_inv (fun σ y => match σ as σ0 return var [σP; σR] σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil)))
                                         = aget y (@acons _ zsym Γ σP _ (tr φ) (@acons _ zsym Γ σR _ (tr ψ) anil))
      | _ => fun _ => True end (vs y)) _ _ _ y); [exact I|intros ? y'; destruct (var_nil y')].
  - intros x.
    refine (var_inv (fun σ y => match σ as σ0 return var [σP; σR] σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil)))
                                         = aget y (@acons _ zsym Γ σP _ (tr φ) (@acons _ zsym Γ σR _ (tr ψ) anil))
      | _ => fun _ => True end y) _ _ σR x); [exact I|intros ? y].
    refine (var_inv (fun σ y => match σ as σ0 return var [σP; σR] σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => tr (aget y (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil)))
                                         = aget y (@acons _ zsym Γ σP _ (tr φ) (@acons _ zsym Γ σR _ (tr ψ) anil))
      | _ => fun _ => True end (vs y)) _ _ _ y); [reflexivity|intros ? y'; destruct (var_nil y')].
Qed.

Lemma tmpl_inst2 {σ τ Γ} (T : zform [σ; τ]) (A : tms zsym Γ σ) (B : tms zsym Γ τ) (Ξ : list (zform Γ)) :
  IZF [σ; τ] [] T -> IZF Γ Ξ (vsubst T (@acons _ zsym Γ σ _ A (@acons _ zsym Γ τ _ B anil))).
Proof. intros H. exact (deriv_weaken _ _ _ (deriv_subst _ _ _ H Γ _) _ (incl_nil_l _)). Qed.

Lemma rec_sound {Γ} (v : vec isym [σP; σR] Γ) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (d_concl (izfe_extra A_rec)) v)).
Proof.
  intros HΓ. rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
  set (φ := ahd v). set (ψ := ahd (atl v)).
  pose proof (izfm_sound [] _ (deriv_subst _ _ _ rec_var Γ (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil))) HΓ) as K.
  cbn [map vsubst_list] in K. unfold Imp in K. rewrite vsubst_Bin in K.
  zap (zimp_E _ (tr (vsubst ArecV (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ anil))))).
  - exact (deriv_weaken _ _ _ K _ (incl_nil_l _)).
  - rewrite (proj2 sch_tr _ _ _ sch_rec Γ _ _ (Wrel_PR φ ψ)). apply tmpl_inst2, tmpl_rec.
Qed.

(** ** La théorie IZFε tout entière *)

Theorem izfe_sound {Γ} (Ξ : list (form Γ)) (φ : form Γ) :
  IZFe Γ Ξ φ -> vctx Γ -> IZF Γ (map tr Ξ) (tr φ).
Proof.
  induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc _ IH|Γ Ξ i v _ IH]; intros HΓ.
  - apply d_ax, in_map, Hin.
  - pose proof (proj1 conv_C_eq _ _ _ _ Hc) as E. subst ψ. exact (IH HΓ).
  - destruct i as [[[i|i]|a]|j].
    + exact (ipc_sound HΓ Ξ i v IH).
    + exact (quant_sound HΓ Ξ i v IH).
    + apply ax_sound, HΓ.
    + clear IH. destruct j; cbn [RIZFe rsum izfe_extra ax d_ctx d_concl] in v |- *.
      * apply rec_sound, HΓ.
      * apply repl_sound, HΓ.
      * apply sp_sound, HΓ.
      * rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))).
        exact (closed_ax HΓ Ξ 2 _ _ ax_power_sub0).
Qed.

(** Théorème 1.5.13 : IZFε est conservative sur IZF. Une formule de
    L_IZF prouvée dans IZFε, lue dans IZF, est prouvée dans IZF. *)
Theorem izfe_conservative {Γ} (Ξ : list (form Γ)) (Ξ' : list (zform Γ)) (φ : form Γ) (φ' : zform Γ) :
  vctx Γ -> Forall2 (pcanon Γ) Ξ Ξ' -> pcanon Γ φ φ' -> IZFe Γ Ξ φ -> IZF Γ Ξ' φ'.
Proof.
  intros HΓ HΞ Hφ H. apply (ziff_E1 _ (tr φ)); [apply pcanon_tr, Hφ|].
  apply (deriv_cut_gen _ _ _ (izfe_sound Ξ φ H HΓ)). intros χ Hχ.
  apply in_map_iff in Hχ. destruct Hχ as [ψ [<- Hψ]]. exact (hyps_tr _ _ HΞ ψ Hψ).
Qed.

Corollary izfe_conservative_closed (φ : form []) (φ' : zform []) :
  pcanon [] φ φ' -> IZFe [] [] φ -> IZF [] [] φ'.
Proof. intros Hφ H. exact (izfe_conservative [] [] φ φ' vctx_nil (Forall2_nil _) Hφ H). Qed.
