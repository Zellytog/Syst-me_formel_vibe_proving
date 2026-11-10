(** * Modèles des systèmes logiques

    Un modèle d'un système logique L (de calcul C, de sorte des propositions
    P) est la donnée :
    - d'un modèle M du calcul dans une CCC (un morphisme de CCC depuis
      [SynConv C], cf. [Calculus.v]) ;
    - d'une hyperdoctrine de Heyting H au-dessus de la CCC ;
    - d'un **prédicat générique** T ∈ H(⟦P⟧), qui se lit « être vrai ».

    Une formule φ, qui est un morphisme Γ → [ι P] de la catégorie
    syntaxique, s'interprète par la réindexation de T le long de M(φ) :

      ⟦φ⟧ := M(φ)*(T) ∈ H(M Γ).

    On ne demande pas que tout prédicat de H soit de cette forme : P
    représente les prédicats *définissables*. Un jugement Γ | Ξ ⊢ φ est
    valide si ⋀ ⟦Ξ⟧ ≤ ⟦φ⟧. Un modèle de L est une telle structure dans
    laquelle chaque règle de L est saine ([mrule_sound]) ; le théorème de
    correction ([soundness]) en découle par récurrence sur les dérivations.

    Les règles sont rendues saines par des propriétés de la structure : les
    connecteurs sont **compatibles** avec la structure de Heyting
    ([imp_compat] etc.), ce qu'il suffit de vérifier sur les formules
    génériques ([bin_compat_generic]) ; les règles de IPC sont alors saines
    ([ipc_sound]), et celles de CPC si les fibres sont booléennes. *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Models Require Import Calculus Hyperdoctrine.

Local Notation ι a := (Spec [] a).

Section Semantics.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι (l_prop Sym L)])).

Local Notation P := (l_prop Sym L).
Local Notation form := (form Sym P).
Local Notation "p ≤ q" := (ple (h := H) p q) (at level 70).

(** ** Interprétation des formules et des jugements *)

Definition interp {Γ} (φ : form Γ) : pred H (M Γ) := reidx (fmap[cm_fun M] (hat (S := l_calc Sym L) φ)) T.

Fixpoint mconj {Γ} (Ξ : list (form Γ)) : pred H (M Γ) :=
  match Ξ with
  | [] => ptop
  | φ :: Ξ' => pand (interp φ) (mconj Ξ')
  end.

Definition mvalid Γ (Ξ : list (form Γ)) (φ : form Γ) : Prop := mconj Ξ ≤ interp φ.

(** Une règle est saine si chacune de ses instances l'est. *)
Definition mrule_sound (r : drule Sym P) : Prop :=
  forall Γ Ξ (v : vec Sym (d_ctx r) Γ),
    (forall p, In p (d_prems r) -> mvalid _ (inst_hyps p v Ξ) (inst_goal p v)) ->
    mvalid Γ Ξ (vsubst (d_concl r) v).

(** ** Propriétés de base *)

Lemma mconj_in {Γ} (Ξ : list (form Γ)) φ : In φ Ξ -> mconj Ξ ≤ interp φ.
Proof.
  induction Ξ as [|ψ Ξ IH]; [intros []|]. intros [<-|Hin]; cbn [mconj].
  - apply and_l.
  - apply ple_and_r, IH, Hin.
Qed.

(** Deux formules convertibles ont la même interprétation. *)
Lemma interp_conv {Γ} (φ ψ : form Γ) : conv (l_calc Sym L) φ ψ -> interp φ ≤ interp ψ.
Proof. intros Hc. apply reidx_proper, (sem_conv _ _ M φ ψ Hc). Qed.

(** La substitution est interprétée par la réindexation. *)
Lemma interp_vsubst {Γ Δ} (φ : form Γ) (v : vec Sym Γ Δ) :
  interp (vsubst φ v) ≤ reidx (fmap[cm_fun M] v) (interp φ) /\
  reidx (fmap[cm_fun M] v) (interp φ) ≤ interp (vsubst φ v).
Proof.
  unfold interp. pose proof (sem_vsubst _ _ M φ v) as E. unfold sem in E.
  split.
  - eapply ple_trans; [apply reidx_proper, E|]. apply reidx_comp.
  - eapply ple_trans; [apply reidx_comp|]. apply reidx_proper. symmetry; exact E.
Qed.

(** ** Le théorème de correction *)

Theorem soundness :
  (forall i, mrule_sound (l_rules Sym L i)) ->
  forall Γ Ξ φ, provable L Γ Ξ φ -> mvalid Γ Ξ φ.
Proof.
  intros HR Γ Ξ φ Hd. unfold provable in Hd.
  induction Hd as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc Hd IH|Γ Ξ i v Hp IH].
  - apply mconj_in, Hin.
  - eapply ple_trans; [exact IH|apply interp_conv, Hc].
  - apply HR. exact IH.
Qed.

(** ** Les prémisses sans variable propre *)

Lemma prem_valid {Θ Γ} (hs : list (form Θ)) (g : form Θ) (v : vec Sym Θ Γ) Ξ :
  mvalid _ (inst_hyps (prem (P := P) hs g) v Ξ) (inst_goal (prem (P := P) hs g) v) ->
  mvalid Γ (vsubst_list hs v ++ Ξ) (vsubst g v).
Proof.
  unfold inst_hyps, inst_goal. cbn [p_ext p_hyps p_goal prem]. rewrite vup_nil, wk_list_nil. exact (fun h => h).
Qed.

End Semantics.

Arguments interp {Srt Sym L C CT CC CL} M H T {Γ} φ.
Arguments mconj {Srt Sym L C CT CC CL} M H T {Γ} Ξ.
Arguments mvalid {Srt Sym L C CT CC CL} M H T Γ Ξ φ.
Arguments mrule_sound {Srt Sym L C CT CC CL} M H T r.

(** ** Les modèles d'un système logique *)

Record lmodel {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym)
  (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC} := {
  lm_calc : cmodel (l_calc Sym L) C;
  lm_hd : hyperdoctrine C;
  lm_truth : pred lm_hd (lm_calc [ι (l_prop Sym L)]);
  lm_rules : forall i, mrule_sound lm_calc lm_hd lm_truth (l_rules Sym L i)
}.

Corollary lmodel_sound {Srt} {Sym : spec Srt -> Type} {L : logic Sym} {C : Category}
  {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC} (N : lmodel L C) Γ Ξ φ :
  provable L Γ Ξ φ -> mvalid (lm_calc L C N) (lm_hd L C N) (lm_truth L C N) Γ Ξ φ.
Proof. apply soundness, lm_rules. Qed.

(** ** Les connecteurs propositionnels *)

Section Propositional.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι (l_prop Sym L)])).

Local Notation P := (l_prop Sym L).
Local Notation form := (form Sym P).
Local Notation "p ≤ q" := (ple (h := H) p q) (at level 70).
Local Notation "⟦ φ ⟧" := (interp M H T φ).

(** Compatibilité d'un connecteur binaire avec une opération des fibres. *)
Definition bin_compat (c : Sym (Spec [ι P; ι P] P)) (op : forall X, pred H X -> pred H X -> pred H X) :=
  forall Γ (a b : form Γ), ⟦Bin c a b⟧ ≤ op _ ⟦a⟧ ⟦b⟧ /\ op _ ⟦a⟧ ⟦b⟧ ≤ ⟦Bin c a b⟧.

Definition cst_compat (c : Sym (ι P)) (k : forall X, pred H X) :=
  forall Γ, ⟦Cst (Γ := Γ) c⟧ ≤ k _ /\ k _ ≤ ⟦Cst (Γ := Γ) c⟧.

(** Il suffit de vérifier la compatibilité sur la formule générique
    c(A, B), dans le contexte [A; B], si l'opération commute à la
    réindexation et est monotone. *)
Lemma bin_compat_generic c (op : forall X, pred H X -> pred H X -> pred H X) :
  (forall X Y (f : X ~> Y) p q,
      reidx f (op _ p q) ≤ op _ (reidx f p) (reidx f q) /\ op _ (reidx f p) (reidx f q) ≤ reidx f (op _ p q)) ->
  (forall X (p p' q q' : pred H X), p ≤ p' -> p' ≤ p -> q ≤ q' -> q' ≤ q -> op _ p q ≤ op _ p' q') ->
  (⟦Bin (Γ := [ι P; ι P]) c (mv vz) (mv (vs vz))⟧ ≤ op _ ⟦mv (Θ := [ι P; ι P]) vz⟧ ⟦mv (Θ := [ι P; ι P]) (vs vz)⟧ /\
   op _ ⟦mv (Θ := [ι P; ι P]) vz⟧ ⟦mv (Θ := [ι P; ι P]) (vs vz)⟧ ≤ ⟦Bin (Γ := [ι P; ι P]) c (mv vz) (mv (vs vz))⟧) ->
  bin_compat c op.
Proof.
  intros Hre Hmono [G1 G2] Γ a b.
  pose (w := v2 P a b).
  assert (Ea : vsubst (mv (Θ := [ι P; ι P]) vz) w = a) by (unfold w, v2; rewrite vsubst_mvar; reflexivity).
  assert (Eb : vsubst (mv (Θ := [ι P; ι P]) (vs vz)) w = b) by (unfold w, v2; rewrite vsubst_mvar; reflexivity).
  assert (Ec : vsubst (Bin (Γ := [ι P; ι P]) c (mv vz) (mv (vs vz))) w = Bin c a b)
    by (rewrite vsubst_Bin, Ea, Eb; reflexivity).
  destruct (interp_vsubst L C M H T (Bin (Γ := [ι P; ι P]) c (mv vz) (mv (vs vz))) w) as [Ic1 Ic2].
  destruct (interp_vsubst L C M H T (mv (Θ := [ι P; ι P]) vz) w) as [Ia1 Ia2].
  destruct (interp_vsubst L C M H T (mv (Θ := [ι P; ι P]) (vs vz)) w) as [Ib1 Ib2].
  rewrite Ec in Ic1, Ic2. rewrite Ea in Ia1, Ia2. rewrite Eb in Ib1, Ib2.
  destruct (Hre _ _ (fmap[cm_fun M] w) ⟦mv (Θ := [ι P; ι P]) vz⟧ ⟦mv (Θ := [ι P; ι P]) (vs vz)⟧) as [R1 R2].
  split.
  - eapply ple_trans; [exact Ic1|]. eapply ple_trans; [apply reidx_mono, G1|].
    eapply ple_trans; [exact R1|]. apply Hmono; assumption.
  - eapply ple_trans; [|exact Ic2]. eapply ple_trans; [|apply reidx_mono, G2].
    eapply ple_trans; [|exact R2]. apply Hmono; assumption.
Qed.

Section Rules.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.


Local Ltac unf := unfold Imp, And, Or, Top, Bot in *; rewrite ?vsubst_Bin, ?vsubst_Cst in *.

(** Les règles de IPC sont saines dans tout modèle compatible. *)
Theorem ipc_sound
  (Cimp : bin_compat c_imp (fun X => pimp)) (Cand : bin_compat c_and (fun X => pand))
  (Cor : bin_compat c_or (fun X => por)) (Ctop : cst_compat c_top (fun X => ptop))
  (Cbot : cst_compat c_bot (fun X => pbot)) i :
  mrule_sound M H T (ipc_rules (Sym := Sym) (P := P) i).
Proof.
  intros Γ Ξ v Hp. unfold mvalid.
  destruct i as [[]|[[]|[[]|[[]|[]]]]]; cbn [ipc_rules rsum imp_rules and_rules or_rules top_rules bot_rules
    d_prems d_concl d_ctx] in *.
  - (* ImpI *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [|apply Cimp]. apply imp_adj. eapply ple_trans; [apply and_comm|exact K].
  - (* ImpE *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. pose proof (Hp _ (or_intror (or_introl eq_refl))) as K'.
    apply prem_valid in K'. cbn [vsubst_list map app mconj] in K'. unf.
    eapply ple_trans; [|apply imp_eval]. apply and_intro; [|exact K'].
    eapply ple_trans; [exact K|apply Cimp].
  - (* AndI *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. pose proof (Hp _ (or_intror (or_introl eq_refl))) as K'.
    apply prem_valid in K'. cbn [vsubst_list map app mconj] in K'. unf.
    eapply ple_trans; [|apply Cand]. apply and_intro; assumption.
  - (* AndE1 *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [exact K|]. eapply ple_trans; [apply Cand|apply and_l].
  - (* AndE2 *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [exact K|]. eapply ple_trans; [apply Cand|apply and_r].
  - (* OrI1 *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [|apply Cor]. eapply ple_trans; [exact K|apply or_l].
  - (* OrI2 *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [|apply Cor]. eapply ple_trans; [exact K|apply or_r].
  - (* OrE *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K.
    pose proof (Hp _ (or_intror (or_introl eq_refl))) as K2. apply prem_valid in K2.
    pose proof (Hp _ (or_intror (or_intror (or_introl eq_refl)))) as K3. apply prem_valid in K3.
    cbn [vsubst_list map app mconj] in K2, K3. unf.
    unfold mvalid in K, K2, K3.
    apply (ple_trans _ (pand (mconj M H T Ξ) (por (interp M H T (vsubst (mv (Θ := Θ3 P) vz) v))
                                                    (interp M H T (vsubst (mv (Θ := Θ3 P) (vs vz)) v))))).
    + apply and_intro; [apply ple_refl|]. eapply ple_trans; [exact K|apply Cor].
    + apply and_or_elim; (eapply ple_trans; [apply and_comm|]); assumption.
  - (* TopI *) unf. eapply ple_trans; [apply top_max|apply Ctop].
  - (* BotE *) pose proof (Hp _ (or_introl eq_refl)) as K; apply prem_valid in K; cbn [vsubst_list map app mconj] in K. unf.
    eapply ple_trans; [exact K|]. eapply ple_trans; [apply Cbot|apply bot_min].
Qed.

(** *** Le tiers exclu dans un modèle booléen *)

Definition boolean := forall X (p : pred H X), ptop ≤ por p (pimp p pbot).

Lemma imp_mono_r X (p q q' : pred H X) : q ≤ q' -> pimp p q ≤ pimp p q'.
Proof. intros Hq. apply imp_adj. eapply ple_trans; [apply imp_eval|exact Hq]. Qed.

Lemma or_mono X (p p' q q' : pred H X) : p ≤ p' -> q ≤ q' -> por p q ≤ por p' q'.
Proof.
  intros Hp Hq. apply or_elim; [eapply ple_trans; [exact Hp|apply or_l]|eapply ple_trans; [exact Hq|apply or_r]].
Qed.

Theorem em_sound
  (Cimp : bin_compat c_imp (fun X => pimp)) (Cor : bin_compat c_or (fun X => por))
  (Cbot : cst_compat c_bot (fun X => pbot)) (Hb : boolean) i :
  mrule_sound M H T (em_rules (Sym := Sym) (P := P) i).
Proof.
  intros Γ Ξ v Hp. unfold mvalid. destruct i. cbn [em_rules d_concl] in *.
  unfold Neg; unf. eapply ple_trans; [apply top_max|]. eapply ple_trans; [apply Hb|].
  eapply ple_trans; [|apply Cor]. apply or_mono; [apply ple_refl|].
  eapply ple_trans; [|apply Cimp]. apply imp_mono_r. apply Cbot.
Qed.

End Rules.

End Propositional.
