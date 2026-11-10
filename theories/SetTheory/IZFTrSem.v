(** * Sémantique de la traduction : valeurs des termes et substitution

    Dans un contexte d'ensembles, le graphe de tout terme est total et
    fonctionnel dans IZF ([tf_term]). Si chaque variable x est la valeur
    de w(x), substituer w ne change pas la traduction, à équivalence
    près ([subst_tr]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFRecV IZFRecW.

Local Notation ι a := (Spec [] a).

(** Le gabarit de rec est gros : on ne le déplie jamais ici. *)
Local Opaque Frec.

(** Contextes d'ensembles. *)
Definition vctx (Γ : ctx isort) : Prop := forall σ (x : var Γ σ), σ = ι V.

Lemma vctx_app D {Γ} : vctx D -> vctx Γ -> vctx (D ++ Γ).
Proof.
  intros HD HΓ σ x. destruct (vsplit_case D x) as [[z _]|[z _]]; [exact (HD σ z)|exact (HΓ σ z)].
Qed.

Lemma vctx_nil : vctx [].
Proof. intros σ x. destruct (var_nil x). Qed.

Lemma vctx_V {Γ} : vctx Γ -> vctx (ι V :: Γ).
Proof. intros H σ x. refine (var_inv (fun σ _ => σ = ι V) _ _ σ x); [reflexivity|intros ? y; apply H, y]. Qed.

Lemma eta_inst {Θ Γ} (x : var Θ σP) (v : vec zsym Θ Γ) :
  vsubst (eta σP x) (vup [ι V] v) = aget x v.
Proof. rewrite <- (vsubst_tms_vup (σ := σP)). exact (vsubst_eta (σ := σP) x v). Qed.

(** ** Le graphe d'une variable : y = x *)

Definition DV {Γ} (x : var Γ (ι V)) : zform (ι V :: Γ) := zEq x0 (var0 (vs x)).

Definition zvx {Γ} (x : var Γ (ι V)) : vec zsym [ι V] Γ := @acons _ zsym Γ (ι V) _ (var0 x) anil.

Lemma DV_inst {Γ} (x : var Γ (ι V)) : vsubst (zEq x0 x1 : zform [ι V; ι V]) (vup [ι V] (zvx x)) = DV x.
Proof.
  unfold zEq, Eq, DV. rewrite vsubst_tsym2, !vsubst_var0. unfold vup, vren. cbn. reflexivity.
Qed.

Lemma tot_DV0 : IZF [ι V] [] (Tot (zEq x0 x1 : zform [ι V; ι V])).
Proof. unfold Tot. zap (zex_I _ _ x0). zap zeq_refl. Qed.

Lemma fun_DV0 : IZF [ι V] [] (Fun (zEq x0 x1 : zform [ι V; ι V])).
Proof.
  unfold Fun, FunP. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I.
  zap (zeq_trans _ x1 x2 x0); [zhyp|]. zap zeq_sym. zhyp.
Qed.

Lemma tot_DV {Γ} (x : var Γ (ι V)) : IZF Γ [] (Tot (DV x)).
Proof.
  pose proof (deriv_subst _ _ _ tot_DV0 Γ (zvx x)) as K. rewrite Tot_vsubst, DV_inst in K. exact K.
Qed.

Lemma fun_DV {Γ} (x : var Γ (ι V)) : IZF Γ [] (Fun (DV x)).
Proof.
  pose proof (deriv_subst _ _ _ fun_DV0 Γ (zvx x)) as K. rewrite Fun_vsubst, DV_inst in K. exact K.
Qed.

(** ** Totalité et fonctionnalité *)

Definition TF (b : isort) (Δ : ctx isort) : Tr b Δ -> Prop :=
  match b as b0 return Tr b0 Δ -> Prop with
  | V => fun A => IZF Δ [] (Tot A) /\ IZF Δ [] (Fun A)
  | Pr => fun _ => True
  end.

Fixpoint TFA {Γ} (Θ : list (spec isort)) : TArgs Γ Θ -> Prop :=
  match Θ as Θ0 return TArgs Γ Θ0 -> Prop with
  | [] => fun _ => True
  | σ :: Θ' => fun X => (vctx (dom σ) -> TF (cod σ) (dom σ ++ Γ) (fst X)) /\ TFA Θ' (snd X)
  end.

Lemma tot_eta {Θ Γ} (x : var Θ σP) (v : vec zsym Θ Γ) Ξ :
  IZF Γ Ξ (Tot (aget x v)) -> IZF Γ Ξ (vsubst (Tot (eta σP x)) v).
Proof. intros H. rewrite Tot_vsubst. exact (eq_rect _ (fun D => IZF Γ Ξ (Tot D)) H _ (eq_sym (eta_inst x v))). Qed.

Lemma fun_eta {Θ Γ} (x : var Θ σP) (v : vec zsym Θ Γ) Ξ :
  IZF Γ Ξ (Fun (aget x v)) -> IZF Γ Ξ (vsubst (Fun (eta σP x)) v).
Proof. intros H. rewrite Fun_vsubst. exact (eq_rect _ (fun D => IZF Γ Ξ (Fun D)) H _ (eq_sym (eta_inst x v))). Qed.

Ltac tf_hyps := intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction;
  first [apply tot_eta | apply fun_eta]; cbn [aget ahd atl v1 v2 vPR vrec].

Lemma args3_inv {Sg : spec isort -> Type} {Θ σ τ υ} (a : args Sg Θ [σ; τ; υ]) :
  { t & { u & { w | a = acons t (acons u (acons w anil)) } } }.
Proof.
  exists (ahd a), (ahd (atl a)), (ahd (atl (atl a))). rewrite (args_eta a) at 1.
  rewrite (args_eta (atl a)), (args_eta (atl (atl a))), (args_nil (atl (atl (atl a)))). reflexivity.
Defined.

Lemma tf_mut :
  (forall Γ s (t : tm Γ s), vctx Γ -> TF s Γ (ttm t)) /\
  (forall Γ Θ (a : args isym Γ Θ), vctx Γ -> TFA Θ (targs a)).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH HΓ. pose proof (HΓ σ x) as E. subst σ. rewrite (args_nil a).
    split; [exact (tot_DV x)|exact (fun_DV x)].
  - intros Γ σ c a IH HΓ. specialize (IH HΓ).
    destruct c; try exact I.
    + split; [apply tot_empty|apply fun_empty].
    + split; [apply tot_omega|apply fun_omega].
    + destruct (args2_inv a) as [t1 [t2 ->]]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [I1 [I2 _]]. destruct (I1 vctx_nil) as [T1 F1], (I2 vctx_nil) as [T2 F2].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_pair _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_pair _ _ _). tf_hyps; assumption.
    + destruct (args1_inv a) as [t1 ->]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [I1 _]. destruct (I1 vctx_nil) as [T1 F1].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_union _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_union _ _ _). tf_hyps; assumption.
    + destruct (args1_inv a) as [t1 ->]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [I1 _]. destruct (I1 vctx_nil) as [T1 F1].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_power _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_power _ _ _). tf_hyps; assumption.
    + destruct (args2_inv a) as [t1 [t2 ->]]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [I1 _]. destruct (I1 vctx_nil) as [T1 F1].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_sep _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_sep _ _ _). tf_hyps; assumption.
    + destruct (args2_inv a) as [t1 [t2 ->]]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [I1 _]. destruct (I1 vctx_nil) as [T1 F1].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_repl _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_repl _ _ _). tf_hyps; assumption.
    + destruct (args3_inv a) as [t1 [t2 [t3 ->]]]. cbn [TFA targs fst snd dom cod] in IH.
      destruct IH as [_ [_ [I3 _]]]. destruct (I3 vctx_nil) as [T3 F3].
      split; cbn [ttm targs tsymT TF].
      * rewrite <- Tot_vsubst. refine (zuse tot_rec _ _ _). tf_hyps; assumption.
      * rewrite <- Fun_vsubst. refine (zuse fun_rec _ _ _). tf_hyps; assumption.
  - intros; exact I.
  - intros Γ σ Θ u IHu a IHa HΓ. split; [|exact (IHa HΓ)].
    intros HD. exact (IHu (vctx_app _ HD HΓ)).
Qed.

Lemma tf_term {Γ} (t : tm Γ V) : vctx Γ -> IZF Γ [] (Tot (ttm t)) /\ IZF Γ [] (Fun (ttm t)).
Proof. intros H. exact (proj1 tf_mut Γ V t H). Qed.

(** ** Lemmes de substitution sur les variables *)

Lemma DV_self {Γ} (x : var Γ (ι V)) : vsubst (DV x) (inst1 (var0 x)) = zEq (var0 x) (var0 x).
Proof. unfold DV, zEq, Eq. rewrite vsubst_tsym2, !vsubst_var0. cbn. rewrite aget_vid. reflexivity. Qed.

Lemma inst_wk_mid D {Γ} (T : zform (ι V :: Γ)) (y : var Γ (ι V)) :
  vsubst (ren_tm T (upr [ι V] (wk D))) (inst1 (var0 (vr D y))) = ren_tm (vsubst T (inst1 (var0 y))) (wk D).
Proof.
  rewrite vsubst_ren, ren_vsubst. f_equal. apply vec_ext; intros σ x; unfold vget.
  rewrite aget_vpre. unfold vren. rewrite aget_vmap.
  change (var ([ι V] ++ Γ) σ) in x. vcase x.
  - refine (var_inv (fun σ z => aget (upr [ι V] (wk D) σ (vl Γ z)) (inst1 (var0 (vr D y)))
                               = ren_tms (aget (vl Γ z) (inst1 (var0 y))) (wk D)) _ _ σ z).
    + reflexivity.
    + intros ? w; inversion w.
  - unfold upr. rewrite vsplit_vr. cbn. rewrite !aget_vid. symmetry. exact (eta_ren σ (wk D) z).
Qed.

(** Une variable x qui est la valeur de T : T(y) ↔ y = x. *)
Lemma var_iff0 : IZF [ι V; σP] [Fun (eta σP (Γ := [ι V; σP]) (vs vz)); zap1 (vs vz) x0]
                   (zAll (zIff (zap1 φ2 x0) (zEq x0 x1))).
Proof.
  zap zall_I. apply ziff_I.
  - zap (zimp_E _ (zap1 φ2 x1)); [|zhyp].
    zinst (Imp (zap1 φ3 x0) (zEq x1 x0)) x1.
    zap (zimp_E _ (zap1 φ2 x0)); [|zhyp].
    zinst (Imp (zap1 φ3 x0) (zAll (Imp (zap1 φ4 x0) (zEq x1 x0)))) x0. zhyp.
  - zap (zeq_subst _ (zap1 φ3 x0) x1 x0); [zap zeq_sym; zhyp|zhyp].
Qed.

Definition wvT {Γ} (x : var Γ (ι V)) (T : zform (ι V :: Γ)) : vec zsym [ι V; σP] Γ :=
  @acons _ zsym Γ (ι V) _ (var0 x) (@acons _ zsym Γ σP _ T anil).

Lemma var_iff {Γ} (Ξ : list (zform Γ)) (T : zform (ι V :: Γ)) (x : var Γ (ι V)) :
  IZF Γ Ξ (Fun T) -> IZF Γ Ξ (vsubst T (inst1 (var0 x))) ->
  IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff T (DV x)).
Proof.
  intros HF HT.
  assert (K : IZF Γ Ξ (vsubst (zAll (zIff (zap1 φ2 x0) (zEq x0 x1))) (wvT x T))).
  { refine (zuse var_iff0 _ _ _). intros χ Hin; repeat (destruct Hin as [<-|Hin]); try contradiction.
    - apply fun_eta. exact HF.
    - rewrite vsubst_app1_gen'. exact HT. }
  change (IZF Γ Ξ (zAll (vsubst (zIff (zap1 φ2 x0) (zEq x0 x1)) (vup [ι V] (wvT x T))))) in K.
  pose proof (zall_E0 _ _ K) as K2.
  assert (E : vsubst (zIff (zap1 φ2 x0) (zEq x0 x1)) (vup [ι V] (wvT x T)) = zIff T (DV x)).
  { unfold zIff, And, Imp. rewrite !vsubst_Bin. f_equal; f_equal.
    all: first [ rewrite vsubst_app1_gen', vsubst_var0; unfold vup, vren; cbn; apply zinst_up
               | unfold zEq, Eq, DV; rewrite vsubst_tsym2, !vsubst_var0; unfold vup, vren; cbn; reflexivity ]. }
  exact (eq_rect _ (fun f => IZF _ _ f) K2 _ E).
Qed.

(** ** Le lemme de substitution *)

(** Chaque variable x est la valeur de w(x). *)
Definition Hw {Γ} (Ξ : list (zform Γ)) (w : vec isym Γ Γ) : Prop :=
  forall x : var Γ (ι V), IZF Γ Ξ (vsubst (ttm (aget x w)) (inst1 (var0 x))).

Definition RelT (b : isort) {Γ} (Ξ : list (zform Γ)) : Tr b Γ -> Tr b Γ -> Prop :=
  match b as b0 return Tr b0 Γ -> Tr b0 Γ -> Prop with
  | V => fun A B => IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff A B)
  | Pr => fun A B => IZF Γ Ξ (zIff A B)
  end.

Fixpoint RA {Γ} (Ξ : list (zform Γ)) (Θ : list (spec isort)) : TArgs Γ Θ -> TArgs Γ Θ -> Prop :=
  match Θ as Θ0 return TArgs Γ Θ0 -> TArgs Γ Θ0 -> Prop with
  | [] => fun _ _ => True
  | σ :: Θ' => fun X Y => (vctx (dom σ) -> RelT (cod σ) (wk_list (dom σ) Ξ) (fst X) (fst Y)) /\ RA Ξ Θ' (snd X) (snd Y)
  end.

Lemma Hw_up D {Γ} (Ξ : list (zform Γ)) (w : vec isym Γ Γ) : Hw Ξ w -> Hw (wk_list D Ξ) (vup D w).
Proof.
  intros H x. vcase x.
  - unfold vup. rewrite aget_vcat_l, aget_etas.
    change (IZF (D ++ Γ) (wk_list D Ξ) (vsubst (DV (vl Γ z)) (inst1 (var0 (vl Γ z))))).
    rewrite DV_self. zap zeq_refl.
  - unfold vup, vren. rewrite aget_vcat_r, aget_vmap.
    change (IZF (D ++ Γ) (wk_list D Ξ) (vsubst (ttm (ren_tm (aget z w) (wk D))) (inst1 (var0 (vr D z))))).
    rewrite ttmV_ren.
    exact (eq_rect _ (fun f => IZF _ _ f) (deriv_wk _ _ _ D (H z)) _ (eq_sym (inst_wk_mid D (ttm (aget z w)) z))).
Qed.

Lemma vrel_nil {Γ} (Ξ : list (zform Γ)) : vrel Ξ (anil (Sym := zsym)) anil.
Proof. split; [|split]; intros x; destruct (var_nil x). Qed.

Lemma vrel_cons {Θ Γ} (Ξ : list (zform Γ)) (A A' : zform (ι V :: Γ)) (v v' : vec zsym Θ Γ) :
  IZF Γ Ξ (zAll (zIff A A')) -> vrel Ξ v v' ->
  vrel Ξ (@acons _ zsym Γ σP _ A v) (@acons _ zsym Γ σP _ A' v').
Proof.
  intros HA [H1 [H2 H3]]. split; [|split].
  - intros x.
    set (P := fun σ (y : var (σP :: Θ) σ) =>
      match σ as σ0 return var (σP :: Θ) σ0 -> Prop with
      | Spec [] V => fun y => aget y (@acons _ zsym Γ σP _ A v) = aget y (@acons _ zsym Γ σP _ A' v')
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ (ι V) x); unfold P; [exact I|].
    intros [[|? ?] [|]] y; try exact I. apply H1.
  - intros x.
    set (P := fun σ (y : var (σP :: Θ) σ) =>
      match σ as σ0 return var (σP :: Θ) σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => IZF Γ Ξ (zAll (zIff (aget y (@acons _ zsym Γ σP _ A v))
                                                         (aget y (@acons _ zsym Γ σP _ A' v'))))
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σP x); unfold P; [exact HA|].
    intros [[|[[|] [|]] [|]] [|]] y; try exact I. apply H2.
  - intros x.
    set (P := fun σ (y : var (σP :: Θ) σ) =>
      match σ as σ0 return var (σP :: Θ) σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => IZF Γ Ξ (zAll (zAll (zIff (aget y (@acons _ zsym Γ σP _ A v))
                                                         (aget y (@acons _ zsym Γ σP _ A' v')))))
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σR x); unfold P; [exact I|].
    intros [[|[[|] [|]] [|[[|] [|]] [|]]] [|]] y; try exact I. apply H3.
Qed.

Lemma vrel_consR {Θ Γ} (Ξ : list (zform Γ)) (A A' : zform (ι V :: ι V :: Γ)) (v v' : vec zsym Θ Γ) :
  IZF Γ Ξ (zAll (zAll (zIff A A'))) -> vrel Ξ v v' ->
  vrel Ξ (@acons _ zsym Γ σR _ A v) (@acons _ zsym Γ σR _ A' v').
Proof.
  intros HA [H1 [H2 H3]]. split; [|split].
  - intros x.
    set (P := fun σ (y : var (σR :: Θ) σ) =>
      match σ as σ0 return var (σR :: Θ) σ0 -> Prop with
      | Spec [] V => fun y => aget y (@acons _ zsym Γ σR _ A v) = aget y (@acons _ zsym Γ σR _ A' v')
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ (ι V) x); unfold P; [exact I|].
    intros [[|? ?] [|]] y; try exact I. apply H1.
  - intros x.
    set (P := fun σ (y : var (σR :: Θ) σ) =>
      match σ as σ0 return var (σR :: Θ) σ0 -> Prop with
      | Spec [Spec [] V] Pr => fun y => IZF Γ Ξ (zAll (zIff (aget y (@acons _ zsym Γ σR _ A v))
                                                         (aget y (@acons _ zsym Γ σR _ A' v'))))
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σP x); unfold P; [exact I|].
    intros [[|[[|] [|]] [|]] [|]] y; try exact I. apply H2.
  - intros x.
    set (P := fun σ (y : var (σR :: Θ) σ) =>
      match σ as σ0 return var (σR :: Θ) σ0 -> Prop with
      | Spec [Spec [] V; Spec [] V] Pr => fun y => IZF Γ Ξ (zAll (zAll (zIff (aget y (@acons _ zsym Γ σR _ A v))
                                                         (aget y (@acons _ zsym Γ σR _ A' v')))))
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ σR x); unfold P; [exact HA|].
    intros [[|[[|] [|]] [|[[|] [|]] [|]]] [|]] y; try exact I. apply H3.
Qed.

Lemma tctx_P1 : tctx [σP].
Proof. apply tctx_cons; [right; left; reflexivity|apply tctx_nil]. Qed.
Lemma tctx_P2 : tctx [σP; σP].
Proof. apply tctx_cons; [right; left; reflexivity|apply tctx_P1]. Qed.
Lemma tctx_PR : tctx [σP; σR].
Proof. apply tctx_cons; [right; left; reflexivity|]. apply tctx_cons; [right; right; reflexivity|apply tctx_nil]. Qed.

Lemma tctx_PRP : tctx [σP; σR; σP].
Proof. apply tctx_cons; [right; left; reflexivity|]. apply tctx_cons; [right; right; reflexivity|apply tctx_P1]. Qed.

Lemma wk_list_VV {Γ} (Ξ : list (zform Γ)) : wk_list [ι V] (wk_list [ι V] Ξ) = wk_list [ι V; ι V] Ξ.
Proof.
  unfold wk_list. rewrite map_map. apply map_ext; intros χ. rewrite ren_ren. apply ren_ext. reflexivity.
Qed.

Lemma iff_closed2 {Γ} (Ξ : list (zform Γ)) (A B : zform (ι V :: ι V :: Γ)) :
  IZF (ι V :: ι V :: Γ) (wk_list [ι V; ι V] Ξ) (zIff A B) -> IZF Γ Ξ (zAll (zAll (zIff A B))).
Proof. intros H. zap zall_I. zap zall_I. exact (eq_rect _ (fun L => IZF _ L _) H _ (eq_sym (wk_list_VV Ξ))). Qed.

Lemma tctx_V : tctx [ι V].
Proof. apply tctx_cons; [left; reflexivity|apply tctx_nil]. Qed.

Lemma iff_closed {Γ} (Ξ : list (zform Γ)) (A B : zform (ι V :: Γ)) :
  IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff A B) -> IZF Γ Ξ (zAll (zIff A B)).
Proof. intros H. zap zall_I. exact H. Qed.

(** La forme des gabarits de termes. *)
Lemma tmpl_cong {Θ Γ} (F : zform (ι V :: Θ)) (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ) :
  tctx Θ -> vrel Ξ v v' ->
  IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff (vsubst F (vup [ι V] v)) (vsubst F (vup [ι V] v'))).
Proof.
  intros HΘ Hv. apply (repl F); [exact (tctx_cons _ (or_introl eq_refl) HΘ)|].
  exact (vrel_up [ι V] Ξ v v' tctx_V Hv).
Qed.

Lemma tsymT_cong {Γ σ} (c : isym σ) (Ξ : list (zform Γ)) (X Y : TArgs Γ (dom σ)) :
  RA Ξ (dom σ) X Y -> RelT (cod σ) Ξ (tsymT c X) (tsymT c Y).
Proof.
  intros H. destruct c; cbn [TArgs dom cod app] in X, Y;
    repeat match goal with p : (_ * _)%type |- _ => destruct p end;
    cbn [RA fst snd dom cod app] in H; cbn [tsymT RelT].
  (* rec d'abord : ne jamais tenter d'unifier deux instances du gros gabarit *)
  all: try (lazymatch goal with |- context [Frec] => idtac end;
    destruct H as [H1 [H2 [H3 _]]]; specialize (H1 (vctx_V vctx_nil));
    specialize (H2 (vctx_V (vctx_V vctx_nil))); specialize (H3 vctx_nil);
    cbn [RelT] in H1, H2, H3; rewrite wk_list_nil in H3;
    apply tmpl_cong; [exact tctx_PRP|];
    apply vrel_cons; [apply iff_closed; exact H1|];
    apply vrel_consR; [apply iff_closed2; exact H2|];
    apply vrel_cons; [apply iff_closed; exact H3|]; apply vrel_nil).
  all: try solve [apply ziff_refl].
  all: try solve [destruct H as [H1 [H2 _]]; specialize (H1 vctx_nil); specialize (H2 vctx_nil);
    cbn [RelT] in H1, H2; rewrite wk_list_nil in H1, H2;
    first [exact (ziff_imp _ _ _ _ _ H1 H2) | exact (ziff_and _ _ _ _ _ H1 H2) | exact (ziff_or _ _ _ _ _ H1 H2)]].
  all: try solve [destruct H as [H1 _]; specialize (H1 (vctx_V vctx_nil));
    first [exact (ziff_all _ _ _ H1) | exact (ziff_ex _ _ _ H1)]].
  all: try solve [destruct H as [H1 [H2 _]]; specialize (H1 vctx_nil); specialize (H2 (vctx_V (vctx_V vctx_nil)));
    cbn [RelT] in H1, H2; rewrite wk_list_nil in H1;
    apply tmpl_cong; [exact tctx_PR|];
    apply vrel_cons; [apply iff_closed; exact H1|];
    apply vrel_consR; [apply iff_closed2; exact H2|]; apply vrel_nil].
  all: first
    [ destruct H as [H1 [H2 _]]; specialize (H1 vctx_nil); specialize (H2 vctx_nil);
      cbn [RelT] in H1, H2; rewrite wk_list_nil in H1, H2;
      first [ apply (repl (Frel _)); [exact tctx_P2|]
            | apply tmpl_cong; [exact tctx_P2|] ];
      apply vrel_cons; [apply iff_closed; exact H1|];
      apply vrel_cons; [apply iff_closed; exact H2|]; apply vrel_nil
    | destruct H as [H1 _]; specialize (H1 vctx_nil); cbn [RelT] in H1; rewrite wk_list_nil in H1;
      apply tmpl_cong; [exact tctx_P1|];
      apply vrel_cons; [apply iff_closed; exact H1|]; apply vrel_nil
    | destruct H as [H1 [H2 _]]; specialize (H1 vctx_nil); specialize (H2 (vctx_V vctx_nil));
      cbn [RelT] in H1, H2; rewrite wk_list_nil in H1;
      apply tmpl_cong; [exact tctx_P2|];
      apply vrel_cons; [apply iff_closed; exact H1|];
      apply vrel_cons; [apply iff_closed; exact H2|]; apply vrel_nil ].
Qed.

Theorem subst_mut :
  (forall Γ s (t : tm Γ s), vctx Γ -> forall (w : vec isym Γ Γ) (Ξ : list (zform Γ)), Hw Ξ w ->
     RelT s Ξ (ttm (vsubst t w)) (ttm t)) /\
  (forall Γ Θ (a : args isym Γ Θ), vctx Γ -> forall (w : vec isym Γ Γ) (Ξ : list (zform Γ)), Hw Ξ w ->
     RA Ξ Θ (targs (vsubst_args a w)) (targs a)).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH HΓ w Ξ Hw0. pose proof (HΓ σ x) as E. subst σ. rewrite (args_nil a).
    change (IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff (ttm (vsubst (var0 (Sym := isym) x) w)) (DV x))).
    rewrite vsubst_var0. apply var_iff; [|exact (Hw0 x)].
    exact (deriv_weaken _ _ _ (proj2 (tf_term (aget x w) HΓ)) _ (incl_nil_l _)).
  - intros Γ σ c a IH HΓ w Ξ Hw0. exact (tsymT_cong c Ξ _ _ (IH HΓ w Ξ Hw0)).
  - intros; exact I.
  - intros Γ σ Θ u IHu a IHa HΓ w Ξ Hw0. split; [|exact (IHa HΓ w Ξ Hw0)].
    intros HD. cbn [fst].
    pose proof (IHu (vctx_app _ HD HΓ) (vup (dom σ) w) (wk_list (dom σ) Ξ) (Hw_up _ Ξ w Hw0)) as K.
    rewrite <- vsubst_tms_vup in K. exact K.
Qed.

(** La forme utilisée : substitution d'un terme à la variable 0. *)
Corollary subst_tr {Γ} (s : isort) (t : tm Γ s) (w : vec isym Γ Γ) (Ξ : list (zform Γ)) :
  vctx Γ -> Hw Ξ w -> RelT s Ξ (ttm (vsubst t w)) (ttm t).
Proof. intros H1 H2. exact (proj1 subst_mut Γ s t H1 w Ξ H2). Qed.
