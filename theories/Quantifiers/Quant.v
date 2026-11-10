(** * Quantificateurs et égalité

    Pour une sorte s, un quantificateur est un symbole lieur
    [Spec [Spec [ι s] P] P] : il prend une formule avec une variable de
    sorte s. L'égalité est un symbole [Spec [ι s; ι s] P].

    Les règles sont des schémas. Pour ∀I, la prémisse étend le contexte de
    termes par une variable propre x : sa conclusion φ(x) est l'η-expansé de
    la métavariable φ sous ce nouveau lieur, et les hypothèses sont affaiblies
    (la condition « x n'apparaît pas dans Ξ » est donc structurelle). ∃E est
    construite de la même manière. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.

Local Notation ι a := (Spec [] a).

(** ** Calculs auxiliaires *)

Section Aux.

Context {Srt : Type} {Sym : spec Srt -> Type}.

Lemma vsubst_eta_up {Θ Γ} D b (x : var Θ (Spec D b)) (v : vec Sym Θ Γ) :
  @vsubst _ Sym (D ++ Θ) b (eta (Spec D b) x) (D ++ Γ) (vup D v) = aget x v.
Proof.
  transitivity (vsubst_tms (σ := Spec D b) (eta (Spec D b) x) v);
    [symmetry; exact (vsubst_tms_vup (σ := Spec D b) (eta (Spec D b) x) v)|exact (vsubst_eta x v)].
Qed.

Lemma ren_tms_nil {Γ Δ} b (u : Terms.tm Sym Γ b) (ξ : ren Γ Δ) :
  ren_tms (σ := ι b) u ξ = ren_tm u ξ.
Proof. unfold ren_tms; apply ren_ext; intros; reflexivity. Qed.

End Aux.

(** Substituer [u] dans un terme affaibli le laisse inchangé ([inst1 u]
    remplace la variable 0 par [u], cf. [SF.Functional.Arrow]). *)
Lemma vsubst_wk_inst1 {Srt} {Sym : spec Srt -> Type} {Γ a s}
  (t : Terms.tm Sym Γ s) (u : Terms.tm Sym Γ a) :
  vsubst (ren_tm t (wk [ι a])) (inst1 u) = t.
Proof.
  rewrite vsubst_ren. rewrite <- (vsubst_vid t) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre; reflexivity.
Qed.

(** ** Symboles et formules *)

Section Symbols.

Context {Srt : Type} (Sym : spec Srt -> Type) (P : Srt) (s : Srt).

Local Notation form := (form Sym P).
Local Notation tm := (Terms.tm Sym).
Local Notation σφ := (Spec [ι s] P).

Class HasForall := { c_all : Sym (Spec [σφ] P) }.
Class HasExists := { c_ex : Sym (Spec [σφ] P) }.
Class HasEq := { c_eq : Sym (Spec [ι s; ι s] P) }.

Definition Qnt (c : Sym (Spec [σφ] P)) {Γ} (φ : form (ι s :: Γ)) : form Γ :=
  @tsym _ Sym Γ (Spec [σφ] P) c (@acons _ Sym Γ σφ [] φ anil).

Definition All `{HasForall} {Γ} (φ : form (ι s :: Γ)) : form Γ := Qnt c_all φ.
Definition Ex `{HasExists} {Γ} (φ : form (ι s :: Γ)) : form Γ := Qnt c_ex φ.
Definition Eq `{HasEq} {Γ} (t u : tm Γ s) : form Γ :=
  @tsym _ Sym Γ (Spec [ι s; ι s] P) c_eq
    (@acons _ Sym Γ (ι s) _ t (@acons _ Sym Γ (ι s) _ u anil)).

(** Métavariables : φ de spécification [s] -> P, termes t, u de sorte s,
    formule C. *)
Local Notation mφ := (eta σφ vz).
Definition app1 {Θ} (x : var Θ σφ) (t : tm Θ s) : form Θ :=
  @tvar _ Sym Θ σφ x (@acons _ Sym Θ (ι s) _ t anil).

Local Notation Θφ := [σφ].
Local Notation Θφt := [σφ; ι s].
Local Notation ΘφC := [σφ; ι P].
Local Notation Θφtu := [σφ; ι s; ι s].
Local Notation Θt := [ι s].

(** ** Familles de règles *)

Definition mkr (Θ : ctx Srt) (ps : list (premise Sym P Θ)) (c : form Θ) : drule Sym P :=
  {| d_ctx := Θ; d_prems := ps; d_concl := c |}.

Inductive all_idx := AllI | AllE.
Inductive ex_idx := ExI | ExE.
Inductive eq_idx := EqR | EqS.

Definition all_rules `{HasForall} (i : all_idx) : drule Sym P :=
  match i with
  | AllI => mkr Θφ [premx (P := P) (Θ := Θφ) [ι s] [] (eta σφ (Γ := Θφ) vz)]
               (All (eta σφ (Γ := Θφ) vz))
  | AllE => mkr Θφt [prem (P := P) (Θ := Θφt) [] (All (eta σφ (Γ := Θφt) vz))]
               (app1 (Θ := Θφt) vz (var0 (vs vz)))
  end.

Definition ex_rules `{HasExists} (i : ex_idx) : drule Sym P :=
  match i with
  | ExI => mkr Θφt [prem (P := P) (Θ := Θφt) [] (app1 vz (var0 (vs vz)))]
               (Ex (eta σφ (Γ := Θφt) vz))
  | ExE => mkr ΘφC [prem (P := P) (Θ := ΘφC) [] (Ex (eta σφ (Γ := ΘφC) vz));
                          premx (P := P) [ι s] [eta σφ (Γ := ΘφC) vz] (var0 (vs (vs vz)))]
               (var0 (Θ := ΘφC) (vs vz))
  end.

Definition eq_rules `{HasEq} (i : eq_idx) : drule Sym P :=
  match i with
  | EqR => mkr Θt []
               (Eq (Γ := Θt) (var0 vz) (var0 vz))
  | EqS => mkr Θφtu [prem (P := P) (Θ := Θφtu) [] (Eq (var0 (vs vz)) (var0 (vs (vs vz))));
                          prem (P := P) [] (app1 vz (var0 (vs vz)))]
               (app1 (Θ := Θφtu) vz (var0 (vs (vs vz))))
  end.

End Symbols.

Arguments c_all {Srt Sym P s HasForall}.
Arguments c_ex {Srt Sym P s HasExists}.
Arguments c_eq {Srt Sym P s HasEq}.
Arguments Qnt {Srt Sym P s} c {Γ} φ.
Arguments All {Srt Sym P} s {_ Γ} φ.
Arguments Ex {Srt Sym P} s {_ Γ} φ.
Arguments Eq {Srt Sym P} s {_ Γ} t u.
Arguments app1 {Srt Sym P s Θ} x t.
Arguments all_rules {Srt Sym P} s {_} i.
Arguments ex_rules {Srt Sym P} s {_} i.
Arguments eq_rules {Srt Sym P} s {_} i.

(** ** Substitution dans les formules quantifiées *)

Section SubstQ.

Context {Srt : Type} {Sym : spec Srt -> Type} {P s : Srt}.

Local Notation σφ := (Spec [ι s] P).

Lemma vsubst_Qnt (c : Sym (Spec [σφ] P)) {Θ Γ} (φ : form Sym P (ι s :: Θ)) (v : vec Sym Θ Γ) :
  vsubst (Qnt c φ) v = Qnt c (vsubst_tms (σ := σφ) φ v).
Proof. reflexivity. Qed.

Lemma vsubst_Qnt_eta (c : Sym (Spec [σφ] P)) {Θ Γ} (x : var Θ σφ) (v : vec Sym Θ Γ) :
  vsubst (Qnt c (eta σφ x)) v = Qnt c (aget x v).
Proof. rewrite vsubst_Qnt, vsubst_eta; reflexivity. Qed.

Lemma vsubst_Eq `{HasEq Srt Sym P s} {Θ Γ} (t u : Terms.tm Sym Θ s) (v : vec Sym Θ Γ) :
  vsubst (Eq s t u) v = Eq s (vsubst t v) (vsubst u v).
Proof.
  unfold Eq.
  transitivity (@tsym _ Sym Γ _ c_eq
                  (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s) t v)
                     (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s) u v) anil)));
    [reflexivity|].
  rewrite !vsubst_tms_nil; reflexivity.
Qed.

(** φ(t), instancié par [φ ; t ; ...], donne φ[t/x]. *)
Lemma vsubst_app1 {Θ Γ} (x : var Θ σφ) (y : var Θ (ι s)) (v : vec Sym Θ Γ) :
  vsubst (app1 x (var0 y)) v = vsubst (aget x v) (inst1 (aget y v)).
Proof.
  change (happ σφ (aget x v)
            (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s) (var0 y) v) anil)
          = vsubst (aget x v) (inst1 (aget y v))).
  rewrite vsubst_tms_nil, vsubst_var0, happ_vsubst; reflexivity.
Qed.

End SubstQ.

(** ** Règles dérivées *)

Section Derived.

Context {Srt : Type} {Sym : spec Srt -> Type} (C : system Sym) (P : Srt).
Context {I : Type} (R : I -> drule Sym P) (s : Srt).

Local Notation form := (form Sym P).
Local Notation tm := (Terms.tm Sym).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).
Local Notation σφ := (Spec [ι s] P).

Lemma deriv_eq {Γ} (Ξ : list (form Γ)) φ ψ : φ = ψ -> Ξ ⊢ φ -> Ξ ⊢ ψ.
Proof. intros <-; exact (fun H => H). Qed.

Lemma deriv_eq2 {Γ} (Ξ Ξ' : list (form Γ)) φ ψ : Ξ = Ξ' -> φ = ψ -> Ξ ⊢ φ -> Ξ' ⊢ ψ.
Proof. intros <- <-; exact (fun H => H). Qed.

Section All.
Context {HA : HasForall Sym P s} `{Includes _ Sym P I all_idx R (all_rules s)}.

(** ∀I : la variable propre est la variable 0 ; les hypothèses sont affaiblies. *)
Lemma all_I {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) :
  deriv C P R (ι s :: Γ) (wk_list [ι s] Ξ) φ -> Ξ ⊢ All s φ.
Proof.
  intros Hφ.
  apply (rule_inc C P R (all_rules s) AllI Ξ (@acons _ Sym Γ σφ _ φ anil)); cbn [all_rules mkr d_ctx d_concl d_prems].
  - unfold All; exact (vsubst_Qnt_eta c_all vz _).
  - intros p [<-|[]]. unfold inst_hyps, inst_goal, vsubst_list; cbn [p_ext p_hyps p_goal premx d_ctx map app].
    eapply deriv_eq; [symmetry; exact (vsubst_eta_up [ι s] P vz (@acons _ Sym Γ σφ _ φ anil))|exact Hφ].
Qed.

(** ∀E : de ∀x. φ, on tire φ[t/x]. *)
Lemma all_E {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (t : tm Γ s) :
  Ξ ⊢ All s φ -> Ξ ⊢ vsubst φ (inst1 t).
Proof.
  intros Hφ. apply (rule_inc C P R (all_rules s) AllE Ξ
                      (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι s) _ t anil)));
    cbn [all_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_app1; reflexivity.
  - intros p [<-|[]]. unfold inst_hyps, inst_goal, vsubst_list; cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    rewrite vup_nil, wk_list_nil. unfold All; rewrite (vsubst_Qnt_eta (P := P) (s := s) c_all vz). exact Hφ.
Qed.
End All.

Section Ex.
Context {HE : HasExists Sym P s} `{Includes _ Sym P I ex_idx R (ex_rules s)}.

Lemma ex_I {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (t : tm Γ s) :
  Ξ ⊢ vsubst φ (inst1 t) -> Ξ ⊢ Ex s φ.
Proof.
  intros Hφ. apply (rule_inc C P R (ex_rules s) ExI Ξ
                      (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι s) _ t anil)));
    cbn [ex_rules mkr d_ctx d_concl d_prems].
  - unfold Ex; rewrite (vsubst_Qnt_eta (P := P) (s := s) c_ex vz); reflexivity.
  - intros p [<-|[]]. unfold inst_hyps, inst_goal, vsubst_list; cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    rewrite vup_nil, wk_list_nil, vsubst_app1. exact Hφ.
Qed.

(** ∃E : avec une variable propre x et l'hypothèse φ(x), on dérive χ
    (affaibli, donc sans x). *)
Lemma ex_E {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (χ : form Γ) :
  Ξ ⊢ Ex s φ ->
  deriv C P R (ι s :: Γ) (φ :: wk_list [ι s] Ξ) (ren_tm χ (wk [ι s])) ->
  Ξ ⊢ χ.
Proof.
  intros H1 H2. apply (rule_inc C P R (ex_rules s) ExE Ξ
                         (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι P) _ χ anil)));
    cbn [ex_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_var0; reflexivity.
  - intros p [<-|[<-|[]]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    + rewrite vup_nil, wk_list_nil. unfold Ex; rewrite (vsubst_Qnt_eta (P := P) (s := s) c_ex vz). exact H1.
    + eapply deriv_eq2; [| |exact H2].
      * f_equal. symmetry.
        exact (vsubst_eta_up [ι s] P vz (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι P) _ χ anil))).
      * symmetry. etransitivity; [exact (vsubst_var0 (vs (vs vz)) _)|].
        unfold vup, vren; cbn [vcat ahd atl aget vmap].
        apply ren_tms_nil.
Qed.
End Ex.

Section Eq.
Context {HQ : HasEq Sym P s} `{Includes _ Sym P I eq_idx R (eq_rules s)}.

Lemma eq_refl_d {Γ} (Ξ : list (form Γ)) (t : tm Γ s) : Ξ ⊢ Eq s t t.
Proof.
  apply (rule_inc C P R (eq_rules s) EqR Ξ (@acons _ Sym Γ (ι s) _ t anil));
    cbn [eq_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_Eq, vsubst_var0; reflexivity.
  - intros p [].
Qed.

(** Transport (égalité de Leibniz) : de t = u et φ[t/x], on tire φ[u/x]. *)
Lemma eq_subst {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (t u : tm Γ s) :
  Ξ ⊢ Eq s t u -> Ξ ⊢ vsubst φ (inst1 t) -> Ξ ⊢ vsubst φ (inst1 u).
Proof.
  intros H1 H2. apply (rule_inc C P R (eq_rules s) EqS Ξ
                         (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι s) _ t
                            (@acons _ Sym Γ (ι s) _ u anil))));
    cbn [eq_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_app1; reflexivity.
  - intros p [<-|[<-|[]]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal prem premx d_ctx map app]; rewrite vup_nil, wk_list_nil.
    + rewrite vsubst_Eq, !vsubst_var0. exact H1.
    + rewrite vsubst_app1. exact H2.
Qed.

Lemma eq_sym_d {Γ} (Ξ : list (form Γ)) (t u : tm Γ s) : Ξ ⊢ Eq s t u -> Ξ ⊢ Eq s u t.
Proof.
  intros Hd.
  pose (φ := Eq s (Γ := ι s :: Γ) (var0 vz) (ren_tm t (wk [ι s]))).
  assert (E : forall w, vsubst φ (inst1 w) = Eq s w t).
  { intros w; unfold φ; rewrite vsubst_Eq; f_equal; [apply vsubst_var0|apply vsubst_wk_inst1]. }
  rewrite <- E. apply (eq_subst _ _ t); [exact Hd|]. rewrite E. apply eq_refl_d.
Qed.

Lemma eq_trans_d {Γ} (Ξ : list (form Γ)) (t u w : tm Γ s) :
  Ξ ⊢ Eq s t u -> Ξ ⊢ Eq s u w -> Ξ ⊢ Eq s t w.
Proof.
  intros H1 H2.
  pose (φ := Eq s (Γ := ι s :: Γ) (ren_tm t (wk [ι s])) (var0 vz)).
  assert (E : forall z, vsubst φ (inst1 z) = Eq s t z).
  { intros z; unfold φ; rewrite vsubst_Eq; f_equal; [apply vsubst_wk_inst1|apply vsubst_var0]. }
  rewrite <- E. apply (eq_subst _ _ u); [exact H2|]. rewrite E. exact H1.
Qed.
End Eq.

End Derived.
