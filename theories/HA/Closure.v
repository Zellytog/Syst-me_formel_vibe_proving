(** * La relativisation est close par tous les symboles

    Dans le système libre, sous les hypothèses de relativisation de ses
    variables, tout terme vérifie la relativisation de sa sorte
    ([closure]) :

      D(x₁), …, D(xₖ) ⊢ D_s(t)        pour t : s dans le contexte x₁ … xₖ.

    La preuve est un « lemme fondamental » : on montre plus généralement
    Ξ ⊢ D_s(t[w]) pour tout vecteur w dont les composantes vérifient la
    relativisation sous Ξ. Les cas intéressants :
    - λ et app, par la définition héréditaire de D_{a → b} et β ;
    - 0 et S, par la définition imprédicative de D_N ;
    - rec, par la récurrence que *contient* D_N : on instancie X par
      λm. D_N(m) ∧ D_s(rec(z, st, m)), et on calcule par β et les règles
      de rec.
    Tous les symboles logiques sont de sorte O, et D_O = ⊤. *)

From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.HA Require Import Signature.

Local Notation ι a := (Spec [] a).

Section Closure.
Context {Ind : Type} {dsc : Ind -> list (list bool)}.
Local Notation ty := (Signature.ty Ind).
Local Notation hsym := (Signature.hsym dsc).
Local Notation tm := (Terms.tm hsym).
Local Notation form := (form hsym tO).
Local Notation FC := (generated free_calc_rules).
Local Notation "Ξ ⊢ φ" := (deriv FC tO free_rules _ Ξ φ) (at level 70).

Local Tactic Notation "nd" uconstr(t) := eapply t; try typeclasses eauto.

Definition hq (s : ty) : quantifiable (Sym := hsym) omega omega s := conj Logic.I Logic.I.

(** ** Calculs de substitution *)

Lemma vsubst_All' s {Θ Γ} (φ : form (ι s :: Θ)) (v : vec hsym Θ Γ) :
  vsubst (All s φ) v = All s (vsubst φ (vup [ι s] v)).
Proof. unfold All. rewrite vsubst_Qnt, vsubst_tms_vup. reflexivity. Qed.

Lemma vsubst_Ex' s {Θ Γ} (φ : form (ι s :: Θ)) (v : vec hsym Θ Γ) :
  vsubst (Ex s φ) v = Ex s (vsubst φ (vup [ι s] v)).
Proof. unfold Ex. rewrite vsubst_Qnt, vsubst_tms_vup. reflexivity. Qed.

Lemma vsubst_Dat s (Ds : form [ι s]) {Θ Γ} (t : tm Θ s) (v : vec hsym Θ Γ) :
  vsubst (Dat s Ds t) v = Dat s Ds (vsubst t v).
Proof.
  unfold Dat. rewrite vsubst_vsubst. f_equal.
  apply vec_ext; intros σ x; unfold vget; revert σ x. refine (var_inv _ _ _); [|intros σ y; destruct (var_nil y)].
  rewrite aget_vcomp. cbn [aget ahd]. apply vsubst_tms_nil.
Qed.

Lemma ren_tms0 {Γ Δ s} (t : tm Γ s) (ξ : ren Γ Δ) : ren_tms (σ := ι s) t ξ = ren_tm t ξ.
Proof. unfold ren_tms. apply ren_ext. intros σ x. reflexivity. Qed.

Lemma ren_Dat s (Ds : form [ι s]) {Γ Δ} (t : tm Γ s) (ξ : ren Γ Δ) :
  ren_tm (Dat s Ds t) ξ = Dat s Ds (ren_tm t ξ).
Proof.
  unfold Dat. rewrite ren_vsubst. reflexivity.
Qed.

(** [vsubst_wk_inst1], énoncé dans le contexte ι a :: Γ (et non [ι a] ++ Γ). *)
Lemma wk1_inst1 {Γ a s} (t : tm Γ s) (u : tm Γ a) :
  @vsubst _ hsym (ι a :: Γ) s (ren_tm t (wk [ι a])) Γ (inst1 u) = t.
Proof. exact (vsubst_wk_inst1 t u). Qed.

Lemma ren_var0 {Γ Δ a} (x : var Γ (ι a)) (ξ : ren Γ Δ) : ren_tm (var0 (Sym := hsym) x) ξ = var0 (ξ _ x).
Proof. reflexivity. Qed.

Lemma conv_Dat s (Ds : form [ι s]) {Γ} (t t' : tm Γ s) : conv FC t t' -> conv FC (Dat s Ds t) (Dat s Ds t').
Proof. intros H. apply conv_subst; [apply conv_refl|]. split; [exact H|exact Logic.I]. Qed.

Lemma conv_bin (c : hsym (Spec [ι tO; ι tO] tO)) {Γ} (a a' b b' : form Γ) :
  conv FC a a' -> conv FC b b' -> conv FC (Bin c a b) (Bin c a' b').
Proof.
  intros H1 H2. unfold Bin.
  exact (conv_tsym FC (σ := Spec [ι tO; ι tO] tO) c
           (@acons _ hsym Γ (ι tO) _ a (@acons _ hsym Γ (ι tO) _ b anil))
           (@acons _ hsym Γ (ι tO) _ a' (@acons _ hsym Γ (ι tO) _ b' anil)) (conj H1 (conj H2 Logic.I))).
Qed.

Lemma conv_App a b {Γ} (f f' : tm Γ (tarr a b)) (u u' : tm Γ a) :
  conv FC f f' -> conv FC u u' -> conv FC (App (w_ab a b) f u) (App (w_ab a b) f' u').
Proof.
  intros H1 H2. unfold App.
  exact (conv_tsym FC (σ := Spec [ι (tarr a b); ι a] b) (h_app a b)
           (@acons _ hsym Γ (ι (tarr a b)) _ f (@acons _ hsym Γ (ι a) _ u anil))
           (@acons _ hsym Γ (ι (tarr a b)) _ f' (@acons _ hsym Γ (ι a) _ u' anil)) (conj H1 (conj H2 Logic.I))).
Qed.

Lemma beta' a b {Γ} (t : tm (ι a :: Γ) b) (u : tm Γ a) :
  conv FC (App (w_ab a b) (Lam (w_ab a b) t) u) (vsubst t (inst1 u)).
Proof. apply beta_conv. typeclasses eauto. Qed.

Lemma rec0' s h {Γ} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) :
  conv FC (Rec s h z st Zero) z.
Proof. apply rec_zero_conv. typeclasses eauto. Qed.

Lemma recS' s h {Γ} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (m : tm Γ tN) :
  conv FC (Rec s h z st (Succ m))
    (vsubst st (@acons _ hsym Γ (ι tN) _ m (@acons _ hsym Γ (ι s) _ (Rec s h z st m) (vid Γ)))).
Proof. apply rec_succ_conv. typeclasses eauto. Qed.

Lemma d_conv' {Γ} (Ξ : list (form Γ)) φ ψ : conv FC φ ψ -> Ξ ⊢ φ -> Ξ ⊢ ψ.
Proof. intros H1 H2. eapply d_conv; [exact H1|exact H2]. Qed.

#[local] Typeclasses Transparent free_rules free_calc_rules ha_calc_rules.
#[local] Hint Unfold free_rules : typeclass_instances.

(** Les règles des quantificateurs, pour les symboles de la signature. *)
Lemma all_I' s {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) :
  deriv FC tO free_rules (ι s :: Γ) (wk_list [ι s] Ξ) φ -> Ξ ⊢ All s φ.
Proof. exact (qall_I FC free_rules s (hq s) Ξ φ). Qed.

Lemma all_E' s {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (t : tm Γ s) :
  Ξ ⊢ All s φ -> Ξ ⊢ vsubst φ (inst1 t).
Proof. exact (qall_E FC free_rules s (hq s) Ξ φ t). Qed.

Lemma ex_I' s {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) (t : tm Γ s) :
  Ξ ⊢ vsubst φ (inst1 t) -> Ξ ⊢ Ex s φ.
Proof. exact (qex_I FC free_rules s (hq s) Ξ φ t). Qed.

Lemma ex_E' s {Γ} (Ξ : list (form Γ)) (φ : form (ι s :: Γ)) χ :
  Ξ ⊢ Ex s φ -> deriv FC tO free_rules (ι s :: Γ) (φ :: wk_list [ι s] Ξ) (ren_tm χ (wk [ι s])) -> Ξ ⊢ χ.
Proof. exact (qex_E FC free_rules s (hq s) Ξ φ χ). Qed.

(** ** La relativisation des flèches *)

Lemma Darr_eq a b {Γ} (F : tm Γ (tarr a b)) :
  Dat (tarr a b) (D (tarr a b)) F
  = All a (Imp (Dat a (D a) (var0 vz)) (Dat b (D b) (App (w_ab a b) (ren_tm F (wk [ι a])) (var0 vz)))).
Proof.
  unfold Dat at 1. cbn [D]. unfold Imp.
  rewrite vsubst_All', vsubst_Bin, !vsubst_Dat, vsubst_App, !vsubst_var0. reflexivity.
Qed.

Lemma arr_intro a b {Γ} (Ξ : list (form Γ)) (F : tm Γ (tarr a b)) :
  deriv FC tO free_rules (ι a :: Γ) (Dat a (D a) (var0 vz) :: wk_list [ι a] Ξ)
    (Dat b (D b) (App (w_ab a b) (ren_tm F (wk [ι a])) (var0 vz))) ->
  Ξ ⊢ Dat (tarr a b) (D (tarr a b)) F.
Proof.
  intros H. rewrite Darr_eq. apply all_I'. nd imp_I. exact H.
Qed.

Lemma arr_elim a b {Γ} (Ξ : list (form Γ)) (F : tm Γ (tarr a b)) (u : tm Γ a) :
  Ξ ⊢ Dat (tarr a b) (D (tarr a b)) F -> Ξ ⊢ Dat a (D a) u -> Ξ ⊢ Dat b (D b) (App (w_ab a b) F u).
Proof.
  rewrite Darr_eq. intros HF Hu.
  pose proof (all_E' a Ξ _ u HF) as K.
  unfold Imp in K. rewrite vsubst_Bin, !vsubst_Dat, vsubst_App, !vsubst_var0, ?vsubst_wk_inst1, ?wk1_inst1 in K.
  nd imp_E; [exact K|exact Hu].
Qed.

(** ** La relativisation des entiers *)

Local Notation XN := (tarr tN tO).
Local Notation wN := (w_ab tN tO).

Definition Step {Γ} (X0 : tm Γ XN) : form Γ :=
  All tN (Imp (App wN (ren_tm X0 (wk [ι tN])) (var0 vz)) (App wN (ren_tm X0 (wk [ι tN])) (Succ (var0 vz)))).

Lemma Dnat_eq {Γ} (t : tm Γ tN) :
  Dat tN NatF t
  = All XN (Imp (App wN (var0 vz) Zero) (Imp (Step (var0 vz)) (App wN (var0 vz) (ren_tm t (wk [ι XN]))))).
Proof.
  unfold Dat, NatF, Step, Imp.
  rewrite vsubst_All', !vsubst_Bin, !vsubst_App, !vsubst_var0, vsubst_All', vsubst_Bin, !vsubst_App,
    !vsubst_var0, vsubst_Succ, vsubst_var0. reflexivity.
Qed.

Lemma nat_intro {Γ} (Ξ : list (form Γ)) (t : tm Γ tN) :
  deriv FC tO free_rules (ι XN :: Γ) (Step (var0 vz) :: App wN (var0 vz) Zero :: wk_list [ι XN] Ξ)
    (App wN (var0 vz) (ren_tm t (wk [ι XN]))) ->
  Ξ ⊢ Dat tN NatF t.
Proof.
  intros H. rewrite Dnat_eq. apply all_I'. nd imp_I. nd imp_I. exact H.
Qed.

Lemma nat_elim {Γ} (Ξ : list (form Γ)) (t : tm Γ tN) (X0 : tm Γ XN) :
  Ξ ⊢ Dat tN NatF t -> Ξ ⊢ App wN X0 Zero -> Ξ ⊢ Step X0 -> Ξ ⊢ App wN X0 t.
Proof.
  rewrite Dnat_eq. intros Hn H0 HS.
  pose proof (all_E' XN Ξ _ X0 Hn) as K.
  unfold Step, Imp in K. rewrite !ren_var0 in K. rewrite !vsubst_Bin, !vsubst_App, !vsubst_var0, vsubst_All', vsubst_Bin, !vsubst_App,
    !vsubst_var0, vsubst_Succ, vsubst_var0, ?vsubst_wk_inst1, ?wk1_inst1 in K.
  nd imp_E; [nd imp_E; [exact K|exact H0]|exact HS].
Qed.

Lemma nat_zero {Γ} (Ξ : list (form Γ)) : Ξ ⊢ Dat tN NatF Zero.
Proof. apply nat_intro. nd hyp. right; left; reflexivity. Qed.

Lemma nat_succ {Γ} (Ξ : list (form Γ)) (t : tm Γ tN) :
  Ξ ⊢ Dat tN NatF t -> Ξ ⊢ Dat tN NatF (Succ t).
Proof.
  intros H. apply nat_intro.
  apply (deriv_wk _ _ _ [ι XN]) in H. rewrite ren_Dat in H.
  assert (Hx : deriv FC tO free_rules (ι XN :: Γ) (Step (var0 vz) :: App wN (var0 vz) Zero :: wk_list [ι XN] Ξ)
                 (App wN (var0 vz) (ren_tm t (wk [ι XN])))).
  { apply nat_elim.
    - eapply deriv_weaken; [exact H|]. intros x Hx; right; right; exact Hx.
    - nd hyp. right; left; reflexivity.
    - nd hyp. left; reflexivity. }
  assert (Hs : deriv FC tO free_rules (ι XN :: Γ) (Step (var0 vz) :: App wN (var0 vz) Zero :: wk_list [ι XN] Ξ)
                 (Step (var0 vz))) by (nd hyp; left; reflexivity).
  pose proof (all_E' tN _ _ (ren_tm t (wk [ι XN])) Hs) as K.
  unfold Imp in K. rewrite vsubst_Bin, !vsubst_App, !vsubst_var0, vsubst_Succ, vsubst_var0 in K.
  change (ren_tm (Succ t) (wk [ι XN])) with (Succ (ren_tm t (wk [ι XN]))).
  nd imp_E; [exact K|exact Hx].
Qed.

(** ** Hypothèses sur un vecteur *)

(** La relativisation d'un corps de spécification σ (⊤ si σ n'est pas une sorte). *)
Definition DAt {Γ} (σ : spec ty) : tms hsym Γ σ -> form Γ :=
  match σ as σ0 return tms hsym Γ σ0 -> form Γ with
  | Spec [] s => fun u => Dat s (D s) u
  | Spec (_ :: _) _ => fun _ => Top
  end.

Definition Hw {Δ Γ} (w : vec hsym Δ Γ) (Ξ : list (form Γ)) : Prop :=
  forall σ (x : var Δ σ), Ξ ⊢ DAt σ (aget x w).

Definition sorted (Δ : ctx ty) : Prop := forall σ (x : var Δ σ), dom σ = [].

Lemma ren_DAt σ {Γ Δ} (u : tms hsym Γ σ) (ξ : ren Γ Δ) : ren_tm (DAt σ u) ξ = DAt σ (ren_tms u ξ).
Proof. destruct σ as [[|τ Θ] b]; cbn [DAt]; [apply ren_Dat|reflexivity]. Qed.

Lemma hw_weaken {Δ Γ} (w : vec hsym Δ Γ) Ξ Ξ' : Hw w Ξ -> incl Ξ Ξ' -> Hw w Ξ'.
Proof. intros H Hi σ x. eapply deriv_weaken; [apply H|exact Hi]. Qed.

Lemma hw_wk Λ {Δ Γ} (w : vec hsym Δ Γ) Ξ : Hw w Ξ -> Hw (vren w (wk Λ)) (wk_list Λ Ξ).
Proof.
  intros H σ x. unfold vren. rewrite aget_vmap, <- ren_DAt. apply (deriv_wk _ _ _ Λ), H.
Qed.

Lemma hw_cons {Δ Γ τ} (u : tms hsym Γ τ) (w : vec hsym Δ Γ) Ξ :
  Ξ ⊢ DAt τ u -> Hw w Ξ -> Hw (@acons _ hsym Γ τ Δ u w) Ξ.
Proof. intros Hu H σ x. revert σ x. refine (var_inv _ _ _); [exact Hu|]. intros σ y. apply H. Qed.

Lemma hw_up a {Δ Γ} (w : vec hsym Δ Γ) Ξ :
  Hw w Ξ -> Hw (vup [ι a] w) (Dat a (D a) (var0 vz) :: wk_list [ι a] Ξ).
Proof.
  intros H. apply hw_cons.
  - nd hyp. left; reflexivity.
  - eapply hw_weaken; [apply hw_wk, H|]. intros x Hx; right; exact Hx.
Qed.

Lemma sorted_cons a Δ : sorted Δ -> sorted (ι a :: Δ).
Proof.
  intros H σ x. revert σ x.
  refine (@var_inv _ (ι a) Δ (fun σ _ => dom σ = []) eq_refl _). intros σ y; exact (H σ y).
Qed.

(** ** Calculs sur les vecteurs *)

Lemma vsubst_tms_wk_cat Λ {Γ Δ σ} (u : tms hsym Γ σ) (a : args hsym Δ Λ) (w : vec hsym Γ Δ) :
  vsubst_tms (ren_tms u (wk Λ)) (vcat Λ a w) = vsubst_tms u w.
Proof.
  unfold vsubst_tms; rewrite subst_tms_ren; apply subst_tms_ext; intros ρ y.
  unfold rs_comp, vget, wk. rewrite aget_vcat_r. reflexivity.
Qed.

Lemma vren_vup Λ {Δ Γ Γ'} (w : vec hsym Δ Γ) (ξ : ren Γ Γ') :
  vren (vup Λ w) (upr Λ ξ) = vup Λ (vren w ξ).
Proof.
  apply vec_ext; intros σ x; unfold vget, vup, vren. rewrite !aget_vmap. vcase x.
  - rewrite !aget_vcat_l, !aget_etas, eta_ren, upr_vl. reflexivity.
  - rewrite !aget_vcat_r, !aget_vmap, !ren_tms_ren. apply ren_tms_ext. intros ρ y. unfold rcomp, wk.
    rewrite upr_vr. reflexivity.
Qed.

Lemma vup_cat Λ {Δ Γ Γ'} (w : vec hsym Δ Γ) (a : args hsym Γ' Λ) (w' : vec hsym Γ Γ') :
  vcomp (vup Λ w) (vcat Λ a w') = vcat Λ a (vcomp w w').
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. vcase x.
  - unfold vup. rewrite !aget_vcat_l, aget_etas, vsubst_eta, aget_vcat_l. reflexivity.
  - unfold vup. rewrite !aget_vcat_r. unfold vren. rewrite aget_vmap, vsubst_tms_wk_cat, aget_vcomp.
    reflexivity.
Qed.

(** Affaiblir sous Λ par une variable, puis l'instancier : identité. *)
Lemma cancel_wk_up Λ τ {Γ s} (t : tm (Λ ++ Γ) s) (u : tm Γ τ) :
  vsubst (ren_tm t (upr Λ (wk [ι τ]))) (vup Λ (inst1 u)) = t.
Proof.
  rewrite vsubst_ren. rewrite <- (vsubst_vid t) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vpre, aget_vid. vcase x.
  - rewrite upr_vl. unfold vup. rewrite aget_vcat_l, aget_etas. reflexivity.
  - rewrite upr_vr. unfold vup, wk. cbn [vr]. rewrite aget_vcat_r. unfold vren. rewrite aget_vmap.
    cbn [aget atl inst1]. rewrite aget_vid, eta_ren. reflexivity.
Qed.

(** ** Le prédicat de la récurrence pour rec *)

Local Notation Λst s := [ι tN; ι s].

(** λm. D_N(m) ∧ D_s(rec(z, st, m)) : le corps, dans m :: Γ. *)
Definition mkB s h {Γ} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) : form (ι tN :: Γ) :=
  And (Dat tN NatF (var0 vz))
      (Dat s (D s) (Rec s h (ren_tm z (wk [ι tN])) (ren_tm st (upr (Λst s) (wk [ι tN]))) (var0 vz))).

Lemma B_inst s h {Γ} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (u : tm Γ tN) :
  vsubst (mkB s h z st) (inst1 u) = And (Dat tN NatF u) (Dat s (D s) (Rec s h z st u)).
Proof.
  unfold mkB, And. rewrite vsubst_Bin, !vsubst_Dat, vsubst_Rec, !vsubst_var0, ?vsubst_wk_inst1, ?wk1_inst1.
  rewrite vsubst_tms_vup. cbn [dom]. rewrite cancel_wk_up. reflexivity.
Qed.

Lemma ren_Rec s h {Γ Γ'} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (n : tm Γ tN) (ξ : ren Γ Γ') :
  ren_tm (Rec s h z st n) ξ = Rec s h (ren_tm z ξ) (ren_tm st (upr (Λst s) ξ)) (ren_tm n ξ).
Proof. reflexivity. Qed.

Lemma ren_And {Γ Γ'} (a b : form Γ) (ξ : ren Γ Γ') : ren_tm (And a b) ξ = And (ren_tm a ξ) (ren_tm b ξ).
Proof. reflexivity. Qed.

Lemma ren_mkB s h {Γ Γ'} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (ξ : ren Γ Γ') :
  ren_tm (mkB s h z st) (upr [ι tN] ξ) = mkB s h (ren_tm z ξ) (ren_tm st (upr (Λst s) ξ)).
Proof.
  unfold mkB. rewrite ren_And, !ren_Dat, ren_Rec. f_equal. f_equal. f_equal.
  - rewrite !ren_ren. apply ren_ext. intros σ x. reflexivity.
  - rewrite !ren_ren. apply ren_ext. intros σ x. unfold rcomp.
    change (var ([ι tN; ι s] ++ Γ) σ) in x. vcase x; rewrite ?upr_vl, ?upr_vr; [rewrite ?upr_vl; reflexivity|].
    unfold wk. rewrite ?upr_vr. reflexivity.
Qed.

Lemma appB s h {Γ} (Ξ : list (form Γ)) (z : tm Γ s) st (u : tm Γ tN) :
  Ξ ⊢ App wN (Lam wN (mkB s h z st)) u -> Ξ ⊢ And (Dat tN NatF u) (Dat s (D s) (Rec s h z st u)).
Proof. intros H. rewrite <- B_inst. eapply d_conv'; [apply beta'|exact H]. Qed.

Lemma appB_inv s h {Γ} (Ξ : list (form Γ)) (z : tm Γ s) st (u : tm Γ tN) :
  Ξ ⊢ And (Dat tN NatF u) (Dat s (D s) (Rec s h z st u)) -> Ξ ⊢ App wN (Lam wN (mkB s h z st)) u.
Proof. intros H. rewrite <- B_inst in H. eapply d_conv'; [apply conv_sym, beta'|exact H]. Qed.

Lemma ren_LamB s h {Γ} (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) :
  ren_tm (Lam wN (mkB s h z st)) (wk [ι tN])
  = Lam wN (mkB s h (ren_tm z (wk [ι tN])) (ren_tm st (upr (Λst s) (wk [ι tN])))).
Proof. exact (f_equal (fun B => Lam wN B) (ren_mkB s h z st (wk [ι tN]))). Qed.

Lemma dat_O {Γ} (Ξ : list (form Γ)) (x : tm Γ tO) : Ξ ⊢ Dat tO (D tO) x.
Proof. change (Ξ ⊢ Top). nd top_I. Qed.

(** ** La relativisation des types inductifs *)

Local Notation XW i := (tarr (tW i) tO).
Local Notation wW i := (w_ab (tW i) tO).
Local Notation cargs i bs := (Inductive.cargs tN tW i bs).
Local Notation sargs i s bs := (Inductive.sargs tN tW i s bs).
Local Notation steps i s := (Inductive.steps tN tW dsc i s).

#[local] Typeclasses Transparent hae_calc_rules.

Lemma vup_cons τ Λ {Γ Δ} (v : vec hsym Γ Δ) : vup [τ] (vup Λ v) = vup (τ :: Λ) v.
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

Lemma vsubst_AllA i bs {Γ Δ} (φ : form (cargs i bs ++ Γ)) (v : vec hsym Γ Δ) :
  vsubst (AllA i bs φ) v = AllA i bs (vsubst φ (vup (cargs i bs) v)).
Proof.
  revert Γ Δ φ v; induction bs as [|b bs IH]; intros Γ Δ φ v; cbn [AllA].
  - cbn [Inductive.cargs map]. rewrite vup_nil. reflexivity.
  - rewrite IH, vsubst_All'. f_equal. f_equal. f_equal. apply vup_cons.
Qed.

Lemma vsubst_Imps {Γ Δ} (hs : list (form Γ)) φ (v : vec hsym Γ Δ) :
  vsubst (Imps hs φ) v = Imps (vsubst_list hs v) (vsubst φ v).
Proof.
  induction hs as [|h hs IH]; [reflexivity|].
  change (vsubst (Imp h (Imps hs φ)) v = Imp (vsubst h v) (Imps (vsubst_list hs v) (vsubst φ v))).
  unfold Imp at 1. rewrite vsubst_Bin, IH. reflexivity.
Qed.

Lemma vsubst_chyps i {Γ Δ} (X : tm Γ (XW i)) bs (a : args hsym Γ (cargs i bs)) (v : vec hsym Γ Δ) :
  vsubst_list (chyps i X bs a) v = chyps i (vsubst X v) bs (vsubst_args a v).
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a; cbn [chyps]; [reflexivity| |].
  - change (args hsym Γ (ι tN :: cargs i bs)) in a.
    change (vsubst (Dat tN NatF (ahd a)) v :: vsubst_list (chyps i X bs (atl a)) v
            = Dat tN NatF (ahd (vsubst_args a v)) :: chyps i (vsubst X v) bs (atl (vsubst_args a v))).
    rewrite IH, vsubst_Dat, (ahd_vsubst (σ := ι tN) (L := cargs i bs)), (atl_vsubst (σ := ι tN) (L := cargs i bs)),
      vsubst_tms_nil. reflexivity.
  - change (args hsym Γ (ι (tW i) :: cargs i bs)) in a.
    change (vsubst (App (wW i) X (ahd a)) v :: vsubst_list (chyps i X bs (atl a)) v
            = App (wW i) (vsubst X v) (ahd (vsubst_args a v)) :: chyps i (vsubst X v) bs (atl (vsubst_args a v))).
    rewrite IH, vsubst_App, (ahd_vsubst (σ := ι (tW i)) (L := cargs i bs)),
      (atl_vsubst (σ := ι (tW i)) (L := cargs i bs)), vsubst_tms_nil. reflexivity.
Qed.

Lemma vsubst_Clos i bs c {Γ Δ} (X : tm Γ (XW i)) (v : vec hsym Γ Δ) :
  vsubst (Clos i bs c X) v = Clos i bs c (vsubst X v).
Proof.
  unfold Clos. rewrite vsubst_AllA, vsubst_Imps, vsubst_chyps, vsubst_App, vsubst_Con, vsubst_lvars_up, vsubst_wk.
  reflexivity.
Qed.

Lemma vsubst_Closs i {Γ Δ} (X : tm Γ (XW i)) (v : vec hsym Γ Δ) :
  vsubst_list (Closs i X) v = Closs i (vsubst X v).
Proof.
  unfold Closs, vsubst_list. rewrite map_map. apply map_ext. intros [bs c]. apply vsubst_Clos.
Qed.

Lemma vsubst_var0_up σ {Γ Δ} (v : vec hsym Γ Δ) : vsubst (var0 (Θ := ι σ :: Γ) vz) (vup [ι σ] v) = var0 vz.
Proof. reflexivity. Qed.

Lemma vsubst_DW i {Γ Δ} (t : tm Γ (tW i)) (v : vec hsym Γ Δ) : vsubst (DW i t) v = DW i (vsubst t v).
Proof.
  unfold DW. rewrite vsubst_All', vsubst_Imps, vsubst_Closs, vsubst_App, vsubst_var0_up.
  do 3 f_equal. exact (vsubst_wk [ι (XW i)] t v).
Qed.

Lemma Dat_W i {Γ} (t : tm Γ (tW i)) : Dat (tW i) (D (tW i)) t = DW i t.
Proof. unfold Dat; cbn [D]. rewrite vsubst_DW, vsubst_var0. reflexivity. Qed.

Lemma ren_DW i {Γ Δ} (t : tm Γ (tW i)) (ξ : ren Γ Δ) : ren_tm (DW i t) ξ = DW i (ren_tm t ξ).
Proof. rewrite !ren_as_vsubst, vsubst_DW. reflexivity. Qed.

Lemma wk_list_cons' τ (Λ : ctx ty) {X} (L : list (form X)) :
  wk_list [τ] (wk_list Λ L) = wk_list (τ :: Λ) L.
Proof.
  unfold wk_list; rewrite map_map; apply map_ext; intros χ.
  rewrite ren_ren; apply ren_ext; intros; reflexivity.
Qed.

Lemma vsubst_wk_cat Λ {Γ Δ s} (t : tm Γ s) (a : args hsym Δ Λ) (w : vec hsym Γ Δ) :
  vsubst (ren_tm t (wk Λ)) (vcat Λ a w) = vsubst t w.
Proof.
  rewrite vsubst_ren. f_equal. apply vec_ext; intros σ x; unfold vget, wk. rewrite aget_vpre, aget_vcat_r.
  reflexivity.
Qed.

(** *** Dérivations *)

Lemma AllA_I i bs {Γ} (Ξ : list (form Γ)) (φ : form (cargs i bs ++ Γ)) :
  deriv FC tO free_rules (cargs i bs ++ Γ) (wk_list (cargs i bs) Ξ) φ -> Ξ ⊢ AllA i bs φ.
Proof.
  revert Γ Ξ φ; induction bs as [|b bs IH]; intros Γ Ξ φ H; cbn [AllA].
  - cbn [Inductive.cargs map] in H. rewrite wk_list_nil in H. exact H.
  - apply IH. apply all_I'. rewrite wk_list_cons'. exact H.
Qed.

Lemma AllA_E i bs {Γ} (Ξ : list (form Γ)) (φ : form (cargs i bs ++ Γ)) (a : args hsym Γ (cargs i bs)) :
  Ξ ⊢ AllA i bs φ -> Ξ ⊢ vsubst φ (vcat (cargs i bs) a (vid Γ)).
Proof.
  revert Γ Ξ φ a; induction bs as [|b bs IH]; intros Γ Ξ φ a H; cbn [AllA] in H.
  - change (args hsym Γ []) in a. rewrite (args_nil a). cbn [vcat Inductive.cargs map]. rewrite vsubst_vid. exact H.
  - change (args hsym Γ (ι (asrt tN tW i b) :: cargs i bs)) in a.
    pose proof (IH _ _ _ (atl a) H) as K. rewrite vsubst_All' in K.
    pose proof (all_E' _ _ _ (ahd a) K) as K'. rewrite vsubst_vsubst in K'.
    refine (eq_ind _ (fun v => deriv FC tO free_rules Γ Ξ (vsubst φ v)) K' _ _).
    etransitivity;
      [exact (vup_cat [ι (asrt tN tW i b)] (vcat (cargs i bs) (atl a) (vid Γ))
                (@acons _ hsym Γ (ι (asrt tN tW i b)) _ (ahd a) anil) (vid Γ))|].
    rewrite vcomp_vid_r. reflexivity.
Qed.

Lemma Imps_I {Γ} (Ξ : list (form Γ)) hs φ : deriv FC tO free_rules Γ (rev hs ++ Ξ) φ -> Ξ ⊢ Imps hs φ.
Proof.
  revert Ξ; induction hs as [|h hs IH]; intros Ξ H; [exact H|].
  change (Ξ ⊢ Imp h (Imps hs φ)). nd imp_I. apply IH. cbn [rev] in H. rewrite <- app_assoc in H. exact H.
Qed.

Lemma Imps_E {Γ} (Ξ : list (form Γ)) hs φ : Ξ ⊢ Imps hs φ -> (forall h, In h hs -> Ξ ⊢ h) -> Ξ ⊢ φ.
Proof.
  induction hs as [|h hs IH]; intros H Hh; [exact H|].
  apply IH; [|intros h' Hh'; apply Hh; right; exact Hh'].
  change (Ξ ⊢ Imp h (Imps hs φ)) in H. nd imp_E; [exact H|apply Hh; left; reflexivity].
Qed.

Lemma DW_elim i {Γ} (Ξ : list (form Γ)) (t : tm Γ (tW i)) (X : tm Γ (XW i)) :
  Ξ ⊢ DW i t -> (forall cl, In cl (Closs i X) -> Ξ ⊢ cl) -> Ξ ⊢ App (wW i) X t.
Proof.
  intros H Hc. unfold DW in H. pose proof (all_E' _ _ _ X H) as K.
  rewrite vsubst_Imps, vsubst_Closs, vsubst_App, vsubst_var0, wk1_inst1 in K.
  exact (Imps_E _ _ _ K Hc).
Qed.

Lemma DW_intro i {Γ} (Ξ : list (form Γ)) (t : tm Γ (tW i)) :
  deriv FC tO free_rules (ι (XW i) :: Γ) (rev (Closs i (var0 vz)) ++ wk_list [ι (XW i)] Ξ)
    (App (wW i) (var0 vz) (ren_tm t (wk [ι (XW i)]))) ->
  Ξ ⊢ DW i t.
Proof. intros H. unfold DW. apply all_I'. apply Imps_I. exact H. Qed.

Lemma Clos_elim i bs c {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) (a : args hsym Γ (cargs i bs)) :
  Ξ ⊢ Clos i bs c X -> (forall h, In h (chyps i X bs a) -> Ξ ⊢ h) -> Ξ ⊢ App (wW i) X (Con i bs c a).
Proof.
  unfold Clos. intros H Hh. apply (AllA_E _ _ _ _ a) in H.
  rewrite vsubst_Imps, vsubst_chyps, vsubst_App, vsubst_Con, vsubst_lvars, vsubst_wk_cat, vsubst_vid in H.
  exact (Imps_E _ _ _ H Hh).
Qed.

Lemma Clos_intro i bs c {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) :
  deriv FC tO free_rules (cargs i bs ++ Γ)
    (rev (chyps i (ren_tm X (wk (cargs i bs))) bs (lvars _ Γ)) ++ wk_list (cargs i bs) Ξ)
    (App (wW i) (ren_tm X (wk (cargs i bs))) (Con i bs c (lvars _ Γ))) ->
  Ξ ⊢ Clos i bs c X.
Proof. intros H. unfold Clos. apply AllA_I. apply Imps_I. exact H. Qed.

(** Les faits de relativisation des arguments d'un constructeur. *)
Fixpoint dfacts i {Γ} (bs : list bool) : args hsym Γ (cargs i bs) -> list (form Γ) :=
  match bs as bs0 return args hsym Γ (cargs i bs0) -> list (form Γ) with
  | [] => fun _ => []
  | b :: bs' =>
      match b as b0 return args hsym Γ (cargs i (b0 :: bs')) -> list (form Γ) with
      | true => fun a => Dat tN NatF (ahd a) :: dfacts i bs' (atl a)
      | false => fun a => DW i (ahd a) :: dfacts i bs' (atl a)
      end
  end.

Lemma dfacts_chyps i {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) bs (a : args hsym Γ (cargs i bs)) :
  (forall h, In h (dfacts i bs a) -> Ξ ⊢ h) -> (forall y, Ξ ⊢ DW i y -> Ξ ⊢ App (wW i) X y) ->
  forall h, In h (chyps i X bs a) -> Ξ ⊢ h.
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a Hd HX h Hh; cbn [chyps dfacts] in *; [destruct Hh| |].
  - destruct Hh as [<-|Hh]; [apply Hd; left; reflexivity|].
    apply (IH (atl a)); [intros; apply Hd; right; assumption|exact HX|exact Hh].
  - destruct Hh as [<-|Hh]; [apply HX, Hd; left; reflexivity|].
    apply (IH (atl a)); [intros; apply Hd; right; assumption|exact HX|exact Hh].
Qed.

Lemma chyps_dfacts i {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) bs (a : args hsym Γ (cargs i bs)) :
  (forall h, In h (chyps i X bs a) -> Ξ ⊢ h) -> (forall y, Ξ ⊢ App (wW i) X y -> Ξ ⊢ DW i y) ->
  forall h, In h (dfacts i bs a) -> Ξ ⊢ h.
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a Hd HX h Hh; cbn [chyps dfacts] in *; [destruct Hh| |].
  - destruct Hh as [<-|Hh]; [apply Hd; left; reflexivity|].
    apply (IH (atl a)); [intros; apply Hd; right; assumption|exact HX|exact Hh].
  - destruct Hh as [<-|Hh]; [apply HX, Hd; left; reflexivity|].
    apply (IH (atl a)); [intros; apply Hd; right; assumption|exact HX|exact Hh].
Qed.

Lemma ren_dfacts i bs {Γ Δ} (a : args hsym Γ (cargs i bs)) (ξ : ren Γ Δ) :
  map (fun h => ren_tm h ξ) (dfacts i bs a) = dfacts i bs (ren_args a ξ).
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a; cbn [dfacts]; [reflexivity| |].
  - change (args hsym Γ (ι tN :: cargs i bs)) in a. cbn [map]. rewrite IH, ren_Dat.
    rewrite (ahd_ren (σ := ι tN) (L := cargs i bs)), (atl_ren (σ := ι tN) (L := cargs i bs)). reflexivity.
  - change (args hsym Γ (ι (tW i) :: cargs i bs)) in a. cbn [map]. rewrite IH, ren_DW.
    rewrite (ahd_ren (σ := ι (tW i)) (L := cargs i bs)), (atl_ren (σ := ι (tW i)) (L := cargs i bs)). reflexivity.
Qed.

Lemma vars_dfacts i {Γ} (Ξ : list (form Γ)) bs (a : args hsym Γ (cargs i bs)) :
  (forall σ (z : var (cargs i bs) σ), Ξ ⊢ DAt σ (aget z a)) -> forall h, In h (dfacts i bs a) -> Ξ ⊢ h.
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a Ha h Hh; cbn [dfacts] in Hh; [destruct Hh| |].
  - destruct Hh as [<-|Hh]; [exact (Ha _ vz)|].
    apply (IH (atl a)); [intros σ z; exact (Ha σ (vs z))|exact Hh].
  - destruct Hh as [<-|Hh]; [rewrite <- Dat_W; exact (Ha _ vz)|].
    apply (IH (atl a)); [intros σ z; exact (Ha σ (vs z))|exact Hh].
Qed.

Lemma in_Closs i bs (c : mem (dsc i) bs) {Γ} (X : tm Γ (XW i)) : In (Clos i bs c X) (Closs i X).
Proof. unfold Closs. apply in_map_iff. exists (existT _ bs c). split; [reflexivity|apply mems_complete]. Qed.

(** La relativisation de Wᵢ est close par les constructeurs. *)
Lemma DW_con i bs (c : mem (dsc i) bs) {Γ} (Ξ : list (form Γ)) (a : args hsym Γ (cargs i bs)) :
  (forall h, In h (dfacts i bs a) -> Ξ ⊢ h) -> Ξ ⊢ DW i (Con i bs c a).
Proof.
  intros Hd. apply DW_intro. rewrite ren_Con.
  set (Ξ' := rev (Closs i (var0 (Θ := ι (XW i) :: Γ) vz)) ++ wk_list [ι (XW i)] Ξ).
  assert (Hcl : forall cl, In cl (Closs i (var0 (Θ := ι (XW i) :: Γ) vz)) -> deriv FC tO free_rules _ Ξ' cl).
  { intros cl Hin. nd hyp. apply in_or_app; left. apply in_rev in Hin. exact Hin. }
  apply Clos_elim; [apply Hcl, in_Closs|].
  apply dfacts_chyps.
  - intros h Hh. rewrite <- ren_dfacts in Hh. apply in_map_iff in Hh as (h0 & <- & Hh0).
    eapply deriv_weaken; [exact (deriv_wk _ _ _ [ι (XW i)] (Hd h0 Hh0))|].
    intros x Hx; apply in_or_app; right; exact Hx.
  - intros y Hy. apply DW_elim; [exact Hy|exact Hcl].
Qed.

Lemma hw_vcat Λ {Δ Γ} (S : args hsym Γ Λ) (w : vec hsym Δ Γ) Ξ :
  (forall σ (z : var Λ σ), Ξ ⊢ DAt σ (aget z S)) -> Hw w Ξ -> Hw (vcat Λ S w) Ξ.
Proof. intros HS H σ x. vcase x; [rewrite aget_vcat_l; apply HS|rewrite aget_vcat_r; apply H]. Qed.

Lemma sorted_sargs i (s : ty) bs (Δ : ctx ty) : sorted Δ -> sorted (sargs i s bs ++ Δ).
Proof.
  intros H. induction bs as [|[|] bs IH]; cbn [Inductive.sargs app]; [exact H|apply sorted_cons, IH|].
  apply sorted_cons, sorted_cons, IH.
Qed.

Lemma cargs_iota (i : Ind) bs (σ : spec ty) (z : var (cargs i bs) σ) : dom σ = [].
Proof.
  revert σ z. induction bs as [|b bs IH]; intros σ z; [destruct (var_nil z)|].
  revert σ z. refine (var_inv _ _ _); [reflexivity|]. intros σ y. exact (IH σ y).
Qed.

(** Le prédicat de la récurrence pour rec_W : λy. D_W(y) ∧ D_s(rec(y, st)). *)
Definition BW i s (h : rec_ok omega s) {Γ} (st : args hsym Γ (steps i s)) : form (ι (tW i) :: Γ) :=
  And (DW i (var0 vz)) (Dat s (D s) (WRec i s h (var0 vz) (ren_args st (wk [ι (tW i)])))).

Lemma vsubst_args_wk1 {Γ τ L} (a : args hsym Γ L) (u : tms hsym Γ τ) :
  vsubst_args (ren_args a (wk [τ])) (@acons _ hsym Γ τ _ u (vid Γ)) = a.
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vsubst_args, aget_ren.
  change (@acons _ hsym Γ τ _ u (vid Γ)) with (vcat [τ] (@acons _ hsym Γ τ _ u anil) (vid Γ)).
  rewrite vsubst_tms_wk_cat, vsubst_tms_vid. reflexivity.
Qed.

Lemma BW_inst i s h {Γ} (st : args hsym Γ (steps i s)) (u : tm Γ (tW i)) :
  vsubst (BW i s h st) (inst1 u) = And (DW i u) (Dat s (D s) (WRec i s h u st)).
Proof.
  unfold BW, And. rewrite vsubst_Bin, vsubst_DW, vsubst_Dat, vsubst_WRec, !vsubst_var0. cbn [aget ahd inst1].
  repeat f_equal. apply vsubst_args_wk1.
Qed.

Lemma ren_BW i s h {Γ Γ'} (st : args hsym Γ (steps i s)) (ξ : ren Γ Γ') :
  ren_tm (BW i s h st) (upr [ι (tW i)] ξ) = BW i s h (ren_args st ξ).
Proof.
  unfold BW. rewrite ren_And, ren_DW, ren_Dat, ren_WRec. f_equal. f_equal. f_equal.
  apply args_ext; intros σ z. rewrite !aget_ren, !ren_tms_ren. apply ren_tms_ext. intros ρ x.
  unfold rcomp, wk. rewrite upr_vr. reflexivity.
Qed.

Lemma appBW i s h {Γ} (Ξ : list (form Γ)) (st : args hsym Γ (steps i s)) (u : tm Γ (tW i)) :
  Ξ ⊢ App (wW i) (Lam (wW i) (BW i s h st)) u -> Ξ ⊢ And (DW i u) (Dat s (D s) (WRec i s h u st)).
Proof. intros H. rewrite <- BW_inst. eapply d_conv'; [apply beta'|exact H]. Qed.

Lemma appBW_inv i s h {Γ} (Ξ : list (form Γ)) (st : args hsym Γ (steps i s)) (u : tm Γ (tW i)) :
  Ξ ⊢ And (DW i u) (Dat s (D s) (WRec i s h u st)) -> Ξ ⊢ App (wW i) (Lam (wW i) (BW i s h st)) u.
Proof. intros H. rewrite <- BW_inst in H. eapply d_conv'; [apply conv_sym, beta'|exact H]. Qed.

(** Les arguments du pas sont relativisés. *)
Lemma sbuild_D i s {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) (R : tm Γ (tW i) -> tm Γ s) bs
  (a : args hsym Γ (cargs i bs)) :
  (forall h, In h (chyps i X bs a) -> Ξ ⊢ h) ->
  (forall y, Ξ ⊢ App (wW i) X y -> Ξ ⊢ DW i y) ->
  (forall y, Ξ ⊢ App (wW i) X y -> Ξ ⊢ Dat s (D s) (R y)) ->
  forall σ (z : var (sargs i s bs) σ), Ξ ⊢ DAt σ (aget z (sbuild i s R bs a)).
Proof.
  intros Hh HD HR. revert a Hh; induction bs as [|[|] bs IH]; intros a Hh; cbn [Inductive.sargs sbuild].
  - intros σ z; destruct (var_nil z).
  - refine (var_inv _ _ _).
    + apply Hh. left. reflexivity.
    + intros σ y. apply (IH (atl a)). intros h' Hh'. apply Hh. right. exact Hh'.
  - refine (var_inv _ _ _); [|refine (var_inv _ _ _)].
    + cbn [aget ahd DAt]. rewrite Dat_W. apply HD, Hh. left. reflexivity.
    + cbn [aget ahd atl DAt]. apply HR, Hh. left. reflexivity.
    + intros σ y. apply (IH (atl a)). intros h' Hh'. apply Hh. right. exact Hh'.
Qed.

(** ** Le lemme fondamental *)

Lemma fundamental :
  (forall Δ s (t : tm Δ s), sorted Δ -> forall Γ (w : vec hsym Δ Γ) Ξ, Hw w Ξ ->
     Ξ ⊢ Dat s (D s) (vsubst t w)) /\
  (forall Δ Θ (ar : args hsym Δ Θ), forall σ (z : var Θ σ), sorted (dom σ ++ Δ) ->
     forall Γ (w : vec hsym (dom σ ++ Δ) Γ) Ξ, Hw w Ξ ->
     Ξ ⊢ Dat (cod σ) (D (cod σ)) (vsubst (aget z ar) w)).
Proof.
  apply tm_args_ind.
  - (* variable *)
    intros Δ σ x ar _ Hs Γ w Ξ Hw. pose proof (Hs σ x) as E. destruct σ as [Dm b]. cbn [dom] in E. subst Dm.
    rewrite (args_nil ar). change (Ξ ⊢ Dat b (D b) (vsubst (var0 (Sym := hsym) x) w)).
    rewrite vsubst_var0. exact (Hw _ x).
  - (* symbole *)
    intros Δ σ c ar IH Hs Γ w Ξ Hw.
    destruct c as [a b|a b| | |s e| | | | | |s|s|s|i bs m|i s e]; try apply dat_O.
    + (* λ *)
      rewrite (args_eta ar), (args_nil (atl ar)). set (u := ahd ar).
      change (tsym (h_lam a b) (acons u anil)) with (Lam (w_ab a b) (Γ := Δ) u).
      rewrite vsubst_Lam, vsubst_tms_vup. cbn [dom].
      apply arr_intro.
      eapply d_conv'; [|exact (IH (Spec [ι a] b) vz (sorted_cons a Δ Hs) _ (vup [ι a] w) _ (hw_up a w Ξ Hw))].
      apply conv_Dat, conv_sym. cbn [aget ahd].
      eapply conv_trans; [apply beta'|].
      pose proof (vsubst_shift_inst1 (Sym := hsym) a b (vsubst u (vup [ι a] w))) as E.
      unfold ren_tms in E. cbn [dom] in E.
      exact (eq_ind_r (fun t => conv FC t (vsubst u (vup [ι a] w))) (conv_refl FC _) E).
    + (* app *)
      rewrite (args_eta ar), (args_eta (atl ar)), (args_nil (atl (atl ar))).
      set (f := ahd ar). set (u := ahd (atl ar)).
      change (tsym (h_app a b) (acons f (acons u anil))) with (App (w_ab a b) (Γ := Δ) f u).
      rewrite vsubst_App. apply arr_elim.
      * exact (IH (ι (tarr a b)) vz Hs Γ w Ξ Hw).
      * exact (IH (ι a) (vs vz) Hs Γ w Ξ Hw).
    + (* 0 *)
      rewrite (args_nil ar). apply nat_zero.
    + (* S *)
      rewrite (args_eta ar), (args_nil (atl ar)). set (u := ahd ar).
      change (tsym h_succ (acons u anil)) with (Succ (Sym := hsym) (Γ := Δ) u).
      rewrite vsubst_Succ. apply nat_succ. exact (IH (ι tN) vz Hs Γ w Ξ Hw).
    + (* rec *)
      rewrite (args_eta ar), (args_eta (atl ar)), (args_eta (atl (atl ar))), (args_nil (atl (atl (atl ar)))).
      set (z := ahd ar). set (st := ahd (atl ar)). set (n := ahd (atl (atl ar))).
      pose (h := (conj Logic.I e : @rec_ok ty hsym h_functional h_graded omega s)).
      change (tsym (h_rec s e) (acons z (acons st (acons n anil)))) with (Rec (N := tN) s h (Γ := Δ) z st n).
      rewrite vsubst_Rec, vsubst_tms_vup. cbn [dom].
      pose proof (IH (ι s) vz Hs Γ w Ξ Hw) as IHz. cbn [aget ahd] in IHz.
      pose proof (IH (ι tN) (vs (vs vz)) Hs Γ w Ξ Hw) as IHn. cbn [aget ahd atl] in IHn.
      assert (IHst : forall Γ0 (w0 : vec hsym (Λst s ++ Δ) Γ0) (Ξ0 : list (form Γ0)), Closure.Hw w0 Ξ0 ->
                       deriv FC tO free_rules Γ0 Ξ0 (Dat s (D s) (vsubst st w0))).
      { intros Γ0 w0 Ξ0 Hw0. exact (IH (Spec (Λst s) s) (vs vz) (sorted_cons tN _ (sorted_cons s _ Hs)) Γ0 w0 Ξ0 Hw0). }
      clear IH. set (z' := vsubst z w). set (st' := vsubst st (vup (Λst s) w)). set (n' := vsubst n w).
      nd and_E2. apply appB. apply nat_elim; [exact IHn| |].
      * apply appB_inv. nd and_I; [apply nat_zero|].
        eapply d_conv'; [apply conv_Dat, conv_sym, rec0'|exact IHz].
      * unfold Step. apply all_I'. nd imp_I.
        rewrite ren_LamB.
        set (z'' := ren_tm z' (wk [ι tN])). set (st'' := ren_tm st' (upr (Λst s) (wk [ι tN]))).
        set (Ξ' := @App ty hsym h_functional tN tO XN wN _ (@Lam ty hsym h_functional tN tO XN wN _ (mkB s h z'' st'')) (var0 vz) :: wk_list [ι tN] Ξ).
        assert (Hx : deriv FC tO free_rules (ι tN :: Γ) Ξ'
                       (And (Dat tN NatF (var0 vz)) (Dat s (D s) (Rec s h z'' st'' (var0 vz))))).
        { apply appB. nd hyp. left; reflexivity. }
        apply appB_inv. nd and_I; [apply nat_succ; nd and_E1; exact Hx|].
        eapply d_conv'; [apply conv_Dat, conv_sym, recS'|].
        set (R := Rec s h z'' st'' (var0 vz)).
        assert (EW : vsubst st'' (@acons _ hsym _ (ι tN) _ (var0 vz) (@acons _ hsym _ (ι s) _ R (vid (ι tN :: Γ))))
                     = vsubst st (@acons _ hsym _ (ι tN) _ (var0 vz) (@acons _ hsym _ (ι s) _ R (vren w (wk [ι tN]))))).
        { clearbody R. unfold st'', st'. rewrite ren_vsubst, vren_vup, vsubst_vsubst. f_equal.
          etransitivity;
            [exact (vup_cat (Λst s) (vren w (wk [ι tN]))
                      (@acons _ hsym _ (ι tN) _ (var0 (Sym := hsym) (Θ := ι tN :: Γ) vz)
                         (@acons _ hsym _ (ι s) _ R anil)) (vid (ι tN :: Γ)))|].
          rewrite vcomp_vid_r. reflexivity. }
        refine (eq_ind _ (fun t => deriv FC tO free_rules _ Ξ' (Dat s (D s) t)) _ _ (eq_sym EW)).
        apply IHst.
        apply hw_cons; [nd and_E1; exact Hx|]. apply hw_cons; [nd and_E2; exact Hx|].
        eapply hw_weaken; [exact (hw_wk [ι tN] w Ξ Hw)|]. intros x Hin; right; exact Hin.
    + (* constructeur *)
      change (Ξ ⊢ Dat (tW i) (D (tW i)) (Con i bs m (vsubst_args ar w))). rewrite Dat_W.
      apply DW_con. apply vars_dfacts. intros σ z. rewrite aget_vsubst_args.
      pose proof (cargs_iota i bs σ z) as E. destruct σ as [Dm b]. cbn [dom] in E. subst Dm.
      cbn [DAt]. rewrite vsubst_tms_nil. exact (IH (ι b) z Hs Γ w Ξ Hw).
    + (* rec_W *)
      pose (h := (conj Logic.I e : rec_ok (Sym := hsym) omega s)).
      rewrite (args_eta ar).
      change (tsym (h_wrec i s e) (acons (ahd ar) (atl ar))) with (WRec i s h (ahd ar) (atl ar)).
      rewrite vsubst_WRec.
      pose proof (IH (ι (tW i)) vz Hs Γ w Ξ Hw) as IHt. cbn [aget cod] in IHt. rewrite Dat_W in IHt.
      set (t' := vsubst (ahd ar) w) in *. set (st' := vsubst_args (atl ar) w).
      assert (IHst : forall bs (c : mem (dsc i) bs) Γ0 (w0 : vec hsym (sargs i s bs ++ Δ) Γ0) (Ξ0 : list (form Γ0)),
                 Closure.Hw w0 Ξ0 ->
                 deriv FC tO free_rules Γ0 Ξ0 (Dat s (D s) (vsubst (aget (mvar (step_spec tN tW i s) c) (atl ar)) w0))).
      { intros bs c Γ0 w0 Ξ0 Hw0.
        exact (IH (step_spec tN tW i s bs) (vs (mvar (step_spec tN tW i s) c)) (sorted_sargs i s bs Δ Hs) Γ0 w0 Ξ0 Hw0). }
      clear IH.
      nd and_E2. apply (appBW i s h Ξ st' t').
      apply DW_elim; [exact IHt|].
      intros cl Hcl. unfold Closs in Hcl. apply in_map_iff in Hcl as ([bs c] & <- & _). cbn [projT1 projT2].
      apply Clos_intro.
      set (A := lvars (cargs i bs) Γ).
      set (st'' := ren_args st' (wk (cargs i bs))).
      assert (EX : ren_tm (Lam (wW i) (BW i s h st')) (wk (cargs i bs)) = Lam (wW i) (BW i s h st'')).
      { exact (f_equal (fun B => Lam (wW i) B) (ren_BW i s h st' (wk (cargs i bs)))). }
      rewrite EX.
      set (X := @Lam ty hsym h_functional (tW i) tO (XW i) (wW i) _ (BW i s h st'')).
      set (Ξc := rev (chyps i X bs A) ++ wk_list (cargs i bs) Ξ).
      assert (Hh : forall h0, In h0 (chyps i X bs A) -> deriv FC tO free_rules _ Ξc h0).
      { intros h0 Hin. nd hyp. apply in_or_app; left. apply in_rev in Hin. exact Hin. }
      assert (HXD : forall y, deriv FC tO free_rules _ Ξc (App (wW i) X y) -> deriv FC tO free_rules _ Ξc (DW i y)).
      { intros y Hy. nd and_E1. apply appBW. exact Hy. }
      assert (HXR : forall y, deriv FC tO free_rules _ Ξc (App (wW i) X y) ->
                              deriv FC tO free_rules _ Ξc (Dat s (D s) (WRec i s h y st''))).
      { intros y Hy. nd and_E2. apply appBW. exact Hy. }
      apply appBW_inv. nd and_I.
      * apply DW_con. apply (chyps_dfacts i Ξc X); [exact Hh|exact HXD].
      * eapply d_conv'; [apply conv_Dat, conv_sym, (wrec_conv free_calc_rules)|].
        rewrite happ_vsubst.
        unfold st''. rewrite aget_ren. unfold st'. rewrite aget_vsubst_args.
        set (u := aget (mvar (step_spec tN tW i s) c) (atl ar)).
        set (S := sbuild i s (fun y => WRec i s h y (ren_args (vsubst_args (atl ar) w) (wk (cargs i bs)))) bs A).
        assert (EW : vsubst (ren_tms (vsubst_tms u w) (wk (cargs i bs))) (vcat (sargs i s bs) S (vid (cargs i bs ++ Γ)))
                     = vsubst u (vcat (sargs i s bs) S (vren w (wk (cargs i bs))))).
        { unfold ren_tms. rewrite vsubst_tms_vup. cbn [dom step_spec].
          rewrite ren_vsubst, vren_vup, vsubst_vsubst, vup_cat, vcomp_vid_r. reflexivity. }
        cbn [dom cod step_spec] in EW |- *. rewrite EW.
        apply IHst. apply hw_vcat.
        -- apply (sbuild_D i s Ξc X); [exact Hh|exact HXD|exact HXR].
        -- eapply hw_weaken; [exact (hw_wk (cargs i bs) w Ξ Hw)|]. intros x Hin; apply in_or_app; right; exact Hin.
  - (* anil *)
    intros Δ σ z. destruct (var_nil z).
  - (* acons *)
    intros Δ σ Θ u IHu ar IHa τ z. revert τ z.
    refine (@var_inv _ σ Θ (fun τ z => sorted (dom τ ++ Δ) -> forall Γ (w : vec hsym (dom τ ++ Δ) Γ) Ξ, Hw w Ξ ->
              Ξ ⊢ Dat (cod τ) (D (cod τ)) (vsubst (aget z (acons u ar)) w)) IHu _).
    intros τ y. exact (IHa τ y).
Qed.

(** ** Le lemme de clôture *)

Corollary closure {Δ s} (t : tm Δ s) (Ξ : list (form Δ)) :
  sorted Δ -> (forall σ (x : var Δ σ), Ξ ⊢ DAt σ (eta σ x)) -> Ξ ⊢ Dat s (D s) t.
Proof.
  intros Hs H. rewrite <- (vsubst_vid t). apply (proj1 fundamental _ _ t Hs _ (vid Δ) Ξ).
  intros σ x. rewrite aget_vid. apply H.
Qed.

End Closure.
