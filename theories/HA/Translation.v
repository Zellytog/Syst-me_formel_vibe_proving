(** * Traduction de HA_ω^{ω,ω} dans le système libre (ω,ω,ω)

    HA (fichier [Signature.v]) : logique intuitionniste d'ordre (ω,ω),
    récurseurs de hauteur ω, β, règles de rec, récurrence et S t ≠ 0.
    Free : la même logique d'ordre (ω,ω) et le même calcul, *sans* règle
    arithmétique, mais avec la réécriture S t = 0 ~ ⊥.

    La traduction [Rel] est l'identité sur les symboles, sauf les
    quantificateurs, relativisés à D (∀x. D_s(x) ⇒ φ, ∃x. D_s(x) ∧ φ), où
    D_N est le prédicat imprédicatif des entiers. Chaque variable x : s du
    contexte apporte l'hypothèse D_s(x).

    Toutes les règles traduites sont admissibles dans Free, pour les
    contextes de sortes ([sctx]) :
    - les règles propositionnelles et d'égalité se traduisent en elles-mêmes ;
    - ∀I/∃E : l'hypothèse D_s(x) est fournie par la prémisse traduite ;
    - ∀E/∃I : D_s(t) est donné par le lemme de clôture ([closure]) ;
    - la récurrence : par D_N(t), instancié en λm. D_N(m) ∧ φ(m) ;
    - S t ≠ 0 : par la conversion S t = 0 ~ ⊥.
    On conclut par [interp_sound_on] (fichier [Admissible.v]). *)

From Stdlib Require Import List. Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Extensions Require Import Conservativity Same.
From SF.HA Require Import Signature Closure.
Local Notation ι a := (Spec [] a).

Section Translation.
Context {Ind : Type} {dsc : Ind -> list (list bool)}.
Local Notation ty := (Signature.ty Ind).
Local Notation hsym := (Signature.hsym dsc).
Local Notation σφ s := (Spec [ι s] tO).
Local Notation tm := (Terms.tm hsym).
Local Notation form := (form hsym tO).
Local Notation D := (Signature.D (dsc := dsc)).
Local Notation Rel := (Signature.Rel (dsc := dsc)).
Local Notation HA := (Signature.HA (dsc := dsc)).
Local Notation Free := (Signature.Free (dsc := dsc)).
Local Notation free_rules := (Signature.free_rules (dsc := dsc)).
Local Notation free_calc_rules := (Signature.free_calc_rules (dsc := dsc)).
Local Notation ha_rules := (Signature.ha_rules (dsc := dsc)).
Local Notation NatF := (Signature.NatF (dsc := dsc)).
Local Notation keep := (Signature.keep (dsc := dsc)).
Local Notation rel_interp := (Signature.rel_interp (dsc := dsc)).

Lemma inst_app1_up (s : ty) {Θ Γ} (w : vec hsym (σφ s :: Θ) Γ) :
  vsubst (app1 (s := s) (Θ := ι s :: σφ s :: Θ) (vs vz) (var0 vz)) (vup [ι s] w) = aget vz w.
Proof.
  rewrite vsubst_app1. unfold vup, vren. cbn [app aget atl ahd vcat etas eta vmap].

  exact (vsubst_shift_inst1 s tO (aget vz w)).
Qed.

Lemma relAll_inst (s : ty) {Γ} (φ : tms hsym Γ (σφ s)) :
  vsubst (relAll s) (@acons _ hsym Γ (σφ s) [] φ anil) = All s (Imp (Dat s (D s) (var0 vz)) φ).
Proof.
  unfold relAll, Imp. rewrite vsubst_All', vsubst_Bin, vsubst_Dat, vsubst_var0.
  rewrite (inst_app1_up s (Θ := []) (acons φ anil)).
  reflexivity. Qed.


Lemma relEx_inst (s : ty) {Γ} (φ : tms hsym Γ (σφ s)) :
  vsubst (relEx s) (@acons _ hsym Γ (σφ s) [] φ anil) = Ex s (And (Dat s (D s) (var0 vz)) φ).
Proof.
  unfold relEx, And. rewrite vsubst_Ex', vsubst_Bin, vsubst_Dat, vsubst_var0.
  rewrite (inst_app1_up s (Θ := []) (acons φ anil)). reflexivity.
Qed.

Local Notation FC := (generated free_calc_rules).
Local Notation "Ξ ⊢ φ" := (deriv FC tO free_rules _ Ξ φ) (at level 70).
Local Tactic Notation "nd" uconstr(t) := eapply t; try typeclasses eauto.

Lemma ren_vl_Dat (s : ty) {Γ} : ren_tm (D s) (fun τ (z : var [ι s] τ) => vl Γ z) = Dat s (D s) (var0 vz).
Proof.
  unfold Dat. rewrite ren_as_vsubst. f_equal.
Qed.

Lemma sorted_cm (Γ : ctx ty) : sctx Γ -> sorted Γ.
Proof.
  induction 1 as [|σ Γ0 Hσ HΓ IH].
  - intros σ x. destruct (var_nil x).
  - destruct σ as [d a]. cbn [dom] in Hσ. subst d. apply sorted_cons, IH.
Qed.

Lemma rel_hyps_D (Γ : ctx ty) : sctx Γ -> forall σ (x : var Γ σ), rel_hyps Rel Γ ⊢ DAt σ (eta σ x).
Proof.
  induction 1 as [|σ0 Γ0 Hσ HΓ IH].
  - intros σ x. destruct (var_nil x).
  - destruct σ0 as [d a]. cbn [dom] in Hσ. subst d.
    change (rel_hyps Rel (ι a :: Γ0)) with
      (ren_tm (D a) (fun τ (z : var [ι a] τ) => vl Γ0 z) :: wk_list [ι a] (rel_hyps Rel Γ0)).
    rewrite ren_vl_Dat.
    change (forall σ (x : var (ι a :: Γ0) σ),
              (Dat a (D a) (var0 vz) :: wk_list [ι a] (rel_hyps Rel Γ0)) ⊢ DAt σ (eta σ x)).
    refine (var_inv _ _ _).
    + nd hyp. left; reflexivity.
    + intros σ y. 
      change (vs y) with (wk [ι a] σ y).
      rewrite <- eta_ren, <- ren_DAt.
      eapply deriv_weaken; [exact (deriv_wk _ _ _ [ι a] (IH σ y))|]. intros z Hz; right; exact Hz.
Qed.

(** Les termes sans quantificateur sont traduits en eux-mêmes. *)
Lemma pure_eta (σ : spec ty) : forall Γ (x : var Γ σ), pure keep (eta σ x).
Proof.
  induction σ as [Dm c IH] using spec_rect'. intros Γ x. rewrite eta_Spec. cbn [pure].
  assert (H : forall Ξ (f : forall τ, var Dm τ -> var Ξ τ), pure_args keep (etas Dm f)).
  { clear x. induction Dm as [|τ Dm IHD]; intros Ξ f; cbn [etas pure_args]; [exact I|].
    split; [apply (IH τ vz)|apply IHD; intros ρ z; exact (IH ρ (vs z))]. }
  apply H.
Qed.

Lemma pure_etas Λ {Ξ} (f : forall τ, var Λ τ -> var Ξ τ) : pure_args keep (etas Λ f).
Proof.
  induction Λ as [|τ Λ IH]; cbn [etas pure_args]; [exact I|]. split; [apply pure_eta|apply IH].
Qed.

Lemma pure_sbuild i s {Θ} (R : tm Θ (tW i) -> tm Θ s) :
  (forall y, pure keep y -> pure keep (R y)) ->
  forall bs (a : args hsym Θ (Inductive.cargs tN tW i bs)), pure_args keep a -> pure_args keep (sbuild i s R bs a).
Proof.
  intros HR bs. induction bs as [|[|] bs IH]; intros a Ha; cbn [sbuild pure_args]; [exact I| |].
  - change (args hsym Θ (ι tN :: Inductive.cargs tN tW i bs)) in a. rewrite (args_eta a) in Ha.
    destruct Ha as [H1 H2]. split; [exact H1|apply IH, H2].
  - change (args hsym Θ (ι (tW i) :: Inductive.cargs tN tW i bs)) in a. rewrite (args_eta a) in Ha.
    destruct Ha as [H1 H2]. split; [exact H1|split; [apply HR, H1|apply IH, H2]].
Qed.

Lemma tr_pure' {Γ s} (t : tm Γ s) : pure keep t -> tr rel_interp t = t.
Proof. apply tr_pure, rel_keep. Qed.

Lemma HC : forall Γ s (t u : Terms.tm hsym Γ s), conv (l_calc hsym HA) t u ->
  conv (l_calc hsym Free) (tr (sl_sig Rel) t) (tr (sl_sig Rel) u).
Proof.
  apply interp_conv. intros [[[[s h] [|]] | [a [b [c w]]]] | [i [s [h [bs c]]]]]; [| |destruct w|].
  - exact (generated_rule free_calc_rules (inl (inl (inl (existT _ s h, true))))).
  - exact (generated_rule free_calc_rules (inl (inl (inl (existT _ s h, false))))).
  - exact (generated_rule free_calc_rules (inl (inl (inr (existT _ a (existT _ b (existT _ _ (tarrw_i a b)))))))).
  - cbn [ha_calc_rules crsum wrec_rules wrec_rule r_lhs r_rhs]. rewrite !tr_pure'.
    + exact (generated_rule free_calc_rules (inl (inr (existT _ i (existT _ s (existT _ h (existT _ bs c))))))).
    + unfold wrec_rhs. cbn [pure]. apply pure_sbuild; [|apply pure_etas].
      intros y Hy. cbn [pure pure_args]. split; [reflexivity|split; [exact Hy|apply pure_etas]].
    + cbn [pure pure_args]. split; [reflexivity|split; [split; [reflexivity|apply pure_etas]|apply pure_etas]].
Qed.

Lemma sctx_cargs i bs (Γ : ctx ty) : sctx Γ -> sctx (Inductive.cargs tN tW i bs ++ Γ).
Proof. intros H. apply Forall_app; split; [|exact H]. induction bs; constructor; [reflexivity|assumption]. Qed.

Lemma HQ : forall i p Γ, In p (d_prems (l_rules hsym HA i)) -> sctx Γ -> sctx (p_ext p ++ Γ).
Proof.
  intros i p Γ Hin HΓ.
  destruct i as [j|[[]|[[]|i]]].
  - apply Forall_app; split; [|exact HΓ].
    destruct j as [[[|]|[[| |]|[[| |]|[[]|[]]]]]|[[k i]|[[k i]|[k i]]]];
      [| | | | | | | | | |destruct i|destruct i|destruct i];
      cbn in Hin; repeat (destruct Hin as [<-|Hin]; [cbn; repeat constructor|]); destruct Hin.
  - apply Forall_app; split; [|exact HΓ].
    cbn in Hin; repeat (destruct Hin as [<-|Hin]; [cbn; repeat constructor|]); destruct Hin.
  - cbn in Hin; repeat (destruct Hin as [<-|Hin]; [cbn; repeat constructor; exact HΓ|]); destruct Hin.
  - cbn [l_rules HA ha_rules rsum wind_rules wind_rule d_prems] in Hin.
    apply in_map_iff in Hin as ([bs c] & <- & _). cbn [ind_prem p_ext premx projT1]. apply sctx_cargs, HΓ.
Qed.

Local Notation RH := (rel_hyps Rel).

Lemma vec1_eta {Γ σ} (w : vec hsym [σ] Γ) : w = @acons _ hsym Γ σ [] (aget vz w) anil.
Proof. rewrite (args_eta w), (args_nil (atl w)). reflexivity. Qed.

Lemma adm_allI s h : tr_rule_adm Rel sctx (ha_rules (inl (inr (inl (existT _ s h, AllI))))).
Proof.
  intros Γ HΓ Ξ w Hp. specialize (Hp _ (or_introl eq_refl)).
  change (vec hsym [σφ s] Γ) in w.
  change (deriv FC tO free_rules (ι s :: Γ)
    (vsubst (ren_tm (D s) (fun τ (z : var [ι s] τ) => vl [σφ s] z)) (vup [ι s] w) :: wk_list [ι s] (RH Γ ++ Ξ))
    (vsubst (app1 (s := s) (Θ := ι s :: [σφ s]) (vs vz) (var0 vz)) (vup [ι s] w))) in Hp.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (vsubst (relAll s) (vid _)) w)).
  rewrite vsubst_vid, (vec1_eta w), relAll_inst.
  rewrite ren_vl_Dat, vsubst_Dat, vsubst_var0, inst_app1_up in Hp.
  apply all_I'. nd imp_I. exact Hp.
Qed.

Lemma closure_ctx {Γ} (HΓ : sctx Γ) (Ξ : list (form Γ)) s (t : tm Γ s) :
  (RH Γ ++ Ξ) ⊢ Dat s (D s) t.
Proof.
  apply closure; [apply sorted_cm, HΓ|]. intros σ x.
  eapply deriv_weaken; [apply rel_hyps_D, HΓ|]. intros z Hz; apply in_or_app; left; exact Hz.
Qed.

Lemma vcomp_eta0 {Θ Γ σ} (w : vec hsym (σ :: Θ) Γ) :
  vcomp (@acons _ hsym (σ :: Θ) σ [] (eta σ vz) anil) w = @acons _ hsym Γ σ [] (aget vz w) anil.
Proof.
  apply vec_ext; intros τ x; revert τ x. refine (var_inv _ _ _); [|intros τ y; destruct (var_nil y)].
  unfold vget. rewrite aget_vcomp. exact (vsubst_eta (Sym := hsym) (vz (Γ := Θ)) w).
Qed.

Lemma adm_allE s h : tr_rule_adm Rel sctx (ha_rules (inl (inr (inl (existT _ s h, AllE))))).
Proof.
  intros Γ HΓ Ξ w Hp. specialize (Hp _ (or_introl eq_refl)).
  change (vec hsym [σφ s; ι s] Γ) in w.
  change (deriv FC tO free_rules ([] ++ Γ) (vsubst_list [] (vup [] w) ++ wk_list [] (RH Γ ++ Ξ))
    (vsubst (vsubst (relAll s) (@acons _ hsym [σφ s; ι s] (σφ s) [] (eta (σφ s) vz) anil)) (vup [] w))) in Hp.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (app1 (s := s) (Θ := [σφ s; ι s]) vz (var0 (vs vz))) w)).
  rewrite vup_nil, wk_list_nil, vsubst_vsubst, vcomp_eta0, relAll_inst in Hp. cbn [vsubst_list map app] in Hp.
  rewrite vsubst_app1.
  pose proof (all_E' s _ _ (aget (vs vz) w) Hp) as K.
  unfold Imp in K. rewrite vsubst_Bin, vsubst_Dat, vsubst_var0 in K. cbn [aget ahd inst1] in K.
  nd imp_E; [exact K|apply (closure_ctx HΓ)].
Qed.

Lemma adm_exI s h : tr_rule_adm Rel sctx (ha_rules (inl (inr (inr (inl (existT _ s h, ExI)))))).
Proof.
  intros Γ HΓ Ξ w Hp. specialize (Hp _ (or_introl eq_refl)).
  change (vec hsym [σφ s; ι s] Γ) in w.
  change (deriv FC tO free_rules ([] ++ Γ) (vsubst_list [] (vup [] w) ++ wk_list [] (RH Γ ++ Ξ))
    (vsubst (app1 (s := s) (Θ := [σφ s; ι s]) vz (var0 (vs vz))) (vup [] w))) in Hp.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ)
    (vsubst (vsubst (relEx s) (@acons _ hsym [σφ s; ι s] (σφ s) [] (eta (σφ s) vz) anil)) w)).
  rewrite vup_nil, wk_list_nil, vsubst_app1 in Hp. cbn [vsubst_list map app] in Hp.
  rewrite vsubst_vsubst, vcomp_eta0, relEx_inst.
  apply (ex_I' s _ _ (aget (vs vz) w)).
  unfold And. rewrite vsubst_Bin, vsubst_Dat, vsubst_var0. cbn [aget ahd inst1].
  nd and_I; [apply (closure_ctx HΓ)|exact Hp].
Qed.

Lemma adm_exE s h : tr_rule_adm Rel sctx (ha_rules (inl (inr (inr (inl (existT _ s h, ExE)))))).
Proof.
  intros Γ HΓ Ξ w Hp.
  pose proof (Hp _ (or_introl eq_refl)) as H1. pose proof (Hp _ (or_intror (or_introl eq_refl))) as H2. clear Hp.
  change (vec hsym [σφ s; ι tO] Γ) in w.
  change (deriv FC tO free_rules ([] ++ Γ) (vsubst_list [] (vup [] w) ++ wk_list [] (RH Γ ++ Ξ))
    (vsubst (vsubst (relEx s) (@acons _ hsym [σφ s; ι tO] (σφ s) [] (eta (σφ s) vz) anil)) (vup [] w))) in H1.
  change (deriv FC tO free_rules (ι s :: Γ)
    (vsubst (ren_tm (D s) (fun τ (z : var [ι s] τ) => vl [σφ s; ι tO] z)) (vup [ι s] w)
     :: vsubst (app1 (s := s) (Θ := ι s :: [σφ s; ι tO]) (vs vz) (var0 vz)) (vup [ι s] w)
     :: wk_list [ι s] (RH Γ ++ Ξ))
    (vsubst (var0 (Θ := ι s :: [σφ s; ι tO]) (vs (vs vz))) (vup [ι s] w))) in H2.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (var0 (Θ := [σφ s; ι tO]) (vs vz)) w)).
  rewrite vup_nil, wk_list_nil, vsubst_vsubst, vcomp_eta0, relEx_inst in H1. cbn [vsubst_list map app] in H1.
  rewrite ren_vl_Dat, vsubst_Dat, !vsubst_var0, inst_app1_up in H2.
  rewrite vsubst_var0.
  apply (ex_E' s _ _ _ H1).
  change (Dat s (D s) (var0 vz) :: aget vz w :: wk_list [ι s] (RH Γ ++ Ξ)
          ⊢ ren_tm (aget (vs vz) w) (wk [ι s])) in H2.
  apply (deriv_cut_gen _ _ _ H2). intros χ [<-|[<-|Hχ]].
  - nd and_E1. nd hyp. left; reflexivity.
  - nd and_E2. nd hyp. left; reflexivity.
  - nd hyp. right; exact Hχ.
Qed.

Local Notation XN := (tarr tN tO).
Local Notation wN := (w_ab tN tO).
Local Notation Nat t := (Dat tN NatF t).
Local Notation LamN B := (@Lam ty hsym h_functional tN tO XN wN _ B).
Local Notation AppN f u := (@App ty hsym h_functional tN tO XN wN _ f u).

Lemma inst_B {Γ} (φ : form (ι tN :: Γ)) (u : tm Γ tN) :
  vsubst (And (Nat (var0 vz)) φ) (inst1 u) = And (Nat u) (vsubst φ (inst1 u)).
Proof. unfold And. rewrite vsubst_Bin, vsubst_Dat, vsubst_var0. reflexivity. Qed.

Lemma inst_B' {Γ} (φ : form (ι tN :: Γ)) (u : tm (ι tN :: Γ) tN) :
  vsubst (ren_tm (And (Nat (var0 vz)) φ) (upr [ι tN] (wk [ι tN]))) (inst1 u)
  = And (Nat u) (vsubst (ren_tms (σ := σφ tN) φ (wk [ι tN])) (inst1 u)).
Proof. rewrite ren_And, ren_Dat, ren_var0. unfold And. rewrite vsubst_Bin, vsubst_Dat, vsubst_var0. reflexivity. Qed.

Lemma adm_ind : tr_rule_adm Rel sctx (ha_rules (inr (inl tt))).
Proof.
  intros Γ HΓ Ξ w Hp.
  pose proof (Hp _ (or_introl eq_refl)) as H1. pose proof (Hp _ (or_intror (or_introl eq_refl))) as H2. clear Hp.
  change (vec hsym [σφ tN; ι tN] Γ) in w.
  change (deriv FC tO free_rules ([] ++ Γ) (vsubst_list [] (vup [] w) ++ wk_list [] (RH Γ ++ Ξ))
    (vsubst (app1 (s := tN) (Θ := [σφ tN; ι tN]) vz Zero) (vup [] w))) in H1.
  change (deriv FC tO free_rules (ι tN :: Γ)
    (vsubst (ren_tm (D tN) (fun τ (z : var [ι tN] τ) => vl [σφ tN; ι tN] z)) (vup [ι tN] w)
     :: vsubst (app1 (s := tN) (Θ := ι tN :: [σφ tN; ι tN]) (vs vz) (var0 vz)) (vup [ι tN] w)
     :: wk_list [ι tN] (RH Γ ++ Ξ))
    (vsubst (app1 (s := tN) (Θ := ι tN :: [σφ tN; ι tN]) (vs vz) (Succ (var0 vz))) (vup [ι tN] w))) in H2.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (app1 (s := tN) (Θ := [σφ tN; ι tN]) vz (var0 (vs vz))) w)).
  rewrite vup_nil, wk_list_nil, vsubst_app1_gen, vsubst_Zero in H1. cbn [vsubst_list map app] in H1.
  rewrite ren_vl_Dat, vsubst_Dat, vsubst_var0, inst_app1_up, vsubst_app1_gen, vsubst_Succ, vsubst_var0 in H2.
  rewrite vsubst_app1. cbn [aget ahd atl] in *.
  set (φ := ahd w) in *. set (t := ahd (atl w)) in *.
  change (Nat (var0 vz) :: φ :: wk_list [ι tN] (RH Γ ++ Ξ)
          ⊢ vsubst (ren_tms (σ := σφ tN) φ (wk [ι tN])) (inst1 (Succ (var0 vz)))) in H2.
  set (B := And (Nat (var0 vz)) φ).
  set (X0 := LamN B).
  assert (Ht : RH Γ ++ Ξ ⊢ AppN X0 t).
  { apply nat_elim.
    - exact (closure_ctx HΓ Ξ tN t).
    - eapply d_conv'; [apply conv_sym, beta'|]. unfold B; rewrite inst_B.
      nd and_I; [apply nat_zero|exact H1].
    - unfold Step. apply all_I'. nd imp_I.
      change (ren_tm X0 (wk [ι tN])) with (LamN (ren_tm B (upr [ι tN] (wk [ι tN])))).
      set (L := AppN (LamN (ren_tm B (upr [ι tN] (wk [ι tN])))) (var0 vz) :: wk_list [ι tN] (RH Γ ++ Ξ)).
      assert (E : vsubst (ren_tm B (upr [ι tN] (wk [ι tN]))) (inst1 (var0 (Θ := ι tN :: Γ) vz))
                  = And (Nat (var0 vz)) φ).
      { unfold B. rewrite inst_B'. rewrite (vsubst_shift_inst1 tN tO φ). reflexivity. }
      assert (Hx : L ⊢ And (Nat (var0 vz)) φ).
      { rewrite <- E. eapply d_conv'; [apply beta'|]. nd hyp. left; reflexivity. }
      eapply d_conv'; [apply conv_sym, beta'|]. change (L ⊢ vsubst (ren_tm B (upr [ι tN] (wk [ι tN]))) (inst1 (Succ (var0 (Θ := ι tN :: Γ) vz)))). unfold B. rewrite inst_B'.
      nd and_I; [apply nat_succ; nd and_E1; exact Hx|].
      apply (deriv_cut_gen _ _ _ H2). intros χ [<-|[<-|Hχ]].
      + nd and_E1. exact Hx.
      + nd and_E2. exact Hx.
      + nd hyp. right; exact Hχ. }
  eapply d_conv' in Ht; [|apply beta']. unfold B in Ht. rewrite inst_B in Ht.
  nd and_E2. exact Ht.
Qed.


Lemma adm_peano : tr_rule_adm Rel sctx (ha_rules (inr (inr (inl tt)))).
Proof.
  intros Γ HΓ Ξ w Hp. specialize (Hp _ (or_introl eq_refl)).
  change (vec hsym [ι tN] Γ) in w.
  change (deriv FC tO free_rules ([] ++ Γ) (vsubst_list [] (vup [] w) ++ wk_list [] (RH Γ ++ Ξ))
    (vsubst (r_lhs neq_rule) (vup [] w))) in Hp.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (r_rhs (free_calc_rules (inr tt))) w)).
  rewrite vup_nil, wk_list_nil in Hp. cbn [vsubst_list map app] in Hp.
  eapply d_conv'; [exact (generated_instance free_calc_rules (inr tt) w)|exact Hp].
Qed.

(** ** La récurrence sur les types inductifs *)

Local Notation XW i := (tarr (tW i) tO).
Local Notation wW i := (w_ab (tW i) tO).
Local Notation cargs i bs := (Inductive.cargs tN tW i bs).

Lemma ltr_pure {Γ} (φ : form Γ) : pure keep φ -> ltr Rel φ = φ.
Proof. intros H. unfold ltr, pcast. cbn [sl_prop Rel]. apply tr_pure', H. Qed.

Lemma map_ltr_ihyps i {Γ} (Φ : tm Γ (tW i) -> form Γ) bs (a : args hsym Γ (cargs i bs)) :
  (forall y, pure keep y -> pure keep (Φ y)) -> pure_args keep a ->
  map (ltr Rel) (ihyps tO i Φ bs a) = ihyps tO i Φ bs a.
Proof.
  intros HΦ. revert a; induction bs as [|[|] bs IH]; intros a Ha; cbn [ihyps map]; [reflexivity| |].
  - change (args hsym Γ (ι tN :: cargs i bs)) in a. rewrite (args_eta a) in Ha. apply IH, Ha.
  - change (args hsym Γ (ι (tW i) :: cargs i bs)) in a. rewrite (args_eta a) in Ha.
    destruct Ha as [H1 H2]. rewrite ltr_pure, IH; [reflexivity|exact H2|apply HΦ, H1].
Qed.

Lemma ren_lvars (σ : spec ty) Λ Γ :
  ren_args (lvars (Sym := hsym) Λ Γ) (wk [σ]) = etas Λ (fun ρ z => vs (vl Γ z)).
Proof.
  apply args_ext; intros τ z. unfold lvars. rewrite aget_ren, !aget_etas, eta_ren. reflexivity.
Qed.

Lemma rel_ext_cargs i bs Γ : rel_ext Rel (cargs i bs) Γ = dfacts i bs (lvars (cargs i bs) Γ).
Proof.
  induction bs as [|[|] bs IH]; [reflexivity| |].
  - cbn [rel_ext Inductive.cargs map]. cbn [sl_rel Rel Dspec asrt]. rewrite ren_vl_Dat.
    change (Dat tN (D tN) (var0 vz) :: wk_list [ι tN] (rel_ext Rel (cargs i bs) Γ)
            = Dat tN NatF (var0 vz) :: dfacts i bs (etas (cargs i bs) (fun ρ z => vs (vl Γ z)))).
    f_equal. rewrite IH, <- (ren_lvars (ι tN)). apply ren_dfacts.
  - cbn [rel_ext Inductive.cargs map]. cbn [sl_rel Rel Dspec asrt]. rewrite ren_vl_Dat, Dat_W.
    change (DW i (var0 vz) :: wk_list [ι (tW i)] (rel_ext Rel (cargs i bs) Γ)
            = DW i (var0 vz) :: dfacts i bs (etas (cargs i bs) (fun ρ z => vs (vl Γ z)))).
    f_equal. rewrite IH, <- (ren_lvars (ι (tW i))). apply ren_dfacts.
Qed.

Lemma ihyps_chyps i {Γ} (Ξ : list (form Γ)) (X : tm Γ (XW i)) (Φ : tm Γ (tW i) -> form Γ) bs
  (a : args hsym Γ (cargs i bs)) :
  (forall h, In h (chyps i X bs a) -> Ξ ⊢ h) -> (forall y, Ξ ⊢ App (wW i) X y -> Ξ ⊢ Φ y) ->
  forall h, In h (ihyps tO i Φ bs a) -> Ξ ⊢ h.
Proof.
  revert a; induction bs as [|[|] bs IH]; intros a Hh HΦ h Hin; cbn [chyps ihyps] in *; [destruct Hin| |].
  - apply (IH (atl a)); [intros; apply Hh; right; assumption|exact HΦ|exact Hin].
  - destruct Hin as [<-|Hin]; [apply HΦ, Hh; left; reflexivity|].
    apply (IH (atl a)); [intros; apply Hh; right; assumption|exact HΦ|exact Hin].
Qed.

Definition BX i {Γ} (φ : form (ι (tW i) :: Γ)) : tm Γ (XW i) :=
  @Lam ty hsym h_functional (tW i) tO (XW i) (wW i) _ (And (DW i (var0 vz)) φ).

Lemma appBX i {Γ} (Ξ : list (form Γ)) (φ : form (ι (tW i) :: Γ)) (u : tm Γ (tW i)) :
  Ξ ⊢ App (wW i) (BX i φ) u -> Ξ ⊢ And (DW i u) (vsubst φ (inst1 u)).
Proof.
  intros H. eapply d_conv' in H; [|apply beta']. unfold And in H. rewrite vsubst_Bin, vsubst_DW, vsubst_var0 in H.
  exact H.
Qed.

Lemma appBX_inv i {Γ} (Ξ : list (form Γ)) (φ : form (ι (tW i) :: Γ)) (u : tm Γ (tW i)) :
  Ξ ⊢ And (DW i u) (vsubst φ (inst1 u)) -> Ξ ⊢ App (wW i) (BX i φ) u.
Proof.
  intros H. eapply d_conv'; [apply conv_sym, beta'|]. unfold And. rewrite vsubst_Bin, vsubst_DW, vsubst_var0.
  exact H.
Qed.

Lemma ren_BX i {Γ Δ} (φ : form (ι (tW i) :: Γ)) (ξ : ren Γ Δ) :
  ren_tm (BX i φ) ξ = BX i (ren_tm φ (upr [ι (tW i)] ξ)).
Proof.
  unfold BX.
  change (@Lam ty hsym h_functional (tW i) tO (XW i) (wW i) _ (ren_tm (And (DW i (var0 vz)) φ) (upr [ι (tW i)] ξ))
          = @Lam ty hsym h_functional (tW i) tO (XW i) (wW i) _ (And (DW i (var0 vz)) (ren_tm φ (upr [ι (tW i)] ξ)))).
  rewrite ren_And, ren_DW. reflexivity.
Qed.

Lemma adm_wind i : tr_rule_adm Rel sctx (ha_rules (inr (inr (inr i)))).
Proof.
  intros Γ HΓ Ξ w Hp.
  change (vec hsym (iΘ (W := tW) tO i) Γ) in w.
  change (deriv FC tO free_rules Γ (RH Γ ++ Ξ) (vsubst (app1 (s := tW i) (Θ := iΘ (W := tW) tO i) vz (var0 (vs vz))) w)).
  rewrite vsubst_app1. cbn [aget ahd atl] in *.
  set (φ := ahd w). set (t := ahd (atl w)).
  enough (Ht : RH Γ ++ Ξ ⊢ App (wW i) (BX i φ) t) by (apply appBX in Ht; nd and_E2; exact Ht).
  apply DW_elim; [rewrite <- Dat_W; apply (closure_ctx HΓ)|].
  intros cl Hcl. unfold Closs in Hcl. apply in_map_iff in Hcl as ([bs c] & <- & Hm). cbn [projT1 projT2].
  apply Clos_intro.
  set (A := lvars (cargs i bs) Γ).
  rewrite ren_BX. set (φ' := ren_tm φ (upr [ι (tW i)] (wk (cargs i bs)))).
  set (Ξc := rev (chyps i (BX i φ') bs A) ++ wk_list (cargs i bs) (RH Γ ++ Ξ)).
  assert (Hh : forall h0, In h0 (chyps i (BX i φ') bs A) -> deriv FC tO free_rules _ Ξc h0).
  { intros h0 Hin. nd hyp. apply in_or_app; left. apply in_rev in Hin. exact Hin. }
  assert (HXD : forall y, deriv FC tO free_rules _ Ξc (App (wW i) (BX i φ') y) -> deriv FC tO free_rules _ Ξc (DW i y)).
  { intros y Hy. apply appBX in Hy. nd and_E1. exact Hy. }
  assert (HXφ : forall y, deriv FC tO free_rules _ Ξc (App (wW i) (BX i φ') y) ->
                          deriv FC tO free_rules _ Ξc (vsubst φ' (inst1 y))).
  { intros y Hy. apply appBX in Hy. nd and_E2. exact Hy. }
  apply appBX_inv. nd and_I; [apply DW_con, (chyps_dfacts i Ξc (BX i φ')); [exact Hh|exact HXD]|].
  (* la prémisse du constructeur *)
  assert (Hin : In (tr_prem Rel (ind_prem tO i (existT _ bs c))) (d_prems (tr_rule Rel (ha_rules (inr (inr (inr i))))))).
  { cbn [tr_rule d_prems ha_rules rsum wind_rules wind_rule]. rewrite map_map.
    exact (in_map (fun x => tr_prem Rel (ind_prem tO i x)) _ _ (mems_complete _ _ c)). }
  specialize (Hp _ Hin). unfold inst_hyps, inst_goal in Hp.
  cbn [tr_prem ind_prem premx p_ext p_hyps p_goal projT1 projT2] in Hp.
  assert (EΦ : forall y, vsubst (app1 (s := tW i) (vr (cargs i bs) vz) y) (vup (cargs i bs) w)
                    = vsubst φ' (inst1 (vsubst y (vup (cargs i bs) w)))).
  { intros y. rewrite vsubst_app1_gen, aget_vup_r. reflexivity. }
  assert (Pv : pure_args keep (lvars (cargs i bs) (iΘ (W := tW) tO i))) by apply pure_etas.
  rewrite ltr_pure, map_ltr_ihyps in Hp.
  2:{ intros y Hy. cbn [pure pure_args]. split; [exact Hy|exact I]. }
  2:{ exact Pv. }
  2:{ cbn [pure pure_args]. split; [split; [reflexivity|exact Pv]|exact I]. }
  rewrite vsubst_list_app in Hp.
  change (d_ctx (tr_rule Rel (ha_rules (inr (inr (inr i)))))) with (iΘ (W := tW) tO i) in Hp.
  rewrite (rel_ext_vup _ _ Rel (cargs i bs) w), rel_ext_cargs in Hp. fold A in Hp.
  rewrite (vsubst_ihyps tO i _ (fun y => vsubst φ' (inst1 y)) _ EΦ), EΦ, vsubst_Con in Hp.
  unfold iΘ in Hp. rewrite !vsubst_lvars_up in Hp. fold A in Hp.
  apply (deriv_cut_gen _ _ _ Hp). intros χ Hχ. rewrite !in_app_iff in Hχ.
  destruct Hχ as [[Hχ|Hχ]|Hχ].
  - apply (chyps_dfacts i Ξc (BX i φ') bs A Hh HXD _ Hχ).
  - apply (ihyps_chyps i Ξc (BX i φ') _ bs A Hh HXφ _ Hχ).
  - nd hyp. apply in_or_app; right. exact Hχ.
Qed.

Lemma adm_all i : tr_rule_adm Rel sctx (l_rules hsym HA i).
Proof.
  destruct i as [[j|[[[s h] [|]]|[[[s h] [|]]|[k i]]]]|[[]|[[]|i]]].
  - apply tr_rule_adm_rule. exists (inl j).
    destruct j as [[|]|[[| |]|[[| |]|[[]|[]]]]]; reflexivity.
  - apply adm_allI.
  - apply adm_allE.
  - apply adm_exI.
  - apply adm_exE.
  - apply tr_rule_adm_rule. exists (inr (inr (inr (k, i)))).
    destruct k as [s h], i; reflexivity.
  - apply adm_ind.
  - apply adm_peano.
  - apply adm_wind.
Qed.

(** ** Le théorème de traduction *)

Theorem ha_to_free Γ (Ξ : list (Judgment.form hsym tO Γ)) φ :
  sctx Γ -> provable HA Γ Ξ φ -> provable Free Γ (RH Γ ++ map (ltr Rel) Ξ) (ltr Rel φ).
Proof.
  intros HΓ H. exact (interp_sound_on HA Free Rel sctx HC HQ adm_all Γ Ξ φ HΓ H).
Qed.

Corollary ha_to_free_closed (φ : Judgment.form hsym tO []) :
  provable HA [] [] φ -> provable Free [] [] (ltr Rel φ).
Proof. intros H. exact (ha_to_free [] [] φ (Forall_nil _) H). Qed.

End Translation.
