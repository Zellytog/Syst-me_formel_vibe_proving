(** * V(E) : collection, remplacement, rec

    On suppose un principe de **collection par valeurs** ([coll]) : pour
    une famille d'ensembles (xₜ)ₜ et une relation ψ, un ensemble B qui
    atteint, pour chaque t, toutes les valeurs de β ↦ ψ(xₜ, β), et qui
    respecte l'égalité. Dans les notes, il vient de la collection de M
    (déf. 2.2.1) ; il se démontre avec le choix et le tiers exclu, mais pas
    en théorie des types sans axiome.

    Le remplacement et rec sont alors interprétés comme dans la
    correction A.5 : {(ψₜ ∧ ψ(xₜ, β), β) | t ∈ a, β ∈ B}, avec xₜ = aₜ pour
    le remplacement et xₜ = rec(aₜ) pour rec, défini par récurrence sur a. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND Cons.

Section Coll.

Context (F : frame).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation V := (V F).
Local Notation Vset := (Vset F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).
Local Notation eps := (eps F).
Local Notation veq := (veq F).

Definition Rproper (ψ : V -> V -> pcar F) : Prop :=
  forall x x' y y', teq F x x' -> teq F y y' -> ψ x y ≡ ψ x' y'.

(** ** L'hypothèse de collection par valeurs *)

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper ψ -> (forall t, teq F (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq F (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar F), Rproper ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).

(** ** {(lbₜ ∧ ψ(xₜ, β), β) | t ∈ T, β ∈ B} *)

Definition vrecB (T : Type) (lb : T -> pcar F) (xs : T -> V) (B : V) (ψ : V -> V -> pcar F) : V :=
  mkS F (T * idx B) (fun p => projT1 (sub B (snd p)))
      (fun p => (fand (lb (fst p)) (ψ (xs (fst p)) (sub B (snd p))), projT2 (sub B (snd p)))).

Lemma vrecB_proper T lb lb' xs xs' B B' ψ ψ' : Rproper ψ ->
  (forall t, lb t ≡ lb' t) -> (forall t, teq F (xs t) (xs' t)) -> teq F B B' -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq F (vrecB T lb xs B ψ) (vrecB T lb' xs' B' ψ').
Proof.
  intros Hψ Hlb Hxs HB Hψ'. destruct B as [s l], B' as [s' l'], HB as [E H]; cbn in E, H. destruct E.
  exists eq_refl. intros [t u]. cbn. destruct (teq_br F s l l' u H) as [H1 H2]. split.
  - apply fand_proper; [apply Hlb|]. eapply peq_trans; [apply Hψ; [apply Hxs|exact H2]|apply Hψ'].
  - exact (proj2 (leq_lab F s l l' H u)).
Qed.

Lemma sub_vrecB T lb xs B ψ p : teq F (sub (vrecB T lb xs B ψ) p) (sub B (snd p)).
Proof. apply teq_refl. Qed.

(** ** Remplacement *)

Definition vrepl (a : V) (ψ : V -> V -> pcar F) : V := vrecB (idx a) (lbl a) (sub a) (coll (idx a) (sub a) ψ) ψ.

Lemma vrepl_proper a a' ψ ψ' : Rproper ψ -> teq F a a' -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq F (vrepl a ψ) (vrepl a' ψ').
Proof.
  intros Hψ Ha Hψ'. destruct a as [s l], a' as [s' l'], Ha as [E H]; cbn in E, H. destruct E.
  unfold vrepl. apply vrecB_proper; try assumption.
  - intros t. exact (proj1 (teq_br F s l l' t H)).
  - intros t. exact (proj2 (teq_br F s l l' t H)).
  - apply coll_proper; [exact Hψ| |exact Hψ']. intros t. exact (proj2 (teq_br F s l l' t H)).
Qed.

(** ** rec, par récurrence sur a *)

Fixpoint vrecS (ψ : V -> V -> pcar F) (s : shape) : lab F s -> V :=
  match s as s0 return lab F s0 -> V with
  | node T k => fun l =>
      let xs := fun t => vrecS ψ (k t) (snd (l t)) in
      vrecB T (fun t => fst (l t)) xs (coll T xs ψ) ψ
  end.

Definition vrec (ψ : V -> V -> pcar F) (a : V) : V := vrecS ψ (projT1 a) (projT2 a).

Lemma vrecS_proper ψ ψ' : Rproper ψ -> (forall x y, ψ x y ≡ ψ' x y) ->
  forall s l l', leq F s l l' -> teq F (vrecS ψ s l) (vrecS ψ' s l').
Proof.
  intros Hψ Hψ'. induction s as [T k IH]; intros l l' H. cbn [vrecS].
  assert (Hxs : forall t, teq F (vrecS ψ (k t) (snd (l t))) (vrecS ψ' (k t) (snd (l' t)))).
  { intros t. apply IH, (proj2 (H t)). }
  apply vrecB_proper; try assumption.
  - intros t. exact (proj1 (H t)).
  - apply coll_proper; assumption.
Qed.

Lemma vrec_proper ψ ψ' a a' : Rproper ψ -> (forall x y, ψ x y ≡ ψ' x y) -> teq F a a' -> teq F (vrec ψ a) (vrec ψ' a').
Proof.
  intros Hψ Hψ' Ha. destruct a as [s l], a' as [s' l'], Ha as [E H]; cbn in E, H. destruct E.
  exact (vrecS_proper ψ ψ' Hψ Hψ' s l l' H).
Qed.

(** ** Réalisation *)

Definition ExU (χ : V -> pcar F) : pcar F :=
  fex (fun β0 : V => fand (χ β0) (fall (fun β' : V => fimp (χ β') (veq β' β0)))).

Definition Pl (ψ : V -> V -> pcar F) (Hψ : Rproper ψ) (β : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => ψ z β) (fun z z' E => Hψ z z' β β E (teq_refl F β)).
Definition Pr (ψ : V -> V -> pcar F) (Hψ : Rproper ψ) (x : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => ψ x z) (fun z z' E => Hψ x x z z' (teq_refl F x) E).

(** La collection : (∀α ε a. ∃β. ψ(α, β)) → ∃b. ∀α ε a. ∃β ε b. ψ(α, β). *)
Definition Bcoll (a : V) (ψ : V -> V -> pcar F) : V :=
  mk F (idx (coll (idx a) (sub a) ψ)) (fun s => (ftop, sub (coll (idx a) (sub a) ψ) s)).

Lemma coll_real : exists e, forall a ψ (Hψ : Rproper ψ),
  fall (fun α : V => fimp (eps α a) (fex (fun β : V => ψ α β))) —[e]→
  fex (fun b : V => fall (fun α : V => fimp (eps α a) (fex (fun β : V => fand (eps β b) (ψ α β))))).
Proof.
  eexists. intros a ψ Hψ.
  eapply (n_exI (fun b : V => fall (fun α : V => fimp (eps α a) (fex (fun β : V => fand (eps β b) (ψ α β))))) (Bcoll a ψ)).
  apply n_gen. intros α. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros t.
  eapply n_exE.
  { eapply n_app; [eapply (n_inst (fun α : V => fimp (eps α a) (fex (fun β : V => ψ α β))) α); apply n_wk, f_fst|].
    apply n_wk, f_snd. }
  intros β.
  destruct (coll_spec (idx a) (sub a) ψ Hψ t β) as [s Hs].
  eapply (n_exI _ (sub (Bcoll a ψ) s)). apply n_pair.
  - eapply (n_exI _ s). apply n_pair; [apply f_top|apply n_refl].
  - eapply (n_leib (Pl ψ Hψ (sub (Bcoll a ψ) s)) (sub a t) α); [eapply n_sym, n_snd, n_snd, n_wk, f_id|].
    eapply n_eq; [apply Hψ; [apply teq_refl|apply teq_sym, sub_mk]|]. eapply n_eq; [exact Hs|].
    eapply (n_leib (Pl ψ Hψ β) α (sub a t)); [eapply n_snd, n_snd, n_wk, f_id|apply n_hyp0].
Qed.

(** Remplacement et rec : W ≜ {(ψₜ ∧ ψ(g(aₜ), β), β) | t ∈ a, β ∈ B}. *)
Definition Gproper (g : V -> V) := forall x x', teq F x x' -> teq F (g x) (g x').

Definition Wset (g : V -> V) (a : V) (ψ : V -> V -> pcar F) : V :=
  vrecB (idx a) (lbl a) (fun t => g (sub a t)) (coll (idx a) (fun t => g (sub a t)) ψ) ψ.

Definition Pg (g : V -> V) (Hg : Gproper g) (ψ : V -> V -> pcar F) (Hψ : Rproper ψ) (β : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => ψ (g z) β) (fun z z' E => Hψ _ _ β β (Hg z z' E) (teq_refl F β)).

Lemma W_to : exists e, forall g (Hg : Gproper g) a ψ (Hψ : Rproper ψ) β,
  eps β (Wset g a ψ) —[e]→ fex (fun α : V => fand (eps α a) (ψ (g α) β)).
Proof.
  eexists. intros g Hg a ψ Hψ β. apply f_exE. intros [t s].
  eapply (n_exI (fun α : V => fand (eps α a) (ψ (g α) β)) (sub a t)). apply n_pair.
  - eapply (n_exI _ t). apply n_pair; [eapply n_fst, f_fst|apply n_refl].
  - eapply (n_leib (Pr ψ Hψ (g (sub a t))) (sub (coll (idx a) (fun t => g (sub a t)) ψ) s) β).
    + eapply n_sym. exact (f_snd _ _ _).
    + eapply n_snd, f_fst.
Qed.

Lemma W_from : exists e, forall g (Hg : Gproper g) a ψ (Hψ : Rproper ψ) β,
  fand (fall (fun α : V => fimp (eps α a) (ExU (fun β : V => ψ (g α) β))))
       (fex (fun α : V => fand (eps α a) (ψ (g α) β))) —[e]→ eps β (Wset g a ψ).
Proof.
  eexists. intros g Hg a ψ Hψ β.
  set (B := coll (idx a) (fun t => g (sub a t)) ψ).
  eapply n_exE; [apply f_snd|]. intros α.
  eapply n_exE; [eapply n_fst, n_hyp0|]. intros t.
  eapply n_exE.
  { eapply n_app; [eapply (n_inst (fun α : V => fimp (eps α a) (ExU (fun β : V => ψ (g α) β))) α);
                   eapply n_fst, n_fst, n_wk, f_id|].
    eapply n_fst, n_snd, n_wk, f_id. }
  intros β0.
  destruct (coll_spec (idx a) (fun t => g (sub a t)) ψ Hψ t β) as [s Hs].
  (* ψ(g(aₜ), β), sous le contexte *)
  assert (K : forall φ e1 e2, φ —[e1]→ veq α (sub a t) -> φ —[e2]→ ψ (g α) β ->
                φ —[e_app (e_comp e1 e_inst) e2]→ ψ (g (sub a t)) β).
  { intros φ e1 e2 H1 H2. exact (n_leib (Pg g Hg ψ Hψ β) α (sub a t) φ e1 e2 H1 H2). }
  eapply (n_exI _ (pair t s)). apply n_pair; [apply n_pair|].
  - eapply n_fst, n_snd, n_wk, f_id.
  - cbn. eapply n_eq; [exact Hs|]. apply K; [eapply n_snd, n_snd, n_wk, f_id|eapply n_snd, n_snd, n_wk, n_wk, f_id].
  - eapply n_eq; [apply veq_proper; [apply teq_refl|apply teq_sym, sub_vrecB]|]. cbn.
    eapply n_trans.
    + eapply n_app; [eapply (n_inst (fun β' : V => fimp (ψ (g α) β') (veq β' β0)) β); eapply n_snd, n_hyp0|].
      eapply n_snd, n_snd, n_wk, n_wk, f_id.
    + eapply n_sym. eapply n_app; [eapply (n_inst (fun β' : V => fimp (ψ (g α) β') (veq β' β0)) (sub B s)); eapply n_snd, n_hyp0|].
      eapply (n_leib (Pg g Hg ψ Hψ (sub B s)) (sub a t) α); [eapply n_sym, n_snd, n_snd, n_wk, f_id|].
      eapply n_eq; [exact Hs|]. apply K; [eapply n_snd, n_snd, n_wk, f_id|eapply n_snd, n_snd, n_wk, n_wk, f_id].
Qed.

Lemma id_proper : Gproper (fun x => x).
Proof. intros x x' E; exact E. Qed.

Lemma vrepl_W a ψ : vrepl a ψ = Wset (fun x => x) a ψ.
Proof. reflexivity. Qed.

Lemma vrec_W ψ a : vrec ψ a = Wset (vrec ψ) a ψ.
Proof. destruct a as [[T k] l]. reflexivity. Qed.

Lemma vrec_gproper ψ : Rproper ψ -> Gproper (vrec ψ).
Proof. intros Hψ x x' E. apply vrec_proper; [exact Hψ|intros; apply peq_refl|exact E]. Qed.

End Coll.
