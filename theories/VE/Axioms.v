(** * Les axiomes de IZFε réalisés dans V(E)

    Chaque axiome de IZF⁻ε et de IZFε reçoit une évidence uniforme
    (indépendante des paramètres) de ⊤ vers sa valeur sémantique, écrite
    ici sous forme « propre » (les lieurs sont des fonctions de V). Les
    réalisateurs viennent de [Real1.v], [Real2.v], [Ind.v] et [Coll.v]. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND Real1 Cons Real2 Ind Coll.

Set Default Proof Using "All".

Section Axioms.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).
Context (yfix : eexp F -> fev F).
Context (yfix_spec : forall a φ ψ, fent (F := F) φ (eeval F (yfix a) a) ψ -> fent (F := F) φ (yfix a) ψ).
Context (coll : forall T, (T -> Trees.V F) -> (Trees.V F -> Trees.V F -> pcar F) -> Trees.V F).
Context (coll_proper : forall T (xs xs' : T -> Trees.V F) ψ ψ', Rproper F ψ ->
           (forall t, teq F (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq F (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V F) ψ, Rproper F ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub F (coll T xs ψ) s)).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation V := (Trees.V F).
Local Notation eps := (eps F).
Local Notation veq := (veq F).
Local Notation vmem := (vmem F).
Local Notation vsub := (vsub F).
Local Notation veqv := (veqv F).
Local Notation vpower := (vpower F Φ0 dec).
Local Notation vrepl := (vrepl F coll).
Local Notation vrec := (vrec F coll).

Definition iff (A B : pcar F) : pcar F := fand (fimp A B) (fimp B A).

Lemma n_iff φ A B e1 e2 : fand φ A —[e1]→ B -> fand φ B —[e2]→ A -> φ —[e_pair (e_lam e1) (e_lam e2)]→ iff A B.
Proof. intros H1 H2. apply n_pair; apply n_lam; assumption. Qed.

Lemma n_use φ A B e : A —[e]→ B -> fand φ A —[e_comp e_snd e]→ B.
Proof. intros H. eapply f_comp; [apply f_snd|exact H]. Qed.

Lemma n_imp φ A B e : A —[e]→ B -> φ —[e_lam (e_comp e_snd e)]→ fimp A B.
Proof. intros H. apply n_lam, n_use, H. Qed.

(** *** IZF⁻ε *)

Lemma R_mem : exists e, forall x y,
  ftop —[e]→ iff (vmem x y) (fex (fun a : V => fand (veqv x a) (eps a y))).
Proof.
  destruct (mem_to F) as [e1 H1], (mem_from F) as [e2 H2].
  eexists. intros x y. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_sub : exists e, forall x y,
  ftop —[e]→ iff (vsub x y) (fall (fun a : V => fimp (eps a x) (vmem a y))).
Proof.
  destruct (sub_to F) as [e1 H1], (sub_from F) as [e2 H2].
  eexists. intros x y. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_eqv : exists e, forall x y, ftop —[e]→ iff (veqv x y) (fand (vsub x y) (vsub y x)).
Proof. eexists. intros x y. apply n_iff; apply f_snd. Qed.

Lemma R_pair : exists e, forall z x y,
  ftop —[e]→ iff (eps z (vpair F x y)) (for_ (veq z x) (veq z y)).
Proof.
  destruct (pair_to F) as [e1 H1], (pair_from F) as [e2 H2].
  eexists. intros z x y. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_union : exists e, forall z x,
  ftop —[e]→ iff (eps z (vunion F x)) (fex (fun b : V => fand (eps z b) (eps b x))).
Proof.
  destruct (union_to F) as [e1 H1], (union_from F) as [e2 H2].
  eexists. intros z x. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_power : exists e, forall x a,
  ftop —[e]→ fex (fun b : V => fand (eps b (vpower x))
                    (fall (fun z : V => iff (eps z b) (fand (eps z x) (eps z a))))).
Proof.
  destruct (bsub_in_power F Φ0 dec) as [e0 H0].
  destruct (bsub_to F Φ0 enc dec dec_enc) as [e1 H1], (bsub_from F Φ0 enc dec dec_enc) as [e2 H2].
  eexists. intros x a.
  eapply (n_exI (fun b : V => fand (eps b (vpower x))
                    (fall (fun z : V => iff (eps z b) (fand (eps z x) (eps z a)))))
                (bsub F Φ0 dec x (gpow F Φ0 enc x a))).
  apply n_pair; [apply H0|]. apply n_gen. intros z. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_coll : exists e, forall a (ψ : V -> V -> pcar F), Rproper F ψ ->
  ftop —[e]→ fimp (fall (fun α : V => fimp (eps α a) (fex (fun β : V => ψ α β))))
                  (fex (fun b : V => fall (fun α : V => fimp (eps α a) (fex (fun β : V => fand (eps β b) (ψ α β)))))).
Proof.
  destruct (coll_real F coll coll_spec) as [e He].
  eexists. intros a ψ Hψ. apply n_imp, He, Hψ.
Qed.

Lemma R_sep : exists e, forall z a (φ : pmor (Vset F) F),
  ftop —[e]→ iff (eps z (vsep F a φ)) (fand (eps z a) (φ z)).
Proof.
  destruct (sep_to F) as [e1 H1], (sep_from F) as [e2 H2].
  eexists. intros z a φ. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_empty : exists e, forall z, ftop —[e]→ fimp (eps z (vempty F)) fbot.
Proof. destruct (empty_real F) as [e He]. eexists. intros z. apply n_imp, He. Qed.

Lemma R_omega : exists e, forall a,
  ftop —[e]→ iff (eps a (vomega F))
                 (for_ (veq a (vempty F)) (fex (fun b : V => fand (eps b (vomega F)) (veq a (vsuc F b))))).
Proof.
  destruct (omega_to F) as [e1 H1], (omega_from F) as [e2 H2].
  eexists. intros a. apply n_iff; apply n_use; [apply H1|apply H2].
Qed.

Lemma R_ind : exists e, forall φ : pmor (Vset F) F,
  ftop —[e]→ fimp (fall (fun a : V => fimp (fall (fun b : V => fimp (eps b a) (φ b))) (φ a)))
                  (fall (fun a : V => φ a)).
Proof. destruct (ind_real F yfix yfix_spec) as [e He]. exists e. exact He. Qed.

(** *** Les axiomes supplémentaires *)

Definition ExU (χ : V -> pcar F) : pcar F :=
  fex (fun β0 : V => fand (χ β0) (fall (fun β' : V => fimp (χ β') (veq β' β0)))).

Lemma R_repl : exists e, forall a (ψ : V -> V -> pcar F), Rproper F ψ ->
  ftop —[e]→ fimp (fall (fun α : V => fimp (eps α a) (ExU (fun β : V => ψ α β))))
                  (fall (fun β : V => iff (eps β (vrepl a ψ)) (fex (fun α : V => fand (eps α a) (ψ α β))))).
Proof.
  destruct (W_to F coll) as [e1 H1], (W_from F coll coll_spec) as [e2 H2].
  eexists. intros a ψ Hψ. apply n_lam. apply n_gen. intros β. apply n_iff.
  - apply n_use. exact (H1 (fun x => x) (id_proper F) a ψ Hψ β).
  - eapply f_comp; [|exact (H2 (fun x => x) (id_proper F) a ψ Hψ β)].
    apply n_pair; [eapply n_snd, n_fst, f_id|apply f_snd].
Qed.

Lemma R_rec : exists e, forall (φ : V -> pcar F) (ψ : V -> V -> pcar F), Rproper F ψ ->
  ftop —[e]→
    fimp (fall (fun a : V => fimp (φ a) (fall (fun α : V => fimp (eps α a)
              (fand (φ α) (ExU (fun β : V => ψ (vrec ψ α) β)))))))
         (fall (fun a : V => fimp (φ a) (fall (fun β : V =>
              iff (eps β (vrec ψ a)) (fex (fun α : V => fand (eps α a) (ψ (vrec ψ α) β))))))).
Proof.
  destruct (W_to F coll) as [e1 H1], (W_from F coll coll_spec) as [e2 H2].
  eexists. intros φ ψ Hψ. apply n_lam. apply n_gen. intros a. apply n_lam. apply n_gen. intros β.
  rewrite (vrec_W F coll ψ a). apply n_iff.
  - apply n_use. exact (H1 (vrec ψ) (vrec_gproper F coll coll_proper ψ Hψ) a ψ Hψ β).
  - eapply f_comp; [|exact (H2 (vrec ψ) (vrec_gproper F coll coll_proper ψ Hψ) a ψ Hψ β)].
    apply n_pair; [|apply f_snd].
    apply n_gen. intros α. apply n_lam.
    eapply n_snd. eapply n_app.
    + eapply (n_inst (fun α : V => fimp (eps α a) (fand (φ α) (ExU (fun β : V => ψ (vrec ψ α) β)))) α).
      eapply n_app.
      * eapply (n_inst (fun a : V => fimp (φ a) (fall (fun α : V => fimp (eps α a)
              (fand (φ α) (ExU (fun β : V => ψ (vrec ψ α) β)))))) a).
        eapply n_snd, n_fst, n_fst, n_fst, f_id.
      * eapply n_snd, n_fst, n_fst, f_id.
    + apply f_snd.
Qed.

Lemma R_sep_power : exists e, forall a (φ : pmor (Vset F) F), ftop —[e]→ eps (vsep F a φ) (vpower a).
Proof. destruct (sep_power_real F Φ0 enc dec dec_enc) as [e He]. exists e. exact He. Qed.

Lemma R_power_sub : exists e, forall x a,
  ftop —[e]→ fimp (eps a (vpower x)) (fex (fun b : V => fall (fun z : V => iff (eps z a) (fand (eps z x) (eps z b))))).
Proof.
  destruct (power_sub_real F Φ0 dec) as [e He].
  eexists. intros x a. apply n_lam.
  eapply (n_exI (fun b : V => fall (fun z : V => iff (eps z a) (fand (eps z x) (eps z b)))) a).
  apply n_gen. intros z. apply n_iff.
  - apply n_pair; [|apply f_snd].
    eapply f_comp; [|exact (He a x z)].
    apply n_pair; [eapply n_snd, n_fst, f_id|apply f_snd].
  - eapply n_snd, n_snd, f_id.
Qed.

End Axioms.
