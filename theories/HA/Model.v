(** * Un modèle de HA_ω^{ω,ω} dans tout cadre d'évidence

    Pour tout cadre d'évidence F (Cohen–Miquey–Tate, [Models/Frame.v]), on
    construit un modèle de Free, le système libre (ω,ω,ω), dans le tripos de
    F, puis un modèle de HA par composition avec la traduction
    [ha_to_free] : ⟦φ⟧_HA := ⟦φ^D⟧_Free.

    Les données ([Tarski.v], [FrameTarski.v]) :
    - N ↦ nat (discret), O ↦ Φ, a → b ↦ ⟦b⟧^⟦a⟧ (l'exponentielle de PSet) ;
    - λ et app : la structure fermée ; 0, S ; rec_s ↦ [nat_rect] ;
    - ⇒, ∧, ∨, ⊤ ↦ ceux de Φ ; ∀ₛ, ∃ₛ ↦ ⋀, ⋁ indexés par ⟦s⟧ ;
    - =ₛ ↦ l'égalité de Leibniz de ⟦s⟧, sauf sur N ;
    - =_N ↦ « (a =? b) = true », au sens de Leibniz sur bool, et
      ⊥ ↦ « false = true ».

    Le choix de =_N et de ⊥ vient de la réécriture S t = 0 ~ ⊥ de Free : une
    règle de calcul doit être validée *à égalité près* dans Φ. Or
    (S a =? 0) se calcule en false, donc ⟦S a = 0⟧ et ⟦⊥⟧ sont le même
    élément de Φ. Ces interprétations ne sont pas égales aux connecteurs
    codés de Φ, mais *uniformément équivalentes* ([Hbot], [eqN_equiv]),
    ce qui suffit au tripos ([FrameTarski.fequiv]).

    Résultats :
    - [free_sound] : réalisabilité de Free ;
    - [ha_sound], [ha_sound_closed] : une preuve dans HA donne une évidence
      uniforme de sa traduction relativisée ;
    - [ha_consistent] : HA_ω^{ω,ω} est cohérente (cadre [prop_frame]). *)

From Category Require Import Lib Theory.Category.
From Stdlib Require Import List Arith.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Models Require Import PSet Frame Semantics Logic Order SetModels Tarski FrameModel FrameTarski.
From SF.Extensions Require Import Same.
From SF.HA Require Import Signature Translation Equational.

Local Notation ι a := (Spec [] a).

(** Les arbres finis : l'interprétation de tous les types inductifs (le
    constructeur est repéré par sa position, ses paramètres et ses
    sous-arbres sont en liste). *)
Inductive wtree : Type := wnode (k : nat) (ps : list nat) (ys : list wtree).

Fixpoint wtree_ind' (P : wtree -> Prop) (H : forall k ps ys, Forall P ys -> P (wnode k ps ys)) (t : wtree) : P t :=
  match t with
  | wnode k ps ys => H k ps ys ((fix go (l : list wtree) : Forall P l :=
                                   match l with
                                   | [] => Forall_nil _
                                   | y :: l' => Forall_cons _ (wtree_ind' P H y) (go l')
                                   end) ys)
  end.

Section Model.
Context (F : frame) {Ind : Type} {dsc : Ind -> list (list bool)}.
Local Notation ty := (Signature.ty Ind).
Local Notation hsym := (Signature.hsym dsc).
Local Notation free_calc_rules := (Signature.free_calc_rules (dsc := dsc)).
Local Notation Rel := (Signature.Rel (dsc := dsc)).
Local Notation HA := (Signature.HA (dsc := dsc)).
Local Notation Free := (Signature.Free (dsc := dsc)).

Fixpoint So (s : ty) : pset :=
  match s with
  | tN => disc nat
  | tO => fprop F
  | tarr a b => pexp (pprod punit (pexp punit (So a))) (So b)
  | tW _ => disc wtree
  end.

Local Notation V s := (pexp punit (So s)).

Definition i_lam a b : pmor (pprod punit (So (tarr a b))) (So (tarr a b)).
Proof.
  refine (Build_pmor (pprod punit (So (tarr a b))) (So (tarr a b))
            (fun q : pcar (pprod punit (So (tarr a b))) => snd q) _).
  intros q q' E. exact (proj2 E).
Defined.

Definition i_app a b : pmor (pprod (pprod punit (V a)) (V (tarr a b))) (So b).
Proof.
  refine (Build_pmor (pprod (pprod punit (V a)) (V (tarr a b))) (So b)
            (fun q : pcar (pprod (pprod punit (V a)) (V (tarr a b))) => (snd q tt : pmor _ _) (fst q)) _).
  intros [[u x] f] [[u' x'] f'] [[_ Ex] Ef]. cbn in *.
  eapply peq_trans; [apply (Ef tt)|]. apply pfun_proper. split; [exact Logic.I|exact Ex].
Defined.

Local Notation cst x := (pconst So x).
Local Notation St s := (pexp (pprod (pprod punit (V s)) (V tN)) (So s)).

Definition rec_val s (z : So s) (st : St s) (m : nat) : So s :=
  nat_rect (fun _ => pcar (So s)) z (fun k acc => (st : pmor _ _) ((tt, cst acc), @pconst _ So tN k)) m.

Lemma rec_val_proper s z z' (st st' : St s) m :
  z ≡ z' -> st ≡ st' -> rec_val s z st m ≡ rec_val s z' st' m.
Proof.
  intros Ez Est. induction m as [|m IH]; cbn; [exact Ez|].
  eapply peq_trans; [apply (Est _)|]. apply pfun_proper.
  split; [split; [exact Logic.I|intros []; exact IH]|intros []; reflexivity].
Qed.

Definition i_zero : pmor punit (disc nat) := Build_pmor punit (disc nat) (fun _ => O) (fun _ _ _ => eq_refl).

Definition i_succ : pmor (pprod punit (V tN)) (disc nat).
Proof.
  refine (Build_pmor (pprod punit (V tN)) (disc nat) (fun q : pcar (pprod punit (V tN)) => S (snd q tt)) _).
  intros [u a] [u' a'] [_ H]. cbn in *. rewrite (H tt). reflexivity.
Defined.

Definition i_rec s : pmor (pprod (pprod (pprod punit (V tN)) (St s)) (V s)) (So s).
Proof.
  refine (Build_pmor (pprod (pprod (pprod punit (V tN)) (St s)) (V s)) (So s)
            (fun q : pcar (pprod (pprod (pprod punit (V tN)) (St s)) (V s)) =>
               rec_val s (snd q tt) (snd (fst q)) (snd (fst (fst q)) tt)) _).
  intros [[[u m] st] z] [[[u' m'] st'] z'] [[[_ Hm] Hst] Hz]. cbn in *.
  rewrite (Hm tt). apply rec_val_proper; [apply Hz|exact Hst].
Defined.

Local Notation Q2 := (pprod (pprod punit (V tO)) (V tO)).

Definition i_bin (op : F -> F -> F) (Hop : forall φ φ' ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> op φ ψ ≡ op φ' ψ') :
  pmor Q2 (So tO).
Proof.
  refine (Build_pmor Q2 (So tO) (fun q : pcar Q2 => op (snd q tt) (snd (fst q) tt)) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. apply Hop; [apply Hb|apply Ha].
Defined.

Definition i_top : pmor punit (So tO) := Build_pmor punit (So tO) (fun _ => ftop) (fun _ _ _ => peq_refl _).

(** ⊥ est interprété par l'égalité de Leibniz false = true sur les booléens :
    uniformément équivalente au ⊥ codé de Φ, elle permet de valider S t = 0 ~ ⊥
    *à égalité près*. *)
Definition bbot : F := leib (F := F) (A := disc bool) false true.
Definition i_bot : pmor punit (So tO) := Build_pmor punit (So tO) (fun _ => bbot) (fun _ _ _ => peq_refl _).

Local Notation Qp s := (pprod punit (pexp (pprod punit (V s)) (So tO))).

Definition i_all s : pmor (Qp s) (So tO).
Proof.
  refine (Build_pmor (Qp s) (So tO) (fun q : pcar (Qp s) => fall (fun a : So s => (snd q : pmor _ _) (up1 So s a))) _).
  intros [u f] [u' f'] [_ H]. cbn in *. apply fall_proper. intros a. apply H.
Defined.

Definition i_ex s : pmor (Qp s) (So tO).
Proof.
  refine (Build_pmor (Qp s) (So tO) (fun q : pcar (Qp s) => fex (fun a : So s => (snd q : pmor _ _) (up1 So s a))) _).
  intros [u f] [u' f'] [_ H]. cbn in *. apply fex_proper. intros a. apply H.
Defined.

Local Notation Qe s := (pprod (pprod punit (V s)) (V s)).

Definition i_leib s : pmor (Qe s) (So tO).
Proof.
  refine (Build_pmor (Qe s) (So tO) (fun q : pcar (Qe s) => leib (snd q tt) (snd (fst q) tt)) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. apply leib_proper; [apply Hb|apply Ha].
Defined.

(** L'égalité des entiers : a = b ↦ (a =? b) = true, à la Leibniz sur les booléens. *)
Definition i_eqN : pmor (Qe tN) (So tO).
Proof.
  refine (Build_pmor (Qe tN) (So tO)
            (fun q : pcar (Qe tN) => leib (F := F) (A := disc bool) (Nat.eqb (snd q tt) (snd (fst q) tt)) true) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. rewrite (Ha tt), (Hb tt). apply peq_refl.
Defined.

Definition i_eq s : pmor (Qe s) (So tO) :=
  match s with
  | tN => i_eqN
  | s => i_leib s
  end.

(** *** Les types inductifs *)

Local Notation ictx := (ictx PSet So).
Local Notation cargs i bs := (Inductive.cargs tN tW i bs).
Local Notation sarg i s bs := (Inductive.sargs tN tW i s bs).
Local Notation steps i s := (Inductive.steps tN tW dsc i s).

Definition kst {s} (x : So s) : pexp punit (So s) := Build_pmor punit (So s) (fun _ => x) (fun _ _ _ => peq_refl x).

(** Un élément de chaque sorte. *)
Fixpoint inh (s : ty) : So s :=
  match s with
  | tN => O
  | tO => ftop
  | tarr a b => Build_pmor (pprod punit (pexp punit (So a))) (So b) (fun _ => inh b) (fun _ _ _ => peq_refl _)
  | tW _ => wnode 0 [] []
  end.

(** Les paramètres et les sous-arbres d'un tuple d'arguments de constructeur. *)
Fixpoint cvals i (bs : list bool) : ictx (cargs i bs) -> list nat * list wtree :=
  match bs as bs0 return ictx (cargs i bs0) -> list nat * list wtree with
  | [] => fun _ => ([], [])
  | b :: bs' =>
      match b as b0 return ictx (cargs i (b0 :: bs')) -> list nat * list wtree with
      | true => fun q => (((snd q : pmor punit (disc nat)) tt) :: fst (cvals i bs' (fst q)), snd (cvals i bs' (fst q)))
      | false => fun q => (fst (cvals i bs' (fst q)), ((snd q : pmor punit (disc wtree)) tt) :: snd (cvals i bs' (fst q)))
      end
  end.

Lemma cvals_proper i bs (q q' : ictx (cargs i bs)) : q ≡ q' -> cvals i bs q = cvals i bs q'.
Proof.
  revert q q'. induction bs as [|[|] bs IH]; intros q q' E; [reflexivity| |]; cbn [cvals];
    destruct E as [E1 E2]; pose proof (IH _ _ E1) as Hr; pose proof (E2 tt) as Ht; cbn in Ht.
  - exact (f_equal2 (fun (x : nat) A => (x :: fst A, snd A)) Ht Hr).
  - exact (f_equal2 (fun (y : wtree) A => (fst A, y :: snd A)) Ht Hr).
Qed.

Definition i_con i bs (c : mem (dsc i) bs) : pmor (ictx (cargs i bs)) (disc wtree) :=
  Build_pmor (ictx (cargs i bs)) (disc wtree)
    (fun q => wnode (mindex c) (fst (cvals i bs q)) (snd (cvals i bs q)))
    (fun q q' E => match cvals_proper i bs q q' E in _ = r
                   return wnode (mindex c) (fst (cvals i bs q)) (snd (cvals i bs q)) = wnode (mindex c) (fst r) (snd r)
                   with eq_refl => eq_refl end).

(** Les arguments d'un pas, à partir des paramètres et des couples
    (sous-arbre, valeur de l'appel récursif). *)
Fixpoint sbval i s (bs : list bool) (ps : list nat) (yr : list (wtree * So s)) : ictx (sarg i s bs) :=
  match bs as bs0 return ictx (sarg i s bs0) with
  | [] => tt
  | true :: bs' => (sbval i s bs' (tl ps) yr, kst (s := tN) (hd O ps))
  | false :: bs' => ((sbval i s bs' ps (tl yr), kst (snd (hd (wnode 0 [] [], inh s) yr))),
                     kst (s := tW i) (fst (hd (wnode 0 [] [], inh s) yr)))
  end.

Definition yr_eq {s} (yr yr' : list (wtree * So s)) : Prop :=
  Forall2 (fun p p' => fst p = fst p' /\ snd p ≡ snd p') yr yr'.

Lemma sbval_proper i s bs ps (yr yr' : list (wtree * So s)) : yr_eq yr yr' -> sbval i s bs ps yr ≡ sbval i s bs ps yr'.
Proof.
  revert ps yr yr'. induction bs as [|[|] bs IH]; intros ps yr yr' E; cbn [sbval]; [exact Logic.I| |].
  - split; [apply IH, E|intros []; reflexivity].
  - assert (E' : yr_eq (tl yr) (tl yr')) by (destruct E; [constructor|exact E]).
    assert (Eh : fst (hd (wnode 0 [] [], inh s) yr) = fst (hd (wnode 0 [] [], inh s) yr')
                 /\ snd (hd (wnode 0 [] [], inh s) yr) ≡ snd (hd (wnode 0 [] [], inh s) yr'))
      by (destruct E as [|p p' l l' Hp _]; [split; [reflexivity|apply peq_refl]|exact Hp]).
    split; [split; [apply IH, E'|intros []; exact (proj2 Eh)]|intros []; exact (proj1 Eh)].
Qed.

(** Le pas du k-ième constructeur, appliqué. *)
Fixpoint sget i s (l : list (list bool)) : ictx (map (step_spec tN tW i s) l) -> nat -> list nat -> list (wtree * So s) -> So s :=
  match l as l0 return ictx (map (step_spec tN tW i s) l0) -> nat -> list nat -> list (wtree * So s) -> So s with
  | [] => fun _ _ _ _ => inh s
  | bs :: l' => fun q k ps yr =>
      match k with
      | O => (snd q : pmor (ictx (sarg i s bs)) (So s)) (sbval i s bs ps yr)
      | S k' => sget i s l' (fst q) k' ps yr
      end
  end.

Lemma sget_proper i s l (q q' : ictx (map (step_spec tN tW i s) l)) k ps yr yr' :
  q ≡ q' -> yr_eq yr yr' -> sget i s l q k ps yr ≡ sget i s l q' k ps yr'.
Proof.
  revert q q' k. induction l as [|bs l IH]; intros q q' k Eq Ey; [apply peq_refl|].
  destruct k as [|k]; cbn [sget].
  - eapply peq_trans; [exact (proj2 Eq (sbval i s bs ps yr))|]. apply pfun_proper, sbval_proper, Ey.
  - apply IH; [apply (proj1 Eq)|exact Ey].
Qed.

Lemma sget_mvar i s l bs (c : mem l bs) (q : ictx (map (step_spec tN tW i s) l)) ps yr :
  sget i s l q (mindex c) ps yr = (proj PSet So (mvar (step_spec tN tW i s) c) q : pmor _ _) (sbval i s bs ps yr).
Proof. induction c as [bs l|bs b l c IH]; [reflexivity|]. cbn [mindex sget mvar proj]. apply IH. Qed.

Definition wrec_val i s (q : ictx (steps i s)) : wtree -> So s :=
  fix go t := match t with wnode k ps ys => sget i s (dsc i) q k ps (map (fun y => (y, go y)) ys) end.

Lemma wrec_val_proper i s (q q' : ictx (steps i s)) t : q ≡ q' -> wrec_val i s q t ≡ wrec_val i s q' t.
Proof.
  intros E. induction t as [k ps ys IH] using wtree_ind'. cbn [wrec_val].
  apply sget_proper; [exact E|]. induction IH as [|y ys Hy _ IHys]; constructor; [split; [reflexivity|exact Hy]|exact IHys].
Qed.

Definition i_wrec i s : pmor (ictx (ι (tW i) :: steps i s)) (So s).
Proof.
  refine (Build_pmor (ictx (ι (tW i) :: steps i s)) (So s)
            (fun q => wrec_val i s (fst q) ((snd q : pmor punit (disc wtree)) tt)) _).
  intros [q t] [q' t'] [Eq Et]. cbn in *. rewrite (Et tt). apply wrec_val_proper, Eq.
Defined.

Definition Iy (σ : spec ty) (c : hsym σ) : ictx (dom σ) ~> So (cod σ) :=
  match c in Signature.hsym _ σ0 return ictx (dom σ0) ~> So (cod σ0) with
  | h_lam a b => i_lam a b
  | h_app a b => i_app a b
  | h_zero => i_zero
  | h_succ => i_succ
  | h_rec s _ => i_rec s
  | h_imp => i_bin fimp (fimp_proper F)
  | h_and => i_bin fand (fand_proper F)
  | h_or => i_bin for_ for_proper
  | h_top => i_top
  | h_bot => i_bot
  | h_all s => i_all s
  | h_ex s => i_ex s
  | h_eq s => i_eq s
  | h_con i bs c => i_con i bs c
  | h_wrec i s _ => i_wrec i s
  end.


Local Notation sv := (sval So Iy).

Lemma neq_valid γ : sv (r_lhs (free_calc_rules (inr tt))) γ ≡ sv (r_rhs (free_calc_rules (inr tt))) γ.
Proof. cbn. apply peq_refl. Qed.

Local Ltac pcong := apply pfun_proper; repeat split; try (intros []); cbn; try apply peq_refl.

Lemma beta_valid (a b : ty) γ :
  sv (r_lhs (free_calc_rules (inl (inl (inr (existT _ a (existT _ b (existT _ _ (tarrw_i a b))))))))) γ
  ≡ sv (r_rhs (free_calc_rules (inl (inl (inr (existT _ a (existT _ b (existT _ _ (tarrw_i a b))))))))) γ.
Proof. cbn. pcong. Qed.

Lemma rec0_valid (s : ty) h γ :
  sv (r_lhs (free_calc_rules (inl (inl (inl (existT _ s h, false)))))) γ
  ≡ sv (r_rhs (free_calc_rules (inl (inl (inl (existT _ s h, false)))))) γ.
Proof. cbn. pcong. Qed.

Lemma nat_rect_ext' {X : pset} (z z' : X) (f g : nat -> X -> X) m :
  z ≡ z' -> (forall k x x', x ≡ x' -> f k x ≡ g k x') ->
  nat_rect (fun _ => pcar X) z f m ≡ nat_rect (fun _ => pcar X) z' g m.
Proof. intros Ez H. induction m as [|m IH]; cbn; [exact Ez|]. apply H, IH. Qed.

Lemma recS_valid (s : ty) h γ :
  sv (r_lhs (free_calc_rules (inl (inl (inl (existT _ s h, true)))))) γ
  ≡ sv (r_rhs (free_calc_rules (inl (inl (inl (existT _ s h, true)))))) γ.
Proof.
  cbn. pcong. apply nat_rect_ext'; [pcong|]. intros k x x' E. pcong. exact E.
Qed.

Lemma sargs_eta_at {Γ σ Θ} (a : args hsym Γ (σ :: Θ)) (γ : ictx Γ) :
  sargs PSet So Iy a (penv PSet So Γ) γ ≡ (sargs PSet So Iy (atl a) (penv PSet So Γ) γ, stms PSet So Iy (ahd a) (penv PSet So Γ) γ).
Proof.
  refine (match a as a0 in Terms.args _ Γ0 L0 return
            forall γ0 : ictx Γ0, match L0 return args hsym Γ0 L0 -> Prop with
            | [] => fun _ => True
            | τ :: L1 => fun a1 => sargs PSet So Iy a1 (penv PSet So Γ0) γ0
                                   ≡ (sargs PSet So Iy (atl a1) (penv PSet So Γ0) γ0,
                                      stms PSet So Iy (ahd a1) (penv PSet So Γ0) γ0)
            end a0 with
          | anil => fun _ => I
          | acons u a' => fun γ0 => peq_refl _
          end γ).
Qed.

Lemma stms0_at {Γ b} (u : tms hsym Γ (ι b)) (γ : ictx Γ) (t : unit) :
  (stms PSet So Iy u (penv PSet So Γ) γ : pmor _ _) t ≡ sv u γ.
Proof. destruct t. exact (stm_ext0_at So Iy u γ tt). Qed.

Lemma sbuild_sem i s {Γ} (R : Terms.tm hsym Γ (tW i) -> Terms.tm hsym Γ s) (G : wtree -> So s) (γ : ictx Γ) :
  (forall y, sv (R y) γ ≡ G (sv y γ)) ->
  forall bs (a : args hsym Γ (cargs i bs)),
  sargs PSet So Iy (sbuild i s R bs a) (penv PSet So Γ) γ
  ≡ sbval i s bs (fst (cvals i bs (sargs PSet So Iy a (penv PSet So Γ) γ)))
      (map (fun y => (y, G y)) (snd (cvals i bs (sargs PSet So Iy a (penv PSet So Γ) γ)))).
Proof.
  intros HR bs. induction bs as [|[|] bs IH]; intros a; [exact Logic.I| |].
  - rewrite (cvals_proper i (true :: bs) (sargs PSet So Iy a (penv PSet So Γ) γ) _
               (sargs_eta_at (σ := ι tN) (Θ := cargs i bs) a γ)).
    cbn [sbuild sargs cvals fst snd tl hd sbval].
    split; [apply IH|]. intros t. exact (peq_trans (stms0_at (b := tN) (ahd a) γ t) (peq_sym (stms0_at (b := tN) (ahd a) γ tt))).
  - rewrite (cvals_proper i (false :: bs) (sargs PSet So Iy a (penv PSet So Γ) γ) _
               (sargs_eta_at (σ := ι (tW i)) (Θ := cargs i bs) a γ)).
    cbn [sbuild sargs cvals fst snd tl hd sbval map].
    split; [split|].
    + apply IH.
    + intros t. eapply peq_trans; [exact (stms0_at (b := s) (R (ahd a)) γ t)|]. cbn.
      eapply peq_trans; [apply HR|]. rewrite <- (stms0_at (b := tW i) (ahd a) γ tt). apply peq_refl.
    + intros t. exact (peq_trans (stms0_at (b := tW i) (ahd a) γ t) (peq_sym (stms0_at (b := tW i) (ahd a) γ tt))).
Qed.

Lemma wrec_valid i s h bs (c : mem (dsc i) bs) γ :
  sv (r_lhs (free_calc_rules (inl (inr (existT _ i (existT _ s (existT _ h (existT _ bs c)))))))) γ
  ≡ sv (r_rhs (free_calc_rules (inl (inr (existT _ i (existT _ s (existT _ h (existT _ bs c)))))))) γ.
Proof.
  cbn [free_calc_rules ha_calc_rules crsum wrec_rules wrec_rule r_lhs r_rhs r_ctx].
  unfold wrec_lhs, wrec_rhs.
  set (Θs := steps i s). set (Θc := cargs i bs).
  set (Q := sargs PSet So Iy (lvars (Sym := hsym) Θs Θc) (penv PSet So (Θs ++ Θc)) γ).
  (* le membre gauche *)
  assert (EL : sv (WRec i s h (Con i bs c (rvars Θs Θc)) (lvars Θs Θc)) γ
               ≡ (proj PSet So (mvar (step_spec tN tW i s) c) Q : pmor _ _)
                   (sbval i s bs (fst (cvals i bs (sargs PSet So Iy (rvars (Sym := hsym) Θs Θc) (penv PSet So _) γ)))
                      (map (fun y => (y, wrec_val i s Q y))
                         (snd (cvals i bs (sargs PSet So Iy (rvars (Sym := hsym) Θs Θc) (penv PSet So _) γ)))))).
  { assert (Ex : (stms PSet So Iy (σ := ι (tW i)) (Con i bs c (rvars Θs Θc)) (penv PSet So _) γ : pmor _ _) tt
                 = sv (Con i bs c (rvars Θs Θc)) γ) by exact (stms0_at (b := tW i) (Con i bs c (rvars Θs Θc)) γ tt).
    eapply (peq_trans (y := wrec_val i s Q (sv (Con i bs c (rvars Θs Θc)) γ))).
    - change (wrec_val i s Q ((stms PSet So Iy (σ := ι (tW i)) (Con i bs c (rvars Θs Θc)) (penv PSet So _) γ : pmor _ _) tt)
              ≡ wrec_val i s Q (sv (Con i bs c (rvars Θs Θc)) γ)).
      rewrite Ex. apply peq_refl.
    - rewrite <- sget_mvar. apply peq_refl. }
  eapply peq_trans; [exact EL|]. clear EL.
  (* les deux pas coïncident *)
  assert (EP : proj PSet So (mvar (step_spec tN tW i s) c) Q ≡ proj PSet So (vl Θc (mvar (step_spec tN tW i s) c)) γ).
  { unfold Q. eapply peq_trans.
    - apply pfun_proper. exact (pset_equiv_at (sargs_etas' PSet So Iy Θs (fun τ z => vl Θc z) (penv PSet So _)) γ).
    - exact (pset_equiv_at (proj_tuple PSet So (mvar (step_spec tN tW i s) c) _) γ). }
  eapply peq_trans; [exact (EP _)|]. clear EP.
  refine (pfun_proper (proj PSet So (vl Θc (mvar (step_spec tN tW i s) c)) γ) (peq_sym _)).
  refine (sbuild_sem i s (fun y => WRec i s h y (lvars Θs Θc)) (wrec_val i s Q) γ _ bs (rvars Θs Θc)).
  intros y.
  assert (E3 : sv (WRec i s h y (lvars Θs Θc)) γ
               = wrec_val i s Q ((stms PSet So Iy (σ := ι (tW i)) y (penv PSet So _) γ : pmor _ _) tt)) by reflexivity.
  rewrite E3, (stms0_at (b := tW i) y γ tt). apply peq_refl.
Qed.

Lemma calc_valid i γ : sv (r_lhs (free_calc_rules i)) γ ≡ sv (r_rhs (free_calc_rules i)) γ.
Proof.
  destruct i as [[[[[s h] [|]]|[a [b [c w]]]]|[i [s [h [bs c]]]]]|[]].
  - apply recS_valid.
  - apply rec0_valid.
  - destruct w. apply beta_valid.
  - apply wrec_valid.
  - apply neq_valid.
Qed.

Definition Hc := pset_generated free_calc_rules So Iy calc_valid.

(** ** Les symboles logiques sont standard *)

Definition T0 : pmor (So tO) F := pmor_id (So tO).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation qs := (qsort hsym omega omega).

Lemma Himp q : T0 (Iy _ c_imp q) ≡ fimp (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Hand q : T0 (Iy _ c_and q) ≡ fand (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Hor q : T0 (Iy _ c_or q) ≡ for_ (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Htop q : T0 (Iy _ c_top q) ≡ ftop.
Proof. apply peq_refl. Qed.

Definition bsel (φ ψ : F) : pmor (disc bool) F :=
  fmor (X := disc bool) (fun c : pcar (disc bool) => if c then φ else ψ)
    (fun c c' (E : c = c') => match E with eq_refl => peq_refl _ end).

(** false = true (à la Leibniz) est uniformément équivalent à ⊥. *)
Lemma Hbot : fequiv (fun q => T0 (Iy _ c_bot q)) (fun _ => fbot).
Proof.
  exists (e_gen (e_comp e_inst (e_comp (e_pair e_id e_top) e_eval))), e_inst. intros q. split.
  - apply f_gen. intros φ. eapply f_comp.
    + exact (f_inst F _ (fun χ : pmor (disc bool) F => fimp (χ false) (χ true)) (bsel φ ftop)).
    + eapply f_comp; [apply f_pair; [apply f_id|apply f_top]|apply f_eval].
  - apply f_bot.
Qed.

Lemma Hall (k : qs) q :
  T0 (Iy _ (Order.q_all (projT1 k) (projT2 k)) q) ≡ fall (fun a : So (projT1 k) => T0 (snd q (up1 So _ a))).
Proof. destruct k. apply peq_refl. Qed.
Lemma Hex (k : qs) q :
  T0 (Iy _ (Order.q_ex (projT1 k) (projT2 k)) q) ≡ fex (fun a : So (projT1 k) => T0 (snd q (up1 So _ a))).
Proof. destruct k. apply peq_refl. Qed.

Lemma bsel_eqb (ψ : pmor (disc nat) F) a b : bsel (ψ b) (ψ a) (Nat.eqb a b) ≡ ψ a.
Proof.
  cbn. destruct (Nat.eqb a b) eqn:E; [|apply peq_refl].
  apply Nat.eqb_eq in E. subst b. apply peq_refl.
Qed.

(** (a =? b) = true est uniformément équivalent à l'égalité de Leibniz de nat. *)
Lemma eqN_equiv :
  fequiv (fun q : pcar (Qe tN) => leib (F := F) (A := disc bool) (Nat.eqb (snd q tt) (snd (fst q) tt)) true)
         (fun q : pcar (Qe tN) => leib (F := F) (A := disc nat) (snd q tt) (snd (fst q) tt)).
Proof.
  exists (e_gen e_inst), (e_gen (e_comp (e_pair e_inst (e_const (e_lam e_snd))) e_eval)).
  intros q. set (a := snd q tt). set (b := snd (fst q) tt). clearbody a b. split.
  - apply f_gen. intros ψ.
    apply (fent_eq_r _ _ _ _ (fimp_proper F _ _ _ _ (bsel_eqb ψ a b) (peq_refl _))).
    exact (f_inst F _ (fun χ : pmor (disc bool) F => fimp (χ (Nat.eqb a b)) (χ true)) (bsel (ψ b) (ψ a))).
  - apply f_gen. intros χ.
    set (ψ := fmor (X := disc nat) (fun z : pcar (disc nat) => fimp (χ (Nat.eqb a z)) (χ true))
                (fun z z' (E : z = z') => match E with eq_refl => peq_refl _ end)).
    eapply f_comp; [apply f_pair|apply f_eval].
    + exact (f_inst F _ (fun ψ0 : pmor (disc nat) F => fimp (ψ0 a) (ψ0 b)) ψ).
    + apply f_const. cbn.
      apply (fent_eq_r _ _ _ _ (fimp_proper F _ _ _ _ (pfun_proper χ (eq_sym (Nat.eqb_refl a))) (peq_refl _))).
      apply f_lam, f_snd.
Qed.

Lemma Heq (k : qs) :
  fequiv (fun q => T0 (Iy _ (Order.q_eq (projT1 k) (projT2 k)) q))
         (fun q => leib (snd q tt) (snd (fst q) tt)).
Proof.
  destruct k as [[| |a b|i] h]; [exact eqN_equiv| | |]; apply fequiv_of_eq; intros q; apply peq_refl.
Qed.

(** ** Le modèle de Free *)

Definition free_model := frame_lmodel F (generated free_calc_rules) tO So Iy Hc T0
  Himp Hand Hor Htop Hbot Hall Hex Heq.

(** Réalisabilité de Free. *)
Theorem free_sound Γ Ξ φ :
  provable Free Γ Ξ φ ->
  exists e, forall γ, fconj F (map (fun χ => T0 (sv χ γ)) Ξ) —[e]→ T0 (sv φ γ).
Proof. exact (frame_sound F (generated free_calc_rules) tO So Iy Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq Γ Ξ φ). Qed.

(** ** Le modèle de HA, par la traduction

    ⟦φ⟧_HA := ⟦φ^D⟧_Free : une preuve dans HA donne, par [ha_to_free], une
    preuve de la traduction dans Free, donc une évidence uniforme. *)

Theorem ha_sound Γ Ξ φ :
  sctx Γ -> provable HA Γ Ξ φ ->
  exists e, forall γ : ictx Γ,
    fconj F (map (fun χ => T0 (sv χ γ)) (rel_hyps Rel Γ ++ map (ltr Rel) Ξ)) —[e]→ T0 (sv (ltr Rel φ) γ).
Proof. intros HΓ H. apply free_sound, ha_to_free; assumption. Qed.

(** Un énoncé clos prouvable dans HA est réalisé. *)
Corollary ha_sound_closed φ :
  provable HA [] [] φ -> exists e, ftop —[e]→ sv (ltr Rel φ) tt.
Proof. intros H. destruct (free_sound _ _ _ (ha_to_free_closed φ H)) as [e He]. exists e. apply He. Qed.

(** La version équationnelle a le même modèle ([Equational.v]). *)
Corollary hae_sound_closed φ :
  provable (HAE (dsc := dsc)) [] [] φ -> exists e, ftop —[e]→ sv (ltr Rel φ) tt.
Proof. intros H. apply ha_sound_closed, hae_to_ha, H. Qed.

End Model.

(** ** Cohérence de HA_ω^{ω,ω}

    Dans le cadre [prop_frame], ⟦⊥⟧ est « false = true » au sens de
    Leibniz, qui n'est pas réalisé. *)
Theorem ha_consistent {Ind} (dsc : Ind -> list (list bool)) : ~ provable (HA (dsc := dsc)) [] [] Bot.
Proof.
  intros H. destruct (ha_sound_closed prop_frame (dsc := dsc) Bot H) as [e He].
  exact (proj1 (prop_fall _) (He Logic.I) (bsel prop_frame False True) Logic.I).
Qed.

Corollary hae_consistent {Ind} (dsc : Ind -> list (list bool)) : ~ provable (HAE (dsc := dsc)) [] [] Bot.
Proof. intros H. exact (ha_consistent dsc (hae_to_ha [] [] Bot H)). Qed.
