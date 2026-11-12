(** * Le cadre Mem-SCA : mémoïsation et non-déterminisme

    D'après Cohen, Faro et Tate (« The Effects of Effects on
    Constructivism », MFPS 2019, §5) et Cohen, Miquey et Tate (LICS 2021).
    Un langage de combinateurs avec
    - un **choix non déterministe** d'entier ([cNd] · a ⇝ n, pour tout n) ;
    - un **état** : une table d'allocation et une table de mémoïsation ;
    - la **mémoïsation** : [cMemo] · g alloue une case ℓ (où g est le
      générateur) et rend [cLook ℓ] ; [cLook ℓ] · n rend la valeur mémoïsée
      pour (ℓ, n) si elle existe, et sinon calcule g · n, puis l'inscrit.

    Les propositions sont les prédicats sur (état, code) stables par
    passage à un état futur (une extension de la liste d'entrées).
    L'entraînement φ —e→ ψ demande, dans tout état atteignable, que e · c
    termine sans blocage (prédicat inductif [safe]) et que *toutes* ses
    issues soient dans ψ.

    On prouve que ce cadre valide le choix dénombrable au niveau du
    tripos ([memo_cc] : [frame_cc]). Le réaliseur est la mémoïsation : la
    relation totale R(t, i) est réalisée par un générateur g qui peut
    rendre des témoins différents à chaque appel (non-déterminisme) ;
    [cLook ℓ] fige le premier, et la sous-relation déterminée S(t, i) dit
    « l'entrée (ℓ, t) de la table vaut c et i est l'indice choisi pour
    elle ».

    **Hypothèse méta-théorique** (la seule, nommée [CC_N]) : le choix sur
    les parties de ℕ, à valeurs dans un type quelconque. Il sert à fixer,
    pour chaque entrée possible de la table (un objet dénombrable,
    codé dans ℕ par [enc_x], injectif, construit sans axiome), un indice i
    tel que R(t, i) soit réalisé par la valeur inscrite. Comme les états
    sont des listes, l'indice ne dépend que du préfixe de l'état qui
    précède l'entrée : il est donc le même dans tous les futurs, ce qui
    rend S stable.

    Le **choix dépendant** ([memo_dc] : [frame_dc]) est réalisé de même,
    par la mémoïsation *récursive* ([cMemoR] : le générateur reçoit sa
    propre case et calcule l'entrée t + 1 à partir de l'entrée t lue dans
    la table). Il demande en plus le choix dépendant méta-théorique
    ([DC_N]) : l'indice de l'entrée t + 1 dépend de celui de l'entrée t,
    qui n'est pas un entier. *)

From Stdlib Require Import Bool List PeanoNat Lia Arith.Cantor.
From SF.Models Require Import PSet Frame FrameModel Tarski.
From SF.VE Require Import Trees Ind Cons Coll CC DC Sound.
From SF.SetTheory Require Import IZFe IZFeCC IZFeDC.
From SF.Logic Require Import Judgment Propositional.
Import ListNotations.

Set Default Proof Using "All".

(** ** Le langage *)

Inductive code : Type :=
| cId | cComp (f g : code) | cTop | cFst | cSnd | cPair (f g : code)
| cLam (f : code) | cClo (f a : code) | cEval | cFix (t : ctm)
| cPv (a b : code) | cNum (n : nat) | cNd | cMemo | cLook (l : nat) | cDec
| cCst (e : code) | cCan
(** La mémoïsation récursive : le générateur reçoit sa propre case. *)
| cMemoR
(** L'analyse de cas sur un numéral (avec un argument passé). *)
| cCase (z s : code)
(** Les expressions de l'opérade de point fixe ([eexp], [Ind.v]),
    à une variable (le point fixe lui-même). *)
with ctm : Type :=
| tvar | tcst (e : code) | tid | tcomp (a b : ctm) | ttop | tfst | tsnd
| tpair (a b : ctm) | tlam (a : ctm) | teval.

Fixpoint inst (t : ctm) (s : code) : code :=
  match t with
  | tvar => s
  | tcst e => e
  | tid => cId
  | tcomp a b => cComp (inst a s) (inst b s)
  | ttop => cTop
  | tfst => cFst
  | tsnd => cSnd
  | tpair a b => cPair (inst a s) (inst b s)
  | tlam a => cLam (inst a s)
  | teval => cEval
  end.

(** Le forçage d'un ⋀ (gelé en fonction) : c ↦ c · ⊤. *)
Definition cForce : code := cComp (cPair cId (cCst cTop)) cEval.
(** Un ⋀ gelé : c ↦ (⊤ ↦ e · c). *)
Definition cGen (e : code) : code := cLam (cComp cFst e).
(** Application à une constante : f ↦ f · x. *)
Definition cAppTo (x : code) : code := cComp (cPair cId (cCst x)) cEval.

(** Le test d'une étiquette : appliqué à un réaliseur de
    tagT = ⋀φψ. φ ⇒ ψ ⇒ φ (resp. tagF), il rend ⌜0⌝ (resp. ⌜1⌝),
    de façon déterminée malgré le non-déterminisme. *)
Definition cTst : code :=
  cComp cForce (cComp cForce (cComp (cAppTo (cNum 0)) (cAppTo (cNum 1)))).

(** Les réaliseurs canoniques des étiquettes et des entiers ⌜t⌝. *)
Definition cTagT : code := cCst (cCst (cLam cFst)).
Definition cTagF : code := cCst (cCst (cLam cSnd)).
Fixpoint can (n : nat) : code :=
  match n with O => cPv cTagT cTop | S m => cPv cTagF (can m) end.

(** ** Les états *)

Inductive entry : Type :=
| eAlloc (g : code)                (* la case ℓ (sa position) et son générateur *)
| eMemo (l n : nat) (c : code).    (* la valeur mémoïsée pour (ℓ, n) *)

Definition state := list entry.

Fixpoint find (σ : state) (l n : nat) : option code :=
  match σ with
  | [] => None
  | eMemo l' n' c :: σ => if Nat.eqb l l' && Nat.eqb n n' then Some c else find σ l n
  | eAlloc _ :: σ => find σ l n
  end.

Definition alloc (σ : state) (l : nat) : option code :=
  match nth_error σ l with Some (eAlloc g) => Some g | _ => None end.

(** Les futurs : les extensions. *)
Definition prefix (σ σ' : state) : Prop := exists δ, σ' = σ ++ δ.

(** ** La sémantique (à grands pas, non déterministe, avec état) *)

Inductive ev : state -> code -> code -> state -> code -> Prop :=
| ev_id σ a : ev σ cId a σ a
| ev_comp σ f g a σ1 b σ2 c : ev σ f a σ1 b -> ev σ1 g b σ2 c -> ev σ (cComp f g) a σ2 c
| ev_top σ a : ev σ cTop a σ cTop
| ev_fst σ a b : ev σ cFst (cPv a b) σ a
| ev_snd σ a b : ev σ cSnd (cPv a b) σ b
| ev_pair σ f g a σ1 b σ2 c : ev σ f a σ1 b -> ev σ1 g a σ2 c -> ev σ (cPair f g) a σ2 (cPv b c)
| ev_lam σ f a : ev σ (cLam f) a σ (cClo f a)
| ev_clo σ f a b σ' r : ev σ f (cPv a b) σ' r -> ev σ (cClo f a) b σ' r
| ev_eval σ h a σ' r : ev σ h a σ' r -> ev σ cEval (cPv h a) σ' r
| ev_fix σ t a σ' r : ev σ (inst t (cFix t)) a σ' r -> ev σ (cFix t) a σ' r
| ev_nd σ a n : ev σ cNd a σ (cNum n)
| ev_memo σ g : ev σ cMemo g (σ ++ [eAlloc g]) (cLook (length σ))
| ev_hit σ l n c : find σ l n = Some c -> ev σ (cLook l) (cNum n) σ c
| ev_miss σ l n g σ1 c : find σ l n = None -> alloc σ l = Some g -> ev σ g (cNum n) σ1 c ->
    find σ1 l n = None -> ev σ (cLook l) (cNum n) (σ1 ++ [eMemo l n c]) c
| ev_race σ l n g σ1 c c' : find σ l n = None -> alloc σ l = Some g -> ev σ g (cNum n) σ1 c ->
    find σ1 l n = Some c' -> ev σ (cLook l) (cNum n) σ1 c'
| ev_dec0 σ a b σ1 : ev σ cTst a σ1 (cNum 0) -> ev σ cDec (cPv a b) σ1 (cNum 0)
| ev_dec1 σ a b σ1 σ2 k : ev σ cTst a σ1 (cNum 1) -> ev σ1 cDec b σ2 (cNum k) ->
    ev σ cDec (cPv a b) σ2 (cNum (S k))
| ev_cst σ e a : ev σ (cCst e) a σ e
| ev_can σ n : ev σ cCan (cNum n) σ (can n)
| ev_memor σ g : ev σ cMemoR g (σ ++ [eAlloc (cClo g (cLook (length σ)))]) (cLook (length σ))
| ev_case0 σ z s a σ' r : ev σ z a σ' r -> ev σ (cCase z s) (cPv a (cNum 0)) σ' r
| ev_caseS σ z s a m σ' r : ev σ s (cPv a (cNum m)) σ' r -> ev σ (cCase z s) (cPv a (cNum (S m))) σ' r.

(** Terminaison sans blocage, sur toutes les branches. *)
Inductive safe : state -> code -> code -> Prop :=
| sf_id σ a : safe σ cId a
| sf_comp σ f g a : safe σ f a -> (forall σ1 b, ev σ f a σ1 b -> safe σ1 g b) -> safe σ (cComp f g) a
| sf_top σ a : safe σ cTop a
| sf_fst σ a b : safe σ cFst (cPv a b)
| sf_snd σ a b : safe σ cSnd (cPv a b)
| sf_pair σ f g a : safe σ f a -> (forall σ1 b, ev σ f a σ1 b -> safe σ1 g a) -> safe σ (cPair f g) a
| sf_lam σ f a : safe σ (cLam f) a
| sf_clo σ f a b : safe σ f (cPv a b) -> safe σ (cClo f a) b
| sf_eval σ h a : safe σ h a -> safe σ cEval (cPv h a)
| sf_fix σ t a : safe σ (inst t (cFix t)) a -> safe σ (cFix t) a
| sf_nd σ a : safe σ cNd a
| sf_memo σ g : safe σ cMemo g
| sf_hit σ l n c : find σ l n = Some c -> safe σ (cLook l) (cNum n)
| sf_miss σ l n g : find σ l n = None -> alloc σ l = Some g -> safe σ g (cNum n) -> safe σ (cLook l) (cNum n)
| sf_dec σ a b : safe σ cTst a ->
    (forall σ1 w, ev σ cTst a σ1 w -> w = cNum 0 \/ w = cNum 1) ->
    (forall σ1, ev σ cTst a σ1 (cNum 1) -> safe σ1 cDec b) ->
    safe σ cDec (cPv a b)
| sf_cst σ e a : safe σ (cCst e) a
| sf_can σ n : safe σ cCan (cNum n)
| sf_memor σ g : safe σ cMemoR g
| sf_case0 σ z s a : safe σ z a -> safe σ (cCase z s) (cPv a (cNum 0))
| sf_caseS σ z s a m : safe σ s (cPv a (cNum m)) -> safe σ (cCase z s) (cPv a (cNum (S m))).

(** Les états atteignables. *)
Inductive reach : state -> Prop :=
| rc_nil : reach []
| rc_step σ f a σ' r : reach σ -> ev σ f a σ' r -> reach σ'.

(** Le non-déterminisme est réel : [cNd] · ⊤ a une infinité d'issues. *)
Example nd_outcomes n : ev [] cNd cTop [] (cNum n).
Proof. constructor. Qed.

(** ** Préfixes *)

Lemma prefix_refl σ : prefix σ σ.
Proof. exists []. now rewrite app_nil_r. Qed.

Lemma prefix_trans a b c : prefix a b -> prefix b c -> prefix a c.
Proof. intros [d ->] [d' ->]. exists (d ++ d'). now rewrite app_assoc. Qed.

Lemma prefix_app σ δ : prefix σ (σ ++ δ).
Proof. now exists δ. Qed.

Lemma ev_prefix σ f a σ' r : ev σ f a σ' r -> prefix σ σ'.
Proof.
  induction 1; try apply prefix_refl; eauto using prefix_trans, prefix_app.
Qed.

Lemma prefix_nth p q k x : prefix p q -> nth_error p k = Some x -> nth_error q k = Some x.
Proof.
  intros [d ->] H. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
Qed.

Lemma prefix_len p q : prefix p q -> length p <= length q.
Proof. intros [d ->]. rewrite length_app. lia. Qed.

Lemma prefix_cmp p q σ : prefix p σ -> prefix q σ -> length p <= length q -> prefix p q.
Proof.
  intros [d Hd] [d' Hd'] Hl. subst σ.
  exists (firstn (length q - length p) d).
  assert (E : firstn (length q) (p ++ d) = firstn (length q) (q ++ d')) by now rewrite Hd'.
  rewrite (firstn_app (length q) p d), (firstn_all2 (n := length q) p ltac:(lia)) in E.
  rewrite (firstn_app (length q) q d'), (firstn_all2 (n := length q) q ltac:(lia)) in E.
  rewrite Nat.sub_diag, firstn_O, app_nil_r in E. exact (eq_sym E).
Qed.

Lemma prefix_snoc_inv p x q y : prefix (p ++ [x]) (q ++ [y]) -> (p = q /\ x = y) \/ prefix (p ++ [x]) q.
Proof.
  intros [d Hd]. destruct d as [|z d] using rev_ind.
  - rewrite app_nil_r in Hd. apply app_inj_tail in Hd. left. intuition congruence.
  - right. exists d. rewrite app_assoc in Hd. apply app_inj_tail in Hd. now destruct Hd.
Qed.

Lemma prefix_snoc p x σ : prefix (p ++ [x]) σ -> prefix p σ.
Proof. intros H. eapply prefix_trans; [apply prefix_app|exact H]. Qed.

(** ** La table de mémoïsation *)

Lemma find_app_some p d l n c : find p l n = Some c -> find (p ++ d) l n = Some c.
Proof.
  induction p as [|[g|l' n' c'] p IH]; cbn; [discriminate|exact IH|].
  destruct (Nat.eqb l l' && Nat.eqb n n'); [easy|exact IH].
Qed.

Lemma find_app_none p d l n : find p l n = None -> find (p ++ d) l n = find d l n.
Proof.
  induction p as [|[g|l' n' c'] p IH]; cbn; [easy|exact IH|].
  destruct (Nat.eqb l l' && Nat.eqb n n'); [discriminate|exact IH].
Qed.

Lemma find_last p l n c : find p l n = None -> find (p ++ [eMemo l n c]) l n = Some c.
Proof. intros H. rewrite (find_app_none _ _ _ _ H). cbn. now rewrite !Nat.eqb_refl. Qed.

Lemma find_split σ l n c : find σ l n = Some c ->
  exists p d, σ = p ++ eMemo l n c :: d /\ find p l n = None.
Proof.
  induction σ as [|[g|l' n' c'] σ IH]; cbn; [discriminate| |].
  - intros H. destruct (IH H) as (p & d & -> & Hp). now exists (eAlloc g :: p), d.
  - destruct (Nat.eqb l l' && Nat.eqb n n') eqn:E.
    + intros [= <-]. apply andb_prop in E as [E1 E2].
      apply Nat.eqb_eq in E1, E2. subst. now exists [], σ.
    + intros H. destruct (IH H) as (p & d & -> & Hp).
      exists (eMemo l' n' c' :: p), d. cbn. now rewrite E.
Qed.

Lemma find_prefix_some p l n c q : prefix (p ++ [eMemo l n c]) q -> exists c0, find q l n = Some c0.
Proof.
  intros [d ->]. destruct (find p l n) eqn:E.
  - exists c0. rewrite <- app_assoc. now apply find_app_some.
  - exists c. apply find_app_some, find_last, E.
Qed.

(** La première entrée pour (ℓ, n) dans un état est unique. *)
Lemma first_unique p q σ l n c c' :
  prefix (p ++ [eMemo l n c]) σ -> prefix (q ++ [eMemo l n c']) σ ->
  find p l n = None -> find q l n = None -> p = q /\ c = c'.
Proof.
  assert (K : forall p q c c', prefix (p ++ [eMemo l n c]) σ -> prefix (q ++ [eMemo l n c']) σ ->
             find q l n = None -> length p <= length q -> p = q /\ c = c').
  { clear. intros p q c c' Hp Hq Fq Hl.
    assert (H := prefix_cmp _ _ _ Hp Hq). rewrite !length_app in H. cbn in H.
    destruct (prefix_snoc_inv _ _ _ _ (H ltac:(lia))) as [[-> E]|H'].
    - split; [reflexivity|congruence].
    - destruct (find_prefix_some _ _ _ _ _ H') as [c0 E]. congruence. }
  intros Hp Hq Fp Fq.
  destruct (Nat.le_ge_cases (length p) (length q)) as [Hl|Hl].
  - exact (K p q c c' Hp Hq Fq Hl).
  - destruct (K q p c' c Hq Hp Fp Hl). split; congruence.
Qed.

(** ** L'invariant des états atteignables

    Toute entrée (ℓ, n, c) de la table a été inscrite par un calcul
    effectif du générateur de ℓ : g · ⌜n⌝ ⇝ c, depuis un état atteignable
    σ₁, en aboutissant à l'état σ₂ qui précède l'entrée. *)

Definition Inv (σ : state) : Prop :=
  forall σ2 l n c, prefix (σ2 ++ [eMemo l n c]) σ ->
  exists g σ1, reach σ1 /\ alloc σ1 l = Some g /\ prefix σ1 σ2 /\ ev σ1 g (cNum n) σ2 c.

Lemma ev_inv σ f a σ' r : ev σ f a σ' r -> reach σ -> Inv σ -> Inv σ'.
Proof.
  induction 1; intros Hr HI; eauto using rc_step.
  - intros σ2 l n c Hp. destruct (prefix_snoc_inv _ _ _ _ Hp) as [[_ E]|Hp']; [discriminate|].
    exact (HI _ _ _ _ Hp').
  - intros σ2 l' n' c' Hp. destruct (prefix_snoc_inv _ _ _ _ Hp) as [[-> E]|Hp'].
    + injection E as <- <- <-. exists g, σ. repeat split; eauto using ev_prefix.
    + exact (IHev Hr HI _ _ _ _ Hp').
  - intros σ2 l n c Hp. destruct (prefix_snoc_inv _ _ _ _ Hp) as [[_ E]|Hp']; [discriminate|].
    exact (HI _ _ _ _ Hp').
Qed.

Lemma reach_inv σ : reach σ -> Inv σ.
Proof.
  induction 1.
  - intros σ2 l n c [d Hd]. apply (f_equal (@length _)) in Hd. rewrite !length_app in Hd. cbn in Hd. lia.
  - eapply ev_inv; eassumption.
Qed.

(** ** Inversions *)

Lemma inv_id σ a σ' r : ev σ cId a σ' r -> σ' = σ /\ r = a.
Proof. inversion 1; auto. Qed.
Lemma inv_comp σ f g a σ' r : ev σ (cComp f g) a σ' r -> exists σ1 b, ev σ f a σ1 b /\ ev σ1 g b σ' r.
Proof. inversion 1; eauto. Qed.
Lemma inv_top σ a σ' r : ev σ cTop a σ' r -> σ' = σ /\ r = cTop.
Proof. inversion 1; auto. Qed.
Lemma inv_fst σ c σ' r : ev σ cFst c σ' r -> exists a b, c = cPv a b /\ σ' = σ /\ r = a.
Proof. inversion 1; eauto. Qed.
Lemma inv_snd σ c σ' r : ev σ cSnd c σ' r -> exists a b, c = cPv a b /\ σ' = σ /\ r = b.
Proof. inversion 1; eauto. Qed.
Lemma inv_pair σ f g a σ' r : ev σ (cPair f g) a σ' r ->
  exists σ1 b d, ev σ f a σ1 b /\ ev σ1 g a σ' d /\ r = cPv b d.
Proof. inversion 1; eauto 7. Qed.
Lemma inv_lam σ f a σ' r : ev σ (cLam f) a σ' r -> σ' = σ /\ r = cClo f a.
Proof. inversion 1; auto. Qed.
Lemma inv_clo σ f a b σ' r : ev σ (cClo f a) b σ' r -> ev σ f (cPv a b) σ' r.
Proof. inversion 1; auto. Qed.
Lemma inv_eval σ c σ' r : ev σ cEval c σ' r -> exists h a, c = cPv h a /\ ev σ h a σ' r.
Proof. inversion 1; eauto. Qed.
Lemma inv_fix σ t a σ' r : ev σ (cFix t) a σ' r -> ev σ (inst t (cFix t)) a σ' r.
Proof. inversion 1; auto. Qed.
Lemma inv_cst σ e a σ' r : ev σ (cCst e) a σ' r -> σ' = σ /\ r = e.
Proof. inversion 1; auto. Qed.
Lemma inv_can σ c σ' r : ev σ cCan c σ' r -> exists n, c = cNum n /\ σ' = σ /\ r = can n.
Proof. inversion 1; eauto. Qed.
Lemma inv_memo σ g σ' r : ev σ cMemo g σ' r -> σ' = σ ++ [eAlloc g] /\ r = cLook (length σ).
Proof. inversion 1; auto. Qed.
Lemma inv_look σ l c σ' r : ev σ (cLook l) c σ' r -> exists n, c = cNum n /\
  ((find σ l n = Some r /\ σ' = σ) \/
   (exists g σ1, find σ l n = None /\ alloc σ l = Some g /\ ev σ g (cNum n) σ1 r /\
                 find σ1 l n = None /\ σ' = σ1 ++ [eMemo l n r]) \/
   (exists g c0, find σ l n = None /\ alloc σ l = Some g /\ ev σ g (cNum n) σ' c0 /\
                 find σ' l n = Some r)).
Proof. inversion 1; subst; eexists; split; eauto 10. Qed.
Lemma inv_memor σ g σ' r : ev σ cMemoR g σ' r ->
  σ' = σ ++ [eAlloc (cClo g (cLook (length σ)))] /\ r = cLook (length σ).
Proof. inversion 1; auto. Qed.
Lemma inv_case σ z s c σ' r : ev σ (cCase z s) c σ' r -> exists a n, c = cPv a (cNum n) /\
  ((n = 0 /\ ev σ z a σ' r) \/ (exists m, n = S m /\ ev σ s (cPv a (cNum m)) σ' r)).
Proof. inversion 1; subst; eauto 8. Qed.
Lemma inv_dec σ c σ' r : ev σ cDec c σ' r -> exists a b, c = cPv a b /\
  ((ev σ cTst a σ' (cNum 0) /\ r = cNum 0) \/
   (exists σ1 k, ev σ cTst a σ1 (cNum 1) /\ ev σ1 cDec b σ' (cNum k) /\ r = cNum (S k))).
Proof. inversion 1; subst; eauto 10. Qed.

(** ** Issues *)

Definition Out (σ : state) (e c : code) (ψ : state -> code -> Prop) : Prop :=
  safe σ e c /\ forall σ' r, ev σ e c σ' r -> ψ σ' r.

Lemma Out_mono σ e c (ψ ψ' : state -> code -> Prop) :
  (forall σ' r, ψ σ' r -> ψ' σ' r) -> Out σ e c ψ -> Out σ e c ψ'.
Proof. intros H [S O]. split; [exact S|]. intros. apply H; eauto. Qed.

Lemma out_id σ a (ψ : state -> code -> Prop) : ψ σ a -> Out σ cId a ψ.
Proof. split; [constructor|]. intros σ' r E. apply inv_id in E as [-> ->]. exact H. Qed.

Lemma out_cst σ e a (ψ : state -> code -> Prop) : ψ σ e -> Out σ (cCst e) a ψ.
Proof. split; [constructor|]. intros σ' r E. apply inv_cst in E as [-> ->]. exact H. Qed.

Lemma out_lam σ f a (ψ : state -> code -> Prop) : ψ σ (cClo f a) -> Out σ (cLam f) a ψ.
Proof. split; [constructor|]. intros σ' r E. apply inv_lam in E as [-> ->]. exact H. Qed.

Lemma out_clo σ f a b ψ : Out σ f (cPv a b) ψ -> Out σ (cClo f a) b ψ.
Proof. intros [S O]. split; [now constructor|]. intros σ' r E. apply O, inv_clo, E. Qed.

Lemma out_eval σ h a ψ : Out σ h a ψ -> Out σ cEval (cPv h a) ψ.
Proof.
  intros [S O]. split; [now constructor|]. intros σ' r E.
  apply inv_eval in E as (h' & a' & [= <- <-] & E). exact (O _ _ E).
Qed.

Lemma out_fix σ t a ψ : Out σ (inst t (cFix t)) a ψ -> Out σ (cFix t) a ψ.
Proof. intros [S O]. split; [now constructor|]. intros σ' r E. apply O, inv_fix, E. Qed.

Lemma out_comp σ f g a (χ : state -> code -> Prop) :
  safe σ f a -> (forall σ1 b, ev σ f a σ1 b -> Out σ1 g b χ) -> Out σ (cComp f g) a χ.
Proof.
  intros S H. split.
  - constructor; [exact S|]. intros σ1 b E. exact (proj1 (H _ _ E)).
  - intros σ' r E. apply inv_comp in E as (σ1 & b & E1 & E2). exact (proj2 (H _ _ E1) _ _ E2).
Qed.

Lemma out_comp_fst σ e a b ψ : Out σ e a ψ -> Out σ (cComp cFst e) (cPv a b) ψ.
Proof.
  intros H. apply out_comp; [constructor|]. intros σ1 c E.
  apply inv_fst in E as (? & ? & [= <- <-] & -> & ->). exact H.
Qed.

Lemma out_appto σ c x ψ : Out σ c x ψ -> Out σ (cAppTo x) c ψ.
Proof.
  intros H. apply out_comp.
  - constructor; [constructor|]. intros. constructor.
  - intros σ1 b E. apply inv_pair in E as (σa & b1 & d & E1 & E2 & ->).
    apply inv_id in E1 as [-> ->]. apply inv_cst in E2 as [-> ->]. apply out_eval, H.
Qed.

Lemma out_force σ c ψ : Out σ c cTop ψ -> Out σ cForce c ψ.
Proof. apply out_appto. Qed.

(** ** Le cadre *)

Definition stable (P : state -> code -> Prop) : Prop :=
  forall σ σ' c, prefix σ σ' -> P σ c -> P σ' c.

Record mprop := MP { mp :> state -> code -> Prop; mp_st : stable mp }.

Definition MPS : pset := {|
  pcar := mprop;
  peq := fun φ ψ => forall σ c, φ σ c <-> ψ σ c;
  peq_refl := fun φ σ c => iff_refl _;
  peq_sym := fun φ ψ H σ c => iff_sym (H σ c);
  peq_trans := fun φ ψ χ H1 H2 σ c => iff_trans (H1 σ c) (H2 σ c)
|}.

Definition ment (φ : mprop) (e : code) (ψ : mprop) : Prop :=
  forall σ c, reach σ -> φ σ c -> Out σ e c ψ.

Program Definition mtop : mprop := MP (fun _ _ => True) _.
Next Obligation. now intros ? ? ? ? ?. Qed.

Program Definition mand (φ ψ : mprop) : mprop :=
  MP (fun σ c => exists a b, c = cPv a b /\ φ σ a /\ ψ σ b) _.
Next Obligation.
  intros σ σ' c P (a & b & -> & Ha & Hb). exists a, b. split; [reflexivity|].
  split; eapply mp_st; eassumption.
Qed.

Program Definition mimp (φ ψ : mprop) : mprop :=
  MP (fun σ c => forall σ', prefix σ σ' -> reach σ' -> forall a, φ σ' a -> Out σ' c a ψ) _.
Next Obligation. intros σ σ' c P H σ'' P' R a Ha. apply H; eauto using prefix_trans. Qed.

Program Definition mallP (S : mprop -> Prop) : mprop :=
  MP (fun σ c => forall ψ : mprop, S ψ -> forall σ', prefix σ σ' -> reach σ' -> Out σ' c cTop ψ) _.
Next Obligation. intros σ σ' c P H ψ Hψ σ'' P' R. apply H; eauto using prefix_trans. Qed.

Lemma m_proper (φ φ' : mprop) e (ψ ψ' : mprop) : (forall σ c, φ σ c <-> φ' σ c) -> (forall σ c, ψ σ c <-> ψ' σ c) ->
  ment φ e ψ -> ment φ' e ψ'.
Proof. intros E1 E2 H σ c R Hc. apply (Out_mono _ _ _ ψ); [apply E2|]. apply H, E1; assumption. Qed.

Lemma m_id φ : ment φ cId φ.
Proof. intros σ c _ Hc. now apply out_id. Qed.

Lemma m_comp φ ψ χ e1 e2 : ment φ e1 ψ -> ment ψ e2 χ -> ment φ (cComp e1 e2) χ.
Proof.
  intros H1 H2 σ c R Hc. destruct (H1 σ c R Hc) as [S O]. apply out_comp; [exact S|].
  intros σ1 b E. exact (H2 _ _ (rc_step _ _ _ _ _ R E) (O _ _ E)).
Qed.

Lemma m_top φ : ment φ cTop mtop.
Proof. intros σ c _ _. split; [constructor|]. now intros. Qed.

Lemma m_fst φ ψ : ment (mand φ ψ) cFst φ.
Proof.
  intros σ c _ (a & b & -> & Ha & _). split; [constructor|].
  intros σ' r E. apply inv_fst in E as (? & ? & [= <- <-] & -> & ->). exact Ha.
Qed.

Lemma m_snd φ ψ : ment (mand φ ψ) cSnd ψ.
Proof.
  intros σ c _ (a & b & -> & _ & Hb). split; [constructor|].
  intros σ' r E. apply inv_snd in E as (? & ? & [= <- <-] & -> & ->). exact Hb.
Qed.

Lemma m_pair φ ψ χ e1 e2 : ment φ e1 ψ -> ment φ e2 χ -> ment φ (cPair e1 e2) (mand ψ χ).
Proof.
  intros H1 H2 σ c R Hc. destruct (H1 σ c R Hc) as [S1 O1]. split.
  - constructor; [exact S1|]. intros σ1 b E.
    exact (proj1 (H2 _ _ (rc_step _ _ _ _ _ R E) (mp_st φ _ _ _ (ev_prefix _ _ _ _ _ E) Hc))).
  - intros σ' r E. apply inv_pair in E as (σ1 & b & d & E1 & E2 & ->).
    pose proof (R1 := rc_step _ _ _ _ _ R E1).
    pose proof (Hc1 := mp_st φ _ _ _ (ev_prefix _ _ _ _ _ E1) Hc).
    exists b, d. split; [reflexivity|]. split.
    + exact (mp_st ψ _ _ _ (ev_prefix _ _ _ _ _ E2) (O1 _ _ E1)).
    + exact (proj2 (H2 _ _ R1 Hc1) _ _ E2).
Qed.

Lemma m_lam φ ψ χ e : ment (mand φ ψ) e χ -> ment φ (cLam e) (mimp ψ χ).
Proof.
  intros H σ c R Hc. apply out_lam. intros σ' P R' a Ha. apply out_clo, H; [exact R'|].
  exists c, a. split; [reflexivity|]. split; [exact (mp_st φ _ _ _ P Hc)|exact Ha].
Qed.

Lemma m_eval ψ χ : ment (mand (mimp ψ χ) ψ) cEval χ.
Proof.
  intros σ c R (h & a & -> & Hh & Ha). apply out_eval. exact (Hh σ (prefix_refl σ) R a Ha).
Qed.

Lemma m_genP (S : mprop -> Prop) φ e : (forall ψ, S ψ -> ment φ e ψ) -> ment φ (cGen e) (mallP S).
Proof.
  intros H σ c R Hc. apply out_lam. intros ψ Hψ σ' P R'.
  apply out_clo, out_comp_fst, (H ψ Hψ); [exact R'|exact (mp_st φ _ _ _ P Hc)].
Qed.

Lemma m_instP (S : mprop -> Prop) ψ : S ψ -> ment (mallP S) cForce ψ.
Proof. intros Hψ σ c R Hc. apply out_force. exact (Hc ψ Hψ σ (prefix_refl σ) R). Qed.

Definition MF : frame := {|
  fprop := MPS; fev := code; fent := ment;
  fent_proper := m_proper;
  e_id := cId; f_id := m_id;
  e_comp := cComp; f_comp := m_comp;
  ftop := mtop; e_top := cTop; f_top := m_top;
  fand := mand;
  fand_proper := fun φ φ' ψ ψ' E1 E2 σ c =>
    conj (fun '(ex_intro _ a (ex_intro _ b (conj H (conj Ha Hb)))) =>
            ex_intro _ a (ex_intro _ b (conj H (conj (proj1 (E1 σ a) Ha) (proj1 (E2 σ b) Hb)))))
         (fun '(ex_intro _ a (ex_intro _ b (conj H (conj Ha Hb)))) =>
            ex_intro _ a (ex_intro _ b (conj H (conj (proj2 (E1 σ a) Ha) (proj2 (E2 σ b) Hb)))));
  e_fst := cFst; f_fst := m_fst; e_snd := cSnd; f_snd := m_snd;
  e_pair := cPair; f_pair := m_pair;
  fimp := mimp;
  fimp_proper := fun φ φ' ψ ψ' E1 E2 σ c =>
    conj (fun H σ' P R a Ha => Out_mono _ _ _ _ _ (fun σ'' r => proj1 (E2 σ'' r)) (H σ' P R a (proj2 (E1 σ' a) Ha)))
         (fun H σ' P R a Ha => Out_mono _ _ _ _ _ (fun σ'' r => proj2 (E2 σ'' r)) (H σ' P R a (proj1 (E1 σ' a) Ha)));
  e_lam := cLam; f_lam := m_lam; e_eval := cEval; f_eval := m_eval;
  fallP := mallP;
  fallP_proper := fun S T E σ c =>
    conj (fun H ψ Hψ => H ψ (proj2 (E ψ) Hψ)) (fun H ψ Hψ => H ψ (proj1 (E ψ) Hψ));
  e_gen := cGen; f_genP := m_genP; e_inst := cForce; f_instP := m_instP
|}.

Local Notation "φ ⊢[ e ] ψ" := (fent (F := MF) φ e ψ) (at level 70).

(** ** Propositions auxiliaires et règles dérivées *)

Program Definition num (n : nat) : mprop := MP (fun _ c => c = cNum n) _.
Next Obligation. now intros ? ? ? ? ?. Qed.

(** La réunion et l'intersection *méta* (non codées). *)
Program Definition Union {J : Type} (f : J -> mprop) : mprop := MP (fun σ c => exists j, f j σ c) _.
Next Obligation. intros σ σ' c P [j H]. exists j. eapply mp_st; eassumption. Qed.

Program Definition MetaAll {J : Type} (f : J -> mprop) : mprop := MP (fun σ c => forall j, f j σ c) _.
Next Obligation. intros σ σ' c P H j. eapply mp_st; eauto. Qed.

Program Definition Cond (P : Prop) (φ : mprop) : mprop := MP (fun σ c => P /\ φ σ c) _.
Next Obligation. intros σ σ' c P' [H1 H2]. split; [exact H1|eapply mp_st; eassumption]. Qed.

Lemma m_incl (φ ψ : mprop) : (forall σ c, φ σ c -> ψ σ c) -> φ ⊢[cId] ψ.
Proof. intros H σ c _ Hc. apply out_id, H, Hc. Qed.

Lemma m_union {J} (f : J -> mprop) e ψ : (forall j, f j ⊢[e] ψ) -> Union f ⊢[e] ψ.
Proof. intros H σ c R [j Hj]. exact (H j σ c R Hj). Qed.

Lemma m_cond P φ e ψ : (P -> φ ⊢[e] ψ) -> Cond P φ ⊢[e] ψ.
Proof. intros H σ c R [HP Hc]. exact (H HP σ c R Hc). Qed.

(** Une condition méta tirée des réaliseurs. *)
Lemma m_meta (P : Prop) (φ ψ : mprop) e : (forall σ c, reach σ -> φ σ c -> P) -> (P -> φ ⊢[e] ψ) -> φ ⊢[e] ψ.
Proof. intros H1 H2 σ c R Hc. exact (H2 (H1 σ c R Hc) σ c R Hc). Qed.

Lemma m_mall {J} (f : J -> mprop) : MetaAll f ⊢[cGen cId] fall (F := MF) f.
Proof. apply f_gen. intros j. apply m_incl. intros σ c H. exact (H j). Qed.

Lemma m_force {J} (j0 : J) (f : J -> mprop) : fall (F := MF) f ⊢[cForce] MetaAll f.
Proof.
  intros σ c R Hc. apply out_force.
  assert (H : forall j, Out σ c cTop (f j)).
  { intros j. exact (Hc (f j) (ex_intro _ j (peq_refl (p := MPS) (f j))) σ (prefix_refl σ) R). }
  split; [exact (proj1 (H j0))|]. intros σ' r E j. exact (proj2 (H j) _ _ E).
Qed.

Lemma fall_cst {J} (f : J -> mprop) σ x :
  (forall σ', prefix σ σ' -> reach σ' -> forall j, f j σ' x) -> fall (F := MF) f σ (cCst x).
Proof. intros H ψ [j Hj] σ' P R. apply out_cst, (proj2 (Hj σ' x)), H; assumption. Qed.

Lemma m_appto (φ ψ : mprop) x : (forall σ, φ σ x) -> mimp φ ψ ⊢[cAppTo x] ψ.
Proof. intros H σ c R Hc. apply out_appto, (Hc σ (prefix_refl σ) R), H. Qed.

(** Transporter une implication. *)
Definition cMap (p q : code) : code := cLam (cComp (cPair cFst (cComp cSnd p)) (cComp cEval q)).

Lemma m_map (φ φ' ψ ψ' : mprop) p q : φ' ⊢[p] φ -> ψ ⊢[q] ψ' -> fimp (F := MF) φ ψ ⊢[cMap p q] fimp (F := MF) φ' ψ'.
Proof.
  intros Hp Hq. apply (m_lam _ _ _ _).
  eapply m_comp; [apply m_pair; [apply m_fst|eapply m_comp; [apply m_snd|exact Hp]]|].
  eapply m_comp; [apply m_eval|exact Hq].
Qed.

Definition cMall (e : code) : code := cGen (cComp cForce e).

Lemma m_mapall {J} (f g : J -> mprop) e : (forall j, f j ⊢[e] g j) -> fall (F := MF) f ⊢[cMall e] fall (F := MF) g.
Proof. intros H. apply f_gen. intros j. eapply m_comp; [apply (f_inst MF J f j)|apply H]. Qed.

(** ** Les entiers ⌜t⌝ : codage canonique et décodage *)

Lemma tagT_can σ : tagT MF σ cTagT.
Proof.
  apply fall_cst. intros σ1 _ _ φ. apply fall_cst. intros σ2 _ _ ψ.
  intros σ3 _ _ a Ha. apply out_lam. intros σ4 P _ b _. apply out_clo.
  split; [constructor|]. intros σ' r E. apply inv_fst in E as (? & ? & [= <- <-] & -> & ->).
  eapply mp_st; eassumption.
Qed.

Lemma tagF_can σ : tagF MF σ cTagF.
Proof.
  apply fall_cst. intros σ1 _ _ φ. apply fall_cst. intros σ2 _ _ ψ.
  intros σ3 _ _ a Ha. apply out_lam. intros σ4 P _ b Hb. apply out_clo.
  split; [constructor|]. intros σ' r E. apply inv_snd in E as (? & ? & [= <- <-] & -> & ->). exact Hb.
Qed.

Lemma pnat_can t σ : pnat MF t σ (can t).
Proof.
  induction t; cbn.
  - exists cTagT, cTop. split; [reflexivity|]. split; [apply tagT_can|exact I].
  - exists cTagF, (can t). split; [reflexivity|]. split; [apply tagF_can|exact IHt].
Qed.

Lemma m_can t : num t ⊢[cCan] pnat MF t.
Proof.
  intros σ c _ Hc. cbn in Hc. subst c. split; [constructor|].
  intros σ' r E. apply inv_can in E as (n & [= <-] & -> & ->). apply pnat_can.
Qed.

Lemma m_tstT : tagT MF ⊢[cTst] num 0.
Proof.
  unfold cTst, tagT. eapply m_comp; [apply (f_inst MF _ _ (num 0))|].
  eapply m_comp; [apply (f_inst MF _ _ (num 1))|].
  eapply m_comp; apply m_appto; reflexivity.
Qed.

Lemma m_tstF : tagF MF ⊢[cTst] num 1.
Proof.
  unfold cTst, tagF. eapply m_comp; [apply (f_inst MF _ _ (num 0))|].
  eapply m_comp; [apply (f_inst MF _ _ (num 1))|].
  eapply m_comp; [apply m_appto; reflexivity|].
  intros σ c R Hc. apply out_appto. exact (Hc σ (prefix_refl σ) R _ eq_refl).
Qed.

Lemma m_dec t : pnat MF t ⊢[cDec] num t.
Proof.
  induction t; intros σ c R (a & b & -> & Ha & Hb).
  - destruct (m_tstT σ a R Ha) as [S O]. split.
    + constructor; [exact S| |].
      * intros σ1 w E. left. exact (O _ _ E).
      * intros σ1 E. discriminate (O _ _ E).
    + intros σ' r E. apply inv_dec in E as (? & ? & [= <- <-] & [[E ->]|(σ1 & k & E & _ & _)]).
      * reflexivity.
      * discriminate (O _ _ E).
  - destruct (m_tstF σ a R Ha) as [S O]. split.
    + constructor; [exact S| |].
      * intros σ1 w E. right. exact (O _ _ E).
      * intros σ1 E. exact (proj1 (IHt σ1 b (rc_step _ _ _ _ _ R E) (mp_st _ _ _ _ (ev_prefix _ _ _ _ _ E) Hb))).
    + intros σ' r E. apply inv_dec in E as (? & ? & [= <- <-] & [[E _]|(σ1 & k & E & E' & ->)]).
      * discriminate (O _ _ E).
      * pose proof (Hb1 := mp_st _ _ _ _ (ev_prefix _ _ _ _ _ E) Hb).
        pose proof (H := proj2 (IHt σ1 b (rc_step _ _ _ _ _ R E) Hb1) _ _ E'). cbn in H |- *.
        now injection H as ->.
Qed.

(** ** Petitesse de Φ et point fixe *)

Program Definition mdec (P : state -> code -> Prop) : mprop :=
  MP (fun σ c => exists σ0, prefix σ0 σ /\ P σ0 c) _.
Next Obligation. intros σ σ' c P' (σ0 & H & Hc). exists σ0. eauto using prefix_trans. Qed.

Lemma mdec_enc (φ : MPS) : @peq MPS (mdec (mp φ)) φ.
Proof.
  intros σ c. split.
  - intros (σ0 & P & H). eapply mp_st; eassumption.
  - intros H. exists σ. split; [apply prefix_refl|exact H].
Qed.

Fixpoint toct (a : eexp MF) : ctm :=
  match a with
  | ex_var _ => tvar
  | ex_cst _ e => tcst e
  | ex_id _ => tid
  | ex_comp _ a b => tcomp (toct a) (toct b)
  | ex_top _ => ttop
  | ex_fst _ => tfst
  | ex_snd _ => tsnd
  | ex_pair _ a b => tpair (toct a) (toct b)
  | ex_lam _ a => tlam (toct a)
  | ex_eval _ => teval
  | ex_gen _ a => tlam (tcomp tfst (toct a))
  | ex_inst _ => tcomp (tpair tid (tcst (cCst cTop))) teval
  end.

Lemma eeval_toct s a : eeval MF s a = inst (toct a) s.
Proof. induction a; cbn; try reflexivity; try (rewrite IHa1, IHa2; reflexivity); rewrite IHa; reflexivity. Qed.

Definition mfix (a : eexp MF) : code := cFix (toct a).

Lemma mfix_spec a φ ψ : φ ⊢[eeval MF (mfix a) a] ψ -> φ ⊢[mfix a] ψ.
Proof. rewrite eeval_toct. intros H σ c R Hc. apply out_fix, H; assumption. Qed.

(** ** Progrès : un calcul sûr a une issue

    D'où la non-trivialité : ⊥ n'est réalisé nulle part. *)

Lemma dec_num σ b σ' r : ev σ cDec b σ' r -> exists k, r = cNum k.
Proof. intros E. apply inv_dec in E as (? & ? & _ & [[_ ->]|(_ & k & _ & _ & ->)]); eauto. Qed.

Lemma progress σ f a : safe σ f a -> exists σ' r, ev σ f a σ' r.
Proof.
  induction 1; try (exists σ, (cNum 0); now constructor);
    try (do 2 eexists; constructor; eassumption); try (do 2 eexists; now constructor).
  - destruct IHsafe as (σ1 & b & E1). destruct (H1 _ _ E1) as (σ2 & c & E2). eauto using ev.
  - destruct IHsafe as (σ1 & b & E1). destruct (H1 _ _ E1) as (σ2 & c & E2). eauto using ev.
  - destruct IHsafe as (σ' & r & E). eauto using ev.
  - destruct IHsafe as (σ' & r & E). eauto using ev.
  - destruct IHsafe as (σ' & r & E). eauto using ev.
  - destruct IHsafe as (σ1 & c & E). destruct (find σ1 l n) eqn:F1; eauto using ev.
  - destruct IHsafe as (σ1 & w & E). destruct (H0 _ _ E) as [->| ->]; [eauto using ev|].
    destruct (H2 _ E) as (σ2 & r & E'). destruct (dec_num _ _ _ _ E') as [k ->]. eauto using ev.
  - destruct IHsafe as (σ' & r & E). eauto using ev.
  - destruct IHsafe as (σ' & r & E). eauto using ev.
Qed.

Program Definition mempty : mprop := MP (fun _ _ => False) _.
Next Obligation. now intros ? ? ? ? ?. Qed.

(** ⊥ n'est pas réalisé : le cadre n'est pas trivial. *)
Lemma fbot_empty σ c : reach σ -> ~ fbot (F := MF) σ c.
Proof.
  intros R H. destruct (H mempty (ex_intro _ mempty (peq_refl (p := MPS) mempty)) σ (prefix_refl σ) R) as [S O].
  destruct (progress _ _ _ S) as (σ' & r & E). exact (O _ _ E).
Qed.

Lemma not_top_bot e : ~ (ftop ⊢[e] fbot (F := MF)).
Proof.
  intros H. destruct (H [] cTop rc_nil I) as [S O]. destruct (progress _ _ _ S) as (σ' & r & E).
  exact (fbot_empty σ' r (rc_step _ _ _ _ _ rc_nil E) (O _ _ E)).
Qed.

(** ** Les entrées possibles de la table sont dénombrables

    Un codage injectif dans ℕ, par l'appariement de Cantor ; sans axiome. *)

Local Notation pr a b := (to_nat (a, b)).

Fixpoint ec (x : code) : nat :=
  match x with
  | cId => pr 0 0 | cComp f g => pr 1 (pr (ec f) (ec g)) | cTop => pr 2 0 | cFst => pr 3 0
  | cSnd => pr 4 0 | cPair f g => pr 5 (pr (ec f) (ec g)) | cLam f => pr 6 (ec f)
  | cClo f a => pr 7 (pr (ec f) (ec a)) | cEval => pr 8 0 | cFix t => pr 9 (et t)
  | cPv a b => pr 10 (pr (ec a) (ec b)) | cNum n => pr 11 n | cNd => pr 12 0 | cMemo => pr 13 0
  | cLook l => pr 14 l | cDec => pr 15 0 | cCst e => pr 16 (ec e) | cCan => pr 17 0
  | cMemoR => pr 18 0 | cCase z s => pr 19 (pr (ec z) (ec s))
  end
with et (t : ctm) : nat :=
  match t with
  | tvar => pr 0 0 | tcst e => pr 1 (ec e) | tid => pr 2 0 | tcomp a b => pr 3 (pr (et a) (et b))
  | ttop => pr 4 0 | tfst => pr 5 0 | tsnd => pr 6 0 | tpair a b => pr 7 (pr (et a) (et b))
  | tlam a => pr 8 (et a) | teval => pr 9 0
  end.

Lemma tn_inj p q : to_nat p = to_nat q -> p = q.
Proof. intros H. rewrite <- (cancel_of_to p), <- (cancel_of_to q). now f_equal. Qed.

Ltac inj_pr :=
  repeat match goal with H : to_nat _ = to_nat _ |- _ =>
    apply tn_inj in H; pose proof (f_equal fst H); pose proof (f_equal snd H); cbn [fst snd] in *; clear H end;
  subst; try discriminate; try reflexivity.

Scheme code_mind := Induction for code Sort Prop with ctm_mind := Induction for ctm Sort Prop.

Lemma ec_et_inj : (forall x y, ec x = ec y -> x = y) /\ (forall t u, et t = et u -> t = u).
Proof.
  split; [apply (code_mind (fun x => forall y, ec x = ec y -> x = y) (fun t => forall u, et t = et u -> t = u))
         |apply (ctm_mind (fun x => forall y, ec x = ec y -> x = y) (fun t => forall u, et t = et u -> t = u))];
  intros; match goal with |- _ = ?y => destruct y end; cbn [ec et] in *; inj_pr; f_equal; eauto.
Qed.

Definition ee (x : entry) : nat :=
  match x with eAlloc g => pr 0 (ec g) | eMemo l n c => pr 1 (pr l (pr n (ec c))) end.

Fixpoint el (σ : state) : nat := match σ with [] => 0 | x :: σ => S (pr (ee x) (el σ)) end.

Definition enc_x (x : state * code * nat) : nat :=
  let '(σ, c, t) := x in pr (el σ) (pr (ec c) t).

Lemma enc_x_inj x y : enc_x x = enc_x y -> x = y.
Proof.
  assert (Hee : forall a b, ee a = ee b -> a = b).
  { destruct a, b; cbn [ee]; intros; inj_pr; f_equal; try (apply ec_et_inj; assumption). }
  assert (Hel : forall σ τ, el σ = el τ -> σ = τ).
  { induction σ; destruct τ; cbn [el]; intros H; try discriminate; [reflexivity|].
    apply Nat.succ_inj in H. inj_pr. f_equal; auto. }
  destruct x as [[σ c] t], y as [[τ d] u]. cbn [enc_x]. intros; inj_pr.
  repeat f_equal; auto. apply ec_et_inj; assumption.
Qed.

(** ** Le choix dénombrable par mémoïsation *)

Section Memo.

(** **L'hypothèse méta-théorique** : le choix sur les parties de ℕ (le
    domaine est {n ∣ ∃i. Q(n, i)}, le codomaine un type quelconque, une
    valeur par défaut [None] hors du domaine). C'est une conséquence de
    ZFC (et même de ZF + ACω), plus faible que le choix général. *)
Context (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i).

Lemma choice_x (I : Type) (Q : state * code * nat -> I -> Prop) :
  exists ch : state * code * nat -> option I, forall x, (exists i, Q x i) -> exists i, ch x = Some i /\ Q x i.
Proof.
  destruct (CC_N I (fun n i => exists x, enc_x x = n /\ Q x i)) as [f Hf].
  exists (fun x => f (enc_x x)). intros x [i Hi].
  destruct (Hf (enc_x x) (ex_intro _ i (ex_intro _ x (conj eq_refl Hi)))) as (j & E & y & Ey & Hj).
  apply enc_x_inj in Ey. subst y. eauto.
Qed.

Context (I : Type) (R : nat -> I -> mprop).

(** La relation, réunie en t : « c réalise R(t, i) pour un i ». *)
Definition U (t : nat) : mprop := Union (R t).

(** Ce que réalise le générateur. *)
Definition GenP : mprop := MetaAll (fun t => mimp (num t) (U t)).

(** La sous-relation déterminée, pour la case ℓ et le choix ch : la
    première entrée (ℓ, t) de la table vaut c, et i est l'indice choisi
    pour elle (il ne dépend que de l'état σ₂ qui la précède). *)
Program Definition Sm (ch : state * code * nat -> option I) (l t : nat) (i : I) : mprop :=
  MP (fun σ c => exists σ2, prefix (σ2 ++ [eMemo l t c]) σ /\ find σ2 l t = None /\
                            ch (σ2, c, t) = Some i /\ R t i σ2 c) _.
Next Obligation. intros σ σ' c P (σ2 & H & ?). exists σ2. eauto using prefix_trans. Qed.

(** Ce que rend la mémoïsation : une sous-relation S ⊆ R, déterminée,
    et un réaliseur de sa totalité. *)
Definition Look : mprop :=
  Union (fun S : nat -> I -> mprop =>
    Cond ((forall t i σ c, S t i σ c -> R t i σ c) /\
          (forall t i i' σ c c', S t i σ c -> S t i' σ c' -> i = i'))
         (MetaAll (fun t => mimp (num t) (Union (S t))))).

Lemma alloc_prefix σ σ' l g : alloc σ l = Some g -> prefix σ σ' -> alloc σ' l = Some g.
Proof.
  unfold alloc. destruct (nth_error σ l) as [[g'|]|] eqn:E; try discriminate. intros [= ->] P.
  now rewrite (prefix_nth _ _ _ _ P E).
Qed.

Lemma m_memo : GenP ⊢[cMemo] Look.
Proof.
  intros σ g R0 Hg. split; [constructor|]. intros σ' r E. apply inv_memo in E as [-> ->].
  set (l := length σ).
  assert (A0 : alloc (σ ++ [eAlloc g]) l = Some g).
  { unfold alloc, l. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  destruct (choice_x I (fun x i => R (snd x) i (fst (fst x)) (snd (fst x)))) as [ch Hch].
  (* Toute entrée (ℓ, t, c) d'un futur est un résultat effectif du générateur. *)
  assert (Good : forall t σ4 σ2 c, reach σ4 -> prefix (σ ++ [eAlloc g]) σ4 ->
                 prefix (σ2 ++ [eMemo l t c]) σ4 -> exists i, R t i σ2 c).
  { intros t σ4 σ2 c R4 P4 P2.
    destruct (reach_inv _ R4 _ _ _ _ P2) as (g' & σ1 & R1 & A1 & P1 & E1).
    pose proof (P14 := prefix_trans _ _ _ P1 (prefix_snoc _ _ _ P2)).
    assert (Eg : g' = g) by (pose proof (alloc_prefix _ _ _ _ A1 P14); pose proof (alloc_prefix _ _ _ _ A0 P4); congruence).
    subst g'.
    assert (L1 : l < length σ1).
    { unfold alloc in A1. destruct (nth_error σ1 l) eqn:N; [|discriminate]. apply nth_error_Some. congruence. }
    assert (P01 : prefix (σ ++ [eAlloc g]) σ1).
    { apply (prefix_cmp _ _ _ P4 P14). rewrite length_app. cbn. unfold l in L1. lia. }
    pose proof (Hg1 := mp_st GenP _ _ _ (prefix_snoc _ _ _ P01) Hg).
    exact (proj2 (Hg1 t σ1 (prefix_refl _) R1 (cNum t) eq_refl) _ _ E1). }
  assert (Hit : forall t σ4 c, reach σ4 -> prefix (σ ++ [eAlloc g]) σ4 -> find σ4 l t = Some c ->
                Union (Sm ch l t) σ4 c).
  { intros t σ4 c R4 P4 F4. destruct (find_split _ _ _ _ F4) as (p & d & -> & Fp).
    assert (Pp : prefix (p ++ [eMemo l t c]) (p ++ eMemo l t c :: d)) by (exists d; now rewrite <- app_assoc).
    destruct (Hch (p, c, t) (Good t _ _ _ R4 P4 Pp)) as (i & Ci & Ri).
    exists i, p. auto. }
  exists (Sm ch l). split; [split|].
  - intros t i σ3 c (σ2 & P & _ & _ & HR). exact (mp_st _ _ _ _ (prefix_snoc _ _ _ P) HR).
  - intros t i i' σ3 c c' (σ2 & P & F & C & _) (σ2' & P' & F' & C' & _).
    destruct (first_unique _ _ _ _ _ _ _ P P' F F') as [<- <-]. congruence.
  - intros t σ3 P3 R3 a Ha. cbn in Ha. subst a.
    pose proof (A3 := alloc_prefix _ _ _ _ A0 P3).
    pose proof (Hg3 := mp_st GenP _ _ _ (prefix_snoc _ _ _ P3) Hg t σ3 (prefix_refl _) R3 (cNum t) eq_refl).
    split.
    + destruct (find σ3 l t) eqn:F3; [eapply sf_hit; eassumption|].
      eapply sf_miss; [exact F3|exact A3|exact (proj1 Hg3)].
    + intros σ'' r E. apply inv_look in E as (n & [= <-] & [[F3 ->]|[(g0 & σ1 & F3 & A & E & F1 & ->)|(g0 & c0 & F3 & A & E & F1)]]).
      * exact (Hit t σ3 r R3 P3 F3).
      * rewrite A3 in A. injection A as <-.
        destruct (Hch (σ1, r, t) (proj2 Hg3 _ _ E)) as (i & Ci & Ri).
        exists i, σ1. repeat split; auto. apply prefix_refl.
      * rewrite A3 in A. injection A as <-.
        exact (Hit t σ'' r (rc_step _ _ _ _ _ R3 E) (prefix_trans _ _ _ P3 (ev_prefix _ _ _ _ _ E)) F1).
Qed.

End Memo.

(** ** Assemblage : le cadre valide [frame_cc] *)

Section Assemble.

Context (I : Type) (R : nat -> I -> mprop).

Lemma m_union_ex t (S : nat -> I -> mprop) : Union (S t) ⊢[e_exI (F := MF)] fex (F := MF) (S t).
Proof. apply m_union. intros i. apply (f_exI (F := MF) I (S t) i). Qed.

Definition cTotS : code := cComp (cGen cId) (cMall (cMap cDec (e_exI (F := MF)))).
Definition cSub : code := cGen (cGen (cLam (cComp cSnd cId))).
Definition cFun : code := cGen (cGen (cGen (cLam (cComp cSnd (cComp cTop (e_exI (F := MF))))))).
Definition cPack : code := cComp (cPair cTotS (cComp cTop (cPair cSub cFun))) (e_exI (F := MF)).

Lemma m_pack : Look I R ⊢[cPack] fex (F := MF) (fun S : nat -> I -> mprop => SPack MF R S).
Proof.
  apply m_union. intros S. apply m_cond. intros [Hsub Hfun].
  eapply m_comp; [|apply (f_exI (F := MF) _ (fun S => SPack MF R S) S)].
  apply m_pair.
  - eapply m_comp; [apply m_mall|]. apply m_mapall. intros t. apply m_map; [apply m_dec|apply m_union_ex].
  - apply (f_const (F := MF)). apply m_pair.
    + apply (f_gen MF). intros t. apply (f_gen MF). intros i. apply m_lam.
      eapply m_comp; [apply m_snd|]. apply m_incl. apply Hsub.
    + apply (f_gen MF). intros t. apply (f_gen MF). intros i. apply (f_gen MF). intros i'. apply m_lam.
      eapply m_comp; [apply m_snd|].
      apply (m_meta (i = i')).
      * intros σ c _ (a & b & _ & Ha & Hb). exact (Hfun _ _ _ _ _ _ Ha Hb).
      * intros E. apply (n_meta MF (i = i') _ E).
Qed.

Definition cHyp : code := cMall (cMap cCan (e_exE (F := MF) cId)).

Lemma m_hyp : fall (F := MF) (fun t => fimp (F := MF) (pnat MF t) (fex (F := MF) (fun i => R t i)))
  ⊢[cComp cHyp cForce] GenP I R.
Proof.
  eapply m_comp; [|apply (m_force 0)].
  apply m_mapall. intros t. apply m_map; [apply m_can|].
  apply (f_exE (F := MF) I (fun i => R t i) (U I R t) cId). intros i. apply m_incl. intros σ c H. now exists i.
Qed.

End Assemble.

(** Le réaliseur du choix dénombrable : la mémoïsation, entourée du
    décodage des entiers. *)
Definition cCC : code := cComp (cComp cHyp cForce) (cComp cMemo cPack).

Theorem memo_cc
  (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
            exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i) :
  frame_cc MF cCC.
Proof.
  intros I R. eapply m_comp; [apply m_hyp|]. eapply m_comp; [apply (m_memo CC_N)|apply m_pack].
Qed.

(** ** V(Mem) ⊨ IZFε + CC

    Φ est petit (Φ₀ := état → code → Prop, [mdec] reclôt par les futurs),
    le point fixe est le combinateur [cFix]. Restent en hypothèses : le
    choix sur les parties de ℕ ([CC_N], méta-théorique) et, comme pour
    toute instance de V(E) ici, la collection. *)

Section VMem.

Context (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i).
Context (coll : forall T, (T -> Trees.V MF) -> (Trees.V MF -> Trees.V MF -> pcar MF) -> Trees.V MF).
Context (coll_proper : forall T (xs xs' : T -> Trees.V MF) ψ ψ', Rproper MF ψ ->
           (forall t, teq MF (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq MF (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V MF) ψ, Rproper MF ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub MF (coll T xs ψ) s)).

Local Notation Iy0 := (Iy' MF (state -> code -> Prop) mp mdec coll coll_proper).

(** Un énoncé clos prouvable dans IZFε + CC est réalisé dans V(Mem). *)
Theorem ve_mem_cc φ : IZFeC [] [] φ -> exists e, ftop ⊢[e] T0 MF (sval (So' MF) Iy0 φ tt).
Proof.
  intros Hd.
  destruct (ve_sound_cc MF _ mp mdec mdec_enc mfix mfix_spec coll coll_proper coll_spec
              cCC (memo_cc CC_N) [] [] φ Hd) as [e He].
  exists e. exact (He tt).
Qed.

(** Cohérence de IZFε + CC (relativement à [CC_N] et à la collection). *)
Corollary izfe_cc_consistent : ~ IZFeC [] [] (Bot (Γ := [])).
Proof. intros Hd. destruct (ve_mem_cc _ Hd) as [e He]. exact (not_top_bot e He). Qed.

End VMem.

(** ** Le choix dépendant par mémoïsation récursive

    Le générateur de la case ℓ reçoit [cLook ℓ] : l'entrée t + 1 est
    calculée par h · a, où a est la première composante de l'entrée t,
    *lue dans la table*. Une issue de [cLook ℓ] · ⌜t⌝ est toujours la
    première entrée (ℓ, t) de l'état d'arrivée ; la suite des entrées est
    donc figée sur chaque branche, et chaque entrée est un successeur de la
    précédente. Le choix des indices se fait niveau par niveau : l'indice
    de l'entrée t + 1 dépend de celui de l'entrée t, d'où le choix
    dépendant méta-théorique. *)

(** Règles dérivées pour les nouvelles primitives. *)

Lemma m_case0 (φ ψ : mprop) z s : φ ⊢[z] ψ -> mand φ (num 0) ⊢[cCase z s] ψ.
Proof.
  intros H σ c R (a & b & -> & Ha & Hb). cbn in Hb. subst b.
  destruct (H σ a R Ha) as [S O]. split; [now constructor|].
  intros σ' r E. apply inv_case in E as (a' & n & [= <- <-] & [[_ E]|(m & [=] & _)]). exact (O _ _ E).
Qed.

Lemma m_caseS (φ ψ : mprop) z s m : mand φ (num m) ⊢[s] ψ -> mand φ (num (S m)) ⊢[cCase z s] ψ.
Proof.
  intros H σ c R (a & b & -> & Ha & Hb). cbn in Hb. subst b.
  assert (Hm : mand φ (num m) σ (cPv a (cNum m))) by (exists a, (cNum m); repeat split; exact Ha).
  destruct (H σ _ R Hm) as [S O]. split; [now constructor|].
  intros σ' r E. apply inv_case in E as (a' & n & [= <- <-] & [[[=] _]|(m' & [= <-] & E)]). exact (O _ _ E).
Qed.

Definition cUnpack : code := e_exE (F := MF) cId.

Lemma m_unpack {J} (f : J -> mprop) : fex (F := MF) f ⊢[cUnpack] Union f.
Proof. apply (f_exE (F := MF)). intros j. apply m_incl. intros σ c H. now exists j. Qed.

(** Garder un fait stable sur l'état. *)
Program Definition Keep (ψ : mprop) (P : state -> Prop) (HP : forall σ σ', prefix σ σ' -> P σ -> P σ') : mprop :=
  MP (fun σ c => ψ σ c /\ P σ) _.
Next Obligation. intros σ σ' c Pr [H1 H2]. split; [eapply mp_st; eassumption|eapply HP; eassumption]. Qed.

Lemma m_keep (φ ψ : mprop) (P : state -> Prop) HP e :
  (forall σ c, φ σ c -> P σ) -> φ ⊢[e] ψ -> φ ⊢[e] Keep ψ P HP.
Proof.
  intros H1 H2 σ c R Hc. destruct (H2 σ c R Hc) as [S O]. split; [exact S|].
  intros σ' r E. split; [exact (O _ _ E)|]. exact (HP _ _ (ev_prefix _ _ _ _ _ E) (H1 _ _ Hc)).
Qed.

Lemma choice_sc (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i)
  (I : Type) (Q : state * code -> I -> Prop) :
  exists ch : state * code -> option I, forall x, (exists i, Q x i) -> exists i, ch x = Some i /\ Q x i.
Proof.
  destruct (choice_x CC_N I (fun x i => Q (fst x) i)) as [ch Hch].
  exists (fun x => ch (x, 0)). intros x H. exact (Hch (x, 0) H).
Qed.

(** Le générateur : gf · ⟨hyp, ⟨L, ⌜n⌝⟩⟩. *)
Definition cRe : code := cPair (cPair cFst (cComp cSnd cFst)) (cComp cSnd cSnd).
Definition cZ : code := cComp cFst (cComp cFst cUnpack).
Definition cSa : code := cPair (cComp cFst cFst) (cComp (cPair (cComp cFst cSnd) cSnd) cEval).
Definition cSb : code := cPair (cComp cFst cSnd) (cComp cSnd cFst).
Definition cSc : code := cComp (cPair (cComp cFst cForce) cSnd) cEval.
Definition cS : code := cComp cSa (cComp cSb (cComp cSc cUnpack)).
Definition cGf : code := cComp cRe (cCase cZ cS).

Lemma alloc_pre σ σ' l g : alloc σ l = Some g -> prefix σ σ' -> alloc σ' l = Some g.
Proof.
  unfold alloc. destruct (nth_error σ l) as [[g'|]|] eqn:E; try discriminate. intros [= ->] P.
  now rewrite (prefix_nth _ _ _ _ P E).
Qed.

Section MemoDC.

(** **Les hypothèses méta-théoriques** : le choix sur les parties de ℕ
    (déjà utilisé pour CC) et le choix dépendant, sous la forme « une
    relation totale, indexée par l'étape, a une suite qui la suit ». *)
Context (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i).
Context (DC_N : forall (T : Type) (Rl : nat -> T -> T -> Prop) (t0 : T),
          (forall n x, exists y, Rl n x y) -> exists f : nat -> T, f 0 = t0 /\ forall n, Rl n (f n) (f (S n))).

Context (I : Type) (A P0 : I -> mprop) (R : I -> I -> mprop).

Local Notation Hm := (DHyp MF A P0 R).

Section Run.

Context (σ : state) (hyp : code) (Hh : Hm σ hyp).

Local Notation l := (length σ).
Local Notation L := (cLook (length σ)).
Local Notation G := (cClo (cClo cGf hyp) (cLook (length σ))).
Local Notation σa := (σ ++ [eAlloc (cClo (cClo cGf hyp) (cLook (length σ)))]).

Definition Q0 (x : state * code) (i : I) : Prop := mand (A i) (P0 i) (fst x) (snd x).
Definition Qs (g : state * code -> option I) (t : nat) (x : state * code) (j : I) : Prop :=
  exists σ2' c' i, prefix (σ2' ++ [eMemo l t c']) (fst x) /\ find σ2' l t = None /\
                   g (σ2', c') = Some i /\ mand (A j) (R i j) (fst x) (snd x).
Definition Qd (ch : nat -> state * code -> option I) (t : nat) : state * code -> I -> Prop :=
  match t with O => Q0 | S m => Qs (ch m) m end.

Context (ch : nat -> state * code -> option I)
        (Hch : forall t x, (exists i, Qd ch t x i) -> exists i, ch t x = Some i /\ Qd ch t x i).

Lemma Qs_st g t σ1 σ2 c j : prefix σ1 σ2 -> Qs g t (σ1, c) j -> Qs g t (σ2, c) j.
Proof.
  intros P (σ2' & c' & i & P' & F & C & H). exists σ2', c', i. cbn in *.
  split; [eapply prefix_trans; eassumption|]. split; [exact F|]. split; [exact C|].
  exact (mp_st (mand (A j) (R i j)) _ _ _ P H).
Qed.

Program Definition Sd (t : nat) (i : I) : mprop :=
  MP (fun σ' c => exists σ2, prefix (σ2 ++ [eMemo l t c]) σ' /\ find σ2 l t = None /\
                             ch t (σ2, c) = Some i /\ Qd ch t (σ2, c) i) _.
Next Obligation. intros σ1 σ2 c P (σ3 & H & ?). exists σ3. eauto using prefix_trans. Qed.

Lemma Qd_A t x i : Qd ch t x i -> exists a b, snd x = cPv a b /\ A i (fst x) a.
Proof.
  destruct t as [|m]; cbn.
  - intros (a & b & E & Ha & _). eauto.
  - intros (_ & _ & _ & _ & _ & _ & a & b & E & Ha & _). eauto.
Qed.

Definition LPt (t : nat) : mprop :=
  match t with O => mtop | S m => mimp (num m) (Union (Sd m)) end.

Program Definition OutT (t : nat) : mprop :=
  MP (fun σ' c => exists i, Qd ch t (σ', c) i) _.
Next Obligation.
  intros σ1 σ2 c P [i H]. exists i. destruct t as [|m]; cbn in *.
  - eapply (mp_st (mand (A i) (P0 i))); eassumption.
  - exact (Qs_st _ _ _ _ _ _ P H).
Qed.

Lemma OutT_Qd t σ' c : OutT t σ' c -> exists i, Qd ch t (σ', c) i.
Proof. exact (fun H => H). Qed.

Lemma out_keep σ0 e c (ψ : state -> code -> Prop) (P : state -> Prop) :
  (forall σ1 σ2, prefix σ1 σ2 -> P σ1 -> P σ2) -> P σ0 -> Out σ0 e c ψ ->
  Out σ0 e c (fun σ' r => ψ σ' r /\ P σ').
Proof.
  intros HP H0 [S O]. split; [exact S|]. intros σ' r E. split; [exact (O _ _ E)|].
  exact (HP _ _ (ev_prefix _ _ _ _ _ E) H0).
Qed.

(** Le pas du générateur, pour un indice précédent i fixé. *)
Lemma m_step i : mand Hm (mand (A i) mtop) ⊢[cComp cSb (cComp cSc cUnpack)]
                 Union (fun j => mand (A j) (R i j)).
Proof.
  eapply m_comp; [apply m_pair; [eapply m_comp; [apply m_fst|apply m_snd]|eapply m_comp; [apply m_snd|apply m_fst]]|].
  eapply m_comp; [|apply m_unpack].
  eapply m_comp; [apply m_pair; [eapply m_comp; [apply m_fst|apply (f_inst MF _ _ i)]|apply m_snd]|].
  apply m_eval.
Qed.

(** La spécification du générateur. *)
Lemma m_gen t : mand Hm (mand (LPt t) (num t)) ⊢[cGf] OutT t.
Proof.
  eapply m_comp.
  { apply m_pair; [apply m_pair; [apply m_fst|eapply m_comp; [apply m_snd|apply m_fst]]|].
    eapply m_comp; [apply m_snd|apply m_snd]. }
  destruct t as [|m].
  - apply m_case0. eapply m_comp; [apply m_fst|]. eapply m_comp; [apply m_fst|].
    intros σ' c R' Hc. apply (Out_mono _ _ _ (Union (fun i => mand (A i) (P0 i)))).
    + intros σ'' r [i H]. now exists i.
    + exact (m_unpack _ σ' c R' Hc).
  - apply m_caseS. unfold cS. eapply m_comp.
    { apply m_pair; [eapply m_comp; [apply m_fst|apply m_fst]|].
      eapply m_comp; [apply m_pair; [eapply m_comp; [apply m_fst|apply m_snd]|apply m_snd]|apply m_eval]. }
    intros σ' c R' (a & b & -> & Ha & [i (σ2 & P & F & C & Q)]).
    destruct (Qd_A _ _ _ Q) as (a' & b' & E & Ha'). cbn in E, Ha'. subst b.
    pose proof (Hb := m_step i σ' (cPv a (cPv a' b')) R'
                  (ex_intro _ a (ex_intro _ (cPv a' b') (conj eq_refl (conj Ha
                    (ex_intro _ a' (ex_intro _ b' (conj eq_refl (conj (mp_st _ _ _ _ (prefix_snoc _ _ _ P) Ha') Logic.I))))))))).
    apply (out_keep _ _ _ _ (fun σ'' => exists σ2' c', prefix (σ2' ++ [eMemo l m c']) σ'' /\
                                         find σ2' l m = None /\ ch m (σ2', c') = Some i)) in Hb.
    + revert Hb. apply Out_mono. intros σ'' r [[j Hj] (σ2' & c' & P' & F' & C')].
      exists j, σ2', c', i. auto.
    + intros σ1 σ3 P1 (p & c' & H & X). exists p, c'. eauto using prefix_trans.
    + exists σ2, (cPv a' b'). auto.
Qed.

Lemma alloc_a : alloc σa l = Some G.
Proof. unfold alloc. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma gen_out t σ1 : reach σ1 -> prefix σa σ1 -> LPt t σ1 L -> Out σ1 G (cNum t) (OutT t).
Proof.
  intros R1 P1 HL. apply out_clo, out_clo. apply (m_gen t σ1 _ R1).
  exists hyp, (cPv L (cNum t)). split; [reflexivity|]. split.
  - exact (mp_st Hm _ _ _ (prefix_snoc _ _ _ P1) Hh).
  - exists L, (cNum t). split; [reflexivity|split; [exact HL|reflexivity]].
Qed.

(** La totalité de [cLook ℓ] au niveau t, si elle vaut au niveau t − 1. *)
Lemma look_from t : (forall σ1, reach σ1 -> prefix σa σ1 -> LPt t σ1 L) ->
  forall σ3, reach σ3 -> prefix σa σ3 -> Out σ3 L (cNum t) (Union (Sd t)).
Proof.
  intros HL.
  assert (Good : forall σ4 p c, reach σ4 -> prefix σa σ4 -> prefix (p ++ [eMemo l t c]) σ4 ->
                 exists i, Qd ch t (p, c) i).
  { intros σ4 p c R4 P4 P2.
    destruct (reach_inv _ R4 _ _ _ _ P2) as (g' & σ1 & R1 & A1 & P1 & E1).
    pose proof (P14 := prefix_trans _ _ _ P1 (prefix_snoc _ _ _ P2)).
    assert (Eg : g' = G) by (pose proof (alloc_pre _ _ _ _ A1 P14); pose proof (alloc_pre _ _ _ _ alloc_a P4); congruence).
    subst g'.
    assert (L1 : l < length σ1).
    { unfold alloc in A1. destruct (nth_error σ1 l) eqn:N; [|discriminate]. apply nth_error_Some. congruence. }
    assert (P01 : prefix σa σ1).
    { apply (prefix_cmp _ _ _ P4 P14). rewrite length_app. cbn. lia. }
    apply OutT_Qd. exact (proj2 (gen_out t σ1 R1 P01 (HL σ1 R1 P01)) _ _ E1). }
  assert (Hit : forall σ4 c, reach σ4 -> prefix σa σ4 -> find σ4 l t = Some c -> Union (Sd t) σ4 c).
  { intros σ4 c R4 P4 F4. destruct (find_split _ _ _ _ F4) as (p & d & -> & Fp).
    assert (Pp : prefix (p ++ [eMemo l t c]) (p ++ eMemo l t c :: d)) by (exists d; now rewrite <- app_assoc).
    destruct (Hch t (p, c) (Good _ _ _ R4 P4 Pp)) as (i & Ci & Qi).
    exists i, p. auto. }
  intros σ3 R3 P3.
  pose proof (A3 := alloc_pre _ _ _ _ alloc_a P3).
  pose proof (Hg3 := gen_out t σ3 R3 P3 (HL σ3 R3 P3)).
  split.
  - destruct (find σ3 l t) eqn:F3; [eapply sf_hit; eassumption|].
    eapply sf_miss; [exact F3|exact A3|exact (proj1 Hg3)].
  - intros σ'' r E. apply inv_look in E as (n & [= <-] & [[F3 ->]|[(g0 & σ1 & F3 & A' & E & F1 & ->)|(g0 & c0 & F3 & A' & E & F1)]]).
    + exact (Hit σ3 r R3 P3 F3).
    + rewrite A3 in A'. injection A' as <-.
      destruct (Hch t (σ1, r) (OutT_Qd _ _ _ (proj2 Hg3 _ _ E))) as (i & Ci & Qi).
      exists i, σ1. repeat split; auto. apply prefix_refl.
    + rewrite A3 in A'. injection A' as <-.
      exact (Hit σ'' r (rc_step _ _ _ _ _ R3 E) (prefix_trans _ _ _ P3 (ev_prefix _ _ _ _ _ E)) F1).
Qed.

Lemma look_tot t : forall σ3, reach σ3 -> prefix σa σ3 -> Out σ3 L (cNum t) (Union (Sd t)).
Proof.
  induction t as [|m IH]; apply look_from.
  - intros. exact Logic.I.
  - intros σ1 R1 P1 σ' P' R' a Ha. cbn in Ha. subst a. apply IH; [exact R'|eapply prefix_trans; eassumption].
Qed.

(** Les propriétés de la suite. *)
Lemma Sd_A t i σ' c : Sd t i σ' c -> exists a b, c = cPv a b /\ A i σ' a.
Proof.
  intros (σ2 & P & _ & _ & Q). destruct (Qd_A _ _ _ Q) as (a & b & E & Ha). cbn in E, Ha.
  exists a, b. split; [exact E|]. exact (mp_st _ _ _ _ (prefix_snoc _ _ _ P) Ha).
Qed.

Lemma Sd_P0 i σ' c : Sd 0 i σ' c -> exists a b, c = cPv a b /\ P0 i σ' b.
Proof.
  intros (σ2 & P & _ & _ & a & b & E & _ & Hb). cbn in E, Hb.
  exists a, b. split; [exact E|]. exact (mp_st _ _ _ _ (prefix_snoc _ _ _ P) Hb).
Qed.

Lemma Sd_fun t i i' σ' c c' : Sd t i σ' c -> Sd t i' σ' c' -> i = i'.
Proof.
  intros (σ2 & P & F & C & _) (σ2' & P' & F' & C' & _).
  destruct (first_unique _ _ _ _ _ _ _ P P' F F') as [<- <-]. congruence.
Qed.

Lemma Sd_step t i j σ' c c' : Sd t i σ' c -> Sd (S t) j σ' c' -> exists a b, c' = cPv a b /\ R i j σ' b.
Proof.
  intros (p & P & F & C & _) (σ2 & P2 & _ & _ & σ2' & c1 & i' & P' & F' & C' & a & b & E & _ & Hb).
  cbn in P', E, Hb.
  pose proof (P'' := prefix_trans _ _ _ P' (prefix_snoc _ _ _ P2)).
  destruct (first_unique _ _ _ _ _ _ _ P P'' F F') as [<- <-].
  assert (E2 : Some i = Some i') by (rewrite <- C; exact C'). injection E2 as <-.
  exists a, b. split; [exact E|]. exact (mp_st _ _ _ _ (prefix_snoc _ _ _ P2) Hb).
Qed.

End Run.

(** Ce que rend la mémoïsation récursive. *)
Definition LookD : mprop :=
  Union (fun S : nat -> I -> mprop =>
    Cond ((forall t i σ' c, S t i σ' c -> exists a b, c = cPv a b /\ A i σ' a) /\
          (forall i σ' c, S 0 i σ' c -> exists a b, c = cPv a b /\ P0 i σ' b) /\
          (forall t i i' σ' c c', S t i σ' c -> S t i' σ' c' -> i = i') /\
          (forall t i j σ' c c', S t i σ' c -> S (Datatypes.S t) j σ' c' -> exists a b, c' = cPv a b /\ R i j σ' b))
         (MetaAll (fun t => mimp (num t) (Union (S t))))).

Lemma m_memor : Hm ⊢[cComp (cLam cGf) cMemoR] LookD.
Proof.
  intros σ hyp R0 Hh. apply out_comp; [constructor|]. intros σ1 b E. apply inv_lam in E as [-> ->].
  split; [constructor|]. intros σ' r E. apply inv_memor in E as [-> ->].
  (* Le choix des indices, niveau par niveau. *)
  destruct (choice_sc CC_N I Q0) as [ch0 H0].
  destruct (DC_N (state * code -> option I)
              (fun n g g' => forall x, (exists j, Qs σ g n x j) -> exists j, g' x = Some j /\ Qs σ g n x j)
              ch0) as (ch & E0 & Hs).
  { intros n g. exact (choice_sc CC_N I (Qs σ g n)). }
  assert (Hch : forall t x, (exists i, Qd σ ch t x i) -> exists i, ch t x = Some i /\ Qd σ ch t x i).
  { intros [|m] x; cbn; [rewrite E0; apply H0|apply Hs]. }
  exists (Sd σ ch). split; [split; [|split; [|split]]|].
  - exact (Sd_A σ hyp Hh ch Hch).
  - exact (Sd_P0 σ hyp Hh ch Hch).
  - exact (Sd_fun σ hyp Hh ch Hch).
  - exact (Sd_step σ hyp Hh ch Hch).
  - intros t σ3 P3 R3 a Ha. cbn in Ha. subst a. exact (look_tot σ hyp Hh ch Hch t σ3 R3 P3).
Qed.

Lemma m_fst_of (φ ψ : mprop) : (forall σ c, φ σ c -> exists a b, c = cPv a b /\ ψ σ a) -> φ ⊢[cFst] ψ.
Proof.
  intros H σ c _ Hc. destruct (H σ c Hc) as (a & b & -> & Ha). split; [constructor|].
  intros σ' r E. apply inv_fst in E as (? & ? & [= <- <-] & -> & ->). exact Ha.
Qed.

Lemma m_snd_of (φ ψ : mprop) : (forall σ c, φ σ c -> exists a b, c = cPv a b /\ ψ σ b) -> φ ⊢[cSnd] ψ.
Proof.
  intros H σ c _ Hc. destruct (H σ c Hc) as (a & b & -> & Hb). split; [constructor|].
  intros σ' r E. apply inv_snd in E as (? & ? & [= <- <-] & -> & ->). exact Hb.
Qed.

Lemma m_snd2_of (φ ψ : mprop) :
  (forall σ c, φ σ c -> exists a b b1 b2, c = cPv a b /\ b = cPv b1 b2 /\ ψ σ b2) -> φ ⊢[cComp cSnd cSnd] ψ.
Proof.
  intros H σ c _ Hc. destruct (H σ c Hc) as (a & b & b1 & b2 & -> & -> & Hb).
  apply out_comp; [constructor|]. intros σ1 r E. apply inv_snd in E as (? & ? & [= <- <-] & -> & ->).
  split; [constructor|]. intros σ' r E. apply inv_snd in E as (? & ? & [= <- <-] & -> & ->). exact Hb.
Qed.

Definition cSubD : code := cGen (cGen (cLam (cComp cSnd cFst))).
Definition cStartD : code := cGen (cLam (cComp cSnd cSnd)).
Definition cStepD : code := cGen (cGen (cGen (cLam (cComp cSnd (cComp cSnd cSnd))))).
Definition cPackD : code :=
  cComp (cPair cTotS (cComp cTop (cPair cSubD (cPair cFun (cPair cStartD cStepD))))) (e_exI (F := MF)).

Lemma m_packD : LookD ⊢[cPackD] fex (F := MF) (fun S : nat -> I -> mprop => DPack MF A P0 R S).
Proof.
  apply m_union. intros S. apply m_cond. intros (HA & HP & Hfun & Hstep).
  eapply m_comp; [|apply (f_exI (F := MF) _ (fun S => DPack MF A P0 R S) S)].
  apply m_pair.
  - eapply m_comp; [apply m_mall|]. apply m_mapall. intros t. apply m_map; [apply m_dec|].
    apply m_union. intros i. apply (f_exI (F := MF) I (S t) i).
  - apply (f_const (F := MF)). apply m_pair; [|apply m_pair; [|apply m_pair]].
    + apply (f_gen MF). intros t. apply (f_gen MF). intros i. apply m_lam.
      eapply m_comp; [apply m_snd|]. apply m_fst_of, HA.
    + apply (f_gen MF). intros t. apply (f_gen MF). intros i. apply (f_gen MF). intros i'. apply m_lam.
      eapply m_comp; [apply m_snd|].
      apply (m_meta (i = i')).
      * intros σ c _ (a & b & _ & Ha & Hb). exact (Hfun _ _ _ _ _ _ Ha Hb).
      * intros E. apply (n_meta MF (i = i') _ E).
    + apply (f_gen MF). intros i. apply m_lam. eapply m_comp; [apply m_snd|]. apply m_snd_of, HP.
    + apply (f_gen MF). intros t. apply (f_gen MF). intros i. apply (f_gen MF). intros j. apply m_lam.
      eapply m_comp; [apply m_snd|]. apply m_snd2_of.
      intros σ c (c1 & c2 & -> & H1 & H2). destruct (Hstep _ _ _ _ _ _ H1 H2) as (a & b & -> & Hb).
      exists c1, (cPv a b), a, b. auto.
Qed.

(** Le réaliseur du choix dépendant : la mémoïsation récursive. *)
Definition cDC : code := cComp (cComp (cLam cGf) cMemoR) cPackD.

Theorem memo_dc_gen : DHyp MF A P0 R ⊢[cDC] fex (F := MF) (fun S : nat -> I -> mprop => DPack MF A P0 R S).
Proof. eapply m_comp; [apply m_memor|apply m_packD]. Qed.

End MemoDC.


Theorem memo_dc
  (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
            exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i)
  (DC_N : forall (T : Type) (Rl : nat -> T -> T -> Prop) (t0 : T),
            (forall n x, exists y, Rl n x y) -> exists f : nat -> T, f 0 = t0 /\ forall n, Rl n (f n) (f (S n))) :
  frame_dc MF cDC.
Proof. intros I A P0 R. exact (memo_dc_gen CC_N DC_N I A P0 R). Qed.

(** ** V(Mem) ⊨ IZFε + DC *)

Section VMemD.

Context (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i).
Context (DC_N : forall (T : Type) (Rl : nat -> T -> T -> Prop) (t0 : T),
          (forall n x, exists y, Rl n x y) -> exists f : nat -> T, f 0 = t0 /\ forall n, Rl n (f n) (f (S n))).
Context (coll : forall T, (T -> Trees.V MF) -> (Trees.V MF -> Trees.V MF -> pcar MF) -> Trees.V MF).
Context (coll_proper : forall T (xs xs' : T -> Trees.V MF) ψ ψ', Rproper MF ψ ->
           (forall t, teq MF (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq MF (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V MF) ψ, Rproper MF ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub MF (coll T xs ψ) s)).

Local Notation Iy0 := (Iy' MF (state -> code -> Prop) mp mdec coll coll_proper).

(** Un énoncé clos prouvable dans IZFε + DC est réalisé dans V(Mem). *)
Theorem ve_mem_dc φ : IZFeD [] [] φ -> exists e, ftop ⊢[e] T0 MF (sval (So' MF) Iy0 φ tt).
Proof.
  intros Hd.
  destruct (ve_sound_dc MF _ mp mdec mdec_enc mfix mfix_spec coll coll_proper coll_spec
              cDC (memo_dc CC_N DC_N) [] [] φ Hd) as [e He].
  exists e. exact (He tt).
Qed.

(** Cohérence de IZFε + DC (relativement à [CC_N], [DC_N] et à la collection). *)
Corollary izfe_dc_consistent : ~ IZFeD [] [] (Bot (Γ := [])).
Proof. intros Hd. destruct (ve_mem_dc _ Hd) as [e He]. exact (not_top_bot e He). Qed.

End VMemD.
