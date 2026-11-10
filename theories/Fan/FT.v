(** * Le théorème de l'éventail dans HA_ω^{ω,ω} + listes

    FT est énoncé dans la théorie elle-même, avec la sorte L des listes
    d'entiers ([Terms.v]) : pour B : L → O,
      Mono(B) := ∀α:N→N. ∀n k. B(α↾n) ⇒ B(α↾(n+k)),
      Bar(B)  := ∀α. ∃n. B(α↾n),
      Unif(B) := ∃n. ∀α. B(α↾n),
      FT      := ∀B. Mono(B) ⇒ Bar(B) ⇒ Unif(B),
    où α↾n est la liste des sg(α i), i < n ([pret]).

    Son interprétation dans le modèle de HA sur un cadre F est celle de sa
    relativisée FT^D ([ltr_FT]). On la calcule ([sv_FTD]), puis on la relie
    à l'énoncé abstrait de [Statement.v] : pour toute donnée d'entiers E sur
    F, les codes de E et D_N sont uniformément équivalents, et FT(E) ≤ ⟦FT^D⟧
    ([FT_FTS]). Avec [Robust.v], on obtient [ft_realized]. Comme D_N est
    lui-même une donnée d'entiers sur tout cadre ([efD]), le théorème
    s'énonce aussi pour un cadre quelconque ([ft_realized_frame]). *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Extensions Require Import Same.
From SF.Models Require Import PSet Frame Semantics Tarski FrameTarski.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Ent Statement PR Robust Terms.
Set Universe Polymorphism.
Local Notation ι a := (Spec [] a).
Local Notation form := (Judgment.form hL tO).
Definition LO : T := tarr tL tO.
Definition Mono : form [ι LO] :=
  All NN (All tN (All tN (Imp (ap v3 (ap (ap pret v2) v1)) (ap v3 (ap (ap pret v2) (ap (ap addt v1) v0)))))).
Definition Bar : form [ι LO] := All NN (Ex tN (ap v2 (ap (ap pret v1) v0))).
Definition Unif : form [ι LO] := Ex tN (All NN (ap v2 (ap (ap pret v0) v1))).
Definition FT : form [] := All LO (Imp Mono (Imp Bar Unif)).
Definition RA (s : T) {Γ} (φ : form (ι s :: Γ)) : form Γ := All s (Imp (Dat s (D s) (var0 vz)) φ).
Definition RE (s : T) {Γ} (φ : form (ι s :: Γ)) : form Γ := Ex s (And (Dat s (D s) (var0 vz)) φ).
Definition MonoD : form [ι LO] :=
  RA NN (RA tN (RA tN (Imp (ap v3 (ap (ap pret v2) v1)) (ap v3 (ap (ap pret v2) (ap (ap addt v1) v0)))))).
Definition BarD : form [ι LO] := RA NN (RE tN (ap v2 (ap (ap pret v1) v0))).
Definition UnifD : form [ι LO] := RE tN (RA NN (ap v2 (ap (ap pret v0) v1))).
Definition FTD : form [] := RA LO (Imp MonoD (Imp BarD UnifD)).
Lemma ltr_FT : ltr (Rel (dsc := dL)) FT = FTD.
Proof. reflexivity. Qed.

(** ** Sémantique des formules dans le modèle d'un cadre *)

Section Sem.

Context (F : frame).

Local Notation So := (So F (Ind := unit)).
Local Notation sv := (sval So (Iy F (dsc := dL))).
Local Notation ictx := (ictx PSet So).
Local Notation V a := (pexp punit (So a)).
Local Notation Φ := (pcar (fprop F)).
Local Notation kv := (kv F).
Local Notation evs f v := (pfun f (tt, kv v)).
Local Notation evn f n := (pfun f (tt, kn F n)).

Lemma sv_Imp {Γ} (φ ψ : form Γ) γ : sv (Imp φ ψ) γ ≡ fimp (sv φ γ) (sv ψ γ).
Proof. exact (fimp_proper F _ _ _ _ (stms0_at F (b := tO) φ γ tt) (stms0_at F (b := tO) ψ γ tt)). Qed.

Lemma sv_And {Γ} (φ ψ : form Γ) γ : sv (And φ ψ) γ ≡ fand (sv φ γ) (sv ψ γ).
Proof. exact (fand_proper F _ _ _ _ (stms0_at F (b := tO) φ γ tt) (stms0_at F (b := tO) ψ γ tt)). Qed.

Lemma body_at {Γ} {a b : T} (t : Terms.tm hL (ι a :: Γ) b) (γ : ictx Γ) (v : V a) :
  stm PSet So (Iy F (dsc := dL)) t (ext PSet So [ι a] (penv PSet So Γ)) (γ, (tt, v)) ≡ sv t (γ, v).
Proof.
  set (h := Build_pmor (pprod (ictx Γ) (pprod punit (V a))) (pprod (ictx Γ) (V a))
              (fun q : pcar (pprod (ictx Γ) (pprod punit (V a))) => (fst q, snd (snd q)))
              (fun q q' E => conj (proj1 E) (proj2 (proj2 E)))).
  assert (He : env_eq PSet So (ext PSet So [ι a] (penv PSet So Γ)) (env_comp PSet So (penv PSet So (ι a :: Γ)) h)).
  { refine (var_inv _ _ _); [|intros σ y]; intros q; apply peq_refl. }
  pose proof (stm_ext PSet So (Iy F (dsc := dL)) t _ _ He (γ, (tt, v))) as E1.
  pose proof (stm_nat PSet So (Iy F (dsc := dL)) t (penv PSet So _) h (γ, (tt, v))) as E2.
  exact (peq_trans E1 (peq_sym E2)).
Qed.

Lemma sv_kv {Γ} {a b : T} (t : Terms.tm hL (ι a :: Γ) b) (γ : ictx Γ) (v : V a) (x : So a) :
  (forall u, (v : pmor _ _) u ≡ x) -> sv t (γ, v) ≡ sv t (γ, kv x).
Proof. intros H. apply pfun_proper. split; [apply peq_refl|intros u; exact (H u)]. Qed.

Lemma sv_All {Γ} (s : T) (φ : form (ι s :: Γ)) γ : sv (All s φ) γ ≡ fall (fun x : So s => sv φ (γ, kv x)).
Proof.
  apply (fall_proper F). intros x. refine (peq_trans (body_at φ γ _) (sv_kv φ γ _ x _)). intros u. apply peq_refl.
Qed.

Lemma sv_Ex {Γ} (s : T) (φ : form (ι s :: Γ)) γ : sv (Ex s φ) γ ≡ fex (fun x : So s => sv φ (γ, kv x)).
Proof.
  refine (@fex_proper F (pcar (So s)) _ _ _). intros x.
  refine (peq_trans (body_at φ γ _) (sv_kv φ γ _ x _)). intros u. apply peq_refl.
Qed.

Lemma sv_Dat {Γ} (s : T) (φ : form [ι s]) (t : Terms.tm hL Γ s) γ : sv (Dat s φ t) γ ≡ sv φ (tt, kv (sv t γ)).
Proof.
  pose proof (stm_vsubst PSet So (Iy F (dsc := dL)) φ (@acons _ hL Γ (ι s) [] t anil) (penv PSet So Γ) γ) as K.
  change (sv (Dat s φ t) γ ≡ pfun (stm PSet So (Iy F (dsc := dL)) φ (penv PSet So [ι s])) (pfun (sargs PSet So (Iy F (dsc := dL)) (@acons _ hL Γ (ι s) [] t anil) (penv PSet So Γ)) γ)) in K.
  refine (peq_trans K _).
  apply pfun_proper. split; [exact I|]. intros u. exact (stms0_at F (b := s) t γ u).
Qed.

(** La relativisation sémantique D_s. *)
Definition Dsem (s : T) (x : So s) : Φ := sv (D s) (tt, kv x).

Lemma Dsem_proper s (x x' : So s) : x ≡ x' -> Dsem s x ≡ Dsem s x'.
Proof. intros E. apply pfun_proper. split; [exact I|intros u; exact E]. Qed.

Lemma sv_RA (s : T) {Γ} (φ : form (ι s :: Γ)) γ :
  sv (RA s φ) γ ≡ fall (fun x : So s => fimp (Dsem s x) (sv φ (γ, kv x))).
Proof.
  eapply peq_trans; [apply sv_All|]. apply (fall_proper F). intros x.
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F); [|apply peq_refl]. apply sv_Dat.
Qed.

Lemma sv_RE (s : T) {Γ} (φ : form (ι s :: Γ)) γ :
  sv (RE s φ) γ ≡ fex (fun x : So s => fand (Dsem s x) (sv φ (γ, kv x))).
Proof.
  eapply peq_trans; [apply sv_Ex|]. refine (@fex_proper F (pcar (So s)) _ _ _). intros x.
  eapply peq_trans; [apply sv_And|]. apply (fand_proper F); [|apply peq_refl]. apply sv_Dat.
Qed.

Lemma Dsem_arr (a b : T) (f : So (tarr a b)) :
  Dsem (tarr a b) f ≡ fall (fun x : So a => fimp (Dsem a x) (Dsem b (evs f x))).
Proof.
  unfold Dsem at 1. cbn [D]. eapply peq_trans; [apply sv_All|]. apply (fall_proper F). intros x.
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F); [apply sv_Dat|].
  eapply peq_trans; [apply sv_Dat|]. apply Dsem_proper. exact (sv_ap F _ _ _).
Qed.

(** Les entiers : D_N(n) est la proposition « n est un entier » du second ordre. *)
Definition pO (f : nat -> Φ) : So (tarr tN tO).
Proof.
  refine (Build_pmor (pprod punit (V tN)) (fprop F) (fun q => f ((snd q : pmor _ _) tt)) _).
  intros q q' E. exact (match proj2 E tt in _ = z return f ((snd q : pmor _ _) tt) ≡ f z with eq_refl => peq_refl _ end).
Defined.

Definition codeN (n : nat) : Φ :=
  fall (fun X : So (tarr tN tO) =>
    fimp (evn X 0) (fimp (fall (fun m : nat => fimp (evn X m) (evn X (S m)))) (evn X n))).

Lemma Dsem_N n : Dsem tN n ≡ codeN n.
Proof.
  unfold Dsem. cbn [D]. unfold NatF. eapply peq_trans; [apply sv_All|]. apply (fall_proper F). intros X.
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F); [exact (sv_ap F _ _ _)|].
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F); [|exact (sv_ap F _ _ _)].
  eapply peq_trans; [apply sv_All|]. apply (fall_proper F). intros m.
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F); exact (sv_ap F _ _ _).
Qed.

(** *** Les règles des entiers pour D_N *)

Local Notation Step Y := (fall (fun m : nat => fimp (evn Y m) (evn Y (S m)))).

Lemma codeN_zero {X} (Γ : X -> Φ) : ENT Γ (fun _ => codeN 0).
Proof.
  unfold codeN. apply (ent_gen Γ (fun _ (Y : So (tarr tN tO)) => fimp (evn Y 0) (fimp (Step Y) (evn Y 0)))).
  apply ent_lam, ent_lam. eapply ent_trans; [apply ent_fst|apply ent_snd].
Qed.

Lemma codeN_succ : ENT codeN (fun n => codeN (S n)).
Proof.
  unfold codeN at 2. apply (ent_gen codeN (fun n (Y : So (tarr tN tO)) => fimp (evn Y 0) (fimp (Step Y) (evn Y (S n))))).
  apply ent_lam, ent_lam.
  set (C := fun x : nat * So (tarr tN tO) => fand (fand (codeN (fst x)) (evn (snd x) 0)) (Step (snd x))).
  assert (Hs : ENT C (fun x => Step (snd x))) by apply ent_snd.
  assert (H0 : ENT C (fun x => evn (snd x) 0)) by (eapply ent_trans; [apply ent_fst|apply ent_snd]).
  assert (Hc : ENT C (fun x => codeN (fst x))) by (eapply ent_trans; [apply ent_fst|apply ent_fst]).
  pose proof (ent_inst C (fun x (Y : So (tarr tN tO)) => fimp (evn Y 0) (fimp (Step Y) (evn Y (fst x)))) snd Hc) as K.
  cbv beta in K. pose proof (ent_app _ _ _ (ent_app _ _ _ K H0) Hs) as Kn.
  exact (ent_app _ _ _ (ent_inst C (fun x m => fimp (evn (snd x) m) (evn (snd x) (S m))) fst Hs) Kn).
Qed.

Definition RecS (f : nat -> Φ) : Φ :=
  fimp (f 0) (fimp (fall (fun n => fimp (codeN n) (fimp (f n) (f (S n))))) (fall (fun n => fimp (codeN n) (f n)))).

(** L'induction : on instancie D_N(n) par m ↦ D_N(m) ∧ f(m). *)
Lemma codeN_rec : ENT (fun _ : nat -> Φ => ftop) RecS.
Proof.
  unfold RecS. apply ent_lam, ent_lam.
  set (H := fun f : nat -> Φ => fall (fun n => fimp (codeN n) (fimp (f n) (f (S n))))).
  apply (ent_gen _ (fun f n => fimp (codeN n) (f n))). apply ent_lam.
  set (C := fun p : (nat -> Φ) * nat => fand (fand (fand ftop (fst p 0)) (H (fst p))) (codeN (snd p))).
  set (Y := fun p : (nat -> Φ) * nat => pO (fun m => fand (codeN m) (fst p m))).
  assert (Hc : ENT C (fun p => codeN (snd p))) by apply ent_snd.
  pose proof (ent_inst C (fun p (Z : So (tarr tN tO)) => fimp (evn Z 0) (fimp (Step Z) (evn Z (snd p)))) Y Hc) as K.
  cbv beta in K.
  assert (K0 : ENT C (fun p => evn (Y p) 0)).
  { apply ent_pair; [apply codeN_zero|]. eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|apply ent_snd]. }
  assert (KS : ENT C (fun p => Step (Y p))).
  { apply (ent_gen C (fun p m => fimp (evn (Y p) m) (evn (Y p) (S m)))). apply ent_lam.
    set (C2 := fun q : ((nat -> Φ) * nat) * nat => fand (C (fst q)) (fand (codeN (snd q)) (fst (fst q) (snd q)))).
    assert (Hm : ENT C2 (fun q => codeN (snd q))) by (eapply ent_trans; [apply ent_snd|apply ent_fst]).
    assert (Hf : ENT C2 (fun q => fst (fst q) (snd q))) by (eapply ent_trans; [apply ent_snd|apply ent_snd]).
    assert (HH : ENT C2 (fun q => H (fst (fst q)))).
    { eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|apply ent_snd]. }
    apply ent_pair; [exact (ent_trans _ _ _ Hm (ent_reindex snd _ _ codeN_succ))|].
    pose proof (ent_inst C2 (fun q n => fimp (codeN n) (fimp (fst (fst q) n) (fst (fst q) (S n)))) snd HH) as K1.
    exact (ent_app _ _ _ (ent_app _ _ _ K1 Hm) Hf). }
  exact (ent_snd' _ _ _ (ent_app _ _ _ (ent_app _ _ _ K K0) KS)).
Qed.

(** *** La forme sémantique de FT^D *)

Definition Bp (B : So LO) (α : So NN) (n : nat) : Φ := evs B (enc (map Nat.b2n (pre (sgb F α) n)) : So tL).

Definition MonoS (B : So LO) : Φ :=
  fall (fun α : So NN => fimp (Dsem NN α) (fall (fun n : So tN => fimp (Dsem tN n)
    (fall (fun k : So tN => fimp (Dsem tN k) (fimp (Bp B α n) (Bp B α (n + k)))))))).

Definition BarS (B : So LO) : Φ :=
  fall (fun α : So NN => fimp (Dsem NN α) (fex (fun n : So tN => fand (Dsem tN n) (Bp B α n)))).

Definition UnifS (B : So LO) : Φ :=
  fex (fun n : So tN => fand (Dsem tN n) (fall (fun α : So NN => fimp (Dsem NN α) (Bp B α n)))).

Definition FTS : Φ :=
  fall (fun B : So LO => fimp (Dsem LO B) (fimp (MonoS B) (fimp (BarS B) (UnifS B)))).

Lemma sv_pre {Γ} (a : Terms.tm hL Γ NN) (m : Terms.tm hL Γ tN) γ :
  sv (ap (ap pret a) m) γ ≡ (enc (map Nat.b2n (pre (sgb F (sv a γ)) (sv m γ))) : So tL).
Proof.
  eapply peq_trans; [exact (sv_ap F _ _ γ)|].
  eapply peq_trans; [exact (evs_proper F _ _ _ _ (sv_ap F pret a γ) (peq_refl _))|].
  exact (pre_sem F Γ γ (sv a γ) (sv m γ)).
Qed.

Lemma sv_Bp {Γ} (b : Terms.tm hL Γ LO) (a : Terms.tm hL Γ NN) (m : Terms.tm hL Γ tN) γ :
  sv (ap b (ap (ap pret a) m)) γ ≡ Bp (sv b γ) (sv a γ) (sv m γ).
Proof. eapply peq_trans; [exact (sv_ap F _ _ γ)|]. exact (evs_proper F _ _ _ _ (peq_refl _) (sv_pre a m γ)). Qed.

Lemma sv_FTD : sv FTD tt ≡ FTS.
Proof.
  unfold FTD, FTS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros B.
  apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F).
  { unfold MonoD, MonoS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros α.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros n.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros k.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F).
    - exact (sv_Bp _ _ _ _).
    - eapply peq_trans; [exact (sv_Bp _ _ _ _)|]. unfold Bp. rewrite (sv_ap2N F), (add_sem F). apply peq_refl. }
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F).
  - unfold BarD, BarS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros α.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RE|].
    refine (@fex_proper F (pcar (So tN)) _ _ _). intros n.
    apply (fand_proper F); [apply peq_refl|exact (sv_Bp _ _ _ _)].
  - unfold UnifD, UnifS. eapply peq_trans; [apply sv_RE|].
    refine (@fex_proper F (pcar (So tN)) _ _ _). intros n.
    apply (fand_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros α.
    apply (fimp_proper F); [apply peq_refl|exact (sv_Bp _ _ _ _)].
Qed.

End Sem.

(** ** Toute EF a des entiers : D_N

    Les entiers relativisés D_N forment une donnée d'entiers ([efdata]) sur
    n'importe quel cadre d'évidence. *)

Definition efD (F : frame) : efdata.
Proof.
  refine {| ef := F; code := codeN F |}.
  - destruct (codeN_zero F (fun _ : unit => ftop)) as [e He]. exists e. exact (He tt).
  - exact (codeN_succ F).
  - exact (codeN_rec F).
Defined.

(** ** Le transfert : FT d'une donnée d'entiers réalise FT^D

    Pour une donnée d'entiers E quelconque sur un cadre F, les codes de E
    et D_N sont uniformément équivalents (dans un sens par la récursion de
    E, dans l'autre en instanciant D_N par les codes de E). Les énoncés de
    [Statement.v] pour E et la sémantique de FT^D se correspondent donc : les
    chemins booléens α codés deviennent des α : N → N relativisés, et
    réciproquement par α ↦ sg ∘ α. *)

Section Transfer.

Context (E : efdata).

Local Notation F := (ef E).
Local Notation So := (So F (Ind := unit)).
Local Notation Φ := (pcar (fprop F)).
Local Notation "⌜ n ⌝" := (code (e := E) n).
Local Notation kv := (kv F).
Local Notation evs f v := (pfun f (tt, kv v)).
Local Notation DN n := (Dsem F tN n).

Lemma ex_map {X I : Type} (f g : X -> I -> Φ) :
  ENT (fun p : X * I => f (fst p) (snd p)) (fun p => g (fst p) (snd p)) ->
  ENT (fun x => fex (f x)) (fun x => fex (g x)).
Proof.
  intros H. eapply ent_trans; [apply (ent_pair _ (fun _ => ftop)); [apply ent_top|apply ent_refl]|].
  apply ent_exE. apply (ent_exI _ (fun p => g (fst p)) snd).
  eapply ent_trans; [apply ent_snd|exact H].
Qed.

Lemma code_N : ENT (fun n => ⌜n⌝) (codeN F).
Proof.
  destruct (crec E) as [e He].
  assert (R : ENT (fun n => ⌜n⌝) (fun _ => fimp (codeN F 0) (fimp (fall (fun m => fimp ⌜m⌝ (fimp (codeN F m) (codeN F (S m)))))
                                                       (fall (fun m => fimp ⌜m⌝ (codeN F m)))))).
  { eapply ent_trans; [apply ent_top|]. exists e. intros _. apply He. }
  assert (S0 : ENT (fun n => ⌜n⌝) (fun _ => fall (fun m => fimp ⌜m⌝ (fimp (codeN F m) (codeN F (S m)))))).
  { apply (ent_gen _ (fun _ m => fimp ⌜m⌝ (fimp (codeN F m) (codeN F (S m))))). apply ent_lam, ent_lam.
    eapply ent_trans; [apply ent_snd|exact (ent_reindex snd _ _ (codeN_succ F))]. }
  pose proof (ent_app _ _ _ (ent_app _ _ _ R (codeN_zero F _)) S0) as K.
  exact (ent_app _ _ _ (ent_inst _ (fun _ m => fimp ⌜m⌝ (codeN F m)) (fun n => n) K) (ent_refl _)).
Qed.

Lemma N_code : ENT (codeN F) (fun n => ⌜n⌝).
Proof.
  pose proof (ent_inst (codeN F) (fun n (Y : So (tarr tN tO)) => fimp (pfun Y (tt, kn F 0))
                (fimp (fall (fun m : nat => fimp (pfun Y (tt, kn F m)) (pfun Y (tt, kn F (S m))))) (pfun Y (tt, kn F n))))
                (fun _ => pO F (fun m => ⌜m⌝)) (ent_refl _)) as K.
  cbv beta in K. eapply ent_app; [eapply ent_app; [exact K|]|].
  - eapply ent_trans; [apply ent_top|]. destruct (c0 E) as [e He]. exists e. intros _. exact He.
  - apply (ent_gen _ (fun _ m => fimp ⌜m⌝ ⌜S m⌝)). apply ent_lam.
    eapply ent_trans; [apply ent_snd|]. destruct (cS E) as [e He]. exists e. intros p. apply He.
Qed.

Lemma rz_D {X} (Γ : X -> Φ) (n : X -> nat) : RZ E Γ n -> ENT Γ (fun x => DN (n x)).
Proof.
  intros H. eapply ent_eq_r; [intros x; apply peq_sym, Dsem_N|].
  exact (ent_trans _ _ _ H (ent_reindex n _ _ code_N)).
Qed.

Lemma D_rz {X} (Γ : X -> Φ) (n : X -> nat) : ENT Γ (fun x => DN (n x)) -> RZ E Γ n.
Proof.
  intros H. eapply ent_trans; [|exact (ent_reindex n _ _ N_code)].
  eapply ent_eq_r; [intros x; apply Dsem_N|exact H].
Qed.

(** Un chemin booléen, vu dans N → N. *)
Definition lb (α : nat -> bool) : So NN := pmN F (fun i => Nat.b2n (α i)).

Lemma pre_lb α n : pre (sgb F (lb α)) n = pre α n.
Proof. unfold pre. apply map_ext. intros i. unfold sgb, lb, pmN. cbn. destruct (α i); reflexivity. Qed.

Lemma cpath_D {X} (Γ : X -> Φ) (α : X -> nat -> bool) :
  ENT Γ (fun x => cpath E (α x)) -> ENT Γ (fun x => Dsem F NN (lb (α x))).
Proof.
  intros H. eapply ent_eq_r; [intros x; apply peq_sym, (Dsem_arr F)|].
  apply (ent_gen _ (fun x (m : So tN) => fimp (DN m) (DN (Nat.b2n (α x m))))). apply ent_lam.
  apply rz_D. eapply ent_app; [exact (ent_inst _ (fun p m => fimp ⌜m⌝ ⌜Nat.b2n (α (fst p) m)⌝) snd
                                       (ent_trans _ _ _ (ent_fst _ _) (ent_reindex fst _ _ H)))|].
  apply D_rz, ent_snd.
Qed.

Lemma D_cpath {X} (Γ : X -> Φ) (β : X -> So NN) :
  ENT Γ (fun x => Dsem F NN (β x)) -> ENT Γ (fun x => cpath E (sgb F (β x))).
Proof.
  intros H. eapply ent_eq_r in H; [|intros x; apply (Dsem_arr F)].
  apply ent_cpath. apply (rz_ext E _ (fun p : X * nat => 1 - (1 - pfun (β (fst p)) (tt, kn F (snd p))))).
  { intros p. unfold sgb. cbn beta. destruct (pfun (β (fst p)) (tt, kn F (snd p))); reflexivity. }
  apply rz_sub; [apply rz_const|]. apply rz_sub; [apply rz_const|]. apply D_rz.
  eapply ent_app; [exact (ent_inst _ (fun (p : X * nat) (m : So tN) => fimp (DN m) (DN (evs (β (fst p)) m))) snd
                            (ent_trans _ _ _ (ent_fst _ _) (ent_reindex fst _ _ H)))|].
  apply rz_D, ent_snd.
Qed.

(** Le prédicat B : L → O, vu sur les mots booléens. *)
Definition Bl (B : So LO) (l : list bool) : Φ := evs B (enc (map Nat.b2n l) : So tL).

Lemma Bp_lb B α n : Bp F B (lb α) n = Bl B (pre α n).
Proof. unfold Bp, Bl. rewrite pre_lb. reflexivity. Qed.

Lemma mono_tr : ENT (MonoS F) (fun B => Statement.Mono E (Bl B)).
Proof.
  apply (ent_gen _ (fun B α => fimp (cpath E α) _)). apply ent_lam.
  apply (ent_gen _ (fun p n => fimp ⌜n⌝ _)). apply ent_lam.
  apply (ent_gen _ (fun p k => fimp ⌜k⌝ _)). apply ent_lam. apply ent_lam.
  set (C := fun q : (((So LO * (nat -> bool)) * nat) * nat) =>
              fand (fand (fand (fand (MonoS F (fst (fst (fst q)))) (cpath E (snd (fst (fst q)))))
                          ⌜snd (fst q)⌝) ⌜snd q⌝) (Bl (fst (fst (fst q))) (pre (snd (fst (fst q))) (snd (fst q))))).
  change (ENT C (fun q => Bl (fst (fst (fst q))) (pre (snd (fst (fst q))) (snd (fst q) + snd q)))).
  assert (HM : ENT C (fun q => MonoS F (fst (fst (fst q))))).
  { do 3 (eapply ent_trans; [apply ent_fst|]). apply ent_fst. }
  assert (Ha : ENT C (fun q => Dsem F NN (lb (snd (fst (fst q)))))).
  { apply cpath_D. do 3 (eapply ent_trans; [apply ent_fst|]). apply ent_snd. }
  assert (Hn : ENT C (fun q => DN (snd (fst q)))).
  { apply rz_D. do 2 (eapply ent_trans; [apply ent_fst|]). apply ent_snd. }
  assert (Hk : ENT C (fun q => DN (snd q))).
  { apply rz_D. eapply ent_trans; [apply ent_fst|]. apply ent_snd. }
  assert (Hb : ENT C (fun q => Bp F (fst (fst (fst q))) (lb (snd (fst (fst q)))) (snd (fst q)))).
  { eapply ent_eq_r; [|apply ent_snd]. intros q. cbv beta. rewrite Bp_lb. apply peq_refl. }
  unfold MonoS in HM.
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun q => lb (snd (fst (fst q)))) HM) Ha) as K1. cbv beta in K1.
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun q => snd (fst q)) K1) Hn) as K2. cbv beta in K2.
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun q => snd q) K2) Hk) as K3. cbv beta in K3.
  pose proof (ent_app _ _ _ K3 Hb) as K4.
  eapply ent_eq_r; [|exact K4]. intros q. cbv beta. rewrite Bp_lb. apply peq_refl.
Qed.

Lemma bar_tr : ENT (BarS F) (fun B => Statement.Bar E (Bl B)).
Proof.
  apply (ent_gen _ (fun B α => fimp (cpath E α) _)). apply ent_lam.
  set (C := fun q : So LO * (nat -> bool) => fand (BarS F (fst q)) (cpath E (snd q))).
  assert (K : ENT C (fun q => fex (fun n : So tN => fand (DN n) (Bp F (fst q) (lb (snd q)) n)))).
  { eapply ent_app; [exact (ent_inst _ _ (fun q => lb (snd q)) (ent_fst _ _))|]. apply cpath_D, ent_snd. }
  eapply ent_trans; [exact K|]. apply ex_map. apply ent_pair.
  - apply D_rz, ent_fst.
  - eapply ent_eq_r; [|apply ent_snd]. intros p. cbv beta. rewrite Bp_lb. apply peq_refl.
Qed.

Lemma unif_tr : ENT (fun B => Statement.Unif E (Bl B)) (UnifS F).
Proof.
  apply ex_map. apply ent_pair; [apply rz_D, ent_fst|].
  apply (ent_gen _ (fun p (α : So NN) => fimp (Dsem F NN α) (Bp F (fst p) α (snd p)))). apply ent_lam.
  set (C := fun q : (So LO * nat) * So NN =>
              fand (fand ⌜snd (fst q)⌝ (fall (fun α => fimp (cpath E α) (Bl (fst (fst q)) (pre α (snd (fst q)))))))
                   (Dsem F NN (snd q))).
  change (ENT C (fun q => Bp F (fst (fst q)) (snd q) (snd (fst q)))).
  eapply ent_app.
  - exact (ent_inst _ (fun q α => fimp (cpath E α) (Bl (fst (fst q)) (pre α (snd (fst q))))) (fun q => sgb F (snd q))
             (ent_trans _ _ _ (ent_fst _ _) (ent_snd _ _))).
  - apply D_cpath, ent_snd.
Qed.

Lemma FT_FTS : ENT (fun _ : unit => Statement.FT E) (fun _ => FTS F).
Proof.
  unfold FTS.
  apply (ent_gen _ (fun _ (B : So LO) => fimp (Dsem F LO B) (fimp (MonoS F B) (fimp (BarS F B) (UnifS F B))))).
  apply ent_lam, ent_lam, ent_lam.
  set (C := fun p : unit * So LO => fand (fand (fand (Statement.FT E) (Dsem F LO (snd p))) (MonoS F (snd p))) (BarS F (snd p))).
  change (ENT C (fun p => UnifS F (snd p))).
  assert (H : ENT C (fun p => fimp (fand (Statement.Mono E (Bl (snd p))) (Statement.Bar E (Bl (snd p)))) (Statement.Unif E (Bl (snd p))))).
  { exact (ent_inst _ (fun _ B => fimp (fand (Statement.Mono E B) (Statement.Bar E B)) (Statement.Unif E B)) (fun p => Bl (snd p))
             (ent_trans _ _ _ (ent_fst _ _) (ent_trans _ _ _ (ent_fst _ _) (ent_fst _ _)))). }
  eapply ent_trans; [|exact (ent_reindex snd _ _ unif_tr)].
  eapply ent_app; [exact H|]. apply ent_pair.
  - eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_snd|exact (ent_reindex snd _ _ mono_tr)].
  - eapply ent_trans; [apply ent_snd|exact (ent_reindex snd _ _ bar_tr)].
Qed.

End Transfer.

(** ** Le théorème : FT est réalisé dans le modèle de HA_ω^{ω,ω} + listes

    Sur toute donnée d'entiers E avec recherche non bornée, existentiel fort
    au type (N → B) → N et continuité partout, sous WKL et Markov méta,
    l'interprétation de FT (relativisée : ⟦FT^D⟧) est réalisée. *)

Theorem ft_realized (E : efdata) :
  WKL_meta -> MP_meta -> search E -> choice E -> continuity E ->
  exists e, fent (F := ef E) ftop e (sval (So (ef E)) (Iy (ef E) (dsc := dL)) (ltr (Rel (dsc := dL)) FT) tt).
Proof.
  intros WKL MP HS HCh HCo. rewrite ltr_FT.
  destruct (fan_realized E WKL MP HS HCh HCo) as [e1 H1].
  destruct (FT_FTS E) as [e2 H2]. exists (e_comp e1 e2).
  apply (fent_eq_r _ _ _ _ (peq_sym (sv_FTD (ef E)))). eapply f_comp; [exact H1|exact (H2 tt)].
Qed.

(** Sur un cadre quelconque, avec les entiers D_N. *)
Corollary ft_realized_frame (F : frame) :
  WKL_meta -> MP_meta -> search (efD F) -> choice (efD F) -> continuity (efD F) ->
  exists e, fent (F := F) ftop e (sval (So F) (Iy F (dsc := dL)) (ltr (Rel (dsc := dL)) FT) tt).
Proof. exact (ft_realized (efD F)). Qed.

(** Conséquence : sur une EF cohérente qui satisfait les conditions,
    HA_ω^{ω,ω} + listes ne réfute pas FT. *)

Lemma ltr_negFT : ltr (Rel (dsc := dL)) (Imp FT Bot) = Imp FTD Bot.
Proof. reflexivity. Qed.

Corollary ha_not_refutes_FT (E : efdata) :
  WKL_meta -> MP_meta -> search E -> choice E -> continuity E ->
  ~ (exists e, fent (F := ef E) ftop e fbot) ->
  ~ provable (HA (dsc := dL)) [] [] (Imp FT Bot).
Proof.
  intros WKL MP HS HCh HCo Hc H. apply Hc.
  destruct (ha_sound_closed (ef E) (dsc := dL) _ H) as [e1 H1]. rewrite ltr_negFT in H1.
  apply (fent_eq_r _ _ _ _ (sv_Imp (ef E) (Γ := []) FTD Bot tt)) in H1.
  destruct (ft_realized E WKL MP HS HCh HCo) as [e2 H2]. rewrite ltr_FT in H2.
  destruct (Hbot (ef E) (dsc := dL)) as (e3 & e4 & H3).
  exists (e_comp (e_comp (e_pair e1 e2) e_eval) e3).
  eapply f_comp; [|exact (proj1 (H3 tt))]. eapply f_comp; [apply f_pair; [exact H1|exact H2]|apply f_eval].
Qed.
