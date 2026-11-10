(** * Le cadre d'évidence d'une algèbre combinatoire partielle

    Une PCA est donnée par une application partielle a·b ↓ c (une relation
    [ap a b c]) et deux combinateurs K et S, avec :
    - K·a ↓ K a et (K a)·b ↓ a ;
    - S·a ↓ S a, (S a)·b ↓ S a b, et (S a b)·c ↓ v dès que a·c ↓ u,
      b·c ↓ w et u·w ↓ v.
    Les applications partielles de K et S sont données comme fonctions
    ([k1], [s1], [s2]), ce qui permet de *calculer* les réalisateurs dérivés.
    L'unicité des valeurs (une PCA au sens strict) n'est pas demandée : la
    construction vaut aussi pour les algèbres combinatoires relationnelles.

    Le cadre de réalisabilité ([pca_frame]), d'après Cohen–Miquey–Tate :
    - Φ := les parties de A, comparées par double inclusion ;
    - E := A ; φ —e→ ψ si pour tout a ∈ φ, il existe b avec e·a ↓ b ∈ ψ ;
    - ⊤ := A ; φ ∧ ψ := les a dont les projections sont dans φ et ψ ;
      φ ⇒ ψ := les f qui envoient φ dans ψ ; ⋀ᵢ φᵢ := les a tels que a·K est
      défini et dans chaque φᵢ (le délai a·K rend ∀I défini même pour une
      famille vide).
    Les évidences sont des λ-termes, compilés en S et K par l'abstraction
    ([lam], [lval]). *)

From SF.Models Require Import PSet Frame.

Record pca := {
  pc :> Type;
  ap : pc -> pc -> pc -> Prop;
  cK : pc;
  cS : pc;
  k1 : pc -> pc;
  s1 : pc -> pc;
  s2 : pc -> pc -> pc;
  ap_K : forall a, ap cK a (k1 a);
  ap_K1 : forall a b, ap (k1 a) b a;
  ap_S : forall a, ap cS a (s1 a);
  ap_S1 : forall a b, ap (s1 a) b (s2 a b);
  ap_S2 : forall a b c u w v, ap a c u -> ap b c w -> ap u w v -> ap (s2 a b) c v
}.

Arguments ap {p} a b c.
Arguments cK {p}.
Arguments cS {p}.
Arguments k1 {p} a.
Arguments s1 {p} a.
Arguments s2 {p} a b.

Section Combinators.

Context (A : pca).

(** ** Expressions et abstraction *)

Inductive cexp : Type :=
| cv (n : nat)
| cc (a : A)
| capp (e1 e2 : cexp).

Definition scons (a : A) (ρ : nat -> A) : nat -> A :=
  fun n => match n with 0 => a | S n => ρ n end.

Inductive ev (ρ : nat -> A) : cexp -> A -> Prop :=
| ev_v n : ev ρ (cv n) (ρ n)
| ev_c a : ev ρ (cc a) a
| ev_app e1 e2 v1 v2 v : ev ρ e1 v1 -> ev ρ e2 v2 -> ap v1 v2 v -> ev ρ (capp e1 e2) v.

(** λx. e (x est la variable 0 ; les autres descendent d'un cran). *)
Fixpoint lam (e : cexp) : cexp :=
  match e with
  | cv 0 => capp (capp (cc cS) (cc cK)) (cc cK)
  | cv (S n) => capp (cc cK) (cv n)
  | cc a => capp (cc cK) (cc a)
  | capp e1 e2 => capp (capp (cc cS) (lam e1)) (lam e2)
  end.

(** Sa valeur, toujours définie. *)
Fixpoint lval (ρ : nat -> A) (e : cexp) : A :=
  match e with
  | cv 0 => s2 cK cK
  | cv (S n) => k1 (ρ n)
  | cc a => k1 a
  | capp e1 e2 => s2 (lval ρ e1) (lval ρ e2)
  end.

Lemma lam_ev ρ e : ev ρ (lam e) (lval ρ e).
Proof.
  induction e as [[|n]|a|e1 IH1 e2 IH2]; cbn.
  - eapply ev_app; [eapply ev_app; [apply ev_c|apply ev_c|apply ap_S]|apply ev_c|apply ap_S1].
  - eapply ev_app; [apply ev_c|apply ev_v|apply ap_K].
  - eapply ev_app; [apply ev_c|apply ev_c|apply ap_K].
  - eapply ev_app; [eapply ev_app; [apply ev_c|exact IH1|apply ap_S]|exact IH2|apply ap_S1].
Qed.

(** β : (λx. e)·a ↓ v dès que e[a/x] ↓ v. *)
Lemma lam_ap ρ e a v : ev (scons a ρ) e v -> ap (lval ρ e) a v.
Proof.
  revert v. induction e as [[|n]|b|e1 IH1 e2 IH2]; intros v H; inversion H; subst; cbn.
  - eapply ap_S2; [apply ap_K|apply ap_K|apply ap_K1].
  - apply ap_K1.
  - apply ap_K1.
  - eapply ap_S2; [apply IH1; eassumption|apply IH2; eassumption|eassumption].
Qed.

(** Les combinateurs clos : abstraction dans l'environnement constant. *)
Definition ρ0 : nat -> A := fun _ => cK.
Definition clo (e : cexp) : A := lval ρ0 e.

Lemma clo_ap e a v : ev (scons a ρ0) e v -> ap (clo e) a v.
Proof. apply lam_ap. Qed.

(** Deux lieurs : (λx.λy. e)·a ↓ lval (a.ρ0) e, puis ·b. *)
Lemma clo2_ap1 e a : ap (clo (lam e)) a (lval (scons a ρ0) e).
Proof. apply clo_ap, lam_ev. Qed.

Lemma clo2_ap2 e a b v : ev (scons b (scons a ρ0)) e v -> ap (lval (scons a ρ0) e) b v.
Proof. apply lam_ap. Qed.

(** ** Identité, couples *)

Definition cI : A := clo (cv 0).

Lemma ap_I a : ap cI a a.
Proof. apply clo_ap, ev_v. Qed.

(** ⟨x, y⟩ := λf. f x y. *)
Definition pbody : cexp := capp (capp (cv 0) (cv 2)) (cv 1).
Definition cPair : A := clo (lam (lam pbody)).
Definition pairv (a b : A) : A := lval (scons b (scons a ρ0)) pbody.

Lemma ap_pair a b : exists p, ap cPair a p /\ ap p b (pairv a b).
Proof.
  exists (lval (scons a ρ0) (lam pbody)). split; [apply clo2_ap1|].
  apply clo2_ap2, lam_ev.
Qed.

Definition cFst : A := clo (capp (cv 0) (cc cK)).
Definition cSnd : A := clo (capp (cv 0) (cc (k1 cI))).

Lemma ap_fst a b : ap cFst (pairv a b) a.
Proof.
  apply clo_ap. eapply ev_app; [apply ev_v|apply ev_c|]. cbn [scons].
  apply (lam_ap (scons b (scons a ρ0)) pbody).
  eapply ev_app; [eapply ev_app; [apply ev_v|apply ev_v|]|apply ev_v|]; cbn [scons].
  - apply ap_K.
  - apply ap_K1.
Qed.

Lemma ap_snd a b : ap cSnd (pairv a b) b.
Proof.
  apply clo_ap. eapply ev_app; [apply ev_v|apply ev_c|]. cbn [scons].
  apply (lam_ap (scons b (scons a ρ0)) pbody).
  eapply ev_app; [eapply ev_app; [apply ev_v|apply ev_v|]|apply ev_v|]; cbn [scons].
  - apply ap_K1.
  - apply ap_I.
Qed.

End Combinators.

Arguments cv {A} n.
Arguments cc {A} a.
Arguments capp {A} e1 e2.

(** ** Le cadre *)

Section Frame.

Context (A : pca).

Local Notation "e · a ↓ b" := (ap (p := A) e a b) (at level 60).

Program Definition ppow : pset := {|
  pcar := A -> Prop;
  peq := fun φ ψ => forall a, φ a <-> ψ a
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. symmetry; auto. Qed.
Next Obligation. etransitivity; eauto. Qed.

Definition rent (φ : ppow) (e : A) (ψ : ppow) : Prop :=
  forall a, φ a -> exists b, e · a ↓ b /\ ψ b.

Definition rtop : ppow := fun _ => True.
Definition rand (φ ψ : ppow) : ppow :=
  fun p => (exists a, cFst A · p ↓ a /\ φ a) /\ (exists b, cSnd A · p ↓ b /\ ψ b).
Definition rimp (φ ψ : ppow) : ppow := fun f => forall a, φ a -> exists b, f · a ↓ b /\ ψ b.
Definition rall {I : Type} (f : I -> ppow) : ppow := fun a => forall i, exists b, a · cK ↓ b /\ f i b.

(** Les évidences. *)
Definition r_comp (e1 e2 : A) : A := clo A (capp (cc e2) (capp (cc e1) (cv 0))).
Definition r_pair (e1 e2 : A) : A :=
  clo A (capp (capp (cc (cPair A)) (capp (cc e1) (cv 0))) (capp (cc e2) (cv 0))).
Definition r_lam (e : A) : A := clo A (lam A (capp (cc e) (capp (capp (cc (cPair A)) (cv 1)) (cv 0)))).
Definition r_eval : A := clo A (capp (capp (cc (cFst A)) (cv 0)) (capp (cc (cSnd A)) (cv 0))).
Definition r_gen (e : A) : A := clo A (lam A (capp (cc e) (cv 1))).

Lemma rent_proper φ φ' e ψ ψ' : φ ≡ φ' -> ψ ≡ ψ' -> rent φ e ψ -> rent φ' e ψ'.
Proof.
  intros E1 E2 H a Ha. destruct (H a (proj2 (E1 a) Ha)) as (b & Hb & Hψ).
  exists b. split; [exact Hb|apply E2, Hψ].
Qed.

Lemma r_id φ : rent φ (cI A) φ.
Proof. intros a Ha. exists a. split; [apply ap_I|exact Ha]. Qed.

Lemma r_comp_ok φ ψ χ e1 e2 : rent φ e1 ψ -> rent ψ e2 χ -> rent φ (r_comp e1 e2) χ.
Proof.
  intros H1 H2 a Ha. destruct (H1 a Ha) as (b & Hb & Hψ). destruct (H2 b Hψ) as (c & Hc & Hχ).
  exists c. split; [|exact Hχ]. apply clo_ap.
  eapply ev_app; [apply ev_c|eapply ev_app; [apply ev_c|apply ev_v|exact Hb]|exact Hc].
Qed.

Lemma r_top φ : rent φ cK rtop.
Proof. intros a _. exists (k1 a). split; [apply ap_K|exact Logic.I]. Qed.

Lemma rand_proper φ φ' ψ ψ' : φ ≡ φ' -> ψ ≡ ψ' -> rand φ ψ ≡ rand φ' ψ'.
Proof.
  intros E1 E2 p. unfold rand. split; intros [(a & Ha & Hφ) (b & Hb & Hψ)];
    (split; [exists a; split; [exact Ha|apply E1, Hφ]|exists b; split; [exact Hb|apply E2, Hψ]]).
Qed.

Lemma r_fst φ ψ : rent (rand φ ψ) (cFst A) φ.
Proof. intros p [H _]. exact H. Qed.
Lemma r_snd φ ψ : rent (rand φ ψ) (cSnd A) ψ.
Proof. intros p [_ H]. exact H. Qed.

Lemma pair_in (φ ψ : ppow) a b : φ a -> ψ b -> rand φ ψ (pairv A a b).
Proof.
  intros Ha Hb. split; [exists a; split; [apply ap_fst|exact Ha]|exists b; split; [apply ap_snd|exact Hb]].
Qed.

Lemma r_pair_ok φ ψ χ e1 e2 : rent φ e1 ψ -> rent φ e2 χ -> rent φ (r_pair e1 e2) (rand ψ χ).
Proof.
  intros H1 H2 a Ha. destruct (H1 a Ha) as (b & Hb & Hψ). destruct (H2 a Ha) as (c & Hc & Hχ).
  destruct (ap_pair A b c) as (p1 & Hp1 & Hp2).
  exists (pairv A b c). split; [|apply pair_in; assumption]. apply clo_ap.
  eapply ev_app; [eapply ev_app; [apply ev_c|eapply ev_app; [apply ev_c|apply ev_v|exact Hb]|exact Hp1]
                 |eapply ev_app; [apply ev_c|apply ev_v|exact Hc]|exact Hp2].
Qed.

Lemma rimp_proper φ φ' ψ ψ' : φ ≡ φ' -> ψ ≡ ψ' -> rimp φ ψ ≡ rimp φ' ψ'.
Proof.
  intros E1 E2 f. unfold rimp. split; intros H a Ha.
  - destruct (H a (proj2 (E1 a) Ha)) as (b & Hb & Hψ). exists b. split; [exact Hb|apply E2, Hψ].
  - destruct (H a (proj1 (E1 a) Ha)) as (b & Hb & Hψ). exists b. split; [exact Hb|apply E2, Hψ].
Qed.

Lemma r_lam_ok φ ψ χ e : rent (rand φ ψ) e χ -> rent φ (r_lam e) (rimp ψ χ).
Proof.
  intros H a Ha. eexists. split; [apply clo2_ap1|].
  intros b Hb. destruct (H _ (pair_in φ ψ a b Ha Hb)) as (c & Hc & Hχ).
  destruct (ap_pair A a b) as (p1 & Hp1 & Hp2).
  exists c. split; [|exact Hχ]. apply clo2_ap2.
  eapply ev_app; [apply ev_c|eapply ev_app; [eapply ev_app; [apply ev_c|apply ev_v|exact Hp1]|apply ev_v|exact Hp2]|exact Hc].
Qed.

Lemma r_eval_ok ψ χ : rent (rand (rimp ψ χ) ψ) r_eval χ.
Proof.
  intros p [(f & Hf & Himp) (b & Hb & Hψ)]. destruct (Himp b Hψ) as (c & Hc & Hχ).
  exists c. split; [|exact Hχ]. apply clo_ap.
  eapply ev_app; [eapply ev_app; [apply ev_c|apply ev_v|exact Hf]|eapply ev_app; [apply ev_c|apply ev_v|exact Hb]|exact Hc].
Qed.

Lemma rall_proper I (f g : I -> ppow) : (forall i, f i ≡ g i) -> rall f ≡ rall g.
Proof.
  intros E a. unfold rall. split; intros H i; destruct (H i) as (b & Hb & Hi);
    exists b; (split; [exact Hb|apply (E i), Hi]).
Qed.

Lemma r_gen_ok I φ (f : I -> ppow) e : (forall i, rent φ e (f i)) -> rent φ (r_gen e) (rall f).
Proof.
  intros H a Ha. eexists. split; [apply clo2_ap1|].
  intros i. destruct (H i a Ha) as (b & Hb & Hi). exists b. split; [|exact Hi].
  apply clo2_ap2. eapply ev_app; [apply ev_c|apply ev_v|exact Hb].
Qed.

Lemma r_inst I (f : I -> ppow) i : rent (rall f) (cFst A) (f i).
Proof.
  intros a Ha. destruct (Ha i) as (b & Hb & Hi). exists b. split; [|exact Hi].
  apply clo_ap. eapply ev_app; [apply ev_v|apply ev_c|exact Hb].
Qed.

(** ⋀ sur une partie S de Φ : indexé par les éléments de S. *)
Definition rallP (S : ppow -> Prop) : ppow := rall (I := {ψ : ppow | S ψ}) (fun p => proj1_sig p).

Lemma rallP_proper (S T : ppow -> Prop) : (forall ψ, S ψ <-> T ψ) -> rallP S ≡ rallP T.
Proof.
  intros E a. unfold rallP, rall. split; intros H [ψ Hψ].
  - exact (H (exist _ ψ (proj2 (E ψ) Hψ))).
  - exact (H (exist _ ψ (proj1 (E ψ) Hψ))).
Qed.

Lemma r_genP (S : ppow -> Prop) φ e : (forall ψ, S ψ -> rent φ e ψ) -> rent φ (r_gen e) (rallP S).
Proof. intros H. apply r_gen_ok. intros [ψ Hψ]. exact (H ψ Hψ). Qed.

Lemma r_instP (S : ppow -> Prop) ψ : S ψ -> rent (rallP S) (cFst A) ψ.
Proof. intros H. exact (r_inst _ (fun p : {ψ : ppow | S ψ} => proj1_sig p) (exist _ ψ H)). Qed.

Definition pca_frame : frame := {|
  fprop := ppow;
  fev := A;
  fent := rent;
  fent_proper := rent_proper;
  e_id := cI A; f_id := r_id;
  e_comp := r_comp; f_comp := r_comp_ok;
  ftop := rtop; e_top := cK; f_top := r_top;
  fand := rand; fand_proper := rand_proper;
  e_fst := cFst A; f_fst := r_fst; e_snd := cSnd A; f_snd := r_snd;
  e_pair := r_pair; f_pair := r_pair_ok;
  fimp := rimp; fimp_proper := rimp_proper;
  e_lam := r_lam; f_lam := r_lam_ok; e_eval := r_eval; f_eval := r_eval_ok;
  fallP := rallP; fallP_proper := rallP_proper;
  e_gen := r_gen; f_genP := r_genP; e_inst := cFst A; f_instP := r_instP
|}.

End Frame.
