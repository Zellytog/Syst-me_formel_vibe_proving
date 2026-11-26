(** * Vérificateur de dérivations

    Seconde brique du vérificateur certifié. Une *théorie brute* est une
    liste de règles de déduction brutes, de la même forme que les règles
    intrinsèques de [Logic/Judgment.v] (contexte de métavariables,
    prémisses avec extension du contexte et hypothèses, conclusion). Une
    *preuve brute* a un constructeur par constructeur de [deriv] :
    hypothèse (désignée par sa position), conversion (avec un certificat),
    règle (avec le vecteur d'instanciation et une sous-preuve par
    prémisse).

    Le vérificateur [chk] travaille sur les formules intrinsèques : il
    élabore les règles et les vecteurs, instancie les prémisses par la
    substitution héréditaire déjà définie ([vsubst]), et compare deux
    formules par l'égalité syntaxique de leurs effacements. Son théorème de
    correction [chk_sound] conclut à [deriv C P R Γ Ξ φ], pour la famille
    [R] des élaborations des règles brutes : tous les méta-théorèmes déjà
    prouvés sur [deriv] s'appliquent donc aux preuves vérifiées.

    Les conversions passent par une interface abstraite : un type de
    certificats et une fonction de vérification correcte pour le système de
    calcul. Les certificats de réécriture viendront dans un fichier à part. *)

From Stdlib Require Import List Eqdep_dec Bool.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment.
From SF.Checker Require Import Raw.

(** ** Règles et preuves brutes *)

Section RawRules.

Context {Srt : Type} (RSym : Type) (Cert : Type).

Record rpremise := {
  rp_ext : list (spec Srt);      (* variables propres ajoutées *)
  rp_hyps : list (rtm RSym);     (* hypothèses ajoutées *)
  rp_goal : rtm RSym             (* formule à dériver *)
}.

Record rrule := {
  rr_ctx : list (spec Srt);      (* métavariables *)
  rr_prems : list rpremise;
  rr_concl : rtm RSym
}.

Inductive rproof : Type :=
| pax (n : nat)                                    (* n-ième hypothèse *)
| pconv (c : Cert) (ψ : rtm RSym) (π : rproof)     (* π prouve ψ, et ψ ∼ but *)
| prule (i : nat) (v : rargs RSym) (ps : rproofs)  (* règle i, instance v *)
with rproofs : Type :=
| pnil
| pcons (π : rproof) (ps : rproofs).

End RawRules.

Arguments rpremise Srt RSym : clear implicits.
Arguments rrule Srt RSym : clear implicits.
Arguments rp_ext {Srt RSym} r.
Arguments rp_hyps {Srt RSym} r.
Arguments rp_goal {Srt RSym} r.
Arguments rr_ctx {Srt RSym} r.
Arguments rr_prems {Srt RSym} r.
Arguments rr_concl {Srt RSym} r.
Arguments rproof RSym Cert : clear implicits.
Arguments rproofs RSym Cert : clear implicits.
Arguments pax {RSym Cert} n.
Arguments pconv {RSym Cert} c ψ π.
Arguments prule {RSym Cert} i v ps.
Arguments pnil {RSym Cert}.
Arguments pcons {RSym Cert} π ps.

Scheme rproof_ind' := Induction for rproof Sort Prop
  with rproofs_ind' := Induction for rproofs Sort Prop.
Combined Scheme rproof_rproofs_ind from rproof_ind', rproofs_ind'.

(** ** Égalité décidable des termes bruts *)

Section RawEq.

Context {RSym : Type} (rsym_eq_dec : forall a b : RSym, {a = b} + {a <> b}).

Fixpoint rtm_eqb (t u : rtm RSym) {struct t} : bool :=
  match t, u with
  | rvar n a, rvar m b => Nat.eqb n m && rargs_eqb a b
  | rsym f a, rsym g b => (if rsym_eq_dec f g then true else false) && rargs_eqb a b
  | _, _ => false
  end
with rargs_eqb (a b : rargs RSym) {struct a} : bool :=
  match a, b with
  | rnil, rnil => true
  | rcons t a', rcons u b' => rtm_eqb t u && rargs_eqb a' b'
  | _, _ => false
  end.

Lemma rtm_eqb_eq_mut :
  (forall t u, rtm_eqb t u = true -> t = u) /\
  (forall a b, rargs_eqb a b = true -> a = b).
Proof.
  apply rtm_rargs_ind.
  - intros n a IH [m b|g b] H; simpl in H; [|discriminate].
    apply andb_true_iff in H as [Hn Ha].
    apply PeanoNat.Nat.eqb_eq in Hn. subst m. f_equal. apply IH, Ha.
  - intros f a IH [m b|g b] H; simpl in H; [discriminate|].
    apply andb_true_iff in H as [Hf Ha].
    destruct (rsym_eq_dec f g); [|discriminate]. subst g. f_equal. apply IH, Ha.
  - intros [|u b] H; [reflexivity|discriminate].
  - intros t IHt a IHa [|u b] H; [discriminate|].
    apply andb_true_iff in H as [Ht Ha]. f_equal; [apply IHt, Ht|apply IHa, Ha].
Qed.

Lemma rtm_eqb_eq t u : rtm_eqb t u = true -> t = u.
Proof. apply rtm_eqb_eq_mut. Qed.

End RawEq.

(** ** Le vérificateur *)

Section Checker.

Context {Srt : Type} (Sym : spec Srt -> Type).
Context (srt_eq_dec : forall a b : Srt, {a = b} + {a <> b}).
Context (RSym : Type) (rspec : RSym -> spec Srt) (rsym_of : forall r, Sym (rspec r)).
Context (rsym_eq_dec : forall a b : RSym, {a = b} + {a <> b}).
Context (renc : forall σ, Sym σ -> RSym).
Context (renc_spec : forall σ (c : Sym σ), rspec (renc σ c) = σ).
Context (renc_sym : forall σ (c : Sym σ),
            eq_rect _ Sym (rsym_of (renc σ c)) _ (renc_spec σ c) = c).
Context (renc_rsym : forall r, renc _ (rsym_of r) = r).

(** Le système de calcul et la sorte des formules. *)
Context (C : system Sym) (P : Srt).

(** Les conversions : un type de certificats et une vérification correcte. *)
Context (Cert : Type).
Context (cert_check : forall Γ, Cert -> form Sym P Γ -> form Sym P Γ -> bool).
Context (cert_sound : forall Γ c (φ ψ : form Sym P Γ),
            cert_check Γ c φ ψ = true -> conv C φ ψ).

(** La théorie brute. *)
Context (rules : list (rrule Srt RSym)).

Local Notation ctx := (ctx Srt).
Local Notation form := (form Sym P).
Local Notation rtm := (rtm RSym).
Local Notation rargs := (rargs RSym).
Local Notation rproof := (rproof RSym Cert).
Local Notation rproofs := (rproofs RSym Cert).
Local Notation elab := (elab Sym srt_eq_dec RSym rspec rsym_of).
Local Notation elab_args := (elab_args Sym srt_eq_dec RSym rspec rsym_of).
Local Notation erase := (erase Sym RSym renc).

(** *** Élaboration des formules et des règles *)

Definition elab_form (Γ : ctx) (t : rtm) : option (form Γ) :=
  match elab Γ t with
  | Some (existT _ s u) =>
      match srt_eq_dec s P with
      | left e => Some (eq_rect _ (tm Sym Γ) u _ e)
      | right _ => None
      end
  | None => None
  end.

Fixpoint elab_forms (Γ : ctx) (l : list rtm) : option (list (form Γ)) :=
  match l with
  | [] => Some []
  | t :: l' =>
      match elab_form Γ t, elab_forms Γ l' with
      | Some φ, Some L => Some (φ :: L)
      | _, _ => None
      end
  end.

Definition elab_prem (Θ : ctx) (p : rpremise Srt RSym) : option (premise Sym P Θ) :=
  match elab_forms (rp_ext p ++ Θ) (rp_hyps p), elab_form (rp_ext p ++ Θ) (rp_goal p) with
  | Some hs, Some g => Some {| p_ext := rp_ext p; p_hyps := hs; p_goal := g |}
  | _, _ => None
  end.

Fixpoint elab_prems (Θ : ctx) (l : list (rpremise Srt RSym)) : option (list (premise Sym P Θ)) :=
  match l with
  | [] => Some []
  | p :: l' =>
      match elab_prem Θ p, elab_prems Θ l' with
      | Some q, Some L => Some (q :: L)
      | _, _ => None
      end
  end.

Definition elab_rule (r : rrule Srt RSym) : option (drule Sym P) :=
  match elab_prems (rr_ctx r) (rr_prems r), elab_form (rr_ctx r) (rr_concl r) with
  | Some ps, Some c => Some {| d_ctx := rr_ctx r; d_prems := ps; d_concl := c |}
  | _, _ => None
  end.

(** La famille intrinsèque engendrée par la théorie brute : les
    élaborations de ses règles. *)
Definition RIdx : Type :=
  { d : drule Sym P | exists i r, nth_error rules i = Some r /\ elab_rule r = Some d }.

Definition Rfam (x : RIdx) : drule Sym P := proj1_sig x.

(** *** Égalité des formules par effacement *)

Definition form_eqb {Γ} (φ ψ : form Γ) : bool :=
  rtm_eqb rsym_eq_dec (erase φ) (erase ψ).

Lemma erase_inj {Γ s} (u u' : tm Sym Γ s) : erase u = erase u' -> u = u'.
Proof.
  intro H.
  pose proof (elab_erase Sym srt_eq_dec RSym rspec rsym_of renc renc_spec renc_sym u) as E.
  pose proof (elab_erase Sym srt_eq_dec RSym rspec rsym_of renc renc_spec renc_sym u') as E'.
  rewrite H in E. rewrite E in E'. injection E' as E'.
  apply (inj_pair2_eq_dec _ srt_eq_dec) in E'. exact E'.
Qed.

Lemma form_eqb_eq {Γ} (φ ψ : form Γ) : form_eqb φ ψ = true -> φ = ψ.
Proof. intro H. apply erase_inj. eapply rtm_eqb_eq. exact H. Qed.

(** *** Le vérificateur *)

Fixpoint chk (Γ : ctx) (Ξ : list (form Γ)) (φ : form Γ) (π : rproof) {struct π} : bool :=
  match π with
  | pax n =>
      match nth_error Ξ n with
      | Some ψ => form_eqb ψ φ
      | None => false
      end
  | pconv c ψr π' =>
      match elab_form Γ ψr with
      | Some ψ => cert_check Γ c ψ φ && chk Γ Ξ ψ π'
      | None => false
      end
  | prule i vr ps =>
      match nth_error rules i with
      | Some r =>
          match elab_rule r with
          | Some d =>
              match elab_args Γ (d_ctx d) vr with
              | Some v => form_eqb (vsubst (d_concl d) v) φ
                          && chk_prems Γ Ξ (d_ctx d) v (d_prems d) ps
              | None => false
              end
          | None => false
          end
      | None => false
      end
  end
with chk_prems (Γ : ctx) (Ξ : list (form Γ)) (Θ : ctx) (v : vec Sym Θ Γ)
       (prems : list (premise Sym P Θ)) (ps : rproofs) {struct ps} : bool :=
  match prems, ps with
  | [], pnil => true
  | p :: prems', pcons π ps' =>
      chk (p_ext p ++ Γ) (inst_hyps p v Ξ) (inst_goal p v) π
      && chk_prems Γ Ξ Θ v prems' ps'
  | _, _ => false
  end.

Lemma chk_sound_mut :
  (forall π Γ Ξ φ, chk Γ Ξ φ π = true -> deriv C P Rfam Γ Ξ φ) /\
  (forall ps Γ Ξ Θ v prems, chk_prems Γ Ξ Θ v prems ps = true ->
     forall p, In p prems -> deriv C P Rfam (p_ext p ++ Γ) (inst_hyps p v Ξ) (inst_goal p v)).
Proof.
  apply rproof_rproofs_ind.
  - intros n Γ Ξ φ H. simpl in H.
    destruct (nth_error Ξ n) as [ψ|] eqn:E; [|discriminate].
    apply form_eqb_eq in H. subst ψ.
    apply d_ax. eapply nth_error_In. exact E.
  - intros c ψr π IH Γ Ξ φ H. simpl in H.
    destruct (elab_form Γ ψr) as [ψ|]; [|discriminate].
    apply andb_true_iff in H as [Hc Hp].
    eapply d_conv; [apply (cert_sound Γ c); exact Hc|apply IH; exact Hp].
  - intros i vr ps IH Γ Ξ φ H. simpl in H.
    destruct (nth_error rules i) as [r|] eqn:Er; [|discriminate].
    destruct (elab_rule r) as [d|] eqn:Ed; [|discriminate].
    destruct (elab_args Γ (d_ctx d) vr) as [v|]; [|discriminate].
    apply andb_true_iff in H as [Hφ Hp].
    apply form_eqb_eq in Hφ. subst φ.
    apply (d_rule_eq C P Rfam Γ Ξ (exist _ d (ex_intro _ i (ex_intro _ r (conj Er Ed)))) d v);
      [reflexivity|].
    apply (IH Γ Ξ (d_ctx d) v (d_prems d) Hp).
  - intros Γ Ξ Θ v prems H p Hin.
    destruct prems; simpl in H; [destruct Hin|discriminate].
  - intros π IHπ ps IHps Γ Ξ Θ v prems H p Hin.
    destruct prems as [|q prems']; simpl in H; [discriminate|].
    apply andb_true_iff in H as [Hq Hps].
    destruct Hin as [<-|Hin]; [apply IHπ; exact Hq|].
    apply (IHps Γ Ξ Θ v prems' Hps p Hin).
Qed.

(** Correction : une preuve acceptée est une dérivation dans la théorie. *)
Theorem chk_sound {Γ Ξ φ} (π : rproof) :
  chk Γ Ξ φ π = true -> deriv C P Rfam Γ Ξ φ.
Proof. apply chk_sound_mut. Qed.

(** Version entièrement brute : le jugement lui-même est donné par des
    termes bruts, élaborés par le vérificateur. *)
Definition check_judgment (Γ : ctx) (Ξr : list rtm) (φr : rtm) (π : rproof) : bool :=
  match elab_forms Γ Ξr, elab_form Γ φr with
  | Some Ξ, Some φ => chk Γ Ξ φ π
  | _, _ => false
  end.

Theorem check_judgment_sound Γ Ξr φr π :
  check_judgment Γ Ξr φr π = true ->
  exists Ξ φ, elab_forms Γ Ξr = Some Ξ /\ elab_form Γ φr = Some φ /\
              deriv C P Rfam Γ Ξ φ.
Proof.
  unfold check_judgment.
  destruct (elab_forms Γ Ξr) as [Ξ|]; [|discriminate].
  destruct (elab_form Γ φr) as [φ|]; [|discriminate].
  intro H. exists Ξ, φ. split; [reflexivity|split; [reflexivity|]].
  apply chk_sound with (π := π). exact H.
Qed.

End Checker.
