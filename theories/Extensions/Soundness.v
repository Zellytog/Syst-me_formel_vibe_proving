(** * Correction des interprétations

    Une interprétation F de L1 dans L2 est saine dès que :

    1. **les conversions sont préservées** : si le calcul de L1 est engendré
       par des règles R, il suffit que chaque règle se traduise en une
       conversion de L2 ([interp_conv]). On le montre en tirant le système
       de L2 en arrière le long de F ([pullback]) : grâce à [tr_vsubst],
       c'est encore un système de calcul ;
    2. **les règles sont préservées** : chaque instance traduite d'une règle
       de L1 est admissible dans L2 ([rule_sound]).

    Le théorème [interp_sound] en déduit la correction de la traduction des
    jugements. Le critère [srule_sound] ramène la condition 2 à une
    vérification **schématique**, pour les règles dont les prémisses
    n'étendent pas le contexte : il suffit que la traduction du schéma soit
    une règle de L2. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment.
From SF.Extensions Require Import Conservativity Interpretation Commute.

(** ** Les contextes ⟦D ++ Γ⟧ et ⟦D⟧ ++ ⟦Γ⟧ *)

Section CApp.
Context {S1 S2 : Type} (f : S1 -> S2).

Local Notation sm := (smap f).
Local Notation cm := (cmap f).

(** Le renommage canonique de ⟦D ++ Γ⟧ vers ⟦D⟧ ++ ⟦Γ⟧ (les deux contextes
    sont égaux, mais pas définitionnellement). *)
Fixpoint capp (D : ctx S1) {Γ} : ren (cm (D ++ Γ)) (cm D ++ cm Γ) :=
  match D return ren (cm (D ++ Γ)) (cm D ++ cm Γ) with
  | [] => fun σ x => x
  | τ :: D' => fun σ x =>
      var_inv (fun σ0 _ => var (sm τ :: cm D' ++ cm Γ) σ0) vz (fun σ0 y => vs (capp D' σ0 y)) σ x
  end.

Lemma capp_cvar D {Γ σ} (x : var (D ++ Γ) σ) :
  capp D (sm σ) (cvar f x) = vlift f D (fun τ y => cvar f y) σ x.
Proof.
  revert σ x; induction D as [|τ D IH]; intros σ x; [reflexivity|].
  revert σ x. refine (var_inv _ _ _); [reflexivity|]. intros σ y.
  cbn [capp cvar var_inv]. rewrite IH. unfold vlift; cbn [vsplit var_inv].
  destruct (vsplit D y); reflexivity.
Qed.

End CApp.

Arguments capp {S1 S2} f D {Γ} σ x.

Section Pullback.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type} (F : interp Sym1 Sym2).
Context (C2 : system Sym2).

Local Notation fs := (i_srt F).
Local Notation cm := (cmap fs).
Local Notation tm1 := (Terms.tm Sym1).

(** Un corps traduit sous ses lieurs est un renommage de sa traduction. *)
Lemma itms_as_ren {Γ D c} (u : tms Sym1 Γ (Spec D c)) :
  itms F u (cm Γ) (fun σ x => cvar fs x) = ren_tm (tr F u) (capp fs D).
Proof.
  rewrite itms_Spec. unfold tr. rewrite (proj1 (ren_itm_mut F)).
  apply itm_ext; intros σ x. rewrite capp_cvar. reflexivity.
Qed.

Definition pconv : trel Sym1 := fun Γ s t u => conv C2 (tr F t) (tr F u).

Lemma arel_trv {Θ Γ} (v v' : vec Sym1 Θ Γ) : arel pconv v v' -> arel (conv C2) (trv F v) (trv F v').
Proof.
  revert v v'; induction Θ as [|σ Θ IH]; intros v v' H; [exact Logic.I|].
  destruct H as [H1 H2]. rewrite (args_eta v), (args_eta v'). unfold trv. rewrite !iargs_acons.
  split; [|apply IH, H2].
  cbn [ahd]. destruct σ as [D c]. rewrite !itms_as_ren. apply conv_ren, H1.
Qed.

(** Le système de L2 tiré en arrière le long de F. *)
Definition pullback : system Sym1.
Proof.
  refine {| conv := pconv |}.
  - intros Γ s t; apply conv_refl.
  - intros Γ s t u H; apply conv_sym, H.
  - intros Γ s t u w H1 H2; eapply conv_trans; [exact H1|exact H2].
  - intros Γ Δ s t t' v v' Ht Hv. unfold pconv. rewrite !tr_vsubst.
    apply conv_subst; [exact Ht|apply arel_trv, Hv].
Defined.

(** Préservation des conversions : il suffit de la vérifier sur les règles
    qui engendrent le calcul. *)
Theorem interp_conv {I} (R : I -> rule Sym1) :
  (forall i, conv C2 (tr F (r_lhs (R i))) (tr F (r_rhs (R i)))) ->
  forall Γ s (t u : tm1 Γ s), conv (generated R) t u -> conv C2 (tr F t) (tr F u).
Proof. intros H Γ s t u Htu. exact (generated_least R pullback H Γ s t u Htu). Qed.

End Pullback.

(** ** Correction de la traduction des jugements *)

Section Sound.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context (L1 : logic Sym1) (L2 : logic Sym2) (F : linterp L1 L2).

Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).
Local Notation C2 := (l_calc Sym2 L2).
Local Notation G := (li_sig F).
Local Notation fs := (i_srt G).
Local Notation cm := (cmap fs).

Lemma conv_cast {Q Q'} (e : Q = Q') {Γ} (t u : Terms.tm Sym2 Γ Q) :
  conv C2 t u ->
  conv C2 (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => t end)
          (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => u end).
Proof. destruct e; exact (fun H => H). Qed.

Lemma vsubst_cast {Q Q'} (e : Q = Q') {Θ Γ} (t : Terms.tm Sym2 Θ Q) (w : vec Sym2 Θ Γ) :
  match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => vsubst t w end
  = vsubst (match e in _ = R return Terms.tm Sym2 Θ R with eq_refl => t end) w.
Proof. destruct e; reflexivity. Qed.

Lemma ltr_vsubst {Θ Γ} (φ : form Sym1 P1 Θ) (v : vec Sym1 Θ Γ) :
  ltr F (vsubst φ v) = vsubst (ltr F φ) (trv G v).
Proof. unfold ltr, pcast. rewrite tr_vsubst. apply vsubst_cast. Qed.

(** Les instances traduites de la règle r sont admissibles dans L2. *)
Definition rule_sound (r : drule Sym1 P1) : Prop :=
  forall Γ Ξ (v : vec Sym1 (d_ctx r) Γ),
    (forall p, In p (d_prems r) ->
       valid L2 (jtr F (mkJ (p_ext p ++ Γ) (inst_hyps p v Ξ) (inst_goal p v)))) ->
    valid L2 (jtr F (mkJ Γ Ξ (vsubst (d_concl r) v))).

Theorem interp_sound :
  (forall Γ s (t u : Terms.tm Sym1 Γ s), conv (l_calc Sym1 L1) t u -> conv C2 (tr G t) (tr G u)) ->
  (forall i, rule_sound (l_rules Sym1 L1 i)) ->
  linterp_sound L1 L2 F.
Proof.
  intros HC HR [Γ Ξ φ] H. unfold valid, provable in *; cbn [j_ctx j_hyps j_goal] in *.
  induction H as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH].
  - apply d_ax. apply in_or_app; right. exact (in_map (ltr F) _ _ Hin).
  - eapply d_conv; [|exact IH]. unfold ltr, pcast. apply conv_cast, HC, Hc.
  - apply HR. intros p Hin. exact (IH p Hin).
Qed.

Definition interp_extension HC HR : extension L1 L2 :=
  linterp_extension L1 L2 F (interp_sound HC HR).

End Sound.

(** ** Un critère schématique *)

(** Une règle *simple* : ses prémisses n'étendent pas le contexte. *)
Section SRule.
Context {Srt : Type} (Sym : spec Srt -> Type) (P : Srt).

Record srule := {
  s_ctx : ctx Srt;
  s_prems : list (list (form Sym P s_ctx) * form Sym P s_ctx);
  s_concl : form Sym P s_ctx
}.

Definition to_drule (r : srule) : drule Sym P :=
  {| d_ctx := s_ctx r;
     d_prems := map (fun hg => prem (P := P) (fst hg) (snd hg)) (s_prems r);
     d_concl := s_concl r |}.
End SRule.

Arguments s_ctx {Srt Sym P} r : rename.
Arguments s_prems {Srt Sym P} r : rename.
Arguments s_concl {Srt Sym P} r : rename.
Arguments to_drule {Srt Sym P} r.

Section SRuleSound.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context (L1 : logic Sym1) (L2 : logic Sym2) (F : linterp L1 L2).

Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).
Local Notation G := (li_sig F).
Local Notation fs := (i_srt G).

(** La traduction d'une règle simple. *)
Definition tr_srule (r : srule Sym1 P1) : srule Sym2 P2 :=
  {| s_ctx := cmap fs (s_ctx r);
     s_prems := map (fun hg => (map (ltr F) (fst hg), ltr F (snd hg))) (s_prems r);
     s_concl := ltr F (s_concl r) |}.

Lemma map_ltr_vsubst {Θ Γ} (L : list (form Sym1 P1 Θ)) (v : vec Sym1 Θ Γ) :
  map (ltr F) (vsubst_list L v) = vsubst_list (map (ltr F) L) (trv G v).
Proof. unfold vsubst_list; rewrite !map_map; apply map_ext; intros; apply ltr_vsubst. Qed.

Lemma incl_swap {A} (X Y Z : list A) : incl (X ++ Y ++ Z) (Y ++ X ++ Z).
Proof. intros a Ha; rewrite !in_app_iff in *; tauto. Qed.

(** Si la traduction d'une règle simple de L1 est une règle de L2, ses
    instances traduites sont admissibles. *)
Theorem srule_sound (r : srule Sym1 P1) :
  (exists j, l_rules Sym2 L2 j = to_drule (tr_srule r)) ->
  rule_sound L1 L2 F (to_drule r).
Proof.
  intros [j Hj] Γ Ξ v Hp. unfold valid, provable, jtr, strans; cbn [j_ctx j_hyps j_goal].
  cbn [to_drule d_concl d_ctx] in *. rewrite ltr_vsubst.
  change (vsubst (ltr F (s_concl r)) (trv G v)) with (vsubst (d_concl (to_drule (tr_srule r))) (trv G v)).
  eapply d_rule_eq; [exact Hj|].
  intros p' Hp'. cbn [to_drule d_prems tr_srule s_prems] in Hp'. rewrite map_map in Hp'.
  apply in_map_iff in Hp' as ([hs g] & <- & Hin).
  specialize (Hp (prem (P := P1) hs g)). cbn [d_prems to_drule] in Hp.
  assert (Hd := Hp (in_map (fun hg => prem (P := P1) (fst hg) (snd hg)) _ _ Hin)).
  unfold valid, provable, jtr, strans, inst_hyps, inst_goal in Hd |- *.
  cbn [j_ctx j_hyps j_goal p_ext p_hyps p_goal prem fst snd] in Hd |- *.
  rewrite !vup_nil, !wk_list_nil in *. rewrite map_app, map_ltr_vsubst, ltr_vsubst in Hd.
  eapply deriv_weaken; [exact Hd|apply incl_swap].
Qed.

End SRuleSound.
