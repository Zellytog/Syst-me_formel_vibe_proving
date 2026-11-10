(** * Couche fonctionnelle : sortes flèches, lambda, app, β et η

    Au lieu d'une opération partielle [_=>_] sur les sortes, on se donne sa
    relation : [Arr a b c] signifie « c est une sorte flèche de a vers b ».
    Les symboles lambda et app sont indexés par un témoin de [Arr]. Une
    sorte trop haute n'a simplement pas de témoin : la troncature est
    gratuite. Rien n'impose l'unicité de c ; si on la veut, c'est la
    propriété [arr_functional].

    Les règles β et η sont des schémas, un par témoin ; elles forment des
    familles de règles de calcul qu'on combine avec les autres. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment.

Section Arrow.

Context {Srt : Type} (Sym : spec Srt -> Type).

Local Notation ι a := (Spec [] a).
Local Notation tm := (Terms.tm Sym).

Class Functional := {
  Arr : Srt -> Srt -> Srt -> Type;
  s_lam {a b c} : Arr a b c -> Sym (Spec [Spec [ι a] b] c);
  s_app {a b c} : Arr a b c -> Sym (Spec [ι c; ι a] b)
}.

(** La relation est fonctionnelle (on a une vraie opération partielle). *)
Definition arr_functional `{Functional} : Prop :=
  forall a b c c' (w : Arr a b c) (w' : Arr a b c'), c = c'.

Context `{Functional}.

Definition Lam {a b c} (w : Arr a b c) {Γ} (t : tm (ι a :: Γ) b) : tm Γ c :=
  @tsym _ Sym Γ (Spec [Spec [ι a] b] c) (s_lam w) (@acons _ Sym Γ (Spec [ι a] b) [] t anil).

Definition App {a b c} (w : Arr a b c) {Γ} (f : tm Γ c) (u : tm Γ a) : tm Γ b :=
  @tsym _ Sym Γ (Spec [ι c; ι a] b) (s_app w)
    (@acons _ Sym Γ (ι c) _ f (@acons _ Sym Γ (ι a) _ u anil)).

(** Métavariable sans argument. *)
Definition var0 {Θ a} (x : var Θ (ι a)) : tm Θ a := @tvar _ Sym Θ (ι a) x anil.

(** Substitution de la variable liée par [u] : [t[u/x0]]. *)
Definition inst1 {Γ a} (u : tm Γ a) : vec Sym (ι a :: Γ) Γ := @acons _ Sym Γ (ι a) _ u (vid Γ).

(** ** Les schémas β et η *)

Definition beta_ctx a b : ctx Srt := [Spec [ι a] b; ι a].
Definition eta_ctx c : ctx Srt := [ι c].

(** app(lambda(x. t(x)), u) ~ t(u), avec t : [a] -> b et u : a.
    Le corps [t(x)] est l'η-expansé de la métavariable t. *)
Definition beta_rule {a b c} (w : Arr a b c) : rule Sym := {|
  r_ctx := beta_ctx a b;
  r_sort := b;
  r_lhs := App w (Lam w (eta (Spec [ι a] b) (Γ := beta_ctx a b) vz)) (var0 (vs vz));
  r_rhs := @tvar _ Sym (beta_ctx a b) (Spec [ι a] b) vz
             (@acons _ Sym _ (ι a) _ (var0 (vs vz)) anil)
|}.

(** lambda(x. app(f, x)) ~ f, avec f : c. *)
Definition eta_rule {a b c} (w : Arr a b c) : rule Sym := {|
  r_ctx := eta_ctx c;
  r_sort := c;
  r_lhs := Lam w (App w (var0 (vs vz)) (var0 vz));
  r_rhs := var0 vz
|}.

Definition beta_idx := { a & { b & { c & Arr a b c } } }.

Definition beta_rules (k : beta_idx) : rule Sym :=
  match k with existT _ a (existT _ b (existT _ c w)) => beta_rule w end.

Definition eta_rules (k : beta_idx) : rule Sym :=
  match k with existT _ a (existT _ b (existT _ c w)) => eta_rule w end.

(** Le λ-calcul de la signature, modulo β, et modulo βη. *)
Definition beta_system : system Sym := generated beta_rules.
Definition beta_eta_system : system Sym := generated (crsum beta_rules eta_rules).

End Arrow.

Arguments Arr {Srt Sym Functional}.
Arguments s_lam {Srt Sym Functional a b c} w.
Arguments s_app {Srt Sym Functional a b c} w.
Arguments Lam {Srt Sym _ a b c} w {Γ} t.
Arguments App {Srt Sym _ a b c} w {Γ} f u.
Arguments var0 {Srt Sym Θ a} x.
Arguments inst1 {Srt Sym Γ a} u.
Arguments beta_rule {Srt Sym _ a b c} w.
Arguments eta_rule {Srt Sym _ a b c} w.
Arguments beta_idx {Srt Sym _}.
Arguments beta_rules {Srt Sym _} k.
Arguments eta_rules {Srt Sym _} k.
Arguments beta_system {Srt} Sym {_}.
Arguments beta_eta_system {Srt} Sym {_}.

(** ** Calculs de substitution et conversions dérivées *)

Section Conversions.

Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym}.

Local Notation ι a := (Spec [] a).
Local Notation tm := (Terms.tm Sym).

Lemma vsubst_Lam {a b c} (w : Arr a b c) {Θ Γ} (t : tm (ι a :: Θ) b) (v : vec Sym Θ Γ) :
  vsubst (Lam w t) v = Lam w (vsubst_tms (σ := Spec [ι a] b) t v).
Proof. reflexivity. Qed.

Lemma vsubst_App {a b c} (w : Arr a b c) {Θ Γ} (f : tm Θ c) (u : tm Θ a) (v : vec Sym Θ Γ) :
  vsubst (App w f u) v = App w (vsubst f v) (vsubst u v).
Proof.
  unfold App.
  transitivity (@tsym _ Sym Γ _ (s_app w)
                  (@acons _ Sym Γ (ι c) _ (vsubst_tms (σ := ι c) f v)
                     (@acons _ Sym Γ (ι a) _ (vsubst_tms (σ := ι a) u v) anil)));
    [reflexivity|].
  rewrite !vsubst_tms_nil; reflexivity.
Qed.

Lemma vsubst_var0 {Θ Γ a} (x : var Θ (ι a)) (v : vec Sym Θ Γ) :
  vsubst (var0 (Sym := Sym) x) v = aget x v.
Proof. apply vsubst_mv. Qed.

Section Beta.
Context {I : Type} (R : I -> rule Sym) `{CIncludes _ Sym I beta_idx R beta_rules}.

(** β : app(lambda(x. t), u) ~ t[u/x]. *)
Theorem beta_conv {a b c} (w : Arr a b c) {Γ} (t : tm (ι a :: Γ) b) (u : tm Γ a) :
  conv (generated R) (App w (Lam w t) u) (vsubst t (inst1 u)).
Proof.
  pose proof (generated_included R beta_rules (existT _ a (existT _ b (existT _ c w)))
                (@acons _ Sym Γ (Spec [ι a] b) _ t (@acons _ Sym Γ (ι a) _ u anil))) as Hb.
  cbn [beta_rules beta_rule r_lhs r_rhs r_ctx] in Hb.
  rewrite vsubst_App, vsubst_Lam, vsubst_var0, vsubst_eta in Hb. cbn [aget ahd atl] in Hb.
  replace (vsubst t (inst1 u)) with
    (vsubst (@tvar _ Sym (beta_ctx a b) (Spec [ι a] b) vz (@acons _ Sym _ (ι a) _ (var0 (vs vz)) anil))
            (@acons _ Sym Γ (Spec [ι a] b) _ t (@acons _ Sym Γ (ι a) _ u anil))).
  - exact Hb.
  - change (happ (Spec [ι a] b) t
              (@acons _ Sym Γ (ι a) _ (vsubst_tms (σ := ι a) (var0 (vs vz))
                 (@acons _ Sym Γ (Spec [ι a] b) _ t (@acons _ Sym Γ (ι a) _ u anil))) anil)
            = vsubst t (inst1 u)).
    rewrite vsubst_tms_nil, vsubst_var0, happ_vsubst; reflexivity.
Qed.
End Beta.

Section Eta.
Context {I : Type} (R : I -> rule Sym) `{CIncludes _ Sym I beta_idx R eta_rules}.

(** η : lambda(x. app(f↑, x)) ~ f, où f↑ est f affaibli sous le lieur. *)
Theorem eta_conv {a b c} (w : Arr a b c) {Γ} (f : tm Γ c) :
  conv (generated R) (Lam w (App w (ren_tm f (wk [ι a])) (var0 vz))) f.
Proof.
  pose proof (generated_included R eta_rules (existT _ a (existT _ b (existT _ c w)))
                (@acons _ Sym Γ (ι c) _ f anil)) as He.
  cbn [eta_rules eta_rule r_lhs r_rhs r_ctx] in He.
  rewrite vsubst_Lam, vsubst_tms_vup in He. cbn [dom] in He.
  rewrite vsubst_App, !vsubst_var0 in He.
  unfold vup, vren in He. cbn [vcat ahd atl aget vmap etas eta vl vr] in He.
  replace (ren_tm f (wk [ι a])) with (ren_tms (σ := ι c) f (wk [ι a])).
  - exact He.
  - unfold ren_tms. apply ren_ext; intros σ x. cbn [dom upr]. unfold upr. reflexivity.
Qed.
End Eta.

End Conversions.
