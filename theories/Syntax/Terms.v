(** * Signatures, termes, renommage, η-expansion et substitution héréditaire

    Une signature est un type de sortes [Srt] et, pour chaque spécification
    [σ], un type [Sym σ] de symboles d'arité [σ]. Les termes sont
    intrinsèquement typés et toujours en forme β-normale η-longue : une
    variable ou un symbole est toujours pleinement appliqué, et les lieurs
    sont implicites dans les arguments.

      x : Spec [σ1..σn] s ∈ Γ     Γ, dom σi ⊢ ti : cod σi
      ----------------------------------------------------
                    Γ ⊢ x(t1,...,tn) : s

    La substitution d'une variable d'ordre supérieur est *héréditaire* :
    [happ σ] instancie le corps [u : tms Ξ σ] par des arguments, ce qui
    peut créer de nouveaux rédex, contractés à leur tour. La terminaison est
    structurelle sur la spécification. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec.

Record signature := {
  srt : Type;
  sym : spec srt -> Type
}.

Section Syntax.

Context {Srt : Type} (Sym : spec Srt -> Type).

Local Notation spec := (spec Srt).
Local Notation ctx := (ctx Srt).

(** ** Termes et listes d'arguments *)

Inductive tm : ctx -> Srt -> Type :=
| tvar {Γ σ} : var Γ σ -> args Γ (dom σ) -> tm Γ (cod σ)
| tsym {Γ σ} : Sym σ -> args Γ (dom σ) -> tm Γ (cod σ)
with args : ctx -> list spec -> Type :=
| anil {Γ} : args Γ []
| acons {Γ σ Θ} : tm (dom σ ++ Γ) (cod σ) -> args Γ Θ -> args Γ (σ :: Θ).

(** Terme « de spécification σ » dans Γ : un corps sous les lieurs de σ. *)
Definition tms (Γ : ctx) (σ : spec) : Type := tm (dom σ ++ Γ) (cod σ).

Scheme tm_ind' := Induction for tm Sort Prop
  with args_ind' := Induction for args Sort Prop.
Combined Scheme tm_args_ind from tm_ind', args_ind'.

(** Inversion des listes d'arguments. *)
Definition ahd {Γ σ Θ} (a : args Γ (σ :: Θ)) : tms Γ σ :=
  match a in args Γ0 L return
    match L with [] => unit | σ0 :: _ => tms Γ0 σ0 end with
  | anil => tt
  | acons t _ => t
  end.

Definition atl {Γ σ Θ} (a : args Γ (σ :: Θ)) : args Γ Θ :=
  match a in args Γ0 L return
    match L with [] => unit | _ :: Θ0 => args Γ0 Θ0 end with
  | anil => tt
  | acons _ a' => a'
  end.

Lemma args_eta {Γ σ Θ} (a : args Γ (σ :: Θ)) : a = acons (ahd a) (atl a).
Proof.
  refine (match a as a1 in args Γ0 L return
            match L return args Γ0 L -> Prop with
            | [] => fun _ => True
            | σ0 :: Θ0 => fun a0 => a0 = acons (ahd a0) (atl a0)
            end a1 with
          | anil => I
          | acons _ _ => eq_refl
          end).
Qed.

Lemma args_nil {Γ} (a : args Γ []) : a = anil.
Proof.
  refine (match a as a1 in args Γ0 L return
            match L return args Γ0 L -> Prop with
            | [] => fun a0 => a0 = anil
            | _ => fun _ => True
            end a1 with
          | anil => eq_refl
          | acons _ _ => I
          end).
Qed.

(** Accès au i-ième argument, i étant une variable du domaine. *)
Fixpoint aget {Γ Θ σ} (z : var Θ σ) : args Γ Θ -> tms Γ σ :=
  match z in var Θ0 σ0 return args Γ Θ0 -> tms Γ σ0 with
  | vz => fun a => ahd a
  | vs z' => fun a => aget z' (atl a)
  end.

Lemma args_ext {Γ Θ} (a a' : args Γ Θ) :
  (forall σ (z : var Θ σ), aget z a = aget z a') -> a = a'.
Proof.
  revert a a'; induction Θ as [|σ Θ IH]; intros a a' H.
  - rewrite (args_nil a), (args_nil a'); reflexivity.
  - rewrite (args_eta a), (args_eta a').
    f_equal.
    + exact (H σ vz).
    + apply IH; intros σ' z; exact (H σ' (vs z)).
Qed.

(** ** Renommages et affaiblissement *)

Definition ren (Γ Δ : ctx) : Type := forall σ, var Γ σ -> var Δ σ.

Definition rid {Γ} : ren Γ Γ := fun _ x => x.
Definition rcomp {Γ Δ Ξ} (ρ : ren Γ Δ) (ξ : ren Δ Ξ) : ren Γ Ξ :=
  fun σ x => ξ σ (ρ σ x).

(** Affaiblissement par un contexte [Λ] placé en tête. *)
Definition wk (Λ : ctx) {Γ} : ren Γ (Λ ++ Γ) := fun _ y => vr Λ y.

(** Relèvement d'un renommage sous les lieurs [Λ]. *)
Definition upr (Λ : ctx) {Γ Δ} (ρ : ren Γ Δ) : ren (Λ ++ Γ) (Λ ++ Δ) :=
  fun σ x => match vsplit Λ x with
             | inl z => vl Δ z
             | inr y => vr Λ (ρ σ y)
             end.

Fixpoint ren_tm {Γ s} (t : tm Γ s) : forall Δ, ren Γ Δ -> tm Δ s :=
  match t with
  | tvar x a => fun Δ ρ => tvar (ρ _ x) (ren_args a Δ ρ)
  | tsym c a => fun Δ ρ => tsym c (ren_args a Δ ρ)
  end
with ren_args {Γ Θ} (a : args Γ Θ) : forall Δ, ren Γ Δ -> args Δ Θ :=
  match a with
  | anil => fun _ _ => anil
  | @acons _ σ _ t a' => fun Δ ρ => acons (ren_tm t _ (upr (dom σ) ρ)) (ren_args a' Δ ρ)
  end.

(** Renommage d'un terme de spécification σ. *)
Definition ren_tms {Γ σ} (u : tms Γ σ) {Δ} (ρ : ren Γ Δ) : tms Δ σ :=
  ren_tm u _ (upr (dom σ) ρ).

(** ** Kits : traversée générique

    Un kit associe à chaque variable soit une variable (renommage), soit un
    corps accompagné d'une fonction d'application (substitution). La
    traversée [trav] est structurelle sur le terme ; toute la récursion sur
    les spécifications est confinée dans les fonctions d'application. *)

Definition applier (σ : spec) : Type :=
  forall Ξ, tms Ξ σ -> args Ξ (dom σ) -> tm Ξ (cod σ).

Definition entry (Δ : ctx) (σ : spec) : Type := (var Δ σ + (tms Δ σ * applier σ))%type.

Definition kit (Γ Δ : ctx) : Type := forall σ, var Γ σ -> entry Δ σ.

Definition eshift (Λ : ctx) {Δ σ} (e : entry Δ σ) : entry (Λ ++ Δ) σ :=
  match e with
  | inl y => inl (vr Λ y)
  | inr (u, f) => inr (ren_tms u (wk Λ), f)
  end.

Definition kup (Λ : ctx) {Γ Δ} (K : kit Γ Δ) : kit (Λ ++ Γ) (Λ ++ Δ) :=
  fun σ x => match vsplit Λ x with
             | inl z => inl (vl Δ z)
             | inr y => eshift Λ (K σ y)
             end.

Fixpoint trav {Γ s} (t : tm Γ s) : forall Δ, kit Γ Δ -> tm Δ s :=
  match t with
  | tvar x a => fun Δ K =>
      match K _ x with
      | inl y => tvar y (trav_args a Δ K)
      | inr (u, f) => f Δ u (trav_args a Δ K)
      end
  | tsym c a => fun Δ K => tsym c (trav_args a Δ K)
  end
with trav_args {Γ Θ} (a : args Γ Θ) : forall Δ, kit Γ Δ -> args Δ Θ :=
  match a with
  | anil => fun _ _ => anil
  | @acons _ σ _ t a' => fun Δ K => acons (trav t _ (kup (dom σ) K)) (trav_args a' Δ K)
  end.

(** ** Application héréditaire

    [happ σ Ξ u a] instancie les variables liées du corps [u : tms Ξ σ] par
    les arguments [a]. C'est la β-réduction hereditaire : chaque variable du
    domaine rencontrée en tête est remplacée en appelant [happ] sur sa
    spécification, structurellement plus petite. *)

Definition inst_kit (Θ : list spec) {Ξ} (a : args Ξ Θ) (fs : All applier Θ) : kit (Θ ++ Ξ) Ξ :=
  fun σ x => match vsplit Θ x with
             | inl z => inr (aget z a, all_get z fs)
             | inr y => inl y
             end.

Fixpoint happ (σ : spec) : applier σ :=
  match σ as σ0 return applier σ0 with
  | Spec Θ b => fun Ξ u a =>
      trav u Ξ (inst_kit Θ a ((fix go (Θ0 : list spec) : All applier Θ0 :=
                                 match Θ0 with
                                 | [] => tt
                                 | τ :: Θ1 => (happ τ, go Θ1)
                                 end) Θ))
  end.

Fixpoint happs (Θ : list spec) : All applier Θ :=
  match Θ with
  | [] => tt
  | τ :: Θ1 => (happ τ, happs Θ1)
  end.

Lemma happ_Spec Θ b Ξ (u : tms Ξ (Spec Θ b)) (a : args Ξ Θ) :
  happ (Spec Θ b) Ξ u a = trav u Ξ (inst_kit Θ a (happs Θ)).
Proof. reflexivity. Qed.

Lemma all_get_happs Θ σ (z : var Θ σ) : all_get z (happs Θ) = happ σ.
Proof. induction z; cbn; auto. Qed.

(** ** η-expansion des variables

    Une variable n'est pas un terme : il faut l'η-expanser.
    [eta σ Γ x] est le terme η-long [x(η y1, ..., η yn)] de spécification σ. *)

Fixpoint eta (σ : spec) : forall Γ, var Γ σ -> tms Γ σ :=
  match σ as σ0 return forall Γ, var Γ σ0 -> tms Γ σ0 with
  | Spec Θ b => fun Γ x =>
      @tvar (Θ ++ Γ) (Spec Θ b) (vr Θ x)
        ((fix go (Θ0 : list spec) : forall Ξ, (forall ρ, var Θ0 ρ -> var Ξ ρ) -> args Ξ Θ0 :=
            match Θ0 with
            | [] => fun _ _ => anil
            | ρ :: Θ1 => fun Ξ f => acons (eta ρ Ξ (f ρ vz)) (go Θ1 Ξ (fun ρ' y => f ρ' (vs y)))
            end) Θ (Θ ++ Γ) (fun ρ z => vl Γ z))
  end.

Fixpoint etas (Θ : list spec) : forall Ξ, (forall ρ, var Θ ρ -> var Ξ ρ) -> args Ξ Θ :=
  match Θ with
  | [] => fun _ _ => anil
  | ρ :: Θ1 => fun Ξ f => acons (eta ρ Ξ (f ρ vz)) (etas Θ1 Ξ (fun ρ' y => f ρ' (vs y)))
  end.

Lemma eta_Spec Θ b Γ (x : var Γ (Spec Θ b)) :
  eta (Spec Θ b) Γ x = @tvar (Θ ++ Γ) (Spec Θ b) (vr Θ x) (etas Θ (Θ ++ Γ) (fun ρ z => vl Γ z)).
Proof. reflexivity. Qed.

(** ** Substitutions fonctionnelles (outil interne)

    [sub Γ Δ] associe à chaque variable de [Γ] un terme de sa spécification
    dans [Δ]. C'est la forme commode pour les preuves, où l'on n'énonce que
    des égalités point par point. Les vecteurs proprement dits, objets finis
    sur lesquels l'égalité est extensionnelle sans axiome, sont définis dans
    [Vectors.v] : [vec Γ Δ := args Δ Γ]. *)

Definition sub (Γ Δ : ctx) : Type := forall σ, var Γ σ -> tms Δ σ.

Definition sub_kit {Γ Δ} (τ : sub Γ Δ) : kit Γ Δ := fun σ x => inr (τ σ x, happ σ).

Definition subst {Γ s} (t : tm Γ s) {Δ} (τ : sub Γ Δ) : tm Δ s := trav t Δ (sub_kit τ).
Definition subst_args {Γ Θ} (a : args Γ Θ) {Δ} (τ : sub Γ Δ) : args Δ Θ := trav_args a Δ (sub_kit τ).
Definition subst_tms {Γ σ} (u : tms Γ σ) {Δ} (τ : sub Γ Δ) : tms Δ σ :=
  trav u _ (kup (dom σ) (sub_kit τ)).

(** Substitution identité : chaque variable par son η-expansé. *)
Definition ids {Γ} : sub Γ Γ := fun σ x => eta σ Γ x.

(** Compositions (ordre diagrammatique : d'abord le premier argument). *)
Definition rs_comp {Γ Δ Ξ} (ρ : ren Γ Δ) (τ : sub Δ Ξ) : sub Γ Ξ := fun σ x => τ σ (ρ σ x).
Definition sr_comp {Γ Δ Ξ} (τ : sub Γ Δ) (ξ : ren Δ Ξ) : sub Γ Ξ := fun σ x => ren_tms (τ σ x) ξ.
Definition ss_comp {Γ Δ Ξ} (τ : sub Γ Δ) (θ : sub Δ Ξ) : sub Γ Ξ := fun σ x => subst_tms (τ σ x) θ.

(** Extension d'une substitution par une liste d'arguments (le « cons »
    généralisé aux contextes) et relèvement sous les lieurs. *)
Definition sapp {Θ Γ Δ} (a : args Δ Θ) (τ : sub Γ Δ) : sub (Θ ++ Γ) Δ :=
  fun σ x => match vsplit Θ x with
             | inl z => aget z a
             | inr y => τ σ y
             end.

Definition up_sub (Λ : ctx) {Γ Δ} (τ : sub Γ Δ) : sub (Λ ++ Γ) (Λ ++ Δ) :=
  sapp (etas Λ (Λ ++ Δ) (fun ρ z => vl Δ z)) (sr_comp τ (wk Λ)).

(** Extension par un seul terme. *)
Definition scons {σ Γ Δ} (u : tms Δ σ) (τ : sub Γ Δ) : sub (σ :: Γ) Δ :=
  var_inv (fun σ' _ => tms Δ σ') u (fun σ' y => τ σ' y).

End Syntax.

Arguments args_eta {Srt Sym Γ σ Θ} a.
Arguments args_nil {Srt Sym Γ} a.
Arguments args_ext {Srt Sym Γ Θ} a a' _.
Arguments happ_Spec {Srt Sym} Θ b {Ξ} u a.
Arguments all_get_happs {Srt Sym} Θ {σ} z.
Arguments eta_Spec {Srt Sym} Θ b {Γ} x.
Arguments tvar {Srt Sym Γ σ} x a.
Arguments tsym {Srt Sym Γ σ} c a.
Arguments anil {Srt Sym Γ}.
Arguments acons {Srt Sym Γ σ Θ} t a.
Arguments ahd {Srt Sym Γ σ Θ} a.
Arguments atl {Srt Sym Γ σ Θ} a.
Arguments aget {Srt Sym Γ Θ σ} z a.
Arguments rid {Srt Γ}.
Arguments rcomp {Srt Γ Δ Ξ} ρ ξ.
Arguments wk {Srt} Λ {Γ}.
Arguments upr {Srt} Λ {Γ Δ} ρ.
Arguments ren_tm {Srt Sym Γ s} t {Δ} ρ.
Arguments ren_args {Srt Sym Γ Θ} a {Δ} ρ.
Arguments ren_tms {Srt Sym Γ σ} u {Δ} ρ.
Arguments eshift {Srt Sym} Λ {Δ σ} e.
Arguments kup {Srt Sym} Λ {Γ Δ} K.
Arguments trav {Srt Sym Γ s} t {Δ} K.
Arguments trav_args {Srt Sym Γ Θ} a {Δ} K.
Arguments inst_kit {Srt Sym} Θ {Ξ} a fs.
Arguments happ {Srt Sym} σ [Ξ] u a.
Arguments happs {Srt Sym} Θ.
Arguments eta {Srt Sym} σ {Γ} x.
Arguments etas {Srt Sym} Θ {Ξ} f.
Arguments sub_kit {Srt Sym Γ Δ} τ.
Arguments subst {Srt Sym Γ s} t {Δ} τ.
Arguments subst_args {Srt Sym Γ Θ} a {Δ} τ.
Arguments subst_tms {Srt Sym Γ σ} u {Δ} τ.
Arguments ids {Srt Sym Γ}.
Arguments rs_comp {Srt Sym Γ Δ Ξ} ρ τ.
Arguments sr_comp {Srt Sym Γ Δ Ξ} τ ξ.
Arguments ss_comp {Srt Sym Γ Δ Ξ} τ θ.
Arguments sapp {Srt Sym Θ Γ Δ} a τ.
Arguments up_sub {Srt Sym} Λ {Γ Δ} τ.
Arguments scons {Srt Sym σ Γ Δ} u τ.

(** Notations à la Autosubst. *)
Declare Scope subst_scope.
Delimit Scope subst_scope with sub.
Notation "t ⟨ ρ ⟩" := (ren_tm t ρ) (at level 7, left associativity, format "t ⟨ ρ ⟩") : subst_scope.
Notation "t .[ τ ]" := (subst t τ) (at level 7, left associativity, format "t .[ τ ]") : subst_scope.
Notation "ρ >> ξ" := (rcomp ρ ξ) (at level 56, left associativity) : subst_scope.
Notation "ρ >>> τ" := (rs_comp ρ τ) (at level 56, left associativity) : subst_scope.
Notation "τ >>! ξ" := (sr_comp τ ξ) (at level 56, left associativity) : subst_scope.
Notation "τ >=> θ" := (ss_comp τ θ) (at level 56, left associativity) : subst_scope.
Notation "u .: τ" := (scons u τ) (at level 55, right associativity) : subst_scope.
