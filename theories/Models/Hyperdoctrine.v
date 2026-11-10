(** * Hyperdoctrines de Heyting

    Une fibration à fibres de Heyting au-dessus d'une catégorie C, présentée
    comme une famille indexée : pour chaque objet X, un préordre de
    prédicats [pred X] muni de ⊤, ⊥, ∧, ∨, ⇒ ; pour chaque morphisme
    f : X ~> Y, une réindexation f* : pred Y → pred X, monotone, fonctorielle
    et qui préserve la structure de Heyting (à équivalence près). Les
    quantificateurs (adjoints à la réindexation le long de certaines
    projections) sont ajoutés dans [Logic.v], seulement pour les sortes
    quantifiables : c'est là que l'ordre (n,p) intervient. *)

From Category Require Import Lib Theory.Category.

Record hyperdoctrine (C : Category) := {
  pred : obj[C] -> Type;
  ple : forall {X}, pred X -> pred X -> Prop;
  ple_refl : forall {X} (p : pred X), ple p p;
  ple_trans : forall {X} (p q r : pred X), ple p q -> ple q r -> ple p r;

  ptop : forall {X}, pred X;
  pbot : forall {X}, pred X;
  pand : forall {X}, pred X -> pred X -> pred X;
  por : forall {X}, pred X -> pred X -> pred X;
  pimp : forall {X}, pred X -> pred X -> pred X;

  top_max : forall {X} (p : pred X), ple p ptop;
  bot_min : forall {X} (p : pred X), ple pbot p;
  and_l : forall {X} (p q : pred X), ple (pand p q) p;
  and_r : forall {X} (p q : pred X), ple (pand p q) q;
  and_intro : forall {X} (p q r : pred X), ple r p -> ple r q -> ple r (pand p q);
  or_l : forall {X} (p q : pred X), ple p (por p q);
  or_r : forall {X} (p q : pred X), ple q (por p q);
  or_elim : forall {X} (p q r : pred X), ple p r -> ple q r -> ple (por p q) r;
  imp_adj : forall {X} (p q r : pred X), ple (pand r p) q <-> ple r (pimp p q);

  reidx : forall {X Y} (f : X ~> Y), pred Y -> pred X;
  reidx_proper : forall {X Y} (f g : X ~> Y) (p : pred Y), f ≈ g -> ple (reidx f p) (reidx g p);
  reidx_mono : forall {X Y} (f : X ~> Y) (p q : pred Y), ple p q -> ple (reidx f p) (reidx f q);
  reidx_id : forall {X} (p : pred X), ple (reidx id p) p /\ ple p (reidx id p);
  reidx_comp : forall {X Y Z} (f : Y ~> Z) (g : X ~> Y) (p : pred Z),
      ple (reidx (f ∘ g) p) (reidx g (reidx f p)) /\ ple (reidx g (reidx f p)) (reidx (f ∘ g) p);
  reidx_top : forall {X Y} (f : X ~> Y), ple ptop (reidx f ptop);
  reidx_bot : forall {X Y} (f : X ~> Y), ple (reidx f pbot) pbot;
  reidx_and : forall {X Y} (f : X ~> Y) (p q : pred Y), ple (pand (reidx f p) (reidx f q)) (reidx f (pand p q));
  reidx_or : forall {X Y} (f : X ~> Y) (p q : pred Y), ple (reidx f (por p q)) (por (reidx f p) (reidx f q));
  reidx_imp : forall {X Y} (f : X ~> Y) (p q : pred Y),
      ple (reidx f (pimp p q)) (pimp (reidx f p) (reidx f q)) /\
      ple (pimp (reidx f p) (reidx f q)) (reidx f (pimp p q))
}.

Arguments pred {C} h X.
Arguments ple {C h X} p q.
Arguments ple_refl {C h X} p.
Arguments ple_trans {C h X} p q r _ _.
Arguments ptop {C h X}.
Arguments pbot {C h X}.
Arguments pand {C h X} p q.
Arguments por {C h X} p q.
Arguments pimp {C h X} p q.
Arguments top_max {C h X} p.
Arguments bot_min {C h X} p.
Arguments and_l {C h X} p q.
Arguments and_r {C h X} p q.
Arguments and_intro {C h X} p q r _ _.
Arguments or_l {C h X} p q.
Arguments or_r {C h X} p q.
Arguments or_elim {C h X} p q r _ _.
Arguments imp_adj {C h X} p q r.
Arguments reidx {C h X Y} f p.
Arguments reidx_proper {C h X Y} f g p _.
Arguments reidx_mono {C h X Y} f p q _.

(** ** Calcul dans une fibre *)

Section Heyting.
Context {C : Category} {H : hyperdoctrine C} {X : obj[C]}.

Local Notation "p ≤ q" := (@ple C H X p q) (at level 70).
Local Notation "p ⊓ q" := (@pand C H X p q) (at level 40, left associativity).

Lemma ple_and_l (p q r : pred H X) : p ≤ r -> p ⊓ q ≤ r.
Proof. intros Hp; eapply ple_trans; [apply and_l|exact Hp]. Qed.

Lemma ple_and_r (p q r : pred H X) : q ≤ r -> p ⊓ q ≤ r.
Proof. intros Hq; eapply ple_trans; [apply and_r|exact Hq]. Qed.

Lemma and_mono (p p' q q' : pred H X) : p ≤ p' -> q ≤ q' -> p ⊓ q ≤ p' ⊓ q'.
Proof. intros H1 H2; apply and_intro; [apply ple_and_l, H1|apply ple_and_r, H2]. Qed.

Lemma and_comm (p q : pred H X) : p ⊓ q ≤ q ⊓ p.
Proof. apply and_intro; [apply and_r|apply and_l]. Qed.

(** Modus ponens interne. *)
Lemma imp_eval (p q : pred H X) : pimp p q ⊓ p ≤ q.
Proof. apply (imp_adj p q (pimp p q)), ple_refl. Qed.

(** Distributivité, conséquence de l'adjonction. *)
Lemma and_or_elim (r p q s : pred H X) : r ⊓ p ≤ s -> r ⊓ q ≤ s -> r ⊓ por p q ≤ s.
Proof.
  intros H1 H2. eapply ple_trans; [apply and_comm|]. apply imp_adj.
  apply or_elim; apply imp_adj; (eapply ple_trans; [apply and_comm|]); assumption.
Qed.

End Heyting.
