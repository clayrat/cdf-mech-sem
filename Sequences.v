(** A library of operators over relations,
    to define transition sequences and their properties. *)

    From Coq Require Import ssreflect ssrbool ssrfun.
    From mathcomp Require Import ssrnat.

    Set Implicit Arguments.

    Section SEQUENCES.

    Variable A: Type.                 (**r the type of states *)
    Variable R: A -> A -> Prop.       (**r the transition relation between states *)

    (** ** Finite sequences of transitions *)

    (** Zero, one or several transitions: reflexive transitive closure of [R]. *)

    Inductive star: A -> A -> Prop :=
      | star_refl: forall a,
          star a a
      | star_step: forall a b c,
          R a b -> star b c -> star a c.

    Lemma inv_star a c : star a c -> c = a \/ exists b, R a b /\ star b c.
    Proof.
    move=>H; case: {-1}_ {-2}_ / H (erefl a) (erefl c).
    - by move=>x _ _; left.
    by move=>{}a b {}c H1 H2 _ _; right; exists b.
    Qed.

    Lemma star_one (a b: A) : R a b -> star a b.
    Proof.
    move=>?.
    by apply/star_step/star_refl.
    Qed.

    Lemma star_trans (a b: A): star a b -> forall c, star b c -> star a c.
    Proof.
    elim=>// ????? IH ??.
    by apply/star_step/IH.
    Qed.

    (** One or several transitions: transitive closure of [R]. *)

    Inductive plus: A -> A -> Prop :=
      | plus_left: forall a b c,
          R a b -> star b c -> plus a c.

    Lemma inv_plus a c : plus a c -> exists b, R a b /\ star b c.
    Proof.
    move=>P; case: {-2}_ {-2}_ / P (erefl a) (erefl c)=>{}a b {}c H1 H2 _ _.
    by exists b.
    Qed.

    Lemma plus_one a b : R a b -> plus a b.
    Proof.
    move=>?.
    by apply/plus_left/star_refl.
    Qed.

    Lemma plus_star a b : plus a b -> star a b.
    Proof.
    by case; exact: star_step.
    Qed.

    Lemma plus_star_trans a b c : plus a b -> star b c -> plus a c.
    Proof.
    case=>???? H1 H2.
    by apply/plus_left/star_trans/H2/H1.
    Qed.

    Lemma star_plus_trans a b c : star a b -> plus b c -> plus a c.
    Proof.
    case=>// {}a {}b d HR HS.
    case: (inv_star HS)=>[EQ|[x [HS1 H1]]] H.
    - rewrite -EQ in HR.
      by apply/plus_left/plus_star/H.
    by apply/(plus_left HR)/star_trans/plus_star/H/star_step/H1.
    Qed.

    Lemma plus_right a b c : star a b -> R b c -> plus a c.
    Proof.
    move=>? H2.
    by apply/star_plus_trans/plus_one/H2.
    Qed.

    (** Absence of transitions from a state. *)

    Definition irred (a: A) : Prop := forall b, ~(R a b).

    (** ** Infinite transition sequences *)

    (** It is easy to characterize the fact that all transition sequences starting
      from a state [a] are infinite: it suffices to say that any finite sequence
      starting from [a] can always be extended by one more transition. *)

    Definition all_seq_inf (a: A) : Prop :=
      forall b, star a b -> exists c, R b c.

    (** However, this is not the notion we are trying to characterize: the case
      where there exists an infinite sequence of transitions starting from [a],
      [a --> a1 --> a2 --> ... -> aN -> ...]
      leaving open the possibility that there exists finite sequences
      starting from [a].

      Example: consider [A = nat] and [R] such that [R 0 0] and [R 0 1].
      [all_seq_inf 0] does not hold, because a sequence [0 -->* 1] cannot
      be extended.  Yet, [R] admits an infinite sequence, namely
      [0 --> 0 --> ...].

      Another attempt would be to represent the sequence of states
      [a0 --> a1 --> a2 --> ... -> aN -> ...] explicitly, as a function
      [f: nat -> A] such that [f i] is the [i]-th state [ai] of the sequence. *)

    Definition infseq_with_function (a: A) : Prop :=
      exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f i.+1).

    (** This is a correct characterization of the existence of an infinite
      sequence of reductions.  However, it is inconvenient to work with
      this definition in Coq's constructive logic: in most use cases, the
      function [f] is not computable and therefore cannot be defined in Coq.

      However, we do not really need the function [f]: its codomain [X] is
      all we need!  What matters is the existence of a set [X] such as
      [a] is in [X], and
      every [b] in [X] can make a transition to an element of [X].
      This suffices to prove the existence of an infinite sequence of transitions
      starting from [a].
    *)

    Definition infseq (a: A) : Prop :=
      exists X: A -> Prop,
      X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

    (** This definition is essentially a coinduction principle.
      Let us show some expected properties.  For instance: if relation [R]
      contains a cycle, an infinite sequence exists. *)

    Remark cycle_infseq a : R a a -> infseq a.
    Proof.
    move=>H.
    exists (fun b => b = a); split=>// ? ->.
    by exists a.
    Qed.

    (** More generally: if all sequences from [a] are infinite, there exists one
      infinite sequence starting in [a]. *)

    Lemma infseq_if_all_seq_inf a :
      all_seq_inf a -> infseq a.
    Proof.
    move=>?.
    exists all_seq_inf; split=>// a1 HA1.
    case: (HA1 a1 (star_refl _))=>a2 R12.
    exists a2; split=>// a3 S23.
    case: (HA1 a3 (star_step R12 S23))=>a4 R23.
    by exists a4.
    Qed.

    (** Likewise, the characterization [infseq_with_function] based on functions
      implies [infseq]. *)

    Lemma infseq_from_function a :
      infseq_with_function a -> infseq a.
    Proof.
    case=>f [??].
    exists (fun a => exists i, f i = a); split.
    - by exists 0.
    move=>a1 [i <-].
    exists (f (S i)); split=>//.
    by exists (S i).
    Qed.

    (** An "inversion lemma" for [infseq]: if [infseq a], i.e. there exists
      an infinite sequence starting in [a], then [a] can transition to a state [b]
      that satisfies [infseq b]. *)

    Lemma infseq_inv a :
      infseq a -> exists b, R a b /\ infseq b.
    Proof.
    case=>X [Xa XP].
    move: (XP a Xa)=>[b [??]].
    exists b; split=>//.
    by exists X.
    Qed.

    (** A very useful coinduction principle considers a set [X] where for
      every [a] in [X], we can make one *or several* transitions to reach
      a state [b] that belongs to [X].  *)

    Lemma infseq_coinduction_principle (X: A -> Prop) :
      (forall a, X a -> exists b, plus a b /\ X b) ->
      forall a, X a -> infseq a.
    Proof.
    move=>H a0 Xa0.
    exists (fun a => exists b, star a b /\ X b); split.
    - exists a0; split=>//; exact: star_refl.
    - move=>a1 [a2 [S12 X2]].
      case: (inv_star S12)=>[<-|[x [HS1 H1]]].
      - case: (H _ X2)=>[a3 [P23 X3]].
        case: (inv_plus P23)=>b [Hr S].
        by exists b; split=>//; exists a3.
      by exists x; split=>//; exists a2.
    Qed.

    (** ** Determinism properties for functional transition relations. *)

    (** A transition relation is functional if every state can transition
      to at most one other state. *)

    Hypothesis R_functional:
      forall a b c, R a b -> R a c -> b = c.

    (** Uniqueness of finite transition sequences. *)

    Lemma star_star_inv a b :
      star a b -> forall c, star a c -> star b c \/ star c b.
    Proof.
    elim.
    - by move=>???; left.
    move=>{}a {}b ? HR S IH c S1.
    case: (inv_star S1)=>[EQ|[x [HR2 S2]]].
    - rewrite -EQ in HR.
      by right; apply/star_step/S.
    by apply: IH; rewrite (R_functional HR HR2).
    Qed.

    Lemma finseq_unique a b b' :
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
    Proof.
    move=>S1 Ib S2 Ic.
    case: (star_star_inv S1 S2)=>S; case: (inv_star S)=>// [[c][HR _]].
    - by move: (Ib _ HR).
    by move: (Ic _ HR).
    Qed.

    (** A state cannot both diverge and terminate on an irreducible state. *)

    Lemma infseq_inv' a b : R a b -> infseq a -> infseq b.
    Proof.
    move=>Rab Ia.
    move: (infseq_inv Ia)=>[? [Rab0 ?]].
    by rewrite (R_functional Rab Rab0).
    Qed.

    Lemma infseq_star_inv a b : star a b -> infseq a -> infseq b.
    Proof.
    elim=>// ????? IH Ia1.
    by apply/IH/infseq_inv'/Ia1.
    Qed.

    Lemma infseq_finseq_excl a b :
      star a b -> irred b -> ~ infseq a.
    Proof.
    move=>S Ib I.
    move: (infseq_star_inv S I) => /infseq_inv [c [? _]].
    by apply: (Ib c).
    Qed.

    (** If there exists an infinite sequence of transitions from [a],
      all sequences of transitions arising from [a] are infinite. *)

    Lemma infseq_all_seq_inf a : infseq a -> all_seq_inf a.
    Proof.
    move=>I ? S.
    move: (infseq_star_inv S I) => /infseq_inv [c [? _]].
    by exists c.
    Qed.

    End SEQUENCES.
