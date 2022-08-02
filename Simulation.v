From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat.
From CDF Require Import Sequences.

(** A generic simulation diagram, to prove semantic equivalence of two
    programs based on their small-step semantics. *)

Section SIMULATION_DIAGRAM.

(** The diagram is parameterized by
    - the small-step semantics for each of the two programs:
      type of configurations and transition relation between configurations;
    - an invariant that connects the configurations of the two programs
    - a nonnegative measure over source configurations.
*)

Variable C1: Type.	            (**r the type of configurations for the source program *)
Variable step1: C1 -> C1 -> Prop.   (**r its transition relation *)

Variable C2: Type.	            (**r the type of configurations for the transformed program *)
Variable step2: C2 -> C2 -> Prop.   (**r its transition relation *)

Variable inv: C1 -> C2 -> Prop.     (**r the invariant *)

Variable measure: C1 -> nat.        (**r the measure that prevents infinite stuttering *)

(** The diagram properly speaking is the following assumption:
    every source program transition is simulated by zero, one or several
    transitions of the transformed program, while preserving the invariant
    and decreasing the measure in the stuttering case. *)

Hypothesis simulation :
  forall c1 c1', step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2',
     (plus step2 c2 c2' \/ (star step2 c2 c2' /\ measure c1' < measure c1))
  /\ inv c1' c2'.

(** We first extend the simulation diagram to finite sequences of
    source transitions.  This is the crucial lemma to show semantic
    preservation when the source program terminates. *)

Lemma simulation_star c1 c1' :
  star step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2', star step2 c2 c2' /\ inv c1' c2'.
Proof.
elim=>[a|a b c H1 H IH] c2 H2 {c1 c1'}.
- (* zero transitions *)
  by exists c2; split=>//; exact: star_refl.
(* one or several transitions *)
case: (simulation _ _ H1 _ H2)=>c2' [P Q].
case: (IH _ Q)=>c2'' [U V].
exists c2''; split=>//.
apply/star_trans/U; case: P.
- by apply: plus_star.
by case.
Qed.

(** Now consider a source program that performs infinitely many
    transitions.  We first show that the transformed program can
    always make progress (perform at least one transition) while
    preserving the invariant [inv].  The proof is by induction on [N],
    the greatest number of stuttering steps that the transformed
    program can make before being forced to take at least one
    transition. *)

Lemma simulation_infseq_productive N c1 c2 :
  measure c1 < N ->
  infseq step1 c1 ->
  inv c1 c2 ->
  exists c1' c2',
   [/\ plus step2 c2 c2',
       infseq step1 c1' &
       inv c1' c2'].
Proof.
elim: N c1 =>// n IH c1 Hm Hi1 Hi.
(* N > 0 *)
rewrite ltnS in Hm.
case: (infseq_inv Hi1)=>c1' [Hs1 Hi1''].
case: (simulation _ _ Hs1 _ Hi)=>c2' [P Hi'].
case: P=>[Hs2|[Hs2 Hm']].
- (* one or several *)
  by exists c1', c2'.
(* zero, one or several transitions *)
case: (inv_star Hs2)=>[E|[b [Hs Hst]]].
- (* zero transitions *)
  rewrite {c2' Hs2}E in Hi'.
  by apply: (IH c1')=>//; apply: (leq_trans Hm').
(* one or several transitions *)
exists c1', c2'; split=>//.
by apply/plus_left/Hst.
Qed.

(** As a consequence, the transformed program performs infinitely many
    transitions if started in a configuration that is related to a
    diverging configuration of the source program. *)

Lemma simulation_infseq c1 c2 :
  infseq step1 c1 ->
  inv c1 c2 ->
  infseq step2 c2.
Proof.
move=>H1 H2.
apply: (infseq_coinduction_principle
         (fun c2 => exists c1, infseq step1 c1 /\ inv c1 c2)); last by exists c1.
move=>{H2}c2 [{H1}c1 [His Hi]].
case: (simulation_infseq_productive (measure c1).+1 c1 c2)=>// c1' [c2'][Hp Hi1' Hi2'].
by exists c2'; split=>//; exists c1'.
Qed.

End SIMULATION_DIAGRAM.
