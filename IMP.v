From Equations Require Import Equations.
From Coq Require Import ssreflect ssrfun ssrbool String.
From mathcomp Require Import ssrnat ssrint ssralg ssrnum eqtype order.
From CDF Require Import Sequences.

Derive Signature for star.

Import Order.Theory GRing.Theory.
Local Open Scope string_scope.
Local Open Scope ring_scope.

Definition eq_string (a b : string) : bool :=
  match string_dec a b with left _ => true | right _ => false end.

Lemma eq_stringP : Equality.axiom eq_string.
Proof. move=>x y; apply: (iffP idP); rewrite /eq_string; by case: (string_dec _ _). Qed.

Canonical Structure string_eqMixin := EqMixin eq_stringP.
Canonical Structure string_eqType := Eval hnf in EqType _ string_eqMixin.

(** * 1.  The IMP language *)

(** ** 1.1 Arithmetic expressions *)

Definition ident := string.

(** The abstract syntax: an arithmetic expression is either... *)

Inductive aexp : Type :=
  | CONST (n: int)                       (**r a constant, or *)
  | VAR (x: ident)                     (**r a variable, or *)
  | PLUS (a1: aexp) (a2: aexp)         (**r a sum of two expressions, or *)
  | MINUS (a1: aexp) (a2: aexp).       (**r a difference of two expressions *)

(** The denotational semantics: an evaluation function that computes
  the integer value denoted by an expression.  This function is
  parameterized by a store [s] that associates values to variables. *)

Definition store : Type := ident -> int.

Fixpoint aeval (a: aexp) (s: store) : int :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(** Such evaluation functions / denotational semantics have many uses.
    First, we can use [aeval] to evaluate a given expression in a given store. *)

Eval compute in (aeval (PLUS (VAR "x") (MINUS (VAR "x") (CONST 1))) (fun => 2)).

(** Result: [ = 3 : int ]. *)

(** We can also do partial evaluation with respect to an unknown store *)

Eval cbn in (aeval (PLUS (VAR "x") (MINUS (CONST 10) (CONST 1)))).

(** Result: [ = fun s : store => s "x" + 9 ]. *)

(** We can prove mathematical properties of a given expression. *)

Lemma aeval_xplus1 s x :
  aeval (PLUS (VAR x) (CONST 1)) s > aeval (VAR x) s.
Proof.
by rewrite ltz_addr1 lexx.
Qed.

(** Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its
  free variables.

  Free variables are defined by this recursive predicate:
*)

Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | CONST n => False
  | VAR y => y = x
  | PLUS a1 a2 | MINUS a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free s1 s2 a :
  (forall x, free_in_aexp x a -> s1 x = s2 x) ->
  aeval a s1 = aeval a s2.
Proof.
elim: a=>/=.
- (* Case a = CONST n *)
  by [].
- (* Case a = VAR x *)
  by move=>x; apply.
- (* Case a = PLUS a1 a2 *)
  move=>a1 IH1 a2 IH2 H.
  rewrite IH1; last by move=>x Hx; apply: H; left.
  by rewrite IH2 //; move=>x Hx; apply: H; right.
(* Case a = MINUS a1 a2 *)
move=>a1 IH1 a2 IH2 H.
rewrite IH1; last by move=>x Hx; apply: H; left.
by rewrite IH2 //; move=>x Hx; apply: H; right.
Qed.

(** ** 1.2.  Growing the language of arithmetic expressions *)

(** We can enrich the language with new operators in several ways.
    The simplest way is to define derived forms in terms of existing operators.
    For example, the "opposite" operator is: *)

Definition OPP (a: aexp) : aexp := MINUS (CONST 0) a.

(** Its semantics is the one we expect. *)

Lemma aeval_OPP s a : aeval (OPP a) s = -aeval a s.
Proof.
by rewrite /= sub0r.
Qed.

(** In other cases, we must add constructors to the [aexp] type
    and cases to the [aeval] function.  For example, let's add multiplication.
*)

Module AExp_mul.

Inductive aexp : Type :=
  | CONST (n: int)
  | VAR (x: ident)
  | PLUS (a1: aexp) (a2: aexp)
  | MINUS (a1: aexp) (a2: aexp)
  | TIMES (a1: aexp) (a2: aexp).      (**r NEW! *)

Fixpoint aeval (a: aexp) (s: store) : int :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  | TIMES a1 a2 => aeval a1 s * aeval a2 s
  end.

End AExp_mul.

(** Why not add division as well? *)

Module AExp_div.

Inductive aexp : Type :=
  | CONST (n: int)
  | VAR (x: ident)
  | PLUS (a1: aexp) (a2: aexp)
  | MINUS (a1: aexp) (a2: aexp)
  | TIMES (a1: aexp) (a2: aexp)
  | QUOT (a1: aexp) (a2: aexp).    (**r NEW! *)

(** We have a problem!  The evaluation of an expression can now fail,
  in case of a division by zero.  We must change the type of [aeval]
  to reflect this error case: [aeval] now returns an option type [option int].
  The result [Some n] means "no errors, and the value is [n]".
  The result [None] means "error during evaluation".

  Now that we know how to handle errors, we can make our semantics more
  realistic in other places:
  - variables can be uninitialized; using such a variable in an expression
    is a run-time error;
  - arithmetic operations can overflow the range of integers representable
    by a machine (e.g. 64-bit integers); this is a run-time error as well.
*)

Definition min_int := - ((2 : int) ^ 63).  (**r the smallest representable integer *)
Definition max_int := (2 : int) ^ 63 - 1.  (**r the greatest representable integer *)

Definition check_for_overflow (n: int): option int :=
  if (min_int <= n) && (n <= max_int) then Some n else None.

Fixpoint aeval (s: ident -> option int) (a: aexp) : option int :=
  match a with
  | CONST n => check_for_overflow n
  | VAR x => s x
  | PLUS a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 + n2)
      | _, _ => None
      end
  | MINUS a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 - n2)
      | _, _ => None
      end
  | TIMES a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 * n2)
      | _, _ => None
      end
  | QUOT a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => if n2 == 0 then None else check_for_overflow (n1 / n2)
      | _, _ => None
      end
  end.

End AExp_div.

(** ** 1.3 Boolean expressions *)

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s == aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <= aeval a2 s
  | NOT b1 => ~~ beval b1 s
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** *** Exercise (1 star) *)
(** Prove that the [OR] derived form has the expected semantics. *)

Lemma beval_OR s b1 b2 : beval (OR b1 b2) s = beval b1 s || beval b2 s.
Proof.
by rewrite /= -negb_or negbK.
Qed.

(** ** 1.4 Commands *)

(** To complete the definition of the IMP language, here is the
  abstract syntax of commands, also known as statements. *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (b: bexp) (c1: com).               (**r loop: [while b do c1 done] *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Here is an IMP program that performs Euclidean division by
  repeated subtraction.  At the end of the program, "q" contains
  the quotient of "a" by "b", and "r" contains the remainder.
  In pseudocode:
<<
       r := a; q := 0;
       while b <= r do r := r - b; q := q + 1 done
>>
  In abstract syntax:
*)

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

(** A useful operation over stores:
    [update x v s] is the store that maps [x] to [v] and is equal to [s] for
    all variables other than [x]. *)

Definition update (x: ident) (v: int) (s: store) : store :=
  fun y => if x == y then v else s y.

Lemma update_same x v s : (update x v s) x = v.
Proof.
by rewrite /update eqxx.
Qed.

Lemma update_other x v s y : x != y -> (update x v s) y = s y.
Proof.
by rewrite /update; case: eqP.
Qed.

(** Naively, we would like to define the semantics of a command with
    an execution function [cexec s c] that runs the command [c]
    in initial store [s] and returns the final store when [c] terminates. *)

Fail Fixpoint cexec (c: com) (s: store) : store :=
  match c with
  | SKIP => s
  | ASSIGN x a => update x (aeval a s) s
  | SEQ c1 c2 => let s' := cexec c1 s in cexec c2 s'
  | IFTHENELSE b c1 c2 => if beval b s then cexec c1 s else cexec c2 s
  | WHILE b c1 =>
      if beval b s
      then (let s' := cexec c1 s in cexec (WHILE b c1) s')
      else s
  end.

(** The definition above is rejected by Coq, and rightly so, because
  all Coq functions must terminate, yet the [WHILE] case may not
  terminate.  Consider for example the infinite loop
  [WHILE TRUE SKIP].

  Let's attempt a different style of semantics, based on sequences
  of reductions.
*)

(** ** 1.5.  Reduction semantics *)

(** The relation [ red (c, s) (c', s') ] defines a basic reduction,
    that is, the first computation step when executing command [c]
    in initial memory state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b s then c1 else c2), s)
  | red_while_done: forall b c s,
      ~~ beval b s ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval b s ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s).

(** An interesting property of this reduction relation is that it is
    functional: a configuration [(c,s)] reduces to at most one configuration.
    This corresponds to the fact that IMP is a deterministic language. *)

(* equations seems to mess with erefl *)
Lemma red_determ cs cs1 : red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
elim.
- move=>x a s cs2 R.
  by case E: _ _ / R => //; case: E=><-<-<-.
- move=>c s cs2 R.
  case: {-2}_ {-1}_ / R (@erefl _ (SKIP;;c, s)) (@erefl _ cs2)=>//.
  - by move=>_ _ [->->].
  move=>?? s1 c2 s2 R; case=>E; rewrite E in R.
  by case: {-2}_ {-1}_ / R (@erefl _ (SKIP, s1)) (@erefl _ (c2, s2)).
- move=>c1 c s1 c2 s2 R' IH cs2 R.
  case: {-2}_ {-1}_ / R (@erefl _ (c1;;c, s1)) (@erefl _ cs2)=>//.
  - move=>c0 s [E]; rewrite -E in R'.
    by case: {-2}_ {-1}_ / R' (@erefl _ (SKIP, s1)) (@erefl _ (c2, s2)).
  move=>c3 c4 s3 c5 s4 R''.
  case=>E1 {c4}-> E2 _; rewrite {c3}E1 {s3}E2 in R''.
  by case: (IH _ R'')=><-<-.
- move=>b c1 c2 s cs2 R.
  case: {-2}_ {-1}_ / R (@erefl _ (IFTHENELSE b c1 c2, s)) (@erefl _ cs2)=>//.
  by move=>_ _ _ _[->->->->].
- move=>b c s H cs2 R.
  case: {-2}_ {-1}_ / R (@erefl _ (WHILE b c, s)) (@erefl _ cs2)=>//.
  - by move=>_ _ _ _ [_ _ ->].
  by move=>??? H2 [E1 _ E2]; rewrite E1 E2 in H2; rewrite H2 in H.
move=>b c s H cs2 R.
case: {-2}_ {-1}_ / R (@erefl _ (WHILE b c, s)) (@erefl _ cs2)=>//.
- by move=>??? H2 [E1 _ E2]; rewrite E1 E2 in H2; rewrite H in H2.
by move=>_ _ _ _ [->->->].
Qed.

(** We define the semantics of a command by chaining successive reductions.
    The command [c] in initial state [s] terminates with final state [s']
    if we can go from [(c, s)] to [(skip, s')] in a finite number of reductions.
*)

Definition terminates (s: store) (c: com) (s': store) : Prop :=
  star red (c, s) (SKIP, s').

(** The [star] operator is defined in library [Sequences].
    [star R] is the reflexive transitive closure of relation [R].
    On paper it is often written [R*].
    The [star red] relation therefore represents zero, one or several
    reduction steps. *)

(** Likewise, command [c] diverges (fails to terminate) in initial state [s]
    if there exists an infinite sequence of reductions starting with [(c, s)].
    The [infseq] relation operator is defined in library [Sequences].
*)

Definition diverges (s: store) (c: com) : Prop :=
  infseq red (c, s).

(** Generally speaking, a third kind of executions is possible:
    "going wrong" after a finite number of reductions.
   A configuration [(c', s')] "goes wrong" if it cannot reduce and is
   not a final configuration, that is, [c' <> SKIP]. *)

Definition goes_wrong (s: store) (c: com) : Prop :=
  exists c' s',
  [/\ star red (c, s) (c', s'), irred red (c', s') & c' <> SKIP].

(** *** Exercise (2 stars) *)
(** Prove that IMP command never go wrong.
    Hint: first show the following "progress" property, showing that
    a command other than [SKIP] can always reduce. *)

Lemma red_progress c s :
  c = SKIP \/ exists c' s', red (c, s) (c', s').
Proof.
elim: c.
- by left.
- move=>x a; right.
  by exists SKIP, (update x (aeval a s) s); constructor.
- move=>c1 H1 c2 _; right.
  case: H1.
  - by move=>->; exists c2, s; constructor.
  by case=>c'[s' R]; exists (c';;c2), s'; constructor.
- move=>b c1 _ c2 _; right.
  by exists (if beval b s then c1 else c2), s; constructor.
move=>b c1 H1; right.
case/boolP: (beval b s)=>H.
- by exists (SEQ c1 (WHILE b c1)), s; constructor.
by exists SKIP, s; constructor.
Qed.

Lemma not_goes_wrong c s : ~(goes_wrong s c).
Proof.
case=>c'[s'][S I N].
by case: (red_progress c' s')=>// [[c1]][s2 /I].
Qed.

(** A technical lemma: a sequence of reductions can take place to the left
    of a [SEQ] constructor.  This generalizes rule [red_seq_step]. *)

Lemma red_seq_steps c2 s c s' c' :
  star red (c, s) (c', s') -> star red ((c;;c2), s) ((c';;c2), s').
Proof.
move=>H; depind H.
- by apply: star_refl.
case: b H H0 IHstar=>c1 s1 R S IH.
apply: (@star_step _ _ _ (c1;;c2, s1)).
- by apply: red_seq_step.
by apply: IH.
Qed.

(** ** 1.6.  Natural semantics *)

Inductive cexec: store -> com -> store -> Prop :=
  | cexec_skip: forall s,
      cexec s SKIP s
  | cexec_assign: forall s x a,
      cexec s (ASSIGN x a) (update x (aeval a s) s)
  | cexec_seq: forall c1 c2 s s' s'',
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (SEQ c1 c2) s''
  | cexec_ifthenelse: forall b c1 c2 s s',
      cexec s (if beval b s then c1 else c2) s' ->
      cexec s (IFTHENELSE b c1 c2) s'
  | cexec_while_done: forall b c s,
      ~~ beval b s ->
      cexec s (WHILE b c) s
  | cexec_while_loop: forall b c s s' s'',
      beval b s -> cexec s c s' -> cexec s' (WHILE b c) s'' ->
      cexec s (WHILE b c) s''.

(** The predicate [cexec s c s'] holds iff there exists a finite derivation
    for this conclusion, using the axioms and inference rules above.

    The structure of this derivation represents the computations performed
    by [c] as a tree --- not as a sequence of reductions.

    The finiteness of the derivation guarantees that only terminating executions
    satisfy [cexec].  As an example, [WHILE TRUE SKIP] does not satisfy [cexec].
*)

Lemma cexec_infinite_loop s : ~ exists s', cexec s (WHILE TRUE SKIP) s'.
Proof.
have A s1 c s2 : cexec s1 c s2 -> c <> WHILE TRUE SKIP.
- by move=>H; elim: H=>//; case.
by case=>s1 H; apply: (A _ _ _ H).
Qed.

(** We now show an equivalence between evaluations that terminate according
    to the natural semantics
        (existence of a derivation of [cexec s c s'])
    and to the reduction semantics
        (existence of a reduction sequence from [(c,s)] to [(SKIP, s')].

    We start with the natural semantics => reduction sequence direction,
    which is proved by an elegant induction on the derivation of [cexec]. *)

Theorem cexec_to_reds s c s' : cexec s c s' -> star red (c, s) (SKIP, s').
Proof.
elim.
- (* SKIP *)
  by move=>x; apply: star_refl.
- (* ASSIGN *)
  by move=>s1 x a; apply/star_one/red_assign.
- (* SEQ *)
  move=>c1 c2 s1 s2 s3 H1 Hs1 H2 Hs2.
  apply: star_trans.
  - by apply/red_seq_steps/Hs1.
  by apply: star_step; first by apply: red_seq_done.
- (* IFTHENELSE *)
  move=>b c1 c2 s1 s2 H1 H2.
  by apply: star_step; first by apply: red_ifthenelse.
- (* WHILE stop *)
  move=>b c1 s1 H.
  by apply/star_one/red_while_done.
(* WHILE loop *)
move=>b c1 s1 s2 s3 Hb Hc1 Hs1 Hc2 Hs2.
apply: star_step; first by apply: red_while_loop.
apply: star_trans; first by apply/red_seq_steps/Hs1.
by apply: star_step; first by apply: red_seq_done.
Qed.

(** The other direction, from a reduction sequence to a [cexec]
    derivation, is more subtle.  Here is the key lemma, showing how a
    reduction step followed by a [cexec] execution can combine into a
    [cexec] execution. *)

Lemma red_append_cexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', cexec s2 c2 s' -> cexec s1 c1 s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros.
- (* red_assign *)
  inversion H; subst. apply cexec_assign.
- (* red_seq_done *)
  apply cexec_seq with s2. apply cexec_skip. auto.
- (* red seq step *)
  inversion H; subst. apply cexec_seq with s'0.
  eapply IHSTEP; eauto.
  auto.
- (* red_ifthenelse *)
  apply cexec_ifthenelse. auto.
- (* red_while_done *)
  inversion H0; subst. apply cexec_while_done. auto.
- (* red while loop *)
  inversion H0; subst. apply cexec_while_loop with s'0; auto.
Qed.

(** By induction on the reduction sequence, it follows that a command
    that reduces to [SKIP] executes according to the natural semantics,
    with the same final state. *)

Theorem reds_to_cexec:
  forall s c s',
  star red (c, s) (SKIP, s') -> cexec s c s'.
Proof.
  intros. dependent induction H.
- apply cexec_skip.
- destruct b as [c1 s1]. apply red_append_cexec with c1 s1; auto.
Qed.

(** ** 1.7.  Bounded interpreter *)

(** We found it impossible to define the semantics of commands as
    a Coq execution function.  However, we can define an approximation
    of such a function by bounding a priori the recursion depth,
    using an extra parameter [fuel] of type [nat].

    The "fuel" is decremented by 1 at each recursive call.  If it drops
    to 0, execution returns [None], meaning that the final state at
    the end of the command execution could not be determined:
    either the command diverges, or more fuel is needed to execute it. *)

Fixpoint cexec_f (fuel: nat) (s: store) (c: com) : option store :=
  match fuel with
  | O => None
  | S fuel' =>
      match c with
      | SKIP => Some s
      | ASSIGN x a => Some (update x (aeval a s) s)
      | SEQ c1 c2 =>
          match cexec_f fuel' s c1 with
          | None  => None
          | Some s' => cexec_f fuel' s' c2
          end
      | IFTHENELSE b c1 c2 =>
          cexec_f fuel' s (if beval b s then c1 else c2)
      | WHILE b c1 =>
          if beval b s then
            match cexec_f fuel' s c1 with
            | None  => None
            | Some s' => cexec_f fuel' s' (WHILE b c1)
            end
          else Some s
      end
  end.

(** This bounded execution function is very useful to compute the semantics
    of test programs.  For example, let's compute the quotient and the remainder
    of 14 divided by 3 using the IMP program for Euclidean division shown
    above. *)

Eval compute in
  (let s := update "a" 14 (update "b" 3 (fun _ => 0)) in
   match cexec_f 100 s Euclidean_division with
   | None => None
   | Some s' => Some (s' "q", s' "r")
   end).

(** *** Exercise (3 stars) *)

(** Show that function [cexec_f] is sound with respect to the natural semantics
    [cexec], by proving the two following lemmas. *)

Lemma cexec_f_sound:
  forall fuel s c s', cexec_f fuel s c = Some s' -> cexec s c s'.
Proof.
  induction fuel as [ | fuel ]; cbn; intros.
- discriminate.
- destruct c.
  (* FILL IN HERE *)
Abort.

Lemma cexec_f_complete:
  forall s c s', cexec s c s' ->
  exists fuel1, forall fuel, (fuel >= fuel1)%nat -> cexec_f fuel s c = Some s'.
Proof.
  induction 1.
  (* FILL IN HERE *)
Abort.

(** ** 1.8.  Transition semantics with continuations *)

(** To help with the verification of a compiler (module [Compil]),
    we now introduce another form of "small-step" semantics
    as an alternative to the reduction semantics.  In the new semantics,
    the command to be executed is explicitly decomposed into
    - a sub-command under focus, where computation takes place;
    - a context that describes the position of the sub-command in the
      whole command; or, equivalently, a continuation that describes
      the parts of the whole command that remain to execute once
      the sub-command terminates.

    Consequently, the semantics is presented as a transition relation
    between triples (sub-command under focus, continuation, state).

    Here is the syntax of continuations:
*)

Inductive cont : Type :=
  | Kstop
  | Kseq (c: com) (k: cont)
  | Kwhile (b: bexp) (c: com) (k: cont).

(** Intuitive meaning of these three constructors:
  - [Kstop] means that nothing remains to be done once the sub-command
    terminates.  In other words, the sub-command under focus is the whole
    command.
  - [Kseq c k] means that when the sub-command terminates, we will then
    execute the command [c], then continue as described by [k].
  - [Kwhile b c k] means that when the sub-command terminates, we will then
    execute the loop [WHILE b DO c END].  When this loop terminates,
    we will continue as described by [k].
*)

(** Another way to form intuitions about continuations is to ponder
    the [apply_cont k c] function below.  It takes the sub-command [c]
    and the continuation [k], and rebuilds the whole command.  This is
    achieved quite simpl by inserting [c] to the left of the nested
    [SEQ] constructors described by [k]. *)

Fixpoint apply_cont (k: cont) (c: com) : com :=
  match k with
  | Kstop => c
  | Kseq c1 k1 => apply_cont k1 (SEQ c c1)
  | Kwhile b1 c1 k1 => apply_cont k1 (SEQ c (WHILE b1 c1))
  end.

(** The transitions between triples (sub-command, continuation, state)
    can be classified in three groups:
    - Computation steps: evaluate an arithmetic or Boolean expression,
      and modify the triple accordingly.
    - Focusing: replace the sub-command by a sub-sub-command that must
      be executed first, enriching the continuation accordingly.
    - Resumption: when the sub-command under focus is [SKIP], and therefore
      has terminated, examine the head of the continuation to find
      the next sub-command to focus on.

    Here are the transition rules, annotated by the groups to which they
    belong.
*)

Inductive step: com * cont * store -> com * cont * store -> Prop :=

  | step_assign: forall x a k s,              (**r computation *)
      step (ASSIGN x a, k, s) (SKIP, k, update x (aeval a s) s)

  | step_seq: forall c1 c2 s k,               (**r focusing *)
      step (SEQ c1 c2, k, s) (c1, Kseq c2 k, s)

  | step_ifthenelse: forall b c1 c2 k s,      (**r computation *)
      step (IFTHENELSE b c1 c2, k, s) ((if beval b s then c1 else c2), k, s)

  | step_while_done: forall b c k s,          (**r computation *)
      beval b s = false ->
      step (WHILE b c, k, s) (SKIP, k, s)

  | step_while_loop: forall b c k s,          (**r computation + focusing *)
      beval b s = true ->
      step (WHILE b c, k, s) (c, Kwhile b c k, s)

  | step_skip_seq: forall c k s,              (**r resumption *)
      step (SKIP, Kseq c k, s) (c, k, s)

  | step_skip_while: forall b c k s,          (**r resumption *)
      step (SKIP, Kwhile b c k, s) (WHILE b c, k, s).

(** As with every small-step semantics, we define termination and
    divergence in terms of transition sequences.
    Initial states are of the shape [(c, Kstop, s_initial)]
    and final states [(SKIP, Kstop, s_final)].
*)

Definition kterminates (s: store) (c: com) (s': store) : Prop :=
  star step (c, Kstop, s) (SKIP, Kstop, s').

Definition kdiverges (s: store) (c: com) : Prop :=
  infseq step (c, Kstop, s).

(** *** Correspondence between continuation semantics and reduction semantics *)

(** To build confidence, we can prove that the two small-step semantics
    for IMP are equivalent: they agree on which commands terminate
    and which commands diverge.

    To prove this claim, we follow the approach based on simulation
    diagrams that we also use to prove the correctness of the IMP compiler
    (module [Compil]).  This proof is fairly technical and can be skipped
    on first reading.

    Here is the relation between a configuration of the continuation semantics
    and a configuration of the reduction semantics.
*)

Inductive match_conf : com * cont * store -> com * store -> Prop :=
  | match_conf_intro: forall c k s c',
      c' = apply_cont k c ->
      match_conf (c, k, s) (c', s).

(** We show that every transition of the continuation semantics
    is simulated by zero, one or several reduction steps.
    The anti-stuttering measure counts the nesting of [SEQ] constructs
    in the command. *)

Fixpoint num_seq (c: com) : nat :=
  match c with
  | SEQ c1 c2 => S (num_seq c1)
  | _ => O
  end.

Definition kmeasure (C: com * cont * store) : nat :=
  let '(c, k, s) := C in num_seq c.

Remark red_apply_cont:
  forall k c1 s1 c2 s2,
  red (c1, s1) (c2, s2) ->
  red (apply_cont k c1, s1) (apply_cont k c2, s2).
Proof.
  induction k; intros; simpl; eauto using red_seq_step.
Qed.

Lemma simulation_cont_red:
  forall C1 C1', step C1 C1' ->
  forall C2, match_conf C1 C2 ->
  exists C2',
     (plus red C2 C2' \/ (star red C2 C2' /\ kmeasure C1' < kmeasure C1))%nat
  /\ match_conf C1' C2'.
Proof.
  destruct 1; intros C2 MC; inversion MC; subst; cbn.
  2: econstructor; split; [right; split; [apply star_refl | lia] | constructor; auto ].
  1-6: econstructor; split; [left; apply plus_one; apply red_apply_cont; auto using red | constructor; auto].
Qed.

(** It follows that termination according to the continuation semantics
    implies termination according to the reduction semantics,
    and likewise for divergence. *)

Theorem kterminates_terminates:
  forall s c s', kterminates s c s' -> terminates s c s'.
Proof.
  intros.
  destruct (simulation_star _ _ _ _ _ _ simulation_cont_red _ _ H (c, s)) as ((c' & s'') & STAR & INV).
  constructor; auto.
  inversion INV; subst. apply STAR.
Qed.

Theorem kdiverges_diverges:
  forall s c, kdiverges s c ->  diverges s c.
Proof.
  intros.
  apply (simulation_infseq _ _ _ _ _ _ simulation_cont_red _ _ H).
  constructor; auto.
Qed.

(** The reverse implications follow from the symmetrical simulation diagram.
    First, we need a technical lemma on reductions of commands of the
    shape [apply_cont k c]. *)

Inductive red_apply_cont_cases: cont -> com -> store -> com -> store -> Prop :=
  | racc_base: forall c1 s1 c2 s2 k,
      red (c1, s1) (c2, s2) ->
      red_apply_cont_cases k c1 s1 (apply_cont k c2) s2
  | racc_skip_seq: forall c k s,
      red_apply_cont_cases (Kseq c k) SKIP s (apply_cont k c) s
  | racc_skip_while: forall b c k s,
      red_apply_cont_cases (Kwhile b c k) SKIP s (apply_cont k (WHILE b c)) s.

Lemma invert_red_apply_cont:
  forall k c s c' s',
  red (apply_cont k c, s) (c', s') ->
  red_apply_cont_cases k c s c' s'.
Proof.
  induction k; simpl; intros.
- (* Kstop *)
  change c' with (apply_cont Kstop c'). apply racc_base; auto.
- (* Kseq *)
  specialize (IHk _ _ _ _ H). inversion IHk; subst.
  + (* base *)
    inversion H0; clear H0; subst.
    * (* seq finish *)
      apply racc_skip_seq.
    * (* seq step *)
      change (apply_cont k (c4;;c)) with (apply_cont (Kseq c k) c4).
      apply racc_base; auto.
- (* Kwhile *)
  specialize (IHk _ _ _ _ H). inversion IHk; subst.
  inversion H0; clear H0; subst.
    * (* seq finish *)
      apply racc_skip_while.
    * (* seq step *)
      change (apply_cont k (c4;;WHILE b c)) with (apply_cont (Kwhile b c k) c4).
      apply racc_base; auto.
Qed.

Definition rmeasure (C: com * store) : nat := O.   (**r there is no stuttering *)

Lemma simulation_red_cont:
  forall C1 C1', red C1 C1' ->
  forall C2, match_conf C2 C1 ->
  exists C2',
     (plus step C2 C2' \/ (star step C2 C2' /\ rmeasure C1' < rmeasure C1))%nat
  /\ match_conf C2' C1'.
Proof.
  intros C1 C1' R C2 MC. inversion MC; subst. destruct C1' as (c' & s').
  assert (A: red_apply_cont_cases k c s c' s') by (apply invert_red_apply_cont; auto).
  clear MC R. inversion A; subst; clear A.
- cut (exists C2', plus step (c, k, s) C2' /\ match_conf C2' (apply_cont k c2, s')).
  intros (C2' & A & B). exists C2'; auto.
  revert k. dependent induction H; intros.
  + econstructor; split. apply plus_one; constructor. constructor; auto.
  + econstructor; split.
    eapply plus_left. constructor. eapply star_one. constructor.
    constructor; auto.
  + edestruct IHred as (((cx & kx) & sx) & A & B); eauto.
    econstructor; split.
    eapply plus_left. constructor. apply plus_star. eexact A.
    exact B.
  + econstructor; split. apply plus_one; constructor. constructor; auto.
  + econstructor; split. apply plus_one; apply step_while_done; auto. constructor; auto.
  + econstructor; split. apply plus_one; apply step_while_loop; auto. constructor; auto.
- econstructor; split.
  left; apply plus_one; constructor.
  constructor; auto.
- econstructor; split.
  left; apply plus_one; constructor.
  constructor; auto.
Qed.

Lemma apply_cont_is_skip:
  forall k c, apply_cont k c = SKIP -> k = Kstop /\ c = SKIP.
Proof.
  induction k; cbn; intros.
- auto.
- apply IHk in H. intuition discriminate.
- apply IHk in H. intuition discriminate.
Qed.

Theorem terminates_kterminates:
  forall s c s', terminates s c s' -> kterminates s c s'.
Proof.
  intros.
  destruct (simulation_star _ _ _ _ _ _ simulation_red_cont _ _ H (c, Kstop, s)) as ((c' & s'') & STAR & INV).
  constructor; auto.
  inversion INV; subst.
  edestruct apply_cont_is_skip; eauto. subst k c0. apply STAR.
Qed.

Theorem diverges_kdiverges:
  forall s c, diverges s c ->  kdiverges s c.
Proof.
  intros.
  apply (simulation_infseq _ _ _ _ _ _ simulation_red_cont _ _ H).
  constructor; auto.
Qed.
