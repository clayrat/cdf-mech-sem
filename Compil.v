From Equations Require Import Equations.
From Coq Require Import ssreflect ssrfun ssrbool String.
From mathcomp Require Import ssrnat ssrint ssralg ssrnum ssrAC eqtype order seq.
From CDF Require Import Sequences IMP Simulation.

Import GRing.Theory.
Local Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(** * 2. Compiling IMP to a stack machine *)

(** ** 2.1.  The target language: a stack machine pile *)

(** Our compiler will translate IMP to the language of a simple stack
    machine.  The stack contains numbers and the machine instructions
    pop their arguments off the stack and push their results back.
    This machine is similar to the "Reverse Polish Notation"
    used by old HP pocket calculators.  It is also close to a subset
    of the JVM, the Java virtual machine. *)

(** *** 2.1.1.  Instruction set *)

(** Here is the instruction set of the machine: *)

Inductive instr : Type :=
  | Iconst (n: int)           (**r push the integer [n] *)
  | Ivar (x: ident)           (**r push the current value of variable [x] *)
  | Isetvar (x: ident)        (**r pop an integer and assign it to variable [x] *)
  | Iadd                      (**r pop two integers, push their sum *)
  | Iopp                      (**r pop one integer, push its opposite *)
  | Ibranch (d: int)          (**r skip forward or backward [d] instructions *)
  | Ibeq (d1: int) (d0: int)  (**r pop two integers, skip [d1] instructions if equal, [d0] if not equal *)
  | Ible (d1: int) (d0: int)  (**r pop two integer, skip [d1] instructions if less or equal, [d0] if greater *)
  | Ihalt.                    (**r stop execution *)

(** A piece of machine code is a list of instructions. *)

Definition code := seq instr.

(** The length (number of instructions) of a piece of code. *)

Definition codelen (c: code) : int := size c.

(** *** 2.1.2.  Operational semantics *)

(** The machine operates on a code [C] (a fixed list of instructions)
    and three variable components:
  - a program counter [pc], denoting a position in [C]
  - an evaluation stack, containing integers
  - a store assigning integer values to variables.
*)

Definition stack : Type := seq int.

Definition config : Type := (int * stack * store)%type.

(** [instr_at C pc = Some i] if [i] is the instruction at position [pc] in [C]. *)

Fixpoint instr_at (C: code) (pc: int) : option instr :=
  if C is i :: C'
    then if pc == 0 then Some i else instr_at C' (pc - 1)
    else None.

(** The semantics of the machine is given in small-step style as a
    transition system: a relation between machine configurations
    "before" and "after" execution of the instruction at the current
    program point.  The transition relation is parameterized by the code
    [C] for the whole program.  There is one transition for each kind of
    instruction, except [Ihalt], which has no transition. *)

Inductive transition (C: code): config -> config -> Prop :=
  | trans_const: forall pc σ s n,
      instr_at C pc = Some(Iconst n) ->
      transition C (pc    , σ     , s)
                   (pc + 1, n :: σ, s)
  | trans_var: forall pc σ s x,
      instr_at C pc = Some(Ivar x) ->
      transition C (pc    , σ       , s)
                   (pc + 1, s x :: σ, s)
  | trans_setvar: forall pc σ s x n,
      instr_at C pc = Some(Isetvar x) ->
      transition C (pc    , n :: σ, s)
                   (pc + 1, σ     , update x n s)
  | trans_add: forall pc σ s n1 n2,
      instr_at C pc = Some(Iadd) ->
      transition C (pc    , n2 :: n1 :: σ , s)
                   (pc + 1, (n1 + n2) :: σ, s)
  | trans_opp: forall pc σ s n,
      instr_at C pc = Some(Iopp) ->
      transition C (pc    , n :: σ    , s)
                   (pc + 1, (- n) :: σ, s)
  | trans_branch: forall pc σ s d pc',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , σ, s)
                   (pc', σ, s)
  | trans_beq: forall pc σ s d1 d0 n1 n2 pc',
      instr_at C pc = Some(Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 == n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: σ, s)
                   (pc', σ            , s)
  | trans_ble: forall pc σ s d1 d0 n1 n2 pc',
      instr_at C pc = Some(Ible d1 d0) ->
      pc' = pc + 1 + (if n1 <= n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: σ, s)
                   (pc', σ            , s).

(** As we did for the IMP reduction semantics, we form sequences of
    machine transitions to define the behavior of a code. *)

Definition transitions (C: code): config -> config -> Prop :=
  star (transition C).

(** Execution starts with [pc = 0] and an empty evaluation stack.
    It stops successfully if [pc] points to an [Ihalt] instruction
    and the evaluation stack is empty. *)

Definition machine_terminates (C: code) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, [::], s_init) (pc, [::], s_final)
          /\ instr_at C pc = Some Ihalt.

(** The machine can also run forever, making infinitely many transitions. *)

Definition machine_diverges (C: code) (s_init: store) : Prop :=
  infseq (transition C) (0, [::], s_init).

(** Yet another possibility is that the machine gets stuck after some
    transitions. *)

Definition machine_goes_wrong (C: code) (s_init: store) : Prop :=
  exists pc σ s,
      transitions C (0, [::], s_init) (pc, σ, s)
   /\ irred (transition C) (pc, σ, s)
   /\ (instr_at C pc <> Some Ihalt \/ σ <> [::]).

(** *** Exercise (2 stars). *)

(** To quickly see how a machine program executes, it is convenient
    to redefine the semantics of the machine as an executable function
    instead of inductively-defined relations.  This is similar to the
    [cinterp] function for the IMP language.

    To ensure termination of the machine interpreter, we need to bound
    the number of instructions it can execute.  The result of the
    machine interpreter, therefore, is of the following type:
*)

Inductive machine_result : Type :=
  | Timeout                (**r the interpreter ran out of fuel *)
  | Stuck                  (**r the machine goes wrong on an impossible case *)
  | Terminates (s: store). (**r the machine successfully stops with the given store *)

(** Please fill in the blanks in the following definition for a
    machine interpreter: *)

Fixpoint mach_exec (C: code) (fuel: nat)
                   (pc: int) (σ: stack) (s: store) : machine_result :=
  match fuel with
  | O => Timeout
  | S fuel' =>
      match instr_at C pc, σ with
      | Some Ihalt, [::] => Terminates s
      | Some (Iconst n), σ => mach_exec C fuel' (pc + 1) (n :: σ) s
      (* FILL IN HERE *)
      | Some (Ivar x), σ => mach_exec C fuel' (pc + 1) (s x :: σ) s
      | Some (Isetvar x), n :: σ => mach_exec C fuel' (pc + 1) σ (update x n s)
      | Some Iadd, n2 :: n1 :: σ => mach_exec C fuel' (pc + 1) ((n1 + n2) :: σ) s
      | Some Iopp, n :: σ => mach_exec C fuel' (pc + 1) ((-n) :: σ) s
      | Some (Ibranch d), σ => mach_exec C fuel' (pc + 1 + d) σ s
      | Some (Ibeq d1 d0), n2 :: n1 :: σ => mach_exec C fuel' (pc + 1 + (if n1 == n2 then d1 else d0)) σ s
      | Some (Ible d1 d0), n2 :: n1 :: σ => mach_exec C fuel' (pc + 1 + (if n1 <= n2 then d1 else d0)) σ s
      | _, _ => Stuck
      end
  end.

(** ** 2.2. The compilation scheme *)

(** We now define the compilation of IMP expressions and commands to
    sequence of machine instructions. *)

(** The code for an arithmetic expression [a] executes in sequence
    (no branches), and deposits the value of [a] at the top of the stack.
    This is the familiar translation to "reverse Polish notation".  The
    only twist here is that the machine has no "subtract" instruction.
    However, it can compute the difference [a - b] by adding [a] to the
    opposite of [b].  *)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | CONST n => [:: Iconst n]
  | VAR x => [:: Ivar x]
  | PLUS a1 a2  => compile_aexp a1 ++ compile_aexp a2 ++ [::Iadd]
  | MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [::Iopp; Iadd]
  end.

(** Examples of compiled code. *)

Eval compute in (compile_aexp (PLUS (CONST 1) (CONST 2))).

(** Result: [:: Iconst 1%Z; Iconst 2%Z; Iadd] *)

Eval compute in (compile_aexp (PLUS (VAR "x") (MINUS (VAR "y") (CONST 1)))).

(** Result: [:: Ivar "x"; Ivar "y"; Iconst 1%Z; Iopp; Iadd; Iadd]. *)

(** For Boolean expressions [b], we could produce code that deposits [1] or [0]
    at the top of the stack, depending on whether [b] is true or false.
    The compiled code for [IFTHENELSE] and [WHILE] commands would, then,
    perform an [Ibeq] jump conditional on this 0/1 value.

    However, it is simpler and more efficient to compile a Boolean
    expression [b] to a piece of code that directly jumps [d1] or [d0]
    instructions forward, depending on whether [b] is true or false.
    The actual value of [b] is never computed as an integer, and the
    stack is unchanged.
*)

Fixpoint compile_bexp (b: bexp) (d1: int) (d0: int) : code :=
  match b with
  | TRUE => if d1 == 0 then [::] else [::Ibranch d1]
  | FALSE => if d0 == 0 then [::] else [::Ibranch d0]
  | EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [::Ibeq d1 d0]
  | LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ [::Ible d1 d0]
  | NOT b1 => compile_bexp b1 d0 d1
  | AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0 in
      let code1 := compile_bexp b1 0 (codelen code2 + d0) in
      code1 ++ code2
  end.

(** See the lecture slides for an explanation of the mysterious
    offsets in the [AND] case. *)

(** Examples are in order. *)

Eval compute in (compile_bexp (EQUAL (VAR "x") (CONST 1)) 12 34).

(** Result: [:: Ivar "x"; Iconst 1%Z; Ibeq 12%Z 34%Z]. *)

Eval compute in (compile_bexp (AND (LESSEQUAL (CONST 1) (VAR "x"))
                                   (LESSEQUAL (VAR "x") (CONST 10))) 0 10).

(** Result: [:: Iconst 1%Z; Ivar "x"; Ible 0%Z 13%Z; Ivar "x";
                Iconst 10%Z; Ible 0%Z 10%Z] *)

Eval compute in (compile_bexp (OR (LESSEQUAL (CONST 1) (VAR "x"))
                                  (LESSEQUAL (VAR "x") (CONST 10))) 0 10).

(** Result: [:: Iconst 1%Z; Ivar "x"; Ible 3%Z 0%Z; Ivar "x";
                Iconst 10%Z; Ible 0%Z 10%Z] *)

Eval compute in (compile_bexp (NOT (AND TRUE FALSE)) 12 34).

(** Result: [:: Ibranch 12%Z] *)

(** Finally, here is the compilation of commands.  The code for a
    command [c] updates the store (the values of variables) as prescribed
    by [c].  It leaves the stack unchanged.

    Again, see the lecture slides for explanations of the generated
    branch offsets.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      [::]
  | ASSIGN x a =>
      compile_aexp a ++ [:: Isetvar x]
  | SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ Ibranch (codelen code_ifnot)
      :: code_ifnot
  | WHILE b body =>
      let code_body := compile_com body in
      let code_test := compile_bexp b 0 (codelen code_body + 1) in
      code_test
      ++ code_body
      ++ [:: Ibranch (- (codelen code_test + codelen code_body + 1))]
  end.

(** The code for a whole program [p] (a command) is similar, but terminates
    cleanly on an [Ihalt] instruction. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ [:: Ihalt].

(** Examples of compilation: *)

Eval compute in (compile_program (ASSIGN "x" (PLUS (VAR "x") (CONST 1)))).

(** Result: [:: Ivar "x"; Iconst 1%Z; Iadd; Isetvar "x"; Ihalt] *)

Eval compute in (compile_program (WHILE TRUE SKIP)).

(** Result: [:: Ibranch (-1)%Z; Ihalt]. *)

Eval compute in (compile_program (IFTHENELSE (EQUAL (VAR "x") (CONST 1)) (ASSIGN "x" (CONST 0)) SKIP)).

(** Result: [:: Ivar "x"; Iconst 1%Z; Ibeq 0%Z 3%Z; Iconst 0%Z;
                Isetvar "x"; Ibranch 0%Z; Ihalt]. *)

(** *** Exercise (1 star) *)

(** The last example shows a slight inefficiency in the code generated for
    [IFTHENELSE b c SKIP].  How would you change [compile_com]
    to generate better code?  Hint: the following function could be useful. *)

Definition smart_Ibranch (d: int) : code :=
  if d == 0 then [::] else [:: Ibranch d].

(** ** 2.3.  Correctness of the compiled code for expressions *)

(** To reason about the execution of compiled code, we need to consider
    code sequences [C2] that are at position [pc] in a bigger code
    sequence [C = C1 ++ C2 ++ C3].  The following predicate
    [code_at C pc C2] does just this. *)

Inductive code_at: code -> int -> code -> Prop :=
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2.

(** We show a number of useful lemmas about [instr_at] and [code_at]. *)

Lemma codelen_cons i c : codelen (i :: c) = codelen c + 1.
Proof.
by rewrite /codelen /= -addn1.
Qed.

Lemma codelen_app c1 c2 :
  codelen (c1 ++ c2) = codelen c1 + codelen c2.
Proof.
elim: c1=>//= c c1 IH.
by rewrite !codelen_cons IH addrAC.
Qed.

Lemma instr_at_app i c2 c1 pc :
  pc = codelen c1 ->
  instr_at (c1 ++ i :: c2) pc = Some i.
Proof.
elim: c1 pc=>/= [|a c1 IH] pc -> //=.
rewrite codelen_cons -addrA subrr addr0.
by apply: IH.
Qed.

Lemma code_at_head C pc i C' :
  code_at C pc (i :: C') ->
  instr_at C pc = Some i.
Proof.
move=>H; case E: _ / H; rewrite -E /=.
by apply: instr_at_app.
Qed.

Lemma code_at_tail C pc i C' :
  code_at C pc (i :: C') ->
  code_at C (pc + 1) C'.
Proof.
move=>H; case E: _ / H => [C1 C2 C3 _ ->].
rewrite -{C2}E /= -cat1s catA; apply: code_at_intro.
by rewrite codelen_app.
Qed.

Lemma code_at_app_left C pc C1 C2 :
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1.
Proof.
move=>H; case E: _ / H => [C3 C4 C5 {}pc E'].
by rewrite -{C4}E -catA; apply: code_at_intro.
Qed.

Lemma code_at_app_right C pc C1 C2 :
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2.
Proof.
move=>H; case E: _ / H => [C3 C4 C5 _ ->].
rewrite -{C4}E -catA catA; apply: code_at_intro.
by rewrite codelen_app.
Qed.

Lemma code_at_app_right2 C pc C1 C2 C3 :
  code_at C pc (C1 ++ C2 ++ C3) ->
  code_at C (pc + codelen C1) C2.
Proof.
move=>H; case E: _ / H => [C4 C5 C6 {}pc E'].
apply/code_at_app_right/(@code_at_app_left _ _ _ C3).
by rewrite -catA -{C5}E.
Qed.

Lemma code_at_nil C pc C1 :
  code_at C pc C1 -> code_at C pc [::].
Proof.
case=>{}C {}C1 C2 _ ->.
by rewrite (_ : C1 ++ C2 = [::] ++ (C1 ++ C2)).
Qed.

Lemma instr_at_code_at_nil C pc i :
  instr_at C pc = Some i -> code_at C pc [::].
Proof.
elim: C pc=>//= a C IH pc.
case: eqP=>[->|Hn].
- case=>{a}->.
  by rewrite (_ : i :: C = [::] ++ [::] ++ (i :: C)).
move/IH=>H; case: {1}_ {1}_ {1}_ / H (@erefl _ (pc - 1)) (@erefl code nil)=>C1 _ C2 _ -> E ->.
rewrite -cat_cons; apply: code_at_intro.
by rewrite codelen_cons E -addrA subrr addr0.
Qed.

(** We put these lemmas in a "hint database" so that Coq can use them
    automatically. *)

#[global] Hint Resolve code_at_head code_at_tail code_at_app_left code_at_app_right
                       code_at_app_right2 code_at_nil instr_at_code_at_nil : code.
#[global] Hint Rewrite codelen_app codelen_cons addrA addr0 : code.

(** Remember the informal specification we gave for the code generated
    for an arithmetic expression [a].  It should
  - execute in sequence (no branches)
  - deposit the value of [a] at the top of the stack
  - preserve the variable state.

    We now prove that the code [compile_aexp a] fulfills this contract.
    The proof is a nice induction on the structure of [a]. *)

Lemma compile_aexp_correct C s a pc σ :
  code_at C pc (compile_aexp a) ->
  transitions C
       (pc, σ, s)
       (pc + codelen (compile_aexp a), aeval a s :: σ, s).
Proof.
elim: a pc σ=>/= [n|x|a1 IH1 a2 IH2|a1 IH1 a2 IH2] pc σ H.
- (* CONST *)
  by apply/star_one/trans_const; eauto with code.
- (* VAR *)
  by apply/star_one/trans_var; eauto with code.
- (* PLUS *)
  apply: star_trans; first by apply IH1; eauto with code.
  apply: star_trans; first by apply: IH2; eauto with code.
  apply: star_one; autorewrite with code.
  by apply: trans_add; eauto with code.
(* MINUS *)
apply: star_trans; first by apply IH1; eauto with code.
apply: star_trans; first by apply: IH2; eauto with code.
apply: star_trans.
- by apply/star_one/trans_opp; eauto with code.
by apply: star_one; autorewrite with code; apply: trans_add; eauto with code.
Qed.

(** The proof for the compilation of Boolean expressions is similar.
    We recall the informal specification for the code generated by
    [compile_bexp b d1 d0]: it should
  - skip [d1] instructions if [b] evaluates to true,
         [d0] if [b] evaluates to false
  - leave the stack unchanged
  - leave the store unchanged.
*)

Lemma compile_bexp_correct C s b d1 d0 pc σ :
  code_at C pc (compile_bexp b d1 d0) ->
  transitions C
       (pc, σ, s)
       (pc + codelen (compile_bexp b d1 d0) + (if beval b s then d1 else d0), σ, s).
Proof.
elim: b d1 d0 pc=>/=.
- (* TRUE *)
  move=>d1 _ pc; case: eqP=>[->|Hn].
  - (* zero displacement: no instruction generated *)
    by move=>_; autorewrite with code; apply: star_refl.
  - (* a branch is generated *)
    move=>H; apply: star_one.
    by apply: (@trans_branch _ _ _ _ d1); eauto with code.
- (* FALSE *)
  move=>_ d0 pc; case: eqP=>[->|Hn].
  + (* zero displacement: no instruction generated *)
    by move=>_; autorewrite with code; apply: star_refl.
  + (* a branch is generated *)
    move=>H; apply: star_one.
    by apply: (@trans_branch _ _ _ _ d0); eauto with code.
- (* EQUAL *)
  move=>a1 a2 d1 d0 pc H.
  apply: star_trans; first by apply: (@compile_aexp_correct _ _ a1); eauto with code.
  apply: star_trans; first by apply: (@compile_aexp_correct _ _ a2); eauto with code.
  apply: star_one; apply: (@trans_beq _ _ _ _ d1 d0); first by eauto with code.
  by autorewrite with code.
- (* LESSEQUAL *)
  move=>a1 a2 d1 d0 pc H.
  apply: star_trans; first by apply: (@compile_aexp_correct _ _ a1); eauto with code.
  apply: star_trans; first by apply: (@compile_aexp_correct _ _ a2); eauto with code.
  apply: star_one; apply: (@trans_ble _ _ _ _ d1 d0); first by eauto with code.
  by autorewrite with code.
- (* NOT *)
  by move=>b + d1 d0; case: (beval b s)=>/=; apply.
(* AND *)
move=>b1 IH1 b2 IH2 d1 d0 pc H.
apply: star_trans; first by apply: IH1; eauto with code.
set code2 := compile_bexp b2 d1 d0 in H *.
set code1 := compile_bexp b1 0 (codelen code2 + d0) in H *.
case: (beval b1 s)=>/=.
- (* b1 evaluates to true, the code for b2 is executed *)
  by autorewrite with code; apply: IH2; eauto with code.
(* b1 evaluates to false, the code for b2 is skipped *)
by autorewrite with code; apply: star_refl.
Qed.

(** ** 2.4.  Correctness of generated code for terminating commands *)

(** Assume that command [c], started in state [s], terminates in state [s'].
    We then show that the machine, started at the beginning of the code
    [compile_com c] and with initial state [s], performs finitely many
    transitions and reaches the end of the code [compile_com c]
    with state [s'].

    To characterize the termination of command [c], we use IMP's natural
    semantics, with its predicate [exec s c s'].
    The proof is a simple induction over the derivation of this
    [exec s c s'] execution.  An induction on the structure of command [c]
    would not suffice in the case of loops.
*)

Lemma compile_com_correct_terminating s c s' :
  cexec s c s' ->
  forall C pc σ,
  code_at C pc (compile_com c) ->
  transitions C
      (pc, σ, s)
      (pc + codelen (compile_com c), σ, s').
Proof.
elim=>/=.
- (* SKIP *)
  move=>s1 C pc σ H.
  by autorewrite with code; apply: star_refl.
- (* ASSIGN *)
  move=>s1 x a C pc σ H.
  apply: star_trans; first by apply: (@compile_aexp_correct _ _ a); eauto with code.
  apply: star_one; autorewrite with code.
  by apply: trans_setvar; eauto with code.
- (* SEQUENCE *)
  move=>c1 c2 s1 s2 s3 H1 IH1 H2 IH2 C pc σ H.
  apply: star_trans; first by apply IH1; eauto with code.
  by autorewrite with code; apply: IH2; eauto with code.
- (* IFTHENELSE *)
  move=>b c1 c2 s1 s2 H IH C pc σ.
  set code1 := compile_com c1.
  set code2 := compile_com c2.
  set codeb := compile_bexp b 0 (codelen code1 + 1).
  move=>H2; apply: star_trans.
  - by apply: (@compile_bexp_correct _ _ b); eauto with code.
  rewrite -/codeb; case: (beval b s1) in IH *; autorewrite with code.
  - (* the "then" branch is executed *)
    apply: star_trans; first by apply: IH; eauto with code.
    rewrite -/code1; apply: star_one.
    apply: (@trans_branch _ _ _ _ (codelen code2)); first by eauto with code.
    by rewrite addrAC.
  (* the "else" branch is executed *)
  rewrite [X in star _ _ ((X, _), _)]addrAC.
  by apply: IH; eauto with code.
- (* WHILE stop *)
  move=>b c1 s1 Hb C pc σ.
  set code_body := compile_com c1.
  set code_branch := compile_bexp b 0 (codelen code_body + 1).
  set d := - (codelen code_branch + codelen code_body + 1).
  move=>H; apply: star_trans.
  - by apply: (@compile_bexp_correct _ _ b); eauto with code.
  rewrite (negbTE Hb) -/code_branch; autorewrite with code.
  by apply: star_refl.
(* WHILE loop *)
move=>b c1 s1 s2 s3 Hb H1.
set code_body := compile_com c1.
move=>IH1 H2.
set code_branch := compile_bexp b 0 (codelen code_body + 1).
set d := - (codelen code_branch + codelen code_body + 1).
move=>IH2 C pc σ H.
apply: star_trans.
- by apply: (@compile_bexp_correct _ _ b); eauto with code.
rewrite Hb -/code_branch; autorewrite with code.
apply: star_trans; first by apply: IH1; eauto with code.
apply: star_trans.
- apply: star_one.
  by apply: (@trans_branch _ _ _ _ d); first by eauto with code.
rewrite [X in star _ ((X, _), _) _](ACl (1*(2*3*4*5))%AC) /= subrr addr0.
rewrite (_ : pc + codelen code_branch + codelen code_body + 1 =
             pc + codelen (compile_com (WHILE b c1))); last first.
- by rewrite /=; autorewrite with code.
by apply: IH2.
Qed.

(** As a corollary, we obtain the correctness of the compiled code for
    a whole program [p], in the case where the execution of [p] terminates. *)

Corollary compile_program_correct_terminating s c s' :
  cexec s c s' ->
  machine_terminates (compile_program c) s s'.
Proof.
move=>H; set C := compile_program c.
have CODEAT: code_at C 0 (compile_com c ++ Ihalt :: [::]).
- rewrite (_ : C = [::] ++ compile_program c ++ [::]) //.
  by rewrite cats0.
rewrite /machine_terminates.
exists (0 + codelen (compile_com c)); split.
- by apply: compile_com_correct_terminating=>//; eauto with code.
by eauto with code.
Qed.

(** *** Exercise (2 stars) *)

(** In a previous exercise, we modified [compile_com] to use
    [smart_Ibranch] instead of [Ibranch], producing more efficient code.
    Now, please update the proof of [compile_com_correct_terminating]
    to take this modification into account.
    Hint: first, show the following lemma. *)

Lemma transitions_smart_Ibranch:
  forall C pc d pc' σ s,
  code_at C pc (smart_Ibranch d) ->
  pc' = pc + codelen (smart_Ibranch d) + d ->
  transitions C (pc, σ, s) (pc', σ, s).
Proof.
  unfold smart_Ibranch; intros.
  (* FILL IN HERE *)
Abort.

(** *** Exercise (4 stars). *)

(** Consider a loop with a simple test, such as [WHILE (LESSEQUAL a1 a2) c].
    Currently, the compiled code executes two branch instructions per
    iteration of the loop: one [Ible] to test the condition and one
    [Ibranch] to go back to the beginning of the loop.  We can reduce
    this to one [Ible] instruction per iteration, by putting the code
    for [c] before the code for the test:
<<
     compile_com c ++ compile_bexp b delta1 0
>>
    with [delta1] chosen so as to branch back to the beginning of
    [compile_com c] when [b] is true.

    By itself, this would compile while loops like do-while loops, which is
    incorrect.  On the first iteration, we must skip over the code for [c]
    and branch to the code that tests [b]:
<<
    Ibranch (codesize(compile_com c)) :: compile_com c ++ compile_bexp b delta1 0
>>
    In this exercise, you should modify [compile_com] to implement this
    alternate compilation schema for loops, then show its correctness
    by updating the statement and proof of [compile_com_correct_terminating].
    The difficulty (and the reason for the 4 stars) is that the hypothesis
    [code_at C pc (compile_com c)] no longer holds if [c] is a while loop
    and we are at the second iteration of the loop.  You need to come up
    with a more flexible way to relate the command [c] and the PC.
*)

(** ** 2.5.  Correctness of generated code for commands, general case *)

(** We would like to strengthen the correctness result above so that it
    is not restricted to terminating source programs, but also applies
    to source program that diverge.  To this end, we abandon the
    big-step semantics for commands and switch to the small-step
    semantics with continuations.  We then show a simulation theorem,
    establishing that every transition of the small-step semantics in
    the source program is simulated (in a sense to be made precise
    below) by zero, one or several transitions of the machine executing
    the compiled code for the source program. *)

(** Our first task is to relate configurations [(c, k, s)] of the small-step
    semantics with configurations [(C, pc, σ, s)] of the machine.
    We already know how to relate a command [c] with the machine code,
    using the [codeseq_at] predicate.  What needs to be defined is a relation
    between the continuation [k] and the machine code.

    Intuitively, when the machine finishes executing the generated code for
    command [c], that is, when it reaches the program point
    [pc + length(compile_com c)], the machine should continue by executing
    instructions that perform the pending computations described by
    continuation [k], then reach an [Ihalt] instruction to stop cleanly.

    We formalize this intuition by the following inductive predicate
    [compile_cont C k pc], which states that, starting at program point [pc],
    there are instructions that perform the computations described in [k]
    and reach an [Ihalt] instruction. *)

Inductive compile_cont (C: code): cont -> int -> Prop :=
  | ccont_stop: forall pc,
      instr_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc d pc' pc'',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall d k pc pc',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc.

Derive Signature for compile_cont.

(** Then, a configuration [(c, k, s)] of the small-step semantics
    matches a configuration [(C, pc, σ, s')] of the machine if the
    following conditions hold:
  - The stores are identical: [s' = s].
  - The machine stack is empty: [σ = [::]].
  - The machine code at point [pc] is the compiled code for [c]:
    [code_at C pc (compile_com c)].
  - The machine code at point [pc + codelen (compile_com c)] matches
    continuation [k], in the sense of [compile_cont] above.
*)

Inductive match_config (C: code): com * cont * store -> config -> Prop :=
  | match_config_intro: forall c k st pc,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st) (pc, [::], st).

(** We are now ready to prove the expected simulation property.
    Since some transitions in the source command correspond to zero
    transitions in the compiled code, we need a simulation diagram of
    the "star" kind (see the lecture slides).
<<
                      match_config
     c / k / st  ----------------------- machconfig
       |                                   |
       |                                   | + or ( * and |c',k'| < |c,k} )
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machconfig'
                      match_config
>>
    Note the stronger conclusion on the right:
  - either the virtual machine does one or several transitions
  - or it does zero, one or several transitions, but the size of the [c,k]
    pair decreases strictly.

    It would be equivalent to state:
  - either the virtual machine does one or several transitions
  - or it does zero transitions, but the size of the [c,k] pair
    decreases strictly.

    However, the formulation above, with the "star" case, is often
    more convenient.
*)

(** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
    After trial and error, we find that the following measure works.
    It is the sum of the sizes of the command [c] under focus and all
    the commands appearing in the continuation [k]. *)

Fixpoint com_size (c: com) : nat :=
  match c with
  | SKIP => 1%nat
  | ASSIGN x a => 1%nat
  | SEQ c1 c2 => (com_size c1 + com_size c2 + 1)%nat
  | IFTHENELSE b c1 c2 => (com_size c1 + com_size c2 + 1)%nat
  | WHILE b c1 => (com_size c1 + 1)%nat
  end.

Remark com_size_nonzero  c : (com_size c > 0)%N.
Proof.
elim: c=>//= [c1 _ c2 _|_ c1 _ c2 _|_ c1 _];
by apply: ltn_addl.
Qed.

Fixpoint cont_size (k: cont) : nat :=
  match k with
  | Kstop => 0%N
  | Kseq c k' => (com_size c + cont_size k')%N
  | Kwhile b c k' => cont_size k'
  end.

Definition measure (impconf: com * cont * store) : nat :=
  let: (c, k, _) := impconf in (com_size c + cont_size k)%N.

(** We will need some inversion lemmas for the [compile_cont] predicate. *)

Lemma compile_cont_Kstop_inv C pc s :
  compile_cont C Kstop pc ->
  exists pc',
  star (transition C) (pc, [::], s) (pc', [::], s)
  /\ instr_at C pc' = Some Ihalt.
Proof.
move=>H; depind H=>//.
- by exists pc; split=>//; apply: star_refl.
case: (IHcompile_cont s)=>pc'' [A B]; exists pc''; split=>//.
apply: (@star_step _ _ _ _ _ _ A).
by apply: (trans_branch _ _ _ _ _ _ H).
Qed.

Lemma compile_cont_Kseq_inv C c k pc s :
  compile_cont C (Kseq c k) pc ->
  exists pc',
  [/\ star (transition C) (pc, [::], s) (pc', [::], s),
      code_at C pc' (compile_com c) &
      compile_cont C k (pc' + codelen(compile_com c))].
Proof.
move=>H; depind H=>//.
- case: H2=>{c0}->{k0}->.
  exists pc; do!split=>//; first by apply star_refl.
  by rewrite -H0.
case: (IHcompile_cont s)=>pc'' [A B].
exists pc''; split=>//.
apply: (@star_step _ _ _ _ _ _ A).
by apply: (@trans_branch _ _ _ _ _ _ H).
Qed.

Lemma compile_cont_Kwhile_inv C b c k pc s :
  compile_cont C (Kwhile b c k) pc ->
  exists pc',
  [/\ plus (transition C) (pc, [::], s) (pc', [::], s),
      code_at C pc' (compile_com (WHILE b c)) &
      compile_cont C k (pc' + codelen(compile_com (WHILE b c)))].
Proof.
move=>H; depind H=>//.
- case: H4=>{b0}->{c0}->{k0}->.
  exists (pc + 1 + d); rewrite -H0 -H2; split=>//.
  by apply/plus_one/(trans_branch _ _ _ _ _ _ H H0).
case: (IHcompile_cont s)=>pc'' [A B D].
exists pc''; do!split=>//.
apply: plus_left; first by apply: (trans_branch _ _ _ _ _ _ H H0).
by apply: plus_star.
Qed.

Lemma match_config_skip C k s pc :
  compile_cont C k pc ->
  match_config C (SKIP, k, s) (pc, [::], s).
Proof.
move=>H; constructor=>/=.
- by case: H; eauto with code.
by autorewrite with code.
Qed.

(** At last, we can state and prove the simulation diagram. *)

Lemma simulation_step C impconf1 impconf2 :
  step impconf1 impconf2 ->
  forall machconf1, match_config C impconf1 machconf1 ->
  exists machconf2,
      (plus (transition C) machconf1 machconf2
       \/ (star (transition C) machconf1 machconf2
           /\ (measure impconf2 < measure impconf1)%N))
   /\ match_config C impconf2 machconf2.
Proof.
case=>[x a k s|c1 c2 s k|b c1 c2 k s|b c k s Hb|b c k s Hb|c k s|b c k s] mc1 M.
- (* assign *)
  case: {1}_ _ / M (@erefl _ (ASSIGN x a, k, s))=>c1 k1 _ pc H H2 [E1 E2 ->];
  rewrite {c1}E1 {k1}E2 /= in H H2.
  exists (pc + codelen (compile_aexp a) + 1, [::], update x (aeval a s) s); split.
  - left; apply: plus_right; first by apply: compile_aexp_correct; eauto with code.
    apply: trans_setvar; eauto with code.
  by autorewrite with code in H2; apply: match_config_skip.
- (* seq *)
  case: {1}_ _ / M (@erefl _ (c1;;c2, k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
  rewrite {c3}E1 {k1}E2 /= in H H2.
  exists (pc, [::], s); split=>/=.
  - right; split; first by apply: star_refl.
    by rewrite addnAC addnA addn1.
  autorewrite with code in H2; constructor; eauto with code.
  by apply: ccont_seq; eauto with code.
- (* if *)
  case: {1}_ _ / M (@erefl _ (IFTHENELSE b c1 c2, k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
  rewrite {c3}E1 {k1}E2 /= in H H2.
  set code1 := compile_com c1 in H H2.
  set codeb := compile_bexp b 0 (codelen code1 + 1) in H H2.
  set code2 := compile_com c2 in H H2.
  autorewrite with code in H2.
  exists (pc + codelen (compile_bexp b 0 (codelen code1 + 1)) +
            (if beval b s then 0 else codelen code1 + 1), [::], s); split=>/=.
  - right; rewrite -/codeb; split.
    - by apply: compile_bexp_correct; eauto with code.
    by rewrite ltn_add2r addn1 ltnS; case: (beval b s); [apply: leq_addr | apply: leq_addl].
  case: (beval b s).
  - autorewrite with code; constructor; eauto with code.
    by apply: ccont_branch; eauto with code; rewrite -/code1 -/codeb addrAC.
  autorewrite with code; constructor; eauto with code.
  by rewrite -/codeb -/code2 addrAC.
- (* while stop *)
  case: {1}_ _ / M (@erefl _ (WHILE b c, k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
  rewrite {c3}E1 {k1}E2 /= in H H2.
  set codec := compile_com c in H H2.
  set codeb := compile_bexp b 0 (codelen codec + 1) in H H2.
  exists (pc + codelen (compile_bexp b 0 (codelen codec + 1)) +
            (if beval b s then 0 else codelen codec + 1), [::], s); split=>/=.
  - right; split.
    - by apply: compile_bexp_correct; rewrite -/codeb; eauto with code.
    by rewrite ltn_add2r addn1 ltnS; apply: com_size_nonzero.
  rewrite (negbTE Hb) -/codeb; autorewrite with code in *.
  by apply: match_config_skip.
- (* while loop *)
  case: {1}_ _ / M (@erefl _ (WHILE b c, k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
  rewrite {c3}E1 {k1}E2 /= in H H2.
  set codec := compile_com c in H H2.
  set codeb := compile_bexp b 0 (codelen codec + 1) in H H2.
  exists (pc + codelen (compile_bexp b 0 (codelen codec + 1)) +
           (if beval b s then 0 else codelen codec + 1), [::], s); split=>/=.
  - right; split.
    - by apply: compile_bexp_correct; rewrite -/codeb; eauto with code.
    by rewrite ltn_add2r addn1 ltnS.
  rewrite Hb -/codeb; autorewrite with code in *.
  constructor; eauto with code.
  apply: ccont_while; eauto with code; rewrite /= -/codeb -/codec.
  - by rewrite (ACl (1*((2*3*4)*5))%AC) /= subrr addr0.
  rewrite (ACl (1*((2*3*4)*5)*6)%AC) /= subrr addr0.
  by autorewrite with code.
- (* skip seq *)
  case: {1}_ _ / M (@erefl _ (SKIP, Kseq c k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
  rewrite {c3}E1 {k1}E2 /= in H H2.
  autorewrite with code in H2.
  case: (compile_cont_Kseq_inv _ _ _ _ s H2)=>pc' [X Y int] /=.
  exists (pc', [::], s); split; first by right.
  by constructor.
(* skip while *)
case: {1}_ _ / M (@erefl _ (SKIP, Kwhile b c k, s))=>c3 k1 st pc H H2 [E1 E2 ->];
rewrite {c3}E1 {k1}E2 /= in H H2.
autorewrite with code in H2.
case: (compile_cont_Kwhile_inv _ _ _ _ _ s H2)=>pc' [X Y int].
exists (pc', [::], s); split=>/=; first by left.
by constructor.
Qed.

(** The hard work is done!  Nice consequences will follow, using
    the general theorems about simulations provided by module [Simulation].

    First, we get an alternate proof that terminating programs are
    correctly compiled, using the continuation semantics instead of
    the big-step semantics to characterize termination of the source
    program. *)

Lemma match_initial_configs c s :
  match_config (compile_program c) (c, Kstop, s) (0, [::], s).
Proof.
set C := compile_program c.
have H: code_at C 0 (compile_com c ++ [::Ihalt]).
- rewrite (_ : C  = [::] ++ (compile_com c ++ [:: Ihalt]) ++ [::]) //.
  by rewrite cats0.
constructor; first by eauto with code.
by apply: ccont_stop; eauto with code.
Qed.

Theorem compile_program_correct_terminating_2 c s s' :
  star step (c, Kstop, s) (SKIP, Kstop, s') ->
  machine_terminates (compile_program c) s s'.
Proof.
move=>H; set C := compile_program c.
case: (simulation_star _ _ _ _ _ _ (simulation_step C) _ _ H _ (match_initial_configs c s))=>ms [A B].
case: {1}_ {-1}_ / B (@erefl _ (SKIP, Kstop, s')) (@erefl _ ms)=>c3 k1 _ pc H1 H2 [E1 E2 ->] E3.
rewrite {c3}E1 {k1}E2 /= in H1 H2; rewrite {ms}E3 in A.
autorewrite with code in H2.
case: (compile_cont_Kstop_inv _ _ s' H2)=>pc' [D E].
by exists pc'; split=>//; apply/star_trans/D.
Qed.

(** Second, and more importantly, we get a proof of semantic
    preservation for diverging source programs: if the program makes
    infinitely many steps, the generated code makes infinitely many
    machine transitions. *)

Theorem compile_program_correct_diverging c s :
  infseq step (c, Kstop, s) ->
  machine_diverges (compile_program c) s.
Proof.
move=>H; set C := compile_program c.
apply: (simulation_infseq _ _ _ _ _ _ (simulation_step C) (c, Kstop, s))=>//.
by apply: match_initial_configs.
Qed.
