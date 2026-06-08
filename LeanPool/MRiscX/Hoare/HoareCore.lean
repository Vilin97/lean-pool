/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.MState
import LeanPool.MRiscX.Semantics.Run
import LeanPool.MRiscX.Hoare.EvalLabelInHoare
import LeanPool.MRiscX.Hoare.HoareAssignmentElab
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra


/-!
Hoare core

This file introduces Hoare logic into the MRiscX programming language.
To gain a deeper understanding of Hoare logic,  you can read the
"Hoare" chapter in Software Foundations - Volume 2. Also, the
components of the MRiscX programming language should be familiar,
which can be found in "Syntax.lean".
Because the MRiscX assembly language produces unstructured programs, we can't just use the "plain"
Hoare-Logic. This led us to implement the logic from
LUNDBERG, Didrik, et al. Hoare-style logic for unstructured programs.
In: International Conference on Software Engineering and Formal Methods.
Cham: Springer International Publishing, 2020. S. 193-213.

In essence, we introduce Assertions, which are logical claims about
states—specifically, machine states in this context. Using these
assertions, we define Hoare triples, which make claims about the
state before and after the execution of a command.
This can be used to perform a structured proof later.
-/
/-- An assertion is a predicate on machine states. -/
abbrev Assertion : Type := MState → Prop

/-- Conjunction of two assertions, holding when both hold. -/
def Assertion.And (P Q : Assertion) : Assertion := fun st => (P st) ∧ (Q st)
/-- Negation of an assertion, holding when the assertion does not. -/
def Assertion.Not (P : Assertion) : Assertion := fun st => ¬(P st)



/--
This **weak** relation, inspired by Lundberg et al. (2020),
is defined over two `MState`s, `s` and `s'`.
Unlike earlier formulations that take a single set of lines `L`,
this relation is parameterized by two sets of lines, `L_w` and `L_b`.

This design has the advantage that the condition `s'.pc ∈ L_w` is already guaranteed
by the relation itself. Since we assume `L_w ∩ L_b = ∅`, it immediately follows that
`s'.pc ∉ L_b` must also hold. Consequently, the explicit postcondition `s'.pc ∈ L_b` in
the *Judgment of* `L_as` could be omitted. However, this simplification has not yet been
applied in the current version.

This relation is defined as follows:

State `s'` is reached from state `s` after exactly `n` steps, where `n > 0`, and the program
counter of `s'` points to a line in `L_w`. Moreover, there exists no `n' ∈ ℕ` with `0 < n' < n`
such that the state reached after `n'` steps from `s` has its program counter in `L_w ∪ L_b`.
In other words, `s'` is the **first** state along the execution path whose program counter lies
in `L_w`.

The **weak** relation is deterministic and partial: a program starting in `s` may never reach a
state whose program counter lies in `L_w`. Additionally, the relation guarantees that no
intermediate state between `s` and `s'` has a program counter in `L_w`.

With the help of this relation, unambiguous statements can be made about the flow of the program.
-/
def weak (s s' : MState) (L_w L_b : Set UInt64) (c : Code) : Prop :=
  s.code = c →
  ∃ (n:Nat), n > 0 ∧ s.runNSteps n = s' ∧ (s'.pc) ∈ L_w ∧
  ∀ (n':Nat), 0 < n' ∧ n' < n →
  (s.runNSteps n').pc ∉ (L_w ∪ L_b)


/--
Inspired by the `judgement of L_{as}` in the paper Lundberg et al. (2020).

Suppose, that `L_w ∩ L_b = ∅` and `L_w ≠ ∅` hold, then the `hoareTripleUp` means:

For all states `s` in which both `P(s)` and `I(s)` are satisfied and whose
program counter points to `l`,
there exists a successor state `s'` for which both the relation
`weak(s, L_w ∪ L_b, s')` and `Q(s')`, `I(s')` and `s'.pc ∉ L_w`
are satisfied.
-/
def hoareTripleUp (P Q : Assertion) (l : UInt64) (L_w L_b : Set UInt64)
  (c : Code)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀ (s : MState), s.code = c →
  s.pc = l →
  P s →
  ∃ (s' : MState), (weak s s' L_w L_b c) ∧ Q s' ∧ s'.pc ∉ L_b


/--
Essentially the same as the `hoareTripleUp`, but instead of inspecting a whole code segment,
this relation only focusses on the instruction which is executed next. This can be used to
reason about single instructions in order to define their specification.
-/
def hoare_triple_up_1 (P Q : Assertion) (l : UInt64) (L_w L_b : Set UInt64) (i : Instr)
:=
  L_w ∩ L_b = ∅ →
  L_w ≠ ∅ →
  ∀ (s : MState), s.currInstruction = i →
  s.pc = l →
  P s →
  ∃ (s' : MState), (weak s s' L_w L_b s.code) ∧ Q s' ∧ s'.pc ∉ L_b
