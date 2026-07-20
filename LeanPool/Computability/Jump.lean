/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.Encoding
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting

/-!
# The Jump Operator

This file defines the jump operator `⌜` for partial functions relative to an oracle and proves its
basic properties, together with the associated notions of recursive enumerability relative to an
oracle.

We identify partial recursive functions with recursively enumerable sets by taking their domain:
if `f : ℕ →. ℕ`, then `dom f : Set ℕ` is `{n | n ∈ f.Dom}`. These are the terms in which the jump
theorems are stated.
-/

open scoped Computability

namespace Computability

/-- A set `A` is recursively enumerable in a set of oracle functions `O` if it is the domain of a
function recursive in `O`. -/
def recursivelyEnumerableIn (O : Set (ℕ →. ℕ)) (A : Set ℕ) :=
  ∃ f, (RecursiveIn O f) ∧ A = f.Dom

/-- A set `A` is recursively enumerable in a family `X` of oracle functions if it is the domain of a
function recursive in the range of `X`. -/
def recursivelyEnumerableIn₁ (X : α → ℕ →. ℕ) (A : Set ℕ) :=
  ∃ f, (RecursiveIn (Set.range X) f) ∧ A = f.Dom

/-- A set `A` is recursively enumerable in a single oracle `g` if it is the domain of a function
recursive in `{g}`. -/
def recursivelyEnumerableIn₂ (g : ℕ →. ℕ) (A : ℕ → Prop) :=
 ∃ f, (RecursiveIn {g} f) ∧ A = f.Dom

/-- A set `A` is recursively enumerable if it is the domain of a partial recursive function. -/
def recursivelyEnumerable (A : Set ℕ) :=
  ∃ f, (RecursiveIn {} f) ∧ A = f.Dom

/-- The jump of `f` is the diagonal of the universal machine relative to `f`:
`f⌜ n = evalo (fun _ => f) (decodeCodeo n) n`. Its domain is the halting problem relative to `f`. -/
def jump (f : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n => evalo (fun _ : Unit => f) (decodeCodeo n) n

/-- The oracle corresponding to a decidable set `A`, returning `0` on elements of `A` and undefined
elsewhere. -/
def setOracle (A : ℕ → Prop) [DecidablePred A] : ℕ →. ℕ :=
  fun n => if A n then Part.some 0 else Part.none

/-- The jump of a decidable set `A`: the set of `n` such that the `n`-th oracle program halts on
input `n` with oracle `A`. -/
def jumpSet (A : ℕ → Prop) [DecidablePred A] : ℕ → Prop :=
  fun n => (evalo (fun (_ : Unit) => setOracle A) (decodeCodeo n) n).Dom

/-- `W e f` is the domain of the `e`-th partial function recursive in the oracle family `f`. -/
abbrev W [Primcodable α] (e : ℕ) (f : α → ℕ →. ℕ) := (evalo f (decodeCodeo e)).Dom

@[inherit_doc] notation:100 f"⌜" => jump f

theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by
  have h_eq : ∀ n, (jump f (s n)) = f n := by
    intro n
    have evalo_const : ∀ n x, evalo (fun _ : Unit => f) (const n) x = Part.some n := by
      intro n x
      induction n generalizing x with
      | zero => rfl
      | succ n ih => simp [evalo, ih, const]
    unfold jump s
    rw [decodeCodeo_encodeCodeo]
    simp [*, evalo]
  have h_s : RecursiveIn {jump f} (fun n => Part.some (s n)) := RecursiveIn.of_primrec s_primrec
  have h_jump : RecursiveIn {jump f} (jump f) := RecursiveIn.oracle _ (by norm_num)
  have h_comp : RecursiveIn {jump f} (fun n => jump f (s n)) := by
    convert RecursiveIn.comp h_jump h_s using 1
    ext; simp [bind]
  exact RecursiveIn.of_eq h_comp h_eq

/-- A predicate `p` is computable relative to `f` if it is decidable and its decision procedure is
computable in `{f}`. -/
def ComputablePredIn (f : ℕ →. ℕ) [Primcodable α] (p : α → Prop) :=
  ∃ (_ : DecidablePred p), ComputableIn {f} (fun n => decide (p n))

/-- A predicate `p` on `ℕ` is recursively enumerable relative to `f` if it is the domain predicate
of a function recursive in `{f}`. -/
def REPredIn (f : ℕ →. ℕ) (p : ℕ → Prop) :=
  ∃ g : ℕ →. ℕ, RecursiveIn {f} g ∧ p = fun n => (g n).Dom

theorem dom_re_in_jump (f : ℕ →. ℕ) :
  REPredIn (f⌜) (fun n => (f n).Dom) :=
  ⟨f, jump_recIn f, rfl⟩

section decide

variable {α} [Primcodable α]

protected lemma ComputablePredIn.decide {p : α → Prop} {f : ℕ →. ℕ} [DecidablePred p]
    (hp : ComputablePredIn f p) :
    ComputableIn {f} (fun a => decide (p a)) := by
  convert hp.choose_spec

lemma ComputableIn.computablePred {p : α → Prop} [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) : ComputablePred p :=
  ⟨inferInstance, hp⟩

lemma computablePredIn_iff_computableIn_decide {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ Computable (fun a => decide (p a)) where
  mp := ComputablePred.decide
  mpr := Computable.computablePred

/-- `PrimrecPredIn p` means `p : α → Prop` is a predicate whose decision procedure is primitive
recursive relative to the oracle `f`. -/
def PrimrecPredIn {α} [Primcodable α] {f : ℕ → ℕ} (p : α → Prop) :=
  ∃ (_ : DecidablePred p), PrimrecIn' {f} fun a => decide (p a)

end decide

/-- The jump set `Kf f` relative to `f`: the set of `n` on which `jump f` is defined. -/
def Kf (f : ℕ →. ℕ) (n : ℕ) : Prop := (jump f n).Dom

theorem re_in_trans (A : Set ℕ) (f h : ℕ →. ℕ) :
  recursivelyEnumerableIn₂ f A →
  f ≤ᵀ h →
  recursivelyEnumerableIn₂ h A := by
  intro freInA fh
  obtain ⟨g, hg, hA⟩ := freInA
  exact ⟨g, TuringReducible.trans hg fh, hA⟩

end Computability
