/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.Jump

/-!
# The Arithmetical Hierarchy

This file develops the iterated jump operator, the sets `∅⁽ⁿ⁾`, and the levels `Σ⁰ₙ`, `Π⁰ₙ`,
`Δ⁰ₙ` of the arithmetical hierarchy relative to oracle computability.
-/

namespace Computability

/-- The iterated Turing jump: `TuringJump n f` is the `n`-fold jump of `f`. -/
def TuringJump (n : ℕ) (f : ℕ →. ℕ) : ℕ →. ℕ :=
  match n with
  | 0 => f
  | n + 1 => (TuringJump n f)⌜

/-- The `n`-fold jump of the empty oracle (totally undefined). Used as an oracle function. -/
def arithJumpBase : ℕ → ℕ →. ℕ
| 0     => fun _ => Part.none
| n + 1 => jump (arithJumpBase n)

/-- The classical `∅⁽ⁿ⁾` set: the domain of the `n`-fold jump of the empty oracle. -/
def arithJumpSet (n : ℕ) : Set ℕ :=
  (arithJumpBase n).Dom

/-- The halting set `K = ∅'`, the domain of the first jump of the empty oracle. -/
abbrev K := arithJumpSet 1

/-- A set `A` is decidable in `O` if its indicator is computable in `O`. -/
def decidableIn (O : Set (ℕ →. ℕ)) (A : Set ℕ) : Prop :=
  ∃ f : ℕ → Bool, ComputableIn O f ∧ ∀ n, A n ↔ f n = true

/-- The base level `Δ⁰₀`: sets decidable in the empty oracle. -/
def Delta00 (A : Set ℕ) : Prop := decidableIn {} A
/-- The base level `Σ⁰₀`, equal to `Δ⁰₀`. -/
def Sigma00 := Delta00
/-- The base level `Π⁰₀`, equal to `Δ⁰₀`. -/
def Pi00 := Delta00

/-- The `Σ⁰ₙ` level of the arithmetical hierarchy. -/
def Sigma0 (n : ℕ) (A : Set ℕ) : Prop :=
  match n with
  | 0 => decidableIn {} A
  | k + 1 => recursivelyEnumerableIn {arithJumpBase k} A

/-- The `Π⁰ₙ` level: complements of `Σ⁰ₙ` sets. -/
def Pi0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n Aᶜ

/-- The `Δ⁰ₙ` level: sets that are both `Σ⁰ₙ` and `Π⁰ₙ`. -/
def Delta0 (n : ℕ) (A : Set ℕ) : Prop :=
  Sigma0 n A ∧ Pi0 n A

@[inherit_doc] notation "Σ⁰_" => Sigma0
@[inherit_doc] notation "Π⁰_" => Pi0
@[inherit_doc] notation "Δ⁰_" => Delta0

end Computability
