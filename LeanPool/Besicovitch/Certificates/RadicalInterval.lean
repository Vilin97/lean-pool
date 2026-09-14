/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Certificates.RationalInterval
public import Mathlib.Analysis.Real.Sqrt

/-!
# Exact interval arithmetic for radical expressions

A square-root node carries rational lower and upper witnesses. The evaluator checks their
squares exactly, so every successful enclosure has a kernel-checked real-number semantics.
-/

@[expose] public section

open Set

namespace LeanPool.Besicovitch

/-- Rational expressions with explicitly certified square-root bounds. -/
inductive RadicalExpression (n : ℕ) where
  | var : Fin n → RadicalExpression n
  | constant : ℚ → RadicalExpression n
  | add : RadicalExpression n → RadicalExpression n → RadicalExpression n
  | neg : RadicalExpression n → RadicalExpression n
  | mul : RadicalExpression n → RadicalExpression n → RadicalExpression n
  | inv : RadicalExpression n → RadicalExpression n
  | sqrt : RadicalExpression n → ℚ → ℚ → RadicalExpression n

namespace RadicalExpression

/-- Evaluate a radical expression in a real environment. -/
noncomputable def eval {n : ℕ} : RadicalExpression n → (Fin n → ℝ) → ℝ
  | .var i, x => x i
  | .constant q, _ => q
  | .add f g, x => f.eval x + g.eval x
  | .neg f, x => -f.eval x
  | .mul f g, x => f.eval x * g.eval x
  | .inv f, x => (f.eval x)⁻¹
  | .sqrt f _ _, x => Real.sqrt (f.eval x)

/-- Evaluate by exact rational intervals, rejecting unsafe inverses or square-root witnesses. -/
def enclosure {n : ℕ} : RadicalExpression n → (Fin n → RationalInterval) →
    Option RationalInterval
  | .var i, X => some (X i)
  | .constant q, _ => some (.singleton q)
  | .add f g, X => do
      let I ← f.enclosure X
      let J ← g.enclosure X
      return I.add J
  | .neg f, X => do
      let I ← f.enclosure X
      return I.neg
  | .mul f g, X => do
      let I ← f.enclosure X
      let J ← g.enclosure X
      return I.mul J
  | .inv f, X => do
      let I ← f.enclosure X
      if h : 0 < I.lower ∨ I.upper < 0 then return I.inv h else none
  | .sqrt f lower upper, X => do
      let I ← f.enclosure X
      if h : 0 ≤ I.lower ∧ 0 ≤ lower ∧ lower ≤ upper ∧
          lower * lower ≤ I.lower ∧ I.upper ≤ upper * upper then
        return ⟨lower, upper, h.2.2.1⟩
      else none

/-- Check an enclosure and widen it to a simpler rational target interval. -/
def enclosureWithin {n : ℕ} (f : RadicalExpression n) (X : Fin n → RationalInterval)
    (target : RationalInterval) : Option RationalInterval := do
  let I ← f.enclosure X
  if target.lower ≤ I.lower ∧ I.upper ≤ target.upper then some target else none

/-- Decide whether the computed enclosure lies in a given rational target interval. -/
def certifiesWithin {n : ℕ} (f : RadicalExpression n) (X : Fin n → RationalInterval)
    (target : RationalInterval) : Bool :=
  match f.enclosure X with
  | none => false
  | some I => decide (target.lower ≤ I.lower ∧ I.upper ≤ target.upper)

/-- Every successful radical enclosure contains the real value of the expression. -/
theorem enclosure_sound {n : ℕ} {f : RadicalExpression n}
    {X : Fin n → RationalInterval} {x : Fin n → ℝ}
    (hx : ∀ i, (X i).Contains (x i)) {I : RationalInterval} (hI : f.enclosure X = some I) :
    I.Contains (f.eval x) := by
  induction f generalizing I with
  | var i =>
      simp only [enclosure, Option.some.injEq] at hI
      subst I
      exact hx i
  | constant q =>
      simp only [enclosure, Option.some.injEq] at hI
      subst I
      exact RationalInterval.singleton_contains q
  | add f g hf hg =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          cases hgI : g.enclosure X with
          | none => simp [hfI, hgI] at hI
          | some Ig =>
              simp [hfI, hgI] at hI
              subst I
              exact RationalInterval.add_contains (hf hfI) (hg hgI)
  | neg f hf =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          simp [hfI] at hI
          subst I
          exact RationalInterval.neg_contains (hf hfI)
  | mul f g hf hg =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          cases hgI : g.enclosure X with
          | none => simp [hfI, hgI] at hI
          | some Ig =>
              simp [hfI, hgI] at hI
              subst I
              exact RationalInterval.mul_contains (hf hfI) (hg hgI)
  | inv f hf =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          rw [hfI] at hI
          dsimp at hI
          split at hI
          · rename_i h
            simp only [Option.some.injEq] at hI
            subst I
            exact RationalInterval.inv_contains (hf hfI) h
          · contradiction
  | sqrt f lower upper hf =>
      simp only [enclosure] at hI
      cases hfI : f.enclosure X with
      | none => simp [hfI] at hI
      | some If =>
          rw [hfI] at hI
          dsimp at hI
          split at hI
          · rename_i h
            simp only [Option.some.injEq] at hI
            subst I
            have hfx := hf hfI
            constructor
            · norm_num [RationalInterval.Contains] at hfx ⊢
              apply Real.le_sqrt_of_sq_le
              have hlower : (↑lower : ℝ) ^ 2 ≤ ↑If.lower := by
                norm_num [pow_two]
                exact_mod_cast h.2.2.2.1
              exact hlower.trans hfx.1
            · apply (Real.sqrt_le_iff).2
              constructor
              · exact_mod_cast h.2.1.trans h.2.2.1
              · norm_num [RationalInterval.Contains] at hfx ⊢
                have hupper : (↑If.upper : ℝ) ≤ (↑upper : ℝ) ^ 2 := by
                  norm_num [pow_two]
                  exact_mod_cast h.2.2.2.2
                exact hfx.2.trans hupper
          · contradiction

/-- A successful widened enclosure contains the real value of the expression. -/
theorem enclosureWithin_sound {n : ℕ} {f : RadicalExpression n}
    {X : Fin n → RationalInterval} {x : Fin n → ℝ} (hx : ∀ i, (X i).Contains (x i))
    {target : RationalInterval} (h : f.enclosureWithin X target = some target) :
    target.Contains (f.eval x) := by
  unfold enclosureWithin at h
  cases hI : f.enclosure X with
  | none => simp [hI] at h
  | some I =>
      rw [hI] at h
      dsimp at h
      split at h
      · rename_i hsub
        have hvalue := enclosure_sound hx hI
        constructor
        · have hlower : (target.lower : ℝ) ≤ I.lower := by exact_mod_cast hsub.1
          exact hlower.trans hvalue.1
        · have hupper : (I.upper : ℝ) ≤ target.upper := by exact_mod_cast hsub.2
          exact hvalue.2.trans hupper
      · contradiction

/-- A successful Boolean certificate encloses the real value of the expression. -/
theorem certifiesWithin_sound {n : ℕ} {f : RadicalExpression n}
    {X : Fin n → RationalInterval} {x : Fin n → ℝ} (hx : ∀ i, (X i).Contains (x i))
    {target : RationalInterval} (h : f.certifiesWithin X target = true) :
    target.Contains (f.eval x) := by
  unfold certifiesWithin at h
  cases hI : f.enclosure X with
  | none => simp [hI] at h
  | some I =>
      rw [hI] at h
      have hsub := of_decide_eq_true h
      have hvalue := enclosure_sound hx hI
      constructor
      · have hlower : (target.lower : ℝ) ≤ I.lower := by exact_mod_cast hsub.1
        exact hlower.trans hvalue.1
      · have hupper : (I.upper : ℝ) ≤ target.upper := by exact_mod_cast hsub.2
        exact hvalue.2.trans hupper

end RadicalExpression

end LeanPool.Besicovitch
