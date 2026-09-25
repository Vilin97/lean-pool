/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic

/-!
# Moduli and Lebesgue integrals of indicator truncations

The Marcinkiewicz interpolation argument used for the Caffarelli–Kohn–Nirenberg
program (CKN 1982) splits a function into a high-frequency part, carried by a
superlevel set of the `ℝ≥0∞`-valued modulus `absE f x = ENNReal.ofReal |f x|`,
and a low-frequency part, carried by its complement.  Both parts are indicator
truncations `s.indicator f` of the original function.

This file records the three elementary identities needed for that bookkeeping.
The first states that `absE` commutes with truncation pointwise, so that
`absE (s.indicator f)` is the truncation of `absE f` and the modulus of a
truncated function vanishes off `s`.  The second and third state that the
Lebesgue integrals of `absE (s.indicator f)` and of its square over all of
`Vec3` agree with the corresponding integrals over `s` alone.  All three are
stated for an arbitrary measurable set `s` and an arbitrary function
`f : Vec3 → ℝ`; the two integral identities use the restriction of Lebesgue
measure to `s`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The `ℝ≥0∞`-valued modulus `absE` commutes with truncation by an indicator:
truncating `f` to `s` before taking the modulus is the same as taking the
modulus first and then truncating it to `s`. -/
lemma absE_indicator_eq (s : Set Vec3) (f : Vec3 → ℝ) :
    absE (s.indicator f) = s.indicator (absE f) := by
  funext x
  change ENNReal.ofReal |(s.indicator f) x| =
    s.indicator (fun y ↦ ENNReal.ofReal |f y|) x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The total mass of the modulus of a truncation is the mass of the modulus over
the truncating set: `∫ absE (s.indicator f) = ∫_s absE f`. -/
lemma lintegral_absE_indicator {s : Set Vec3} (hs : MeasurableSet s) (f : Vec3 → ℝ) :
    ∫⁻ x, absE (s.indicator f) x = ∫⁻ x in s, absE f x := by
  rw [absE_indicator_eq, lintegral_indicator hs]

/-- The same identity for the square of the modulus:
`∫ absE (s.indicator f) ^ 2 = ∫_s absE f ^ 2`. -/
lemma lintegral_absE_indicator_sq {s : Set Vec3} (hs : MeasurableSet s) (f : Vec3 → ℝ) :
    ∫⁻ x, absE (s.indicator f) x ^ 2 = ∫⁻ x in s, absE f x ^ 2 := by
  have hpow : (fun x ↦ absE (s.indicator f) x ^ 2) =
      s.indicator (fun x ↦ absE f x ^ 2) := by
    rw [absE_indicator_eq]
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [hpow, lintegral_indicator hs]

end CKN.Foundation.Euclidean
