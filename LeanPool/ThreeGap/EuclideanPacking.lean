/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Planar packing: at most 5 vectors pairwise more than 60° apart

The sharp Euclidean five-distance bound `g₂ ≤ 5` needs to cap the number of best-approximation
remainder vectors in a doubling window. The metric→angle crux (`EuclideanAngle`) shows they are
pairwise **strictly** more than `π/3` apart; this file supplies the **planar packing count**:

  **at most 5 vectors in the plane can be pairwise more than `π/3` apart** — equivalently, six are
  impossible.

The proof is the circular gap-sum. Via the oriented angle `oangle` (valued in `ℝ/2πℤ`, *additive*),
the pairwise angle is `|(φ i − φ j).toReal|` for `φ i = oangle (v 0) (v i)`. Sorting the
representatives `(φ i).toReal ∈ (−π, π]` gives six points on the circle whose six consecutive gaps
(five interior + one wrap) sum to `2π`; each gap exceeds `π/3` (the circular distance is `≤` the
gap),
so `2π = Σ gaps > 6 · π/3 = 2π`, a contradiction.

The one analytic input is `abs_toReal_coe_le`: `|(↑x).toReal| ≤ |x|` — the circular distance never
exceeds the representative distance. Applied to `−D` and to `2π − D` it yields both the interior and
the wrap bound with no case analysis.

This is the `K = 5` packing count (`g₂ ≤ 6`); the sharp `≤ 4` (`g₂ ≤ 5`) is Romanov's finer
argument.
Axiom-clean; elementary.
-/

namespace ThreeGap.EuclideanPacking

open Real InnerProductGeometry

/-- **The circular distance never exceeds the representative distance:** `|(↑x).toReal| ≤ |x|`.
(If `|x| ≥ π` use `|toReal| ≤ π`; if `|x| < π` then `x ∈ (−π, π]` and `(↑x).toReal = x`.) -/
theorem abs_toReal_coe_le (x : ℝ) : |(↑x : Real.Angle).toReal| ≤ |x| := by
  rcases le_or_gt π |x| with h | h
  · exact le_trans (Real.Angle.abs_toReal_le_pi _) h
  · rw [abs_lt] at h
    rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr ⟨h.1, h.2.le⟩]

/-! ## The combinatorial core: six points on the circle -/

/-- **Six points of `ℝ/2πℤ` cannot be pairwise more than `π/3` apart** (in the `toReal` circular
metric). -/
theorem not_six_circle (φ : Fin 6 → Real.Angle)
    (h : ∀ i j, i ≠ j → π / 3 < |(φ i - φ j).toReal|) : False := by
  -- representatives in `(−π, π]`
  set a : Fin 6 → ℝ := fun i => (φ i).toReal with ha
  have ha_mem : ∀ i, a i ∈ Set.Ioc (-π) π := fun i => Real.Angle.toReal_mem_Ioc (φ i)
  -- the difference of two angles is the coe of the representative difference
  have hcoe : ∀ i j : Fin 6, φ i - φ j = ((a i - a j : ℝ) : Real.Angle) := by
    simp_all
  -- interior bound: for `a i ≤ a j`, distinct, the gap exceeds `π/3`
  have gapBound : ∀ i j : Fin 6, a i ≤ a j → i ≠ j → π / 3 < a j - a i := by
    intro i j hle hne
    have hsep := h i j hne
    have key := abs_toReal_coe_le (-(a j - a i))
    rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ a j - a i)] at key
    rw [hcoe i j, show (a i - a j : ℝ) = -(a j - a i) by ring] at hsep
    linarith [hsep, key]
  -- wrap bound: for `a i ≤ a j`, distinct, `2π − (a j − a i)` exceeds `π/3`
  have wrapBound : ∀ i j : Fin 6, a i ≤ a j → i ≠ j → π / 3 < 2 * π - (a j - a i) := by
    intro i j hle hne
    have hsep := h i j hne
    have hai := ha_mem i
    have haj := ha_mem j
    simp only [Set.mem_Ioc] at hai haj
    have hnn : (0:ℝ) ≤ 2 * π - (a j - a i) := by linarith [hai.1, haj.2]
    have key := abs_toReal_coe_le (2 * π - (a j - a i))
    rw [abs_of_nonneg hnn] at key
    rw [hcoe i j, show (a i - a j : ℝ) = -(a j - a i) by ring,
      show ((-(a j - a i) : ℝ) : Real.Angle) = ((2 * π - (a j - a i) : ℝ) : Real.Angle) by
        rw [show (2 * π - (a j - a i) : ℝ) = 2 * π + (-(a j - a i)) by ring,
          Real.Angle.coe_add, Real.Angle.coe_two_pi, zero_add]] at hsep
    linarith [hsep, key]
  -- sort the representatives
  set σ : Equiv.Perm (Fin 6) := Tuple.sort a with hσ
  have hmono : Monotone (a ∘ σ) := Tuple.monotone_sort a
  have hinj : Function.Injective σ := σ.injective
  -- the five interior gaps and the wrap gap each exceed `π/3`
  have g0 := gapBound (σ 0) (σ 1) (hmono (by decide)) (hinj.ne (by decide))
  have g1 := gapBound (σ 1) (σ 2) (hmono (by decide)) (hinj.ne (by decide))
  have g2 := gapBound (σ 2) (σ 3) (hmono (by decide)) (hinj.ne (by decide))
  have g3 := gapBound (σ 3) (σ 4) (hmono (by decide)) (hinj.ne (by decide))
  have g4 := gapBound (σ 4) (σ 5) (hmono (by decide)) (hinj.ne (by decide))
  have gw := wrapBound (σ 0) (σ 5) (hmono (by decide)) (hinj.ne (by decide))
  -- the six gaps sum to `2π`, each exceeds `π/3`: `2π > 2π`
  have hpi := Real.pi_pos
  linarith

/-! ## The vector form -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- **At most 5 vectors pairwise more than `π/3` apart** (the planar packing count). For an oriented
plane `E` there are no six nonzero vectors that are pairwise strictly more than `π/3` apart. -/
theorem not_six_separated (o : Orientation ℝ E (Fin 2)) (v : Fin 6 → E) (hv : ∀ i, v i ≠ 0)
    (hsep : ∀ i j, i ≠ j → π / 3 < InnerProductGeometry.angle (v i) (v j)) : False := by
  set φ : Fin 6 → Real.Angle := fun i => o.oangle (v 0) (v i) with hφ
  refine not_six_circle φ (fun i j hne => ?_)
  -- `oangle (v j) (v i) = φ i − φ j`, so the angle is `|(φ i − φ j).toReal|`
  have hoa : o.oangle (v j) (v i) = φ i - φ j := by
    simp_all
  have hangle : InnerProductGeometry.angle (v j) (v i) = |(φ i - φ j).toReal| := by
    rw [o.angle_eq_abs_oangle_toReal (hv j) (hv i), hoa]
  rw [← hangle, InnerProductGeometry.angle_comm]
  exact hsep i j hne

end ThreeGap.EuclideanPacking
