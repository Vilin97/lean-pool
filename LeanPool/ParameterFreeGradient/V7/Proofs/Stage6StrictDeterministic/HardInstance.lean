/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.ScalarHard

/-!
The one-dimensional hard family has a unique minimizer and exact smoothness and radius
constants.
-/

@[expose] public section

namespace V7.Stage6StrictDeterministic

/-- The one-dimensional hard objective paired with its exact derivative oracle. -/
noncomputable def hardOracle (eps : ℝ) (x0 : StrictPoint) (H : ℝ) : PairOracle 1 :=
  { value := strictHardFamily eps x0 H
    gradient := strictHardDerivative eps x0 H }

/-- The minimizer located a distance `2 * H` to the right of the initial point. -/
def hardMinimizer (x0 : StrictPoint) (H : ℝ) : StrictPoint :=
  fun _ ↦ x0 0 + 2 * H

theorem strictPoint_ext {x y : StrictPoint} (h : x 0 = y 0) : x = y := by
  funext i
  fin_cases i
  exact h

@[simp] theorem hardMinimizer_apply (x0 : StrictPoint) (H : ℝ) (i : Fin 1) :
    hardMinimizer x0 H i = x0 0 + 2 * H := rfl

theorem strictHardFamily_eq_hardValue (eps : ℝ) (x0 : StrictPoint) (H : ℝ)
    (x : StrictPoint) :
    strictHardFamily eps x0 H x = hardValue eps H (x 0 - x0 0) := rfl

theorem strictHardDerivative_apply (eps : ℝ) (x0 : StrictPoint) (H : ℝ)
    (x : StrictPoint) (i : Fin 1) :
    strictHardDerivative eps x0 H x i = hardSlope eps H (x 0 - x0 0) := rfl

/-- The continuous linear functional multiplying the unique coordinate by `a`. -/
noncomputable def scalarPairingCLM (a : ℝ) : StrictPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ a).comp
    (ContinuousLinearMap.proj 0 : StrictPoint →L[ℝ] ℝ)

@[simp] theorem scalarPairingCLM_apply (a : ℝ) (h : StrictPoint) :
    scalarPairingCLM a h = a * h 0 := by
  simp [scalarPairingCLM, ContinuousLinearMap.toSpanSingleton_apply]
  ring

theorem strictHardFamily_hasFDerivAt {eps H : ℝ} (x0 : StrictPoint)
    (hH : 0 < H) (x : StrictPoint) :
    HasFDerivAt (strictHardFamily eps x0 H)
      (scalarPairingCLM (hardSlope eps H (x 0 - x0 0))) x := by
  have hz : HasFDerivAt (fun y : StrictPoint ↦ y 0 - x0 0)
      (ContinuousLinearMap.proj 0 : StrictPoint →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj 0 : StrictPoint →L[ℝ] ℝ).hasFDerivAt.sub_const
      (x0 0)
  have hs := (hardValue_hasDerivAt (eps := eps) hH (x 0 - x0 0)).hasFDerivAt
  have hc := hs.comp x hz
  change HasFDerivAt (strictHardFamily eps x0 H)
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (hardSlope eps H (x 0 - x0 0))).comp
        (ContinuousLinearMap.proj 0 : StrictPoint →L[ℝ] ℝ)) x
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with y
  rfl

theorem strictHard_coordinateGradient {eps H : ℝ} (x0 : StrictPoint)
    (hH : 0 < H) :
    O3.IsCoordinateGradient (strictHardFamily eps x0 H)
      (strictHardDerivative eps x0 H) := by
  intro x
  have hfd := strictHardFamily_hasFDerivAt (eps := eps) x0 hH x
  refine ⟨hfd.differentiableAt, ?_⟩
  intro h
  rw [hfd.fderiv]
  simp [O3.pairing, strictHardDerivative_apply]

theorem strictHard_convex {eps H : ℝ} (x0 : StrictPoint)
    (heps : 0 < eps) (hH : 0 < H) :
    O3.IsConvexObjective (strictHardFamily eps x0 H) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hs := (hardValue_convex heps hH).2
      (Set.mem_univ (x 0 - x0 0)) (Set.mem_univ (y 0 - x0 0)) ha hb hab
  change hardValue eps H (a * (x 0 - x0 0) + b * (y 0 - x0 0)) ≤
    a * hardValue eps H (x 0 - x0 0) + b * hardValue eps H (y 0 - x0 0) at hs
  rw [strictHardFamily_eq_hardValue, strictHardFamily_eq_hardValue,
    strictHardFamily_eq_hardValue]
  change hardValue eps H (a * x 0 + b * y 0 - x0 0) ≤
    a * hardValue eps H (x 0 - x0 0) + b * hardValue eps H (y 0 - x0 0)
  have harg : a * x 0 + b * y 0 - x0 0 =
      a * (x 0 - x0 0) + b * (y 0 - x0 0) := by
    linear_combination (x0 0) * hab
  rw [harg]
  exact hs

theorem strictHard_coercive {eps H : ℝ} (x0 : StrictPoint)
    (heps : 0 < eps) (hH : 0 < H) :
    IsCoerciveReal (strictHardFamily eps x0 H) := by
  intro B
  let g : ℝ := 2 * eps
  let R : ℝ := |x0 0| + 4 * H + |B| / g + 1
  have hg : 0 < g := by dsimp [g]; linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro x hx
  have htriangle : |x 0| - |x0 0| ≤ |x 0 - x0 0| := by
    exact abs_sub_abs_le_abs_sub _ _
  have hlarge : 4 * H + |B| / g + 1 ≤ |x 0 - x0 0| := by
    dsimp [R] at hx
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlarge hg.le
  have hcancel : g * (|B| / g) = |B| := by field_simp [ne_of_gt hg]
  have hB : B ≤ g * |x 0 - x0 0| - 4 * g * H := by
    have hBabs : B ≤ |B| := le_abs_self B
    nlinarith
  rw [strictHardFamily_eq_hardValue]
  exact hB.trans (by simpa [g] using hardValue_linear_lower heps hH (x 0 - x0 0))

theorem strictHard_uniqueMinimizer {eps H : ℝ} (x0 : StrictPoint)
    (heps : 0 < eps) (hH : 0 < H) :
    UniqueMinimizer (strictHardFamily eps x0 H) (hardMinimizer x0 H) := by
  constructor
  · intro x
    rw [strictHardFamily_eq_hardValue, strictHardFamily_eq_hardValue]
    have hzstar : hardMinimizer x0 H 0 - x0 0 = 2 * H := by
      simp [hardMinimizer]
    rw [hzstar]
    exact hardValue_minimum heps hH (x 0 - x0 0)
  · intro x heq
    rw [strictHardFamily_eq_hardValue, strictHardFamily_eq_hardValue] at heq
    have hscalar : hardValue eps H (x 0 - x0 0) = hardValue eps H (2 * H) := by
      simpa [hardMinimizer] using heq
    have hz := (hardValue_eq_minimizer_iff heps hH (x 0 - x0 0)).mp hscalar
    apply strictPoint_ext
    simp [hardMinimizer]
    linarith

theorem strictHard_exactLipschitz {eps H : ℝ} (x0 : StrictPoint)
    (heps : 0 < eps) (hH : 0 < H) :
    ExactGradientLipschitzConstant (hardOracle eps x0 H) ((2 * eps) / H) := by
  constructor
  · intro x y
    change |hardSlope eps H (x 0 - x0 0) - hardSlope eps H (y 0 - x0 0)| ≤
      (2 * eps / H) * |x 0 - y 0|
    have hs := hardSlope_lipschitz heps hH (x 0 - x0 0) (y 0 - x0 0)
    convert hs using 1; ring
  · intro L' hL'
    let xH : StrictPoint := fun _ ↦ x0 0 + H
    let x2H : StrictPoint := fun _ ↦ x0 0 + 2 * H
    have hb := hL' xH x2H
    have hsH : hardSlope eps H H = -(2 * eps) := hardSlope_of_le le_rfl
    have hs2H : hardSlope eps H (2 * H) = 0 := by
      rw [hardSlope_of_middle (by linarith : H < 2 * H) (by linarith : 2 * H ≤ 3 * H)]
      field_simp [ne_of_gt hH]
      ring
    have hbound0 : 2 * eps ≤ L' * |H - 2 * H| := by
      simpa [hardOracle, xH, x2H, strictHardDerivative_apply, hsH, hs2H,
        abs_of_pos heps] using hb
    have habs : |H - 2 * H| = H := by
      rw [show H - 2 * H = -H by ring, abs_neg, abs_of_pos hH]
    rw [habs] at hbound0
    have hbound : 2 * eps ≤ L' * H := hbound0
    exact (div_le_iff₀ hH).mpr hbound

theorem strictHard_radius (x0 : StrictPoint) {H : ℝ} (hH : 0 < H) :
    |hardMinimizer x0 H 0 - x0 0| = 2 * H := by
  simp [hardMinimizer, abs_of_pos (by linarith : 0 < 2 * H)]

/-- Full frozen hard-instance package with the exact choices `L=2 eps/H`,
`R=2H`, and normalization four. -/
theorem strictHardInstance (eps : ℝ) (x0 : StrictPoint) (H : ℝ)
    (heps : 0 < eps) (hH : 0 < H) :
    StrictHardInstance eps x0 H ((2 * eps) / H) (2 * H)
      (hardOracle eps x0 H) (hardMinimizer x0 H) := by
  refine ⟨hH, rfl, rfl, strictHard_convex x0 heps hH,
    strictHard_coercive x0 heps hH, strictHard_coordinateGradient x0 hH,
    strictHard_uniqueMinimizer x0 heps hH,
    strictHard_exactLipschitz x0 heps hH, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hH
  · exact (strictHard_radius x0 hH).symm
  · field_simp [ne_of_gt heps, ne_of_gt hH]
    ring

end V7.Stage6StrictDeterministic
