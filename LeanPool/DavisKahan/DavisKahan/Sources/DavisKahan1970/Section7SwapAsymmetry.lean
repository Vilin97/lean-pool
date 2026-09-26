/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Sharpness
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-! # Section7Swap Asymmetry -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Section 7 residual swap asymmetry

After proving the sine double-angle theorem, Davis and Kahan point out an
asymmetry.  The ambient perturbation estimate can be obtained after swapping
the unperturbed and perturbed operators, but the directed residual estimate
cannot.  Their two-dimensional family is

`A = diag(0, delta)`, `H = !![0, 1; 1, -delta]`.

Thus `A + H` is the coordinate flip.  The line at angle `pi / 4` is a reducing
eigenline of `A + H`, the residual of the coordinate line has norm one, and
the doubled directed sine is one.  Consequently the incorrectly swapped
right-hand side is `2` while the left-hand side is `delta`, which is
unbounded as the source gap grows.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section7SwapAsymmetry

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

/-- The two-dimensional model space in which the Section 7 swap asymmetry is
exhibited. -/
abbrev Plane := PlanarModelSpace ℂ

/-- The source unperturbed operator `diag(0, delta)`. -/
def section7SwapA (delta : ℝ) : Plane →L[ℂ] Plane :=
  planarAmbient delta

/-- The source perturbation `!![0, 1; 1, -delta]`. -/
def section7SwapH (delta : ℝ) : Plane →L[ℂ] Plane :=
  (Matrix.toEuclideanLin
    !![(0 : ℂ), 1; 1, ((-delta : ℝ) : ℂ)]).toContinuousLinearMap

/-- The perturbed operator `A + H = !![0, 1; 1, 0]`. -/
def section7SwapPerturbed : Plane →L[ℂ] Plane :=
  (Matrix.toEuclideanLin
    !![(0 : ℂ), 1; 1, 0]).toContinuousLinearMap

/-- The source family has exactly the displayed perturbation identity. -/
theorem section7SwapPerturbed_eq_A_add_H (delta : ℝ) :
    section7SwapPerturbed = section7SwapA delta + section7SwapH delta := by
  ext x i
  fin_cases i
  · simp [section7SwapPerturbed, section7SwapA, section7SwapH,
      planarAmbient, Matrix.toLpLin_apply]
  · simp [section7SwapPerturbed, section7SwapA, section7SwapH,
      planarAmbient, Matrix.toLpLin_apply]

/-- The coordinate line is the zero spectral block of `A`. -/
theorem section7SwapA_exact_block (delta : ℝ) :
    section7SwapA delta ∘L planarExactMap = 0 := by
  ext i
  fin_cases i
  · simp [section7SwapA, planarAmbient, planarModelE0,
      Matrix.toLpLin_apply]
  · simp [section7SwapA, planarAmbient, planarModelE0,
      Matrix.toLpLin_apply]

/-- The complementary coordinate line is the `delta` spectral block of `A`. -/
theorem section7SwapA_complement_block (delta : ℝ) :
    section7SwapA delta ∘L planarComplementMap =
      ((delta : ℝ) : ℂ) • planarComplementMap := by
  ext i
  fin_cases i
  · simp [section7SwapA, planarAmbient, planarModelE1,
      Matrix.toLpLin_apply]
  · simp [section7SwapA, planarAmbient, planarModelE1,
      Matrix.toLpLin_apply]

/-- The perturbed operator fixes the line at angle `pi / 4`; hence that line is
a reducing eigenspace of the Hermitian coordinate flip. -/
theorem section7SwapPerturbed_trial_eigenline :
    section7SwapPerturbed ∘L planarTrialMap (Real.pi / 4) =
      planarTrialMap (Real.pi / 4) := by
  ext i
  fin_cases i
  · simp [section7SwapPerturbed, planarTrialMap, scalarColumn,
      planarModelE0, planarModelE1, Matrix.toLpLin_apply,
      Real.sin_pi_div_four, Real.cos_pi_div_four]
  · simp [section7SwapPerturbed, planarTrialMap, scalarColumn,
      planarModelE0, planarModelE1, Matrix.toLpLin_apply,
      Real.sin_pi_div_four, Real.cos_pi_div_four]

/-- The residual row for the coordinate trial line is the unit complementary
column. -/
def section7SwapResidual : ℂ →L[ℂ] Plane :=
  planarComplementMap

/-- The residual is exactly `(A + H) E0 - E0 A0` with `A0 = 0`. -/
theorem section7SwapResidual_identity :
    section7SwapPerturbed ∘L planarExactMap -
        planarExactMap ∘L planarTrialOperator =
      section7SwapResidual := by
  ext i
  fin_cases i
  · simp [section7SwapPerturbed, section7SwapResidual,
      planarExactMap, planarComplementMap, scalarColumn,
      planarTrialOperator, planarModelE0, planarModelE1,
      Matrix.toLpLin_apply]
  · simp [section7SwapPerturbed, section7SwapResidual,
      planarExactMap, planarComplementMap, scalarColumn,
      planarTrialOperator, planarModelE0, planarModelE1,
      Matrix.toLpLin_apply]

/-- A singular-value representative of the directed `sin 2 Theta_0` block.
The selected eigenspace is at angle `pi / 4`, so its doubled sine is one. -/
def section7SwapSinTwoTheta0 : ℂ →L[ℂ] Plane :=
  planarSineBlock (2 * (Real.pi / 4))

/-- The doubled directed sine representative is the unit complementary
column. -/
theorem section7SwapSinTwoTheta0_eq_complement :
    section7SwapSinTwoTheta0 = planarComplementMap := by
  rw [section7SwapSinTwoTheta0, planarSineBlock]
  have hangle : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [hangle, Real.sin_pi_div_two]
  simp

/-- Every normalized source unitary-invariant norm gives residual norm one. -/
theorem section7SwapResidual_gauge (N : SymmetricNormingFunction) :
    N.gauge section7SwapResidual = 1 := by
  have hV := planarComplementMap_norm_rank (𝕜 := ℂ)
  exact N.gauge_rankOne hV.1 hV.2

/-- Every normalized source unitary-invariant norm gives the doubled directed
sine block norm one. -/
theorem section7SwapSinTwoTheta0_gauge (N : SymmetricNormingFunction) :
    N.gauge section7SwapSinTwoTheta0 = 1 := by
  rw [section7SwapSinTwoTheta0_eq_complement]
  have hV := planarComplementMap_norm_rank (𝕜 := ℂ)
  exact N.gauge_rankOne hV.1 hV.2

/-- The two sides highlighted by Davis--Kahan are exactly `2` and `delta`. -/
theorem section7Swap_quantities (N : SymmetricNormingFunction) (delta : ℝ) :
    2 * N.gauge section7SwapResidual = 2 ∧
      delta * N.gauge section7SwapSinTwoTheta0 = delta := by
  rw [section7SwapResidual_gauge, section7SwapSinTwoTheta0_gauge]
  simp

/-- **Davis--Kahan 1970, Section 7 swap-asymmetry counterexample.**
For every source gap `delta > 2`, the residual conclusion obtained by an
illegitimate swap fails: `2 ||R|| < delta ||sin 2 Theta_0||`.  Since `delta`
is arbitrary, the left side of the proposed estimate can be made as large as
desired while `2 ||R|| = 2`. -/
theorem section7_residual_inference_cannot_be_swapped
    (N : SymmetricNormingFunction) {delta : ℝ} (hdelta : 2 < delta) :
    2 * N.gauge section7SwapResidual <
      delta * N.gauge section7SwapSinTwoTheta0 := by
  rw [section7SwapResidual_gauge, section7SwapSinTwoTheta0_gauge]
  simpa using hdelta

end

end Section7SwapAsymmetry
end DavisKahan1970
end TauCeti
