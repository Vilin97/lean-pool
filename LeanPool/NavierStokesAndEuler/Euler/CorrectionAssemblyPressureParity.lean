/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyReconstruction

/-! Pointwise parity and canonical normalization of the assembled actual pressure. -/

@[expose] public section


noncomputable section

namespace EulerGraphPressurePotential

open EulerLiftedGradientSpace

/-- The physical phase graph respects joint spatial and angular reflection. -/
theorem cylinderGraph_neg (period k : ℝ) (m x : Vector3) :
    cylinderGraph period k m (-x) = -cylinderGraph period k m x := by
  simp [cylinderGraph]

end EulerGraphPressurePotential

namespace EulerCanonicalGraphPotential

open EulerLiftedGradientSpace

/-- The canonical radial scalar potential of an odd vector field is even.
This identity does not need a choice of additive gauge or a potential-existence assumption. -/
theorem radialPotential_even (V : Vector3 → Vector3)
    (hV : ∀ x, V (-x) = -V x) (x : Vector3) :
    radialPotential V (-x) = radialPotential V x := by
  simp only [radialPotential, smul_neg, hV, inner_neg_neg]

end EulerCanonicalGraphPotential

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerGraphPressurePotential EulerCanonicalGraphPotential
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The canonical pressure representative is pointwise odd, as a consequence
of genuine PDE uniqueness and parity of the prescribed data. -/
theorem FiniteFamily.pointPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointPressure period t (-x) = -F.pointPressure period t x :=
  continuous_representative_odd period (F.commonPressure period t)
    (F.pointPressure period t) (F.commonPressure_odd period C P t)
    (Continuous.uncurry_left t (F.pointPressure_joint_continuous period))
    (F.pointPressure_ae period t) x

/-- The actual signed pressure-gradient vector on the physical phase graph is odd. -/
theorem FiniteFamily.graphPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    F.graphPressure period k t (-x) = -F.graphPressure period k t x := by
  unfold FiniteFamily.graphPressure
  rw [cylinderGraph_neg, F.pointPressure_odd period C P, smul_neg]

/-- The origin-normalized scalar pressure is even at every time.
In particular parity is an exact identity, not merely equality modulo a constant. -/
theorem FiniteFamily.normalizedGraphPotential_even (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    F.normalizedGraphPotential period k t (-x) =
      F.normalizedGraphPotential period k t x :=
  radialPotential_even _ (F.graphPressure_odd period C P k t) x

/-- Any smooth potential of the same graph field agrees with the canonical
radial potential after subtracting its value at the origin. -/
theorem FiniteFamily.normalizedGraphPotential_eq_sub (F : FiniteFamily period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = F.graphPressure period k t x) (x : Vector3) :
    F.normalizedGraphPotential period k t x = q x - q 0 :=
  radialPotential_eq_sub _
    (Continuous.uncurry_left t (F.graphPressure_joint_continuous period k)) q hq hgrad x

/-- The constructed scalar pressure is the unique smooth potential of its
graph field with the prescribed zero value at the origin. -/
theorem FiniteFamily.normalizedGraphPotential_unique (F : FiniteFamily period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = F.graphPressure period k t x) (hq0 : q 0 = 0) :
    F.normalizedGraphPotential period k t = q := by
  funext x
  rw [F.normalizedGraphPotential_eq_sub period k t q hq hgrad x, hq0, sub_zero]

end EulerCorrectionAssembly
