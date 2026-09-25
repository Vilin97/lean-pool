/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.QuadraticCarleson.QuadraticCarleson.PaperTheorems

/-!
# Statement solution surface

The statement-level definitions are repeated under
`QuadraticCarleson.StatementSurface`
so Comparator can compare this module independently with `Challenge.lean`.
Each theorem is then obtained by definitional transport from the canonical
theorem in `QuadraticCarleson.PaperTheorems`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology


namespace QuadraticCarleson.StatementSurface

/-- The unit complex phase with exponent `2πis` used in the statement surface. -/
noncomputable def phase (s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)

/-- The iterated logarithm with additive shift ten at each iteration. -/
noncomputable def paperLog : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => fun t => Real.log (10 + paperLog n t)

/-- Little-o growth relative to the endpoint function `t * paperLog 2 t` at infinity. -/
def GrowsSlowerThanEndpoint (Phi : YoungFunction) : Prop :=
  (fun t : ℝ => Phi t) =o[atTop] (fun t : ℝ => t * paperLog 2 t)

/-- The quadratic Hilbert integral truncated outside the symmetric interval of radius epsilon. -/
noncomputable def quadraticHilbertTrunc
    (modulation epsilon : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in {t : ℝ | epsilon < |t|}, f (x - t) * phase (modulation * t ^ 2) / (t : ℂ)

/-- Convergence of the truncated quadratic Hilbert integrals as the positive cutoff tends to
zero. -/
def HasQuadraticPrincipalValue (modulation : ℝ) (f : ℝ → ℂ) (x : ℝ) (z : ℂ) : Prop :=
  Tendsto (fun epsilon : ℝ => quadraticHilbertTrunc modulation epsilon f x)
    (nhdsWithin 0 (Ioi 0)) (nhds z)

/-- The dyadic modulation corresponding to an integer exponent. -/
noncomputable def dyadicModulation (n : ℤ) : ℝ :=
  (2 : ℝ) ^ n

/-- The chosen quadratic principal value when it exists, and zero otherwise. -/
noncomputable def principalValueRepresentative (lam : ℝ) (f : L0Infinity) (x : ℝ) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, HasQuadraticPrincipalValue lam f x z then h.choose else 0

/-- The supremum of principal-value norms over all real modulations. -/
noncomputable def fullPrincipalValueMaximal (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : ℝ, ENNReal.ofReal ‖principalValueRepresentative lam f x‖

/-- The supremum of principal-value norms over the dyadic modulation sequence. -/
noncomputable def lacunaryPrincipalValueMaximal (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℤ, ENNReal.ofReal ‖principalValueRepresentative (dyadicModulation m) f x‖

/-- The set where the operator on a test function exceeds the specified real level. -/
def functionOperatorLevelSet
    (T : L0Infinity → ℝ → ℝ≥0∞) (f : L0Infinity) (alpha : ℝ) : Set ℝ :=
  {x | ENNReal.ofReal alpha < T f x}

/-- A uniform distributional estimate by the Young-function modular of each normalized test
input. -/
def HasFunctionPhiModularEstimate
    (Phi : YoungFunction) (T : L0Infinity → ℝ → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (alpha : ℝ), 0 < alpha →
    volume (functionOperatorLevelSet T f alpha) ≤
      ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (Phi (‖f x‖ / alpha))

namespace PaperTheorems


theorem lacunary_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi lacunaryPrincipalValueMaximal := by
  exact QuadraticCarleson.PaperTheorems.lacunary_sub_log2_modular_failure Phi hPhi

theorem full_sub_log2_modular_failure
    (Phi : YoungFunction) (hPhi : GrowsSlowerThanEndpoint Phi) :
    ¬HasFunctionPhiModularEstimate Phi fullPrincipalValueMaximal := by
  exact QuadraticCarleson.PaperTheorems.full_sub_log2_modular_failure Phi hPhi

theorem full_LlogL_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ lam : ℝ,
        HasQuadraticPrincipalValue lam f x (principalValueRepresentative lam f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < fullPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  exact QuadraticCarleson.PaperTheorems.full_LlogL_endpoint

theorem lacunary_log2_squared_log4_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  exact QuadraticCarleson.PaperTheorems.lacunary_log2_squared_log4_endpoint

end PaperTheorems
end QuadraticCarleson.StatementSurface
