/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingCertificate
import LeanPool.PoincareThreeBody.PoincareSet

/-!
# Finite certificates for the classical Poincaré set

This file is the interface between verified numerical computation and the classical density
argument.  A certificate records one rational resonance, two orientations, a finite trapezoidal
sum, and a rigorous second-derivative error bound.  The analytic quadrature theorem turns that
finite data into membership in the exact Poincaré set.  Consequently, it is enough to prove that
the set of actions carrying such certificates is dense.
-/

namespace LeanPool.PoincareThreeBody

open scoped Interval

/-- Finite, checkable data proving that one interior action belongs to the classical Poincaré
set.  The second-derivative field is intended to be discharged by interval arithmetic, while the
last inequality is a finite trapezoidal computation. -/
structure ClassicalPoincareCertificate
    (action : InteriorProgradeEllipticAction) where
  p : ℕ
  q : ℕ
  hp : 0 < p
  hq : 0 < q
  firstAction_eq : action.1 0 = resonantFirstAction p q
  phaseA : ℝ
  phaseB : ℝ
  errorBound : ℝ
  steps : ℕ
  secondDerivative : ∀ time,
    |iteratedDerivWithin 2
      (resonantDisturbingDifference p q
        (eccentricityFromActions action.1) phaseA phaseB)
      [[0, resonantOrbitPeriod p]] time| ≤ errorBound
  steps_pos : 0 < steps
  trapezoidal_nonzero :
    |resonantOrbitPeriod p| ^ 3 * errorBound / (12 * steps ^ 2) <
      |trapezoidal_integral
        (resonantDisturbingDifference p q
          (eccentricityFromActions action.1) phaseA phaseB)
        steps 0 (resonantOrbitPeriod p)|

/-- Any action carrying a finite certificate belongs to the exact classical Poincaré set. -/
theorem ClassicalPoincareCertificate.mem_classicalPoincareSet
    {action : InteriorProgradeEllipticAction}
    (certificate : ClassicalPoincareCertificate action) :
    action ∈ classicalPoincareSet := by
  let eccentricity := eccentricityFromActions action.1
  have heccentricity : 0 ≤ eccentricity :=
    eccentricityFromActions_nonneg action.1
  have heccentricityOne : eccentricity < 1 :=
    eccentricityFromActions_lt_one action.2.1
  have hapoapsis : resonantFirstAction certificate.p certificate.q ^ 2 *
      (1 + eccentricity) < 1 := by
    rw [← certificate.firstAction_eq]
    exact action.2.2
  have hderivative :=
    exists_deriv_resonantDisturbingAverage_ne_zero_of_trapezoidal_certificate
      certificate.hp certificate.hq heccentricity heccentricityOne hapoapsis
      certificate.secondDerivative certificate.steps_pos
      certificate.trapezoidal_nonzero
  exact ⟨certificate.p, certificate.q, certificate.hp, certificate.hq,
    certificate.firstAction_eq, hderivative⟩

/-- The subset of interior actions whose Poincaré-set membership has been reduced to finite
validated numerical data. -/
def certifiedClassicalPoincareSet : Set InteriorProgradeEllipticAction :=
  {action | Nonempty (ClassicalPoincareCertificate action)}

theorem certifiedClassicalPoincareSet_subset_classicalPoincareSet :
    certifiedClassicalPoincareSet ⊆ classicalPoincareSet := by
  intro action hcertificate
  exact hcertificate.some.mem_classicalPoincareSet

/-- Density of finitely certified actions is sufficient for the exact classical Poincaré-set
hypothesis used by the nonintegrability argument. -/
theorem hasDenseClassicalPoincareSet_of_dense_certified
    (hdense : Dense certifiedClassicalPoincareSet) :
    HasDenseClassicalPoincareSet :=
  Dense.mono certifiedClassicalPoincareSet_subset_classicalPoincareSet hdense

end LeanPool.PoincareThreeBody
