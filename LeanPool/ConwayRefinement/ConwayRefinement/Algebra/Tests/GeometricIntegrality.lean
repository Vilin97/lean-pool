/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GeometricIntegrality

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# API checks for geometric integrality

The coefficient algebra is the nontrivial polynomial algebra `ℚ[V]`. After every field
extension `K / ℚ`, tensor commutativity and polynomial base change identify
`ℚ[V] ⊗[ℚ] K` with the domain `K[V]`. The geometric-integrality theorem is then applied to
the irreducible auxiliary polynomial `U`, proving that its coefficient extension generates a
prime ideal in `ℚ[V][U]`.

Using a nontrivial coefficient algebra ensures that this client exercises scalar extension rather
than reducing geometric integrality to the base field itself.
-/

open scoped TensorProduct

public noncomputable section

namespace Tests

/-- The polynomial coefficient algebra in the geometric-integrality fixture. -/
abbrev GeometricCoefficientAlgebra := MvPolynomial (Fin 1) ℚ

/-- A polynomial algebra over `ℚ` remains a domain after every field extension. -/
theorem geometricCoefficientAlgebra_isGeometricallyIntegral :
    Algebra.IsGeometricallyIntegral ℚ GeometricCoefficientAlgebra := by
  rw [Algebra.isGeometricallyIntegral_iff]
  intro K _ _
  let e : GeometricCoefficientAlgebra ⊗[ℚ] K ≃+* MvPolynomial (Fin 1) K :=
    (Algebra.TensorProduct.comm ℚ GeometricCoefficientAlgebra K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv ℚ K).toRingEquiv
  exact e.toMulEquiv.isDomain (MvPolynomial (Fin 1) K)

/-- The irreducible polynomial `U` over the base field. -/
def geometricLinearPolynomial : MvPolynomial (Fin 1) ℚ :=
  MvPolynomial.X 0

theorem geometricLinearPolynomial_irreducible :
    Irreducible geometricLinearPolynomial := by
  exact MvPolynomial.X_prime.irreducible

/-- Extending `U` to `ℚ[V][U]` and quotienting by it leaves a domain. -/
theorem geometricLinearPolynomial_baseChange_quotient_isDomain :
    IsDomain
      (MvPolynomial (Fin 1) GeometricCoefficientAlgebra ⧸
        Ideal.span
          {MvPolynomial.map (algebraMap ℚ GeometricCoefficientAlgebra)
            geometricLinearPolynomial}) :=
  geometricCoefficientAlgebra_isGeometricallyIntegral
    |>.isDomain_mvPolynomial_quotient_span_map
    geometricLinearPolynomial_irreducible

end Tests
