/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LoweringDerivation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree

/-!
# API checks for the quotient `P̂/I`

The quotient `P̂/I` satisfies two conclusions of different strength: the ideal `I` is prime,
equivalently `P̂/I` is a domain, and `P̂/I` is geometrically integral over `K`.

Geometric integrality is strictly stronger than integrality over `K`: tensoring with every field
extension must give a domain, with no finiteness or separability hypothesis.

The separate nontriviality statement matters because a quotient by the whole ring would satisfy
the no-zero-divisors condition vacuously, while `IsDomain` also requires `0 ≠ 1`.
-/

open scoped TensorProduct

public noncomputable section

namespace Tests

open Berarducci
open Berarducci

universe v

variable {K : Type v} [Field K]

variable (K) in
/-- The ideal `I = I_{≥1}` is proper, so the quotient `P̂/I` is nontrivial, over every field. -/
theorem coefficientIdeal_ne_top :
    principalFibreIdeal K ≠ ⊤ :=
  fun h ↦ LoweringDerivation.one_notMem_fibreIdeal _ (h ▸ Submodule.mem_top)

variable [CharZero K]

variable (K) in
/-- The quotient `P̂/I` is a domain. -/
theorem coefficientQuotient_isDomain :
    IsDomain (PrincipalFibre K) :=
  principalFibre_isDomain K

variable (K) in
/-- Tensoring `P̂/I` with an arbitrary field extension gives a domain. -/
theorem coefficientQuotient_isDomain_tensor (L : Type (max 1 v)) [Field L] [Algebra K L] :
    IsDomain (PrincipalFibre K ⊗[K] L) :=
  Algebra.isGeometricallyIntegral_iff.mp
    (principalFibre_isGeometricallyIntegral K) L

variable (K) in
/-- The quotient `P̂/I` is geometrically integral over `K`. -/
theorem coefficientQuotient_isGeometricallyIntegral :
    Algebra.IsGeometricallyIntegral K (PrincipalFibre K) :=
  principalFibre_isGeometricallyIntegral K

end Tests
