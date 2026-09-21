/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.BaseChange
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.InternalGrading
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GeometricIntegrality
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SuccessorLeibniz
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus.Pointwise
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalIdealGE
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.BaseChange

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAtInjective
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# `(P̂, ∂)` is a graded domain over `K` with a lowering derivation

The ring `P̂ = ⨁ P_α` is internally graded by its components `P_α`, with `P_0 = K`, and the
maps `∂ : P_{α+1} → Fun_{0⁻}(P_α)` assemble into a single `K`-linear derivation
`∂ : P̂ → Fun_{0⁻}(P̂)`: the Leibniz identity on components of successor degree is the Leibniz
rule (D1) for `∂`, `∂` lowers the degree by one by construction (D2), and `∂` is injective on every
component of successor degree (D3). Hence `(P̂, ∂)` is a graded domain over `K` with a lowering
derivation (prop:P-lowering); the ideals `I_{≥j}` and the quotient `P̂/I` of the abstract theory are
those of `P̂`.

The grading and `∂` exist over every coefficient field. In characteristic zero the abstract
structure theorem gives that `P̂/I` is a domain, and, applied to the base change `E ⊗[K] P̂` (a
domain, being a subring of the domain `P̂_E`), that `E ⊗[K] P̂/I` is a domain for every field
extension `E / K`: `P̂/I` is geometrically integral over `K`.
-/

universe v

open Filter Topology
open scoped DirectSum HahnSeries NatOrdinal TensorProduct

public noncomputable section

namespace Berarducci

open Berarducci LoweringDerivation

variable {K : Type v} [Field K]

/-! ### The derivation `∂` of `P̂` -/

variable (K) in
/-- `∂` on a single homogeneous component `P_α`, valued in `Fun_{0⁻}(P̂)`: for `α` a successor,
`∂` on `P_α` followed by the inclusion of the component `P_{α⁻}` indexed by its predecessor
into `P̂`; zero for `α` zero or a
limit (D2). -/
def principalComponentDerivation (α : NatOrdinal) :
    PrincipalComponent K α →ₗ[K] FunAtZeroMinus (PrincipalSubring K) :=
  if hα : 0 < α.constantCoeff then
    (Filter.Germ.mapLinear (DirectSum.lof K NatOrdinal (PrincipalComponent K) (α.removeNat 1))).comp
      (principalComponentDerivAt K α hα)
  else 0

theorem principalComponentDerivation_of_pos {α : NatOrdinal} (hα : 0 < α.constantCoeff)
    (a : PrincipalComponent K α) :
    principalComponentDerivation K α a =
      Filter.Germ.mapLinear (DirectSum.lof K NatOrdinal (PrincipalComponent K) (α.removeNat 1))
        (principalComponentDerivAt K α hα a) := by
  rw [principalComponentDerivation, dif_pos hα, LinearMap.comp_apply]

theorem principalComponentDerivation_of_eq_zero {α : NatOrdinal} (hα : α.constantCoeff = 0)
    (a : PrincipalComponent K α) : principalComponentDerivation K α a = 0 := by
  rw [principalComponentDerivation, dif_neg (by omega), LinearMap.zero_apply]

/-- For `α` a successor, `∂` of the class of `u` is the function at `0⁻` `γ ↦ ∂(u)(γ)`, the class
of the translated truncation `u^{|γ}` in `P_{α⁻}` included into `P̂`. -/
theorem principalComponentDerivation_principalComponentMk
    {α : NatOrdinal} (hα : 0 < α.constantCoeff)
    (u : Series K) (hu : ordinalValue u < ω^ (α + 1)) :
    principalComponentDerivation K α (principalComponentMk α u hu) =
      ((fun γ ↦ DirectSum.of (PrincipalComponent K) (α.removeNat 1) (derivAt α u γ) :
        ℝ → PrincipalSubring K) : FunAtZeroMinus (PrincipalSubring K)) := by
  rw [principalComponentDerivation_of_pos hα, principalComponentDerivAt_principalComponentMk,
    Filter.Germ.mapLinear_coe]
  rfl

variable (K) in
/-- The derivation `∂ : P̂ → Fun_{0⁻}(P̂)`: `∂ : P_{α+1} → Fun_{0⁻}(P_α) ⊆ Fun_{0⁻}(P̂)` on each
component of successor degree, extended `K`-linearly, vanishing on components indexed by limit
ordinals
and of degree `0`. -/
def principalSubringDerivation : PrincipalSubring K →ₗ[K] FunAtZeroMinus (PrincipalSubring K) :=
  DirectSum.toModule K NatOrdinal _ (principalComponentDerivation K)

theorem principalSubringDerivation_of (α : NatOrdinal) (a : PrincipalComponent K α) :
    principalSubringDerivation K (DirectSum.of (PrincipalComponent K) α a) =
      principalComponentDerivation K α a := by
  rw [principalSubringDerivation, ← DirectSum.lof_eq_of K, DirectSum.toModule_lof]

/-- `∂` vanishes on scalars. -/
theorem principalSubringDerivation_algebraMap (k : K) :
    principalSubringDerivation K (algebraMap K (PrincipalSubring K) k) = 0 := by
  rw [principalSubring_algebraMap_apply, principalSubringDerivation_of,
    principalComponentDerivation_of_eq_zero NatOrdinal.constantCoeff_zero]

/-- The Leibniz rule for `∂` on homogeneous elements, in the main case: `α` a successor and
`β > 0`. The translated-truncation identity in `P_{(α+β)⁻}` is pushed into `Fun_{0⁻}(P̂)`. -/
private theorem principalSubringDerivation_of_mul_of_of_pos {α β : NatOrdinal}
    (hα : 0 < α.constantCoeff)
    (a : PrincipalComponent K α) (b : PrincipalComponent K β) :
    principalSubringDerivation K
        (DirectSum.of (PrincipalComponent K) α a * DirectSum.of (PrincipalComponent K) β b) =
      principalSubringDerivation K (DirectSum.of (PrincipalComponent K) α a) *
          ((DirectSum.of (PrincipalComponent K) β b : PrincipalSubring K) : FunAtZeroMinus _) +
        ((DirectSum.of (PrincipalComponent K) α a : PrincipalSubring K) : FunAtZeroMinus _) *
          principalSubringDerivation K (DirectSum.of (PrincipalComponent K) β b) := by
  obtain ⟨u, hu, rfl⟩ := exists_principalComponentMk α a
  obtain ⟨v, hv, rfl⟩ := exists_principalComponentMk β b
  have hsum : 0 < (α + β).constantCoeff := by
    rw [NatOrdinal.constantCoeff_add]; omega
  rw [← of_principalComponentMul, principalComponentMul_mk, principalSubringDerivation_of,
    principalSubringDerivation_of, principalSubringDerivation_of,
    principalComponentDerivation_principalComponentMk hsum,
    principalComponentDerivation_principalComponentMk hα]
  by_cases hβc : 0 < β.constantCoeff
  · rw [principalComponentDerivation_principalComponentMk hβc]
    change _ = ((fun γ ↦ _ : ℝ → PrincipalSubring K) : FunAtZeroMinus (PrincipalSubring K))
    rw [Filter.Germ.coe_eq]
    exact eventually_of_derivAt_mul_of_pos hα hβc u v hu hv
  · rw [principalComponentDerivation_of_eq_zero (by omega), mul_zero, add_zero]
    change _ = ((fun γ ↦ _ : ℝ → PrincipalSubring K) : FunAtZeroMinus (PrincipalSubring K))
    rw [Filter.Germ.coe_eq]
    exact eventually_of_derivAt_mul_of_eq_zero hα (by omega) u v hu hv

/-- The Leibniz rule for `∂` on homogeneous elements. -/
theorem principalSubringDerivation_of_mul_of (α β : NatOrdinal) (a : PrincipalComponent K α)
    (b : PrincipalComponent K β) :
    principalSubringDerivation K
        (DirectSum.of (PrincipalComponent K) α a * DirectSum.of (PrincipalComponent K) β b) =
      principalSubringDerivation K (DirectSum.of (PrincipalComponent K) α a) *
          ((DirectSum.of (PrincipalComponent K) β b : PrincipalSubring K) : FunAtZeroMinus _) +
        ((DirectSum.of (PrincipalComponent K) α a : PrincipalSubring K) : FunAtZeroMinus _) *
          principalSubringDerivation K (DirectSum.of (PrincipalComponent K) β b) := by
  -- Scalars: a degree-zero factor is a constant `k`, and `k v` represents `k • B`.
  rcases eq_or_ne α 0 with rfl | hα0
  · obtain ⟨k, rfl⟩ := principalComponentScalarHom_surjective K a
    rw [← principalSubring_algebraMap_apply, ← Algebra.smul_def, map_smul,
      principalSubringDerivation_algebraMap, zero_mul, zero_add,
      FunAtZeroMinus.const_algebraMap_mul]
  rcases eq_or_ne β 0 with rfl | hβ0
  · obtain ⟨k, rfl⟩ := principalComponentScalarHom_surjective K b
    rw [← principalSubring_algebraMap_apply, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
      principalSubringDerivation_algebraMap, mul_zero, add_zero,
      FunAtZeroMinus.mul_const_algebraMap]
  by_cases hαc : 0 < α.constantCoeff
  · exact principalSubringDerivation_of_mul_of_of_pos hαc a b
  by_cases hβc : 0 < β.constantCoeff
  · -- Symmetric case: apply the main case to `b * a`.
    have h := principalSubringDerivation_of_mul_of_of_pos hβc b a
    rw [mul_comm] at h
    rw [h, add_comm]
    simp only [mul_comm]
  · -- Neither grade is a successor: both sides vanish.
    have hsum : (α + β).constantCoeff = 0 := by
      rw [NatOrdinal.constantCoeff_add]; omega
    rw [← of_principalComponentMul, principalSubringDerivation_of, principalSubringDerivation_of,
      principalSubringDerivation_of, principalComponentDerivation_of_eq_zero hsum,
      principalComponentDerivation_of_eq_zero (by omega),
      principalComponentDerivation_of_eq_zero (by omega), zero_mul, mul_zero, add_zero]

/-- The Leibniz rule (D1) for `∂`. -/
@[blueprint "thm:leibniz-rule-lowering-derivation"
  (phase := "Translated truncations")
  (title := "Leibniz rule for the lowering derivation")
  (statement := /--
    Let $K$ be a field. On each successor component
    $\mathrm P_{\alpha+1}\subseteq\widehat{\mathrm P}$, let $\partial$ send a
    class represented by $b$ to the germ at $0^-$ of
    \[
      \gamma\longmapsto
      b^{\vert\gamma}+J_{\omega^\alpha}\in\mathrm P_\alpha,
    \]
    and let $\partial$ vanish on $\mathrm P_0$ and on components of limit
    degree. Extend this map $K$-linearly to
    \[
      \partial:\widehat{\mathrm P}\longrightarrow
      \operatorname{Fun}_{0^-}(\widehat{\mathrm P}).
    \]
    Then, for all $B,C\in\widehat{\mathrm P}$,
    \[
      \partial(BC)=\partial(B)C+B\partial(C)
    \]
    in $\operatorname{Fun}_{0^-}(\widehat{\mathrm P})$.
  -/)
  (proof := /--
  First suppose $B$ and $C$ are homogeneous. Degree-zero components are
  scalars, so the identity follows from $K$-linearity. For positive degrees,
  use \ref{fact:principal-series-representatives} to choose representatives.
  If the degree of $B$ is a
  successor, apply \ref{lem:convolution-formula} to $(BC)^{\vert\gamma}$. The two
  boundary terms give $\partial(B)C+B\partial(C)$; by
  \ref{lem:truncation-drop}, every interior term has smaller ordinal value and
  vanishes in the target component. The case where only the degree of $C$ is a
  successor follows by commutativity. If both positive degrees are limits,
  their natural sum is a limit and all three derivatives vanish.

  Finally decompose arbitrary $B$ and $C$ into their finite sums of homogeneous
  components. $K$-linearity of $\partial$ and distributivity extend the
  homogeneous identity to all of $\widehat{\mathrm P}$.
  -/)]
theorem principalSubringDerivation_mul (x y : PrincipalSubring K) :
    principalSubringDerivation K (x * y) =
      principalSubringDerivation K x * (y : FunAtZeroMinus _) +
        (x : FunAtZeroMinus _) * principalSubringDerivation K y := by
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul, FunAtZeroMinus.const_zero, zero_mul, add_zero]
  | of α a =>
    induction y using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero, FunAtZeroMinus.const_zero, mul_zero, add_zero]
    | of β b => exact principalSubringDerivation_of_mul_of α β a b
    | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, FunAtZeroMinus.const_add, mul_add, mul_add]
      abel
  | add x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, FunAtZeroMinus.const_add, add_mul, add_mul]
    abel

variable (K) in
/-- `∂` is a lowering derivation of `P̂` for its grading by the homogeneous components `P_α`: (D1)
the Leibniz
rule, (D2) `∂(P_{α+1}) ⊆ Fun_{0⁻}(P_α)` and `∂(P_α) = 0` for `α` zero or a limit, (D3) injectivity
on every `P_{α+1}`. With `P̂` a domain and `P_0 = K` this is prop:P-lowering: `(P̂, ∂)` is a
graded domain over `K` with a lowering derivation. -/
theorem principalSubringDerivation_isLoweringDerivation :
    IsLoweringDerivation (principalGrading K) (principalSubringDerivation K) where
  map_mul := principalSubringDerivation_mul
  mem_lower := by
    intro α hα x hx
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ x).mp hx
    rw [DirectSum.lof_eq_of, principalSubringDerivation_of,
      principalComponentDerivation_of_pos hα, principalGrading,
      DirectSum.rangeLof_eq_range]
    exact mapLinear_mem_funAtZeroMinusSubmodule_range
      (DirectSum.lof K NatOrdinal (PrincipalComponent K) (α.removeNat 1)) _
  eq_zero := by
    intro α hα x hx
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ x).mp hx
    rw [DirectSum.lof_eq_of, principalSubringDerivation_of,
      principalComponentDerivation_of_eq_zero hα]
  injective := by
    intro α hα x hx h
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ x).mp hx
    rw [DirectSum.lof_eq_of, principalSubringDerivation_of,
      principalComponentDerivation_of_pos hα] at h
    have h1 := Filter.Germ.mapLinear_injective _ (DirectSum.of_injective _) (by rw [h, map_zero] :
      Filter.Germ.mapLinear (DirectSum.lof K NatOrdinal (PrincipalComponent K) (α.removeNat 1))
        (principalComponentDerivAt K α hα a) = Filter.Germ.mapLinear _ 0)
    have h2 := principalComponentDerivAt_injective K α hα (by rw [h1, map_zero] :
      principalComponentDerivAt K α hα a = principalComponentDerivAt _ α hα 0)
    rw [h2, map_zero]

/-! ### The quotient `P̂/I` is a domain -/

variable [CharZero K]

variable (K) in
/-- The quotient `P̂/I` (Lean `PrincipalFibre K`) is an integral domain. -/
theorem principalFibre_isDomain :
    IsDomain (PrincipalFibre K) :=
  haveI : IsDomain (PrincipalSubring K) := principalSubringIsDomain
  (principalSubringDerivation_isLoweringDerivation K).fibre_isDomain
    (principalGrading_gradeZeroScalars K)

variable (K) in
/-- `E ⊗[K] P̂/I` is a domain for every field extension `E / K`, in every universe: the base
change `E ⊗[K] P̂` is a graded domain over `E` with a lowering derivation, its quotient is
`E ⊗[K] P̂/I`, and the quotient `A/I` of every such ring is a domain. -/
theorem isDomain_tensor_principalFibre (E : Type*) [Field E] [Algebra K E] :
    IsDomain (E ⊗[K] PrincipalFibre K) := by
  haveI := charZero_of_algebra K E
  haveI : IsDomain (E ⊗[K] PrincipalSubring K) := isDomain_tensor_principalSubring K E
  exact isDomain_tensor_fibre E (principalGrading K) (principalGrading_gradeZeroScalars K)
    (principalSubringDerivation_isLoweringDerivation K)

variable (K) in
/-- The quotient `P̂/I` is geometrically integral over `K`. -/
theorem principalFibre_isGeometricallyIntegral :
    Algebra.IsGeometricallyIntegral K (PrincipalFibre K) := by
  rw [Algebra.isGeometricallyIntegral_iff]
  intro E _ _
  haveI := isDomain_tensor_principalFibre K E
  exact (Algebra.TensorProduct.comm K _ _).toMulEquiv.isDomain _

variable (K) in
/-- `P̂/I ⊗[K] D` is a domain for every domain `D` over `K`, in every universe. -/
theorem isDomain_principalFibre_tensor (D : Type*) [CommRing D] [IsDomain D] [Algebra K D] :
    IsDomain (PrincipalFibre K ⊗[K] D) :=
  Algebra.isDomain_tensor_of_isDomain_of_forall_field
    (fun L _ _ ↦
      haveI := isDomain_tensor_principalFibre K L
      (Algebra.TensorProduct.comm K (PrincipalFibre K) L).toMulEquiv.isDomain _) D

end Berarducci
