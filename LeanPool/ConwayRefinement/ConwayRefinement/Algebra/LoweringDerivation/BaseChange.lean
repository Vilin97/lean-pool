/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Correction
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient

import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.CharP.Algebra

/-!
# Extension of the coefficient field

Let `A` (Lean `R`) be a `NatOrdinal`-graded algebra over a field `K` with grading `𝒜` and a
lowering derivation `∂` (Lean `Δ`), and let `E / K` be a field extension. The `E`-algebra
`E ⊗_K A` is graded by the base-changed submodules `E ⊗_K A_α`, and the composite

`∂_E = θ ∘ (1 ⊗ ∂) : E ⊗ A → E ⊗ Fun_{0⁻}(A) → Fun_{0⁻}(E ⊗ A)`,

where `θ` is the pointwise tensor map, is again a lowering derivation: the Leibniz rule extends
bilinearly, and injectivity on `E ⊗_K A_{α+1}` follows from the injectivity of `θ`, `E` being
flat over `K`. Degree zero is still the scalars, and `(E ⊗_K A)/I = E ⊗_K (A/I)`. Consequently,
whenever `E ⊗_K A` is a domain, so is `E ⊗_K (A/I)`.
-/

universe u u' v

open scoped DirectSum TensorProduct
open Filter Topology

public noncomputable section

namespace LoweringDerivation

variable {K : Type u} {E : Type u'} {R : Type v} [Field K] [Field E] [Algebra K E]
variable [CommRing R] [Algebra K R]

/-! ### Functions at `0⁻` with values in a tensor product -/

section TensorFunAtZeroMinus

variable (K E R)

/-- The pointwise tensor map `e ⊗ g ↦ (γ ↦ e ⊗ g(γ))`. -/
def tensorFunAtZeroMinusLeft (e : E) : FunAtZeroMinus R →ₗ[K] FunAtZeroMinus (E ⊗[K] R) :=
  Filter.Germ.mapLinear (TensorProduct.mk K E R e)

theorem tensorFunAtZeroMinusLeft_coe (e : E) (f : ℝ → R) :
    tensorFunAtZeroMinusLeft K E R e (f : FunAtZeroMinus R) =
      ((fun γ ↦ e ⊗ₜ[K] f γ : ℝ → E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) := by
  rw [tensorFunAtZeroMinusLeft, Filter.Germ.mapLinear_coe]
  rfl

/-- The canonical map `θ : E ⊗ Fun_{0⁻}(A) → Fun_{0⁻}(E ⊗ A)`. -/
def tensorFunAtZeroMinus : E ⊗[K] FunAtZeroMinus R →ₗ[E] FunAtZeroMinus (E ⊗[K] R) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := tensorFunAtZeroMinusLeft K E R
      map_add' := fun e e' ↦ LinearMap.ext fun g ↦ by
        induction g using Filter.Germ.inductionOn with
        | _ f =>
          rw [LinearMap.add_apply, tensorFunAtZeroMinusLeft_coe, tensorFunAtZeroMinusLeft_coe,
            tensorFunAtZeroMinusLeft_coe]
          change _ = ((fun γ ↦ e ⊗ₜ[K] f γ + e' ⊗ₜ[K] f γ : ℝ → E ⊗[K] R) :
            FunAtZeroMinus (E ⊗[K] R))
          congr 1
          funext γ
          rw [TensorProduct.add_tmul]
      map_smul' := fun c e ↦ LinearMap.ext fun g ↦ by
        induction g using Filter.Germ.inductionOn with
        | _ f =>
          rw [RingHom.id_apply, LinearMap.smul_apply, tensorFunAtZeroMinusLeft_coe,
            tensorFunAtZeroMinusLeft_coe]
          change _ = ((fun γ ↦ c • (e ⊗ₜ[K] f γ) : ℝ → E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R))
          congr 1 }

theorem tensorFunAtZeroMinus_tmul (e : E) (g : FunAtZeroMinus R) :
    tensorFunAtZeroMinus K E R (e ⊗ₜ[K] g) = tensorFunAtZeroMinusLeft K E R e g := by
  rw [tensorFunAtZeroMinus, TensorProduct.AlgebraTensorModule.lift_tmul]
  rfl

theorem tensorFunAtZeroMinus_tmul_coe (e : E) (f : ℝ → R) :
    tensorFunAtZeroMinus K E R (e ⊗ₜ[K] (f : FunAtZeroMinus R)) =
      ((fun γ ↦ e ⊗ₜ[K] f γ : ℝ → E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) := by
  rw [tensorFunAtZeroMinus_tmul, tensorFunAtZeroMinusLeft_coe]

theorem tensorFunAtZeroMinusLeft_mul_const (e e' : E) (g : FunAtZeroMinus R) (b : R) :
    tensorFunAtZeroMinusLeft K E R e g * ((e' ⊗ₜ[K] b : E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) =
      tensorFunAtZeroMinusLeft K E R (e * e') (g * (b : FunAtZeroMinus R)) := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [tensorFunAtZeroMinusLeft_coe]
    change _ =
      tensorFunAtZeroMinusLeft K E R (e * e') ((fun γ ↦ f γ * b : ℝ → R) : FunAtZeroMinus R)
    rw [tensorFunAtZeroMinusLeft_coe]
    change ((fun γ ↦ e ⊗ₜ[K] f γ * e' ⊗ₜ[K] b : ℝ → E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) = _
    congr 1
    funext γ
    rw [Algebra.TensorProduct.tmul_mul_tmul]

theorem const_mul_tensorFunAtZeroMinusLeft (e e' : E) (a : R) (g : FunAtZeroMinus R) :
    ((e ⊗ₜ[K] a : E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) * tensorFunAtZeroMinusLeft K E R e' g =
      tensorFunAtZeroMinusLeft K E R (e * e') ((a : FunAtZeroMinus R) * g) := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [tensorFunAtZeroMinusLeft_coe]
    change _ =
      tensorFunAtZeroMinusLeft K E R (e * e') ((fun γ ↦ a * f γ : ℝ → R) : FunAtZeroMinus R)
    rw [tensorFunAtZeroMinusLeft_coe]
    change ((fun γ ↦ e ⊗ₜ[K] a * e' ⊗ₜ[K] f γ : ℝ → E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) = _
    congr 1
    funext γ
    rw [Algebra.TensorProduct.tmul_mul_tmul]

end TensorFunAtZeroMinus

/-! ### The base-changed derivation -/

variable (E) in
/-- The base change `∂_E = θ ∘ (1 ⊗ ∂)` of a derivation with values in functions at `0⁻`. -/
def baseChangeDerivation (Δ : R →ₗ[K] FunAtZeroMinus R) :
    E ⊗[K] R →ₗ[E] FunAtZeroMinus (E ⊗[K] R) :=
  (tensorFunAtZeroMinus K E R).comp (Δ.baseChange E)

theorem baseChangeDerivation_tmul (Δ : R →ₗ[K] FunAtZeroMinus R) (e : E) (x : R) :
    baseChangeDerivation E Δ (e ⊗ₜ[K] x) = tensorFunAtZeroMinusLeft K E R e (Δ x) := by
  rw [baseChangeDerivation, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    tensorFunAtZeroMinus_tmul]

variable {𝒜 : NatOrdinal → Submodule K R} [GradedAlgebra 𝒜]

/-- The base change of the grading: `E ⊗_K A_α`. -/
abbrev baseChangeGrading (E : Type u') [Field E] [Algebra K E] (𝒜 : NatOrdinal → Submodule K R) :
    NatOrdinal → Submodule E (E ⊗[K] R) :=
  fun α ↦ (𝒜 α).baseChange E

omit [GradedAlgebra 𝒜] in
theorem gradeZeroScalars_baseChange (h0 : GradeZeroScalars 𝒜) :
    GradeZeroScalars (baseChangeGrading E 𝒜) := by
  rw [gradeZeroScalars_iff] at h0 ⊢
  intro x hx
  obtain ⟨x', rfl⟩ := hx
  induction x' using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul e a =>
    obtain ⟨k, hk⟩ := h0 a a.2
    refine ⟨k • e, ?_⟩
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, hk,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_self_apply]
  | add x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨k', hk'⟩ := hy
    exact ⟨k + k', by rw [map_add, hk, hk', map_add]⟩

namespace IsLoweringDerivation

variable {Δ : R →ₗ[K] FunAtZeroMinus R} (hΔ : IsLoweringDerivation 𝒜 Δ)
include hΔ

omit [GradedAlgebra 𝒜] in
theorem baseChangeDerivation_mul (x y : E ⊗[K] R) :
    baseChangeDerivation E Δ (x * y) =
      baseChangeDerivation E Δ x * (y : FunAtZeroMinus _) +
        (x : FunAtZeroMinus _) * baseChangeDerivation E Δ y := by
  have hconst_add : ∀ u v : E ⊗[K] R, ((u + v : E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) =
    (u : FunAtZeroMinus (E ⊗[K] R)) + (v : FunAtZeroMinus (E ⊗[K] R)) := fun _ _ ↦ rfl
  have hconst_zero : ((0 : E ⊗[K] R) : FunAtZeroMinus (E ⊗[K] R)) = 0 := rfl
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul, hconst_zero, zero_mul, add_zero]
  | tmul e a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero, hconst_zero, mul_zero, add_zero]
    | tmul e' b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeDerivation_tmul, baseChangeDerivation_tmul,
        baseChangeDerivation_tmul, hΔ.map_mul, map_add, tensorFunAtZeroMinusLeft_mul_const,
        const_mul_tensorFunAtZeroMinusLeft]
    | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, hconst_add, mul_add, mul_add]
      abel
  | add x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, hconst_add, add_mul, add_mul]
    abel

omit hΔ [GradedAlgebra 𝒜] in
/-- Membership statements for `∂_E` reduce to pure tensors `e ⊗ a` with `a ∈ A_α`. -/
theorem baseChange_induction {α : NatOrdinal} (P : Submodule E (FunAtZeroMinus (E ⊗[K] R)))
    (h : ∀ (e : E) (a : R), a ∈ 𝒜 α → baseChangeDerivation E Δ (e ⊗ₜ[K] a) ∈ P)
    {x : E ⊗[K] R} (hx : x ∈ (𝒜 α).baseChange E) : baseChangeDerivation E Δ x ∈ P := by
  obtain ⟨x', rfl⟩ := hx
  induction x' using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact P.zero_mem
  | tmul e a =>
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
    exact h e a a.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact P.add_mem hx hy

omit [GradedAlgebra 𝒜] in
theorem baseChangeDerivation_mem_lower {α : NatOrdinal} (hα : 0 < α.constantCoeff) {x : E ⊗[K] R}
    (hx : x ∈ (𝒜 α).baseChange E) :
    baseChangeDerivation E Δ x ∈ funAtZeroMinusSubmodule ((𝒜 (α.removeNat 1)).baseChange E) := by
  refine baseChange_induction _ (fun e a ha ↦ ?_) hx
  obtain ⟨f, hf, hfeq⟩ := exists_coe_eq_of_mem_funAtZeroMinusSubmodule _ (hΔ.mem_lower hα ha)
  rw [baseChangeDerivation_tmul, hfeq, tensorFunAtZeroMinusLeft_coe,
    coe_mem_funAtZeroMinusSubmodule_iff]
  exact Eventually.of_forall fun γ ↦ Submodule.tmul_mem_baseChange_of_mem e (hf γ)

omit [GradedAlgebra 𝒜] in
theorem baseChangeDerivation_eq_zero {α : NatOrdinal} (hα : α.constantCoeff = 0) {x : E ⊗[K] R}
    (hx : x ∈ (𝒜 α).baseChange E) : baseChangeDerivation E Δ x = 0 := by
  have := baseChange_induction (Δ := Δ) (⊥ : Submodule E (FunAtZeroMinus (E ⊗[K] R)))
    (fun e a ha ↦ by rw [baseChangeDerivation_tmul, hΔ.eq_zero hα ha, map_zero]; exact rfl) hx
  exact (Submodule.mem_bot E).mp this

/-- `∂` on `A_α`, `α` a successor, as a map into functions at `0⁻` with values in the degree one
below (Lean `𝒜 (α.removeNat 1)`). -/
def derivLinearAt {α : NatOrdinal} (hα : 0 < α.constantCoeff) :
    𝒜 α →ₗ[K] FunAtZeroMinus (𝒜 (α.removeNat 1)) :=
  (funAtZeroMinusSubmoduleEquiv (𝒜 (α.removeNat 1))).symm.toLinearMap.comp
    ((Δ.comp (𝒜 α).subtype).codRestrict _ fun a ↦ hΔ.mem_lower hα a.2)

omit [GradedAlgebra 𝒜] in
theorem funAtZeroMinusSubmoduleMap_derivLinearAt {α : NatOrdinal} (hα : 0 < α.constantCoeff)
    (a : 𝒜 α) :
    funAtZeroMinusSubmoduleMap _ (hΔ.derivLinearAt hα a) = Δ a := by
  rw [derivLinearAt, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← coe_funAtZeroMinusSubmoduleEquiv_apply, LinearEquiv.apply_symm_apply]
  rfl

omit [GradedAlgebra 𝒜] in
theorem derivLinearAt_injective {α : NatOrdinal} (hα : 0 < α.constantCoeff) :
    Function.Injective (hΔ.derivLinearAt hα) := by
  intro a a' h
  apply Subtype.ext
  refine sub_eq_zero.mp (hΔ.injective hα ((𝒜 α).sub_mem a.2 a'.2) ?_)
  rw [map_sub, ← hΔ.funAtZeroMinusSubmoduleMap_derivLinearAt hα,
    ← hΔ.funAtZeroMinusSubmoduleMap_derivLinearAt hα,
    h, sub_self]

/-- The embedding `A_{α'} ⊗ E → E ⊗ A`, `α'` the degree one below `α`. -/
def lowerGradeTensorEmbedding (α : NatOrdinal) : 𝒜 (α.removeNat 1) ⊗[K] E →ₗ[K] E ⊗[K] R :=
  ((𝒜 (α.removeNat 1)).subtype.baseChange E).restrictScalars K ∘ₗ
    (TensorProduct.comm K (𝒜 (α.removeNat 1)) E).toLinearMap

omit hΔ [GradedAlgebra 𝒜] in
theorem lowerGradeTensorEmbedding_injective (α : NatOrdinal) :
    Function.Injective (lowerGradeTensorEmbedding (𝒜 := 𝒜) (E := E) α) := by
  have h1 : Function.Injective ((𝒜 (α.removeNat 1)).subtype.baseChange E) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  intro x y h
  exact (TensorProduct.comm K _ E).injective (h1 h)

omit [GradedAlgebra 𝒜] in
theorem baseChangeDerivation_baseChange {α : NatOrdinal} (hα : 0 < α.constantCoeff)
    (x : 𝒜 α ⊗[K] E) :
    baseChangeDerivation E Δ ((𝒜 α).subtype.baseChange E (TensorProduct.comm K _ _ x)) =
      Filter.Germ.mapLinear (lowerGradeTensorEmbedding α)
        (funAtZeroMinusTensorId (hΔ.derivLinearAt hα) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    obtain ⟨f, hf⟩ : ∃ f : ℝ → 𝒜 (α.removeNat 1), hΔ.derivLinearAt hα a = (f : FunAtZeroMinus _) :=
      ⟨Quotient.out _, (Quotient.out_eq _).symm⟩
    rw [TensorProduct.comm_tmul, LinearMap.baseChange_tmul, baseChangeDerivation_tmul,
      funAtZeroMinusTensorId_tmul_of_eq_coe _ _ _ _ hf, Filter.Germ.mapLinear_coe]
    have hΔa : Δ a = ((fun γ ↦ (f γ : R)) : FunAtZeroMinus R) := by
      rw [← hΔ.funAtZeroMinusSubmoduleMap_derivLinearAt hα, hf, funAtZeroMinusSubmoduleMap_coe]
    rw [Submodule.subtype_apply, hΔa, tensorFunAtZeroMinusLeft_coe]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

omit [GradedAlgebra 𝒜] in
theorem baseChangeDerivation_injective {α : NatOrdinal} (hα : 0 < α.constantCoeff) {x : E ⊗[K] R}
    (hx : x ∈ (𝒜 α).baseChange E) (h : baseChangeDerivation E Δ x = 0) : x = 0 := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨x'', rfl⟩ := (TensorProduct.comm K (𝒜 α) E).surjective x'
  rw [hΔ.baseChangeDerivation_baseChange hα] at h
  have h1 := Filter.Germ.mapLinear_injective _
    (lowerGradeTensorEmbedding_injective (𝒜 := 𝒜) (E := E) α)
    (by rw [h, map_zero] : Filter.Germ.mapLinear (lowerGradeTensorEmbedding α)
      (funAtZeroMinusTensorId (hΔ.derivLinearAt hα) x'') = Filter.Germ.mapLinear _ 0)
  have h2 : x'' = 0 := funAtZeroMinusTensorId_injective_of_injective _
    (hΔ.derivLinearAt_injective hα) (by rw [h1, map_zero])
  rw [h2, map_zero, map_zero]

omit [GradedAlgebra 𝒜] in
/-- The base change of a lowering derivation is a lowering derivation for the base-changed
grading. -/
theorem baseChange :
    IsLoweringDerivation (baseChangeGrading E 𝒜) (baseChangeDerivation E Δ) where
  map_mul := hΔ.baseChangeDerivation_mul
  mem_lower hα _ hx := hΔ.baseChangeDerivation_mem_lower hα hx
  eq_zero hα _ hx := hΔ.baseChangeDerivation_eq_zero hα hx
  injective hα _ hx h := hΔ.baseChangeDerivation_injective hα hx h

end IsLoweringDerivation

/-! ### The quotient of the base change -/

variable (E 𝒜)

omit [GradedAlgebra 𝒜] in
theorem fibreIdeal_baseChange :
    fibreIdeal (baseChangeGrading E 𝒜) =
      (fibreIdeal 𝒜).map (Algebra.TensorProduct.includeRight : R →ₐ[K] E ⊗[K] R) := by
  rw [fibreIdeal, fibreIdeal, idealGE_eq_span, idealGE_eq_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_))
  · intro x hx
    obtain ⟨e, hje, x', rfl⟩ := (mem_idealGEGenerators_iff _ 1 x).mp hx
    clear hx
    induction x' using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul c a =>
      rw [LinearMap.baseChange_tmul, Submodule.subtype_apply,
        show c ⊗ₜ[K] (a : R) = (c ⊗ₜ[K] (1 : R)) *
            (Algebra.TensorProduct.includeRight (R := K) (A := E) (a : R)) by
          rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
        (Ideal.subset_span ((mem_idealGEGenerators_iff 𝒜 1 _).mpr ⟨e, hje, a.2⟩)))
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro a ha
    obtain ⟨e, hje, hae⟩ := (mem_idealGEGenerators_iff 𝒜 1 a).mp ha
    refine Ideal.subset_span ((mem_idealGEGenerators_iff _ 1 _).mpr ⟨e, hje, ?_⟩)
    rw [Algebra.TensorProduct.includeRight_apply]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hae

/-- `(E ⊗_K A)/I = E ⊗_K (A/I)`: the quotient of the base change is the base change of the
quotient. -/
def fibreBaseChangeEquiv : E ⊗[K] Fibre 𝒜 ≃ₐ[E] Fibre (baseChangeGrading E 𝒜) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) E R E (fibreIdeal 𝒜)).trans
    (Ideal.quotientEquivAlgOfEq E (fibreIdeal_baseChange E 𝒜).symm)

/-- If `E ⊗_K A` is a domain, so is `E ⊗_K (A/I)`: the base change is again a graded domain over
`E` with a lowering derivation, and its quotient is `E ⊗_K (A/I)`. -/
theorem isDomain_tensor_fibre [CharZero K] [IsDomain (E ⊗[K] R)] (h0 : GradeZeroScalars 𝒜)
    {Δ : R →ₗ[K] FunAtZeroMinus R} (hΔ : IsLoweringDerivation 𝒜 Δ) :
    IsDomain (E ⊗[K] Fibre 𝒜) :=
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI := hΔ.baseChange.fibre_isDomain (gradeZeroScalars_baseChange (E := E) h0)
  (fibreBaseChangeEquiv E 𝒜).toMulEquiv.isDomain _

end LoweringDerivation
