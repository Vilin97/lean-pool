/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Positive scalar spectral measures for split abelian extensions.  This is the
analytic bridge used in Zhou's §4: the commuting kernel unitaries give a joint
functional calculus on the compact character space, vector states give
positive functionals, and the real Riesz--Markov--Kakutani theorem gives the
scalar spectral measures needed by finite spectral detection.  Working with
scalar measures avoids assuming a general projection-valued spectral theorem.

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 16868-16878,
16894-18024, and 18037-19073.
Modifications: adapted the positive-functional, projection, and joint
functional-calculus spine to local interfaces, moved the dual-action and
energy guards to their first consumer, and added the later Zhou-specific
extensions in this file.
See the upstream PORT_MAP.md.
-/
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Order.Hom.Esakia
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.Projection.ValuedSpectralMeasure

/-!
The positive spectral measure component of the Connes rigidity formalization.
-/

namespace Connes

noncomputable
section

open Connes MeasureTheory
open scoped ENNReal NNReal CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/--
The `spectralUnitTest` construction used in the Connes rigidity formalization.
-/
def spectralUnitTest (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun _ := 1
  continuous_toFun := continuous_const
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
@[simp] theorem spectralUnitTest_apply (χ : DiscreteCharacterSpace A) :
    spectralUnitTest A χ = 1 := rfl

/-- A positive spectral functional associated with a unitary representation. -/
structure PositiveSpectralFunctional
    (E : SplitAbelianExtension A G H)
    (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) where
  /--
  The `functional` component of `PositiveSpectralFunctional`.
  -/
  functional : V → C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ
  normalization : ∀ x : V,
    functional x (spectralUnitTest A) = ‖x‖ ^ 2
  energy : ∀ (x : V) (a : A),
    functional x (spectralEnergyTest a) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x - x‖ ^ 2
  covariance : ∀ (h : H) (x : V),
    (RealRMK.rieszMeasure (functional x)).map
      (dualCharacterAction E.action h) =
        RealRMK.rieszMeasure
          (functional ((π (E.splitting h) : V →L[ℂ] V) x))

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

/--
The `measure` construction used in the Connes rigidity formalization.
-/
def measure (Φ : PositiveSpectralFunctional E V π) (x : V) :
    Measure (DiscreteCharacterSpace A) :=
  RealRMK.rieszMeasure (Φ.functional x)

instance measure_regular
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    (Φ.measure x).Regular := by
  unfold measure
  infer_instance

instance measure_isFiniteMeasure
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    IsFiniteMeasure (Φ.measure x) := by
  unfold measure
  infer_instance

theorem integral_measure
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    (f : C_c(DiscreteCharacterSpace A, ℝ)) :
    (∫ χ, f χ ∂(Φ.measure x)) = Φ.functional x f := by
  exact RealRMK.integral_rieszMeasure (Φ.functional x) f

theorem measure_univ_real
    (Φ : PositiveSpectralFunctional E V π) (x : V) :
    (Φ.measure x).real Set.univ = ‖x‖ ^ 2 := by
  have h := Φ.integral_measure x (spectralUnitTest A)
  simpa only [spectralUnitTest_apply, integral_const, smul_eq_mul, mul_one,
    Φ.normalization x] using h

theorem measure_isProbabilityMeasure
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (hx : ‖x‖ = 1) :
    IsProbabilityMeasure (Φ.measure x) := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [Φ.measure_univ_real x, hx]
  norm_num

/--
The `probabilityMeasure` construction used in the Connes rigidity formalization.
-/
def probabilityMeasure
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (hx : ‖x‖ = 1) :
    ProbabilityMeasure (DiscreteCharacterSpace A) :=
  ⟨Φ.measure x, Φ.measure_isProbabilityMeasure x hx⟩

@[simp] theorem probabilityMeasure_toMeasure
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (hx : ‖x‖ = 1) :
    (Φ.probabilityMeasure x hx : Measure (DiscreteCharacterSpace A)) =
      Φ.measure x := rfl

theorem measure_energy
    (Φ : PositiveSpectralFunctional E V π)
    (x : V) (a : A) :
    (∫ χ : DiscreteCharacterSpace A,
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
        ∂(Φ.measure x)) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x - x‖ ^ 2 := by
  exact (Φ.integral_measure x (spectralEnergyTest a)).trans (Φ.energy x a)

theorem probabilityMeasure_invariant
    (Φ : PositiveSpectralFunctional E V π)
    (x : QuotientFixedUnitVector E V π) :
    IsInvariantSpectralMeasure E.action
      (Φ.probabilityMeasure x.vector x.norm_one) := by
  intro h
  change (Φ.measure x.vector).map (dualCharacterAction E.action h) =
    Φ.measure x.vector
  change
    (RealRMK.rieszMeasure (Φ.functional x.vector)).map
        (dualCharacterAction E.action h) =
      RealRMK.rieszMeasure (Φ.functional x.vector)
  rw [Φ.covariance h x.vector, x.quotient_fixed h]

theorem probabilityMeasure_energy
    (Φ : PositiveSpectralFunctional E V π)
    (x : QuotientFixedUnitVector E V π) (a : A) :
    spectralDetectionEnergy
        (Φ.probabilityMeasure x.vector x.norm_one) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          x.vector - x.vector‖ ^ 2 := by
  exact Φ.measure_energy x.vector a

end PositiveSpectralFunctional

/--
The `kernelFixedSubmodule` construction used in the Connes rigidity formalization.
-/
def kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : Submodule ℂ V :=
  ⨅ a : A,
    LinearMap.ker
      (((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) -
        ContinuousLinearMap.id ℂ V).toLinearMap)

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem mem_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V) :
    x ∈ kernelFixedSubmodule E π ↔
      ∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x = x := by
  simp only [kernelFixedSubmodule, ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
    LinearMap.id_coe, id_eq, sub_eq_zero]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem kernelFixedSubmodule_isClosed
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    IsClosed (kernelFixedSubmodule E π : Set V) := by
  rw [kernelFixedSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun a ↦
    (((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) -
      ContinuousLinearMap.id ℂ V).isClosed_ker)

instance kernelFixedSubmodule_completeSpace
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    CompleteSpace (kernelFixedSubmodule E π) :=
  (kernelFixedSubmodule_isClosed E π).isComplete.completeSpace_coe

/--
The `trivialCharacterProjection` construction used in the Connes rigidity formalization.
-/
def trivialCharacterProjection
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : V →L[ℂ] V :=
  (kernelFixedSubmodule E π).starProjection

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem trivialCharacterProjection_kernel_fixed
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V) (a : A) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        (trivialCharacterProjection E π x) =
      trivialCharacterProjection E π x := by
  apply (mem_kernelFixedSubmodule E π _).mp
  exact Submodule.starProjection_apply_mem _ _

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem kernel_map_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) :
    (kernelFixedSubmodule E π).map
      (Unitary.linearIsometryEquiv
        (π (E.inclusion (Multiplicative.ofAdd a)))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x ∈
        kernelFixedSubmodule E π
    rw [(mem_kernelFixedSubmodule E π x).mp hx a]
    exact hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    exact (mem_kernelFixedSubmodule E π x).mp hx a

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem trivialCharacterProjection_kernel_commutes
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) (x : V) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
      (trivialCharacterProjection E π x) =
        trivialCharacterProjection E π
          ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) := by
  let U := Unitary.linearIsometryEquiv
    (π (E.inclusion (Multiplicative.ofAdd a)))
  have hmap :
      (kernelFixedSubmodule E π).map U.toLinearIsometry.toLinearMap =
        kernelFixedSubmodule E π := by
    change
      (kernelFixedSubmodule E π).map
        (Unitary.linearIsometryEquiv
          (π (E.inclusion
            (Multiplicative.ofAdd a)))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π
    exact kernel_map_kernelFixedSubmodule E π a
  let mappedProjection : ((kernelFixedSubmodule E π).map
      U.toLinearIsometry.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  have hprojection := U.toLinearIsometry.map_starProjection
    (kernelFixedSubmodule E π) x
  change
    U ((kernelFixedSubmodule E π).starProjection x) =
      (kernelFixedSubmodule E π).starProjection (U x)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, hmap] using hprojection

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem trivialCharacterProjection_kernel_orbit
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (a : A) (x : V) :
    trivialCharacterProjection E π
      ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) =
        trivialCharacterProjection E π x := by
  rw [← trivialCharacterProjection_kernel_commutes E π a x,
    trivialCharacterProjection_kernel_fixed E π x a]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem quotient_preserves_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V)
    (h : H) {x : V} (hx : x ∈ kernelFixedSubmodule E π) :
    (π (E.splitting h) : V →L[ℂ] V) x ∈ kernelFixedSubmodule E π := by
  apply (mem_kernelFixedSubmodule E π _).mpr
  intro a
  let b : A := (Multiplicative.toAdd (E.action h⁻¹)) a
  have haction : (Multiplicative.toAdd (E.action h)) b = a := by
    change (Multiplicative.toAdd (E.action h * E.action h⁻¹)) a = a
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, toAdd_one, AddAut.zero_apply]
  have hconj := E.conjugation h b
  rw [haction] at hconj
  have hcomm :
      E.inclusion (Multiplicative.ofAdd a) * E.splitting h =
        E.splitting h * E.inclusion (Multiplicative.ofAdd b) := by
    calc
      E.inclusion (Multiplicative.ofAdd a) * E.splitting h =
          (E.splitting h * E.inclusion (Multiplicative.ofAdd b) *
            (E.splitting h)⁻¹) * E.splitting h := by rw [hconj]
      _ = E.splitting h * E.inclusion (Multiplicative.ofAdd b) := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hfixed := (mem_kernelFixedSubmodule E π x).mp hx b
  calc
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        ((π (E.splitting h) : V →L[ℂ] V) x) =
      (π (E.inclusion (Multiplicative.ofAdd a) * E.splitting h) :
        V →L[ℂ] V) x := by rw [map_mul]; rfl
    _ = (π (E.splitting h * E.inclusion (Multiplicative.ofAdd b)) :
        V →L[ℂ] V) x := by rw [hcomm]
    _ = (π (E.splitting h) : V →L[ℂ] V)
          ((π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V) x) := by
        rw [map_mul]
        rfl
    _ = (π (E.splitting h) : V →L[ℂ] V) x := by rw [hfixed]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem quotient_map_kernelFixedSubmodule
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (h : H) :
    (kernelFixedSubmodule E π).map
      (Unitary.linearIsometryEquiv (π (E.splitting h))).toLinearEquiv.toLinearMap =
        kernelFixedSubmodule E π := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact quotient_preserves_kernelFixedSubmodule E π h hx
  · intro x hx
    refine ⟨(π (E.splitting h⁻¹) : V →L[ℂ] V) x,
      quotient_preserves_kernelFixedSubmodule E π h⁻¹ hx, ?_⟩
    change
      (π (E.splitting h) : V →L[ℂ] V)
        ((π (E.splitting h⁻¹) : V →L[ℂ] V) x) = x
    have hop :
        π (E.splitting h) * π (E.splitting h⁻¹) = 1 := by
      rw [← map_mul, ← map_mul]
      simp only [mul_inv_cancel, map_one]
    have hx' := DFunLike.congr_fun
      (congrArg (fun U : unitary (V →L[ℂ] V) ↦ (U : V →L[ℂ] V)) hop) x
    exact hx'

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem trivialCharacterProjection_quotient_commutes
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (h : H) (x : V) :
    (π (E.splitting h) : V →L[ℂ] V)
      (trivialCharacterProjection E π x) =
        trivialCharacterProjection E π
          ((π (E.splitting h) : V →L[ℂ] V) x) := by
  let U := Unitary.linearIsometryEquiv (π (E.splitting h))
  have hmap :
      (kernelFixedSubmodule E π).map U.toLinearIsometry.toLinearMap =
        kernelFixedSubmodule E π := by
    change
      (kernelFixedSubmodule E π).map
        (Unitary.linearIsometryEquiv
          (π (E.splitting h))).toLinearEquiv.toLinearMap =
          kernelFixedSubmodule E π
    exact quotient_map_kernelFixedSubmodule E π h
  let mappedProjection : ((kernelFixedSubmodule E π).map
      U.toLinearIsometry.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  have hprojection := U.toLinearIsometry.map_starProjection
    (kernelFixedSubmodule E π) x
  change
    U ((kernelFixedSubmodule E π).starProjection x) =
      (kernelFixedSubmodule E π).starProjection (U x)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, hmap] using hprojection

end

noncomputable
section
open Connes MeasureTheory
open scoped BigOperators CompactlySupported

universe u v

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]
variable {E : SplitAbelianExtension A G H}
variable {π : UnitaryRepresentation G W}

theorem measureReal_singleton_le_integral_of_nonneg
    {Ω : Type v} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (x : Ω)
    (hf : Integrable f μ) (hpos : ∀ y, 0 ≤ f y)
    (hone : 1 ≤ f x) :
    μ.real {x} ≤ ∫ y, f y ∂μ := by
  have hmass : 0 ≤ μ.real {x} := measureReal_nonneg
  calc
    μ.real {x} ≤ μ.real {x} * f x := by nlinarith
    _ = ∫ y in {x}, f y ∂μ := by
      rw [integral_singleton]
      simp only [smul_eq_mul]
    _ ≤ ∫ y, f y ∂μ :=
      setIntegral_le_integral hf (Filter.Eventually.of_forall hpos)

namespace PositiveSpectralFunctional

theorem trivial_atom_le_functional_of_nonneg
    (Φ : PositiveSpectralFunctional E W π) (x : W)
    (f : C_c(DiscreteCharacterSpace A, ℝ))
    (hpos : ∀ χ, 0 ≤ f χ) (hone : 1 ≤ f 1) :
    (Φ.measure x).real {1} ≤ Φ.functional x f := by
  calc
    (Φ.measure x).real {1} ≤ ∫ χ, f χ ∂(Φ.measure x) := by
      apply measureReal_singleton_le_integral_of_nonneg
        (Φ.measure x) (fun χ ↦ f χ) 1
      · exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      · exact hpos
      · exact hone
    _ = Φ.functional x f := Φ.integral_measure x f

end PositiveSpectralFunctional

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)] in
theorem kernel_orbit_sub_norm
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a b : A) :
    ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
      (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x‖ =
    ‖(π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x‖ := by
  let U := π (E.inclusion (Multiplicative.ofAdd b))
  let z :=
    (π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x
  have hfactor :
      (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
        (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x =
      (U : W →L[ℂ] W) z := by
    dsimp [U, z]
    rw [map_sub]
    congr 1
    change (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x =
      ((π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W)
        ((π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x))
    have hmul :
        E.inclusion (Multiplicative.ofAdd a) =
          E.inclusion (Multiplicative.ofAdd b) *
            E.inclusion (Multiplicative.ofAdd (a - b)) := by
      rw [← map_mul]
      apply congrArg E.inclusion
      apply Multiplicative.toAdd.injective
      change a = b + (a - b)
      abel
    rw [hmul, map_mul]
    rfl
  rw [hfactor]
  exact Unitary.norm_map U z

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)] in
theorem kernel_orbit_sub_norm_sq
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a b : A) :
    ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x -
      (π (E.inclusion (Multiplicative.ofAdd b)) : W →L[ℂ] W) x‖ ^ 2 =
    ‖(π (E.inclusion (Multiplicative.ofAdd (a - b))) : W →L[ℂ] W) x - x‖ ^ 2 := by
  rw [kernel_orbit_sub_norm E π x a b]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem character_sub_norm
    (χ : DiscreteCharacterSpace A) (a b : A) :
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
      ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ =
    ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ := by
  calc
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
        ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ =
      ‖((χ (Multiplicative.ofAdd b) : Circle) : ℂ) *
        (((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one]
      congr 1
      change
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ) =
          ((χ (Multiplicative.ofAdd b) *
            χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ)
      congr 1
      rw [← map_mul]
      apply congrArg χ
      apply Multiplicative.toAdd.injective
      change a = b + (a - b)
      abel
    _ = ‖((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ *
      ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ :=
        norm_mul _ _
    _ = ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ := by
      rw [Circle.norm_coe, one_mul]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem character_sub_norm_sq
    (χ : DiscreteCharacterSpace A) (a b : A) :
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) -
      ((χ (Multiplicative.ofAdd b) : Circle) : ℂ)‖ ^ 2 =
    ‖((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ) - 1‖ ^ 2 := by
  rw [character_sub_norm χ a b]

/--
The `spectralFiniteAverageTest` construction used in the Connes rigidity formalization.
-/
def spectralFiniteAverageTest
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ) :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun χ :=
    ‖∑ i ∈ s, (w i : ℂ) *
      ((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2
  continuous_toFun := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum s
    intro i _
    exact continuous_const.mul (continuous_character_evaluation (a i))
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
@[simp] theorem spectralFiniteAverageTest_apply
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (χ : DiscreteCharacterSpace A) :
    spectralFiniteAverageTest s a w χ =
      ‖∑ i ∈ s, (w i : ℂ) *
        ((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2 := rfl

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
theorem spectralFiniteAverageTest_nonneg
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (χ : DiscreteCharacterSpace A) :
    0 ≤ spectralFiniteAverageTest s a w χ := sq_nonneg _

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
theorem spectralFiniteAverageTest_one
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    spectralFiniteAverageTest s a w 1 = 1 := by
  change ‖∑ i ∈ s, (w i : ℂ) *
    (((1 : DiscreteCharacterSpace A)
      (Multiplicative.ofAdd (a i)) : Circle) : ℂ)‖ ^ 2 = 1
  have hchar (i : ι) :
      (((1 : DiscreteCharacterSpace A)
        (Multiplicative.ofAdd (a i)) : Circle) : ℂ) = 1 := rfl
  simp_rw [hchar, mul_one]
  rw [← Complex.ofReal_sum, hw]
  norm_num

namespace PositiveSpectralFunctional

theorem trivial_atom_le_finiteAverage_functional
    (Φ : PositiveSpectralFunctional E W π) (x : W)
    {ι : Type v} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    (Φ.measure x).real {1} ≤
      Φ.functional x (spectralFiniteAverageTest s a w) := by
  apply Φ.trivial_atom_le_functional_of_nonneg x
    (spectralFiniteAverageTest s a w)
  · exact spectralFiniteAverageTest_nonneg s a w
  · rw [spectralFiniteAverageTest_one s a w hw]

end PositiveSpectralFunctional

end

noncomputable
section

open Connes MeasureTheory
open scoped ENNReal NNReal CompactlySupported

universe u

theorem weighted_norm_sq_eq_sub_pairwise_dist_sq
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Finset ι) (w : ι → ℝ) (v : ι → V)
    (hw : ∑ i ∈ s, w i = 1) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 =
      (∑ i ∈ s, w i * ‖v i‖ ^ 2) -
        (1 / 2 : ℝ) *
          ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 := by
  have hinner :
      ‖∑ i ∈ s, w i • v i‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * @inner ℝ V _ (v i) (v j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirst :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i‖ ^ 2) =
        ∑ i ∈ s, w i * ‖v i‖ ^ 2 := by
    simp_rw [show ∀ i j, w i * w j * ‖v i‖ ^ 2 =
      (w i * ‖v i‖ ^ 2) * w j by intros; ring]
    simp_rw [← Finset.mul_sum, hw, mul_one]
  have hsecond :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v j‖ ^ 2) =
        ∑ j ∈ s, w j * ‖v j‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * ‖v j‖ ^ 2 =
      (w j * ‖v j‖ ^ 2) * w i by intros; ring]
    simp_rw [← Finset.mul_sum, hw, mul_one]
  rw [hinner]
  simp_rw [norm_sub_sq_real, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]
  have hcross :
      (∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (2 * @inner ℝ V _ (v i) (v j))) =
        2 * (∑ i ∈ s, ∑ j ∈ s,
          w i * w j * @inner ℝ V _ (v i) (v j)) := by
    simp_rw [show ∀ i j, w i * w j * (2 * @inner ℝ V _ (v i) (v j)) =
      2 * (w i * w j * @inner ℝ V _ (v i) (v j)) by intros; ring]
    simp_rw [← Finset.mul_sum]
  rw [hcross]
  ring

theorem weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Finset ι) (w : ι → ℝ) (v : ι → V) (r : ℝ)
    (hw : ∑ i ∈ s, w i = 1)
    (hv : ∀ i ∈ s, ‖v i‖ = r) :
    ‖∑ i ∈ s, w i • v i‖ ^ 2 = r ^ 2 -
      (1 / 2 : ℝ) *
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖v i - v j‖ ^ 2 := by
  rw [weighted_norm_sq_eq_sub_pairwise_dist_sq s w v hw]
  congr 1
  calc
    (∑ i ∈ s, w i * ‖v i‖ ^ 2) =
        ∑ i ∈ s, w i * r ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi]
    _ = (∑ i ∈ s, w i) * r ^ 2 := by
          rw [Finset.sum_mul]
    _ = r ^ 2 := by rw [hw, one_mul]

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
theorem spectralFiniteAverageTest_eq_sub_energy {ι : Type*}
    (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    spectralFiniteAverageTest s a w = spectralUnitTest A -
      (1 / 2 : ℝ) •
        ∑ i ∈ s, ∑ j ∈ s,
          (w i * w j) • spectralEnergyTest (a i - a j) := by
  ext χ
  have hvariance := weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    s w (fun i ↦ (((χ (Multiplicative.ofAdd (a i)) : Circle) : ℂ))) 1 hw
      (fun i _ ↦ Circle.norm_coe _)
  simp only [one_pow, character_sub_norm_sq] at hvariance
  simpa only [spectralFiniteAverageTest_apply, one_div, CompactlySupportedContinuousMap.coe_sub,
    CompactlySupportedContinuousMap.coe_smul, CompactlySupportedContinuousMap.coe_sum, Pi.sub_apply,
    spectralUnitTest_apply, Pi.smul_apply, Finset.sum_apply, spectralEnergyTest_apply, ofAdd_sub,
    map_div, Circle.coe_div, smul_eq_mul, Complex.real_smul] using hvariance

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

theorem finiteAverage_functional_eq_kernel_orbit_norm_sq
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    {ι : Type*} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    Φ.functional x (spectralFiniteAverageTest s a w) =
      ‖∑ i ∈ s, w i •
        ((π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)‖ ^ 2 := by
  let realInnerProduct : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  have hvariance := weighted_norm_sq_eq_sub_pairwise_dist_sq_of_constant_norm
    s w
      (fun i ↦
        (π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)
      ‖x‖ hw (fun i _ ↦ Unitary.norm_map _ x)
  simp only [kernel_orbit_sub_norm_sq] at hvariance
  rw [spectralFiniteAverageTest_eq_sub_energy s a w hw]
  simp only [map_sub, map_smul, map_sum, Φ.normalization, Φ.energy,
    smul_eq_mul]
  exact hvariance.symm

theorem trivial_atom_le_kernel_orbit_norm_sq
    (Φ : PositiveSpectralFunctional E V π) (x : V)
    {ι : Type*} (s : Finset ι) (a : ι → A) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    (Φ.measure x).real {1} ≤
      ‖∑ i ∈ s, w i •
        ((π (E.inclusion (Multiplicative.ofAdd (a i))) : V →L[ℂ] V) x)‖ ^ 2 := by
  rw [← Φ.finiteAverage_functional_eq_kernel_orbit_norm_sq x s a w hw]
  exact Φ.trivial_atom_le_finiteAverage_functional x s a w hw

end PositiveSpectralFunctional

end

noncomputable
section

open Connes MeasureTheory

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/--
The `HasKernelOrbitAffineApproximation` construction used in the Connes rigidity formalization.
-/
def HasKernelOrbitAffineApproximation
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) : Prop :=
  ∀ (x : V), trivialCharacterProjection E π x = 0 →
    ∀ (ε : ℝ), 0 < ε →
      ∃ (s : Finset A) (w : A → ℝ),
        (∑ a ∈ s, w a) = 1 ∧
          ‖∑ a ∈ s, w a •
            ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)‖ < ε

namespace PositiveSpectralFunctional

variable {E : SplitAbelianExtension A G H}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : UnitaryRepresentation G V}

theorem trivialCharacterProjection_ne_zero_of_atom_pos_of_orbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (Φ.probabilityMeasure x.vector x.norm_one)) :
    trivialCharacterProjection E π x.vector ≠ 0 := by
  intro hprojection
  change 0 < (Φ.measure x.vector).real {1} at hx
  let ε : ℝ := min 1 ((Φ.measure x.vector).real {1})
  have hε : 0 < ε := lt_min (by norm_num) hx
  obtain ⟨s, w, hw, hsmall⟩ :=
    approximation x.vector hprojection ε hε
  have hbound := Φ.trivial_atom_le_kernel_orbit_norm_sq
    x.vector s (fun a : A ↦ a) w hw
  let z : V := ∑ a ∈ s, w a •
    ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x.vector)
  change (Φ.measure x.vector).real {1} ≤ ‖z‖ ^ 2 at hbound
  change ‖z‖ < ε at hsmall
  have hzone : ‖z‖ < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hzatom : ‖z‖ < (Φ.measure x.vector).real {1} :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hznorm : 0 ≤ ‖z‖ := norm_nonneg _
  linarith [mul_nonneg hznorm (sub_nonneg.mpr (le_of_lt hzone))]

theorem positive_atom_invariant_of_orbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π)
    (x : QuotientFixedUnitVector E V π)
    (hx : 0 < spectralTrivialAtom
      (Φ.probabilityMeasure x.vector x.norm_one)) :
    ∃ η : V, η ≠ 0 ∧
      (∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) η = η) ∧
      (∀ h : H,
        (π (E.splitting h) : V →L[ℂ] V) η = η) := by
  refine ⟨trivialCharacterProjection E π x.vector,
    Φ.trivialCharacterProjection_ne_zero_of_atom_pos_of_orbitApproximation
      approximation x hx,
    trivialCharacterProjection_kernel_fixed E π x.vector, ?_⟩
  intro h
  rw [trivialCharacterProjection_quotient_commutes E π h x.vector,
    x.quotient_fixed h]

/--
The `toSpectralMeasureInterfaceOfOrbitApproximation` construction used in the
Connes rigidity formalization.
-/
def toSpectralMeasureInterfaceOfOrbitApproximation
    (Φ : PositiveSpectralFunctional E V π)
    (approximation : HasKernelOrbitAffineApproximation E π) :
    SpectralMeasureInterface E V π where
  quotient_fixed_approximation :=
    ProjectionValuedSpectralMeasure.hasQuotientFixedApproximation
  measure x := Φ.probabilityMeasure x.vector x.norm_one
  measure_invariant := Φ.probabilityMeasure_invariant
  energy_eq := Φ.probabilityMeasure_energy
  positive_atom_invariant :=
    Φ.positive_atom_invariant_of_orbitApproximation approximation

end PositiveSpectralFunctional

theorem spectral_criterion_of_positive_functional_and_orbitApproximation
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (functional : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        PositiveSpectralFunctional E V π)
    (approximation : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        HasKernelOrbitAffineApproximation E π) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion E hH J hc hdetection
  intro V _ _ _ π
  exact (functional V inferInstance inferInstance inferInstance π)
    |>.toSpectralMeasureInterfaceOfOrbitApproximation
      (approximation V inferInstance inferInstance inferInstance π)

end

noncomputable
section

open Connes Metric WeakDual
open scoped CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `spectralOperatorGenerators` construction used in the Connes rigidity formalization.
-/
def spectralOperatorGenerators
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : Set (V →L[ℂ] V) :=
  Set.range fun a : A ↦
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)

/--
The `spectralOperatorAlgebra` construction used in the Connes rigidity formalization.
-/
def spectralOperatorAlgebra
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) : StarSubalgebra ℂ (V →L[ℂ] V) :=
  (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)).topologicalClosure

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem spectralOperatorGenerators_commute
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    {S T : V →L[ℂ] V}
    (hS : S ∈ spectralOperatorGenerators E π)
    (hT : T ∈ spectralOperatorGenerators E π) : S * T = T * S := by
  obtain ⟨a, rfl⟩ := hS
  obtain ⟨b, rfl⟩ := hT
  have hkernel :
      E.inclusion (Multiplicative.ofAdd a) *
        E.inclusion (Multiplicative.ofAdd b) =
      E.inclusion (Multiplicative.ofAdd b) *
        E.inclusion (Multiplicative.ofAdd a) := by
    rw [← E.inclusion.map_mul, ← E.inclusion.map_mul]
    congr 1
    exact mul_comm _ _
  simpa only [map_mul, Submonoid.coe_mul] using congrArg
    (fun U : unitary (V →L[ℂ] V) ↦ (U : V →L[ℂ] V))
    (congrArg π hkernel)

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem star_mem_spectralOperatorGenerators
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    {T : V →L[ℂ] V}
    (hT : T ∈ spectralOperatorGenerators E π) :
    star T ∈ spectralOperatorGenerators E π := by
  obtain ⟨a, rfl⟩ := hT
  refine ⟨-a, ?_⟩
  change (π (E.inclusion (Multiplicative.ofAdd (-a))) : V →L[ℂ] V) =
    star (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
  change
    (π (E.inclusion ((Multiplicative.ofAdd a)⁻¹)) : V →L[ℂ] V) =
      star (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
  rw [map_inv, map_inv]
  rw [← Unitary.star_eq_inv]
  exact Unitary.coe_star

instance spectralOperatorAdjoin_isMulCommutative
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    IsMulCommutative
      (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · exact fun _ hS _ hT ↦ spectralOperatorGenerators_commute E π hS hT
  · intro S hS T hT
    exact spectralOperatorGenerators_commute E π hS
      (star_mem_spectralOperatorGenerators E π hT)

instance spectralOperatorAlgebraCommCStarAlgebra
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    CommCStarAlgebra (spectralOperatorAlgebra E π) := by
  let commRingInstance : CommRing (spectralOperatorAlgebra E π) :=
    StarSubalgebra.commRingTopologicalClosure _
      (isMulCommutative_iff.mp
        (spectralOperatorAdjoin_isMulCommutative E π))
  let closedInstance : IsClosed (spectralOperatorAlgebra E π : Set (V →L[ℂ] V)) :=
    (StarAlgebra.adjoin ℂ
      (spectralOperatorGenerators E π)).isClosed_topologicalClosure
  exact { mul_comm := mul_comm }

/--
The `spectralKernelOperator` construction used in the Connes rigidity formalization.
-/
def spectralKernelOperator
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    spectralOperatorAlgebra E π :=
  ⟨(π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V),
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩)⟩

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem spectralKernelOperator_coe
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    ((spectralKernelOperator E π a : spectralOperatorAlgebra E π) :
      V →L[ℂ] V) =
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) := rfl

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem spectralKernelOperator_zero
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    spectralKernelOperator E π 0 = 1 := by
  apply Subtype.ext
  simp only [spectralKernelOperator, ofAdd_zero, map_one, OneMemClass.coe_one]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem spectralKernelOperator_add
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a b : A) :
    spectralKernelOperator E π (a + b) =
      spectralKernelOperator E π a * spectralKernelOperator E π b := by
  apply Subtype.ext
  change
    (π (E.inclusion (Multiplicative.ofAdd (a + b))) : V →L[ℂ] V) =
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) *
        (π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V)
  change
    (π (E.inclusion
      (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) :
      V →L[ℂ] V) = _
  rw [E.inclusion.map_mul]
  simp only [map_mul, Submonoid.coe_mul]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem spectralKernelOperator_unitary
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    spectralKernelOperator E π a ∈
      unitary (spectralOperatorAlgebra E π) := by
  rw [Unitary.mem_iff]
  constructor
  · apply Subtype.ext
    exact Unitary.coe_star_mul_self
      (π (E.inclusion (Multiplicative.ofAdd a)))
  · apply Subtype.ext
    exact Unitary.coe_mul_star_self
      (π (E.inclusion (Multiplicative.ofAdd a)))

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem spectralCharacter_generator_mem_circle
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) (a : A) :
    φ (spectralKernelOperator E π a) ∈ sphere (0 : ℂ) 1 := by
  apply mem_sphere_zero_iff_norm.mpr
  exact CStarRing.norm_of_mem_unitary
    (Unitary.map_mem φ (spectralKernelOperator_unitary E π a))

/--
The `spectralCharacter` construction used in the Connes rigidity formalization.
-/
def spectralCharacter
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) :
    DiscreteCharacterSpace A where
  toFun a :=
    ⟨φ (spectralKernelOperator E π (Multiplicative.toAdd a)),
      spectralCharacter_generator_mem_circle E π φ
        (Multiplicative.toAdd a)⟩
  map_one' := by
    apply Circle.ext
    change φ (spectralKernelOperator E π 0) = 1
    rw [spectralKernelOperator_zero]
    exact map_one φ
  map_mul' a b := by
    apply Circle.ext
    change
      φ (spectralKernelOperator E π
        (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      φ (spectralKernelOperator E π (Multiplicative.toAdd a)) *
        φ (spectralKernelOperator E π (Multiplicative.toAdd b))
    rw [spectralKernelOperator_add, map_mul]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem spectralCharacter_apply_coe
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) (a : A) :
    ((spectralCharacter E π φ (Multiplicative.ofAdd a) : Circle) : ℂ) =
      φ (spectralKernelOperator E π a) := rfl

theorem spectralCharacter_continuous
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    Continuous (spectralCharacter E π) := by
  apply
    (ContinuousMonoidHom.isClosedEmbedding_coe
      (A := Multiplicative A) (B := Circle)).toIsInducing.continuous_iff.mpr
  apply continuous_pi
  intro a
  exact Continuous.subtype_mk
    ((gelfandTransform ℂ (spectralOperatorAlgebra E π)
      (spectralKernelOperator E π (Multiplicative.toAdd a))).continuous) _

/--
The `spectralCharacterMap` construction used in the Connes rigidity formalization.
-/
def spectralCharacterMap
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    C(characterSpace ℂ (spectralOperatorAlgebra E π),
      DiscreteCharacterSpace A) :=
  ⟨spectralCharacter E π, spectralCharacter_continuous E π⟩

/--
The `jointFunctionalCalculus` construction used in the Connes rigidity formalization.
-/
def jointFunctionalCalculus
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      spectralOperatorAlgebra E π :=
  (gelfandStarTransform (spectralOperatorAlgebra E π)).symm.toStarAlgHom.comp
    ((spectralCharacterMap E π).compStarAlgHom' ℂ ℂ)

/--
The `spectralCharacterEvaluation` construction used in the Connes rigidity formalization.
-/
def spectralCharacterEvaluation
    (a : A) : C(DiscreteCharacterSpace A, ℂ) :=
  ⟨fun χ ↦ ((χ (Multiplicative.ofAdd a) : Circle) : ℂ),
    continuous_character_evaluation a⟩

omit [DiscreteTopology A] in
@[simp] theorem spectralCharacterEvaluation_apply
    (a : A) (χ : DiscreteCharacterSpace A) :
    spectralCharacterEvaluation a χ =
      ((χ (Multiplicative.ofAdd a) : Circle) : ℂ) := rfl

theorem jointFunctionalCalculus_characterEvaluation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (a : A) :
    jointFunctionalCalculus E π (spectralCharacterEvaluation a) =
      spectralKernelOperator E π a := by
  apply (gelfandStarTransform (spectralOperatorAlgebra E π)).injective
  change
    (gelfandStarTransform (spectralOperatorAlgebra E π))
      ((gelfandStarTransform (spectralOperatorAlgebra E π)).symm
        ((spectralCharacterEvaluation a).comp
          (spectralCharacterMap E π))) =
      (gelfandStarTransform (spectralOperatorAlgebra E π))
        (spectralKernelOperator E π a)
  rw [StarAlgEquiv.apply_symm_apply]
  ext φ
  rfl

end

noncomputable
section

open WeakDual

universe u v

variable {B : Type u} [CommCStarAlgebra B]
variable {X : Type v} [TopologicalSpace X]

theorem inverseGelfand_naturality
    (α : B →⋆ₐ[ℂ] B)
    (p : C(WeakDual.characterSpace ℂ B, X))
    (d : C(X, X))
    (hp : ∀ φ : WeakDual.characterSpace ℂ B,
      p (WeakDual.CharacterSpace.compContinuousMap α φ) = d (p φ))
    (f : C(X, ℂ)) :
    α ((gelfandStarTransform B).symm (f.comp p)) =
      (gelfandStarTransform B).symm ((f.comp d).comp p) := by
  apply (gelfandStarTransform B).injective
  ext φ
  change
    (WeakDual.CharacterSpace.compContinuousMap α φ)
        ((gelfandStarTransform B).symm (f.comp p)) =
      φ ((gelfandStarTransform B).symm ((f.comp d).comp p))
  have hleft := congrArg
    (fun F : C(WeakDual.characterSpace ℂ B, ℂ) ↦
      F (WeakDual.CharacterSpace.compContinuousMap α φ))
    ((gelfandStarTransform B).apply_symm_apply (f.comp p))
  have hright := congrArg
    (fun F : C(WeakDual.characterSpace ℂ B, ℂ) ↦ F φ)
    ((gelfandStarTransform B).apply_symm_apply ((f.comp d).comp p))
  change
    (WeakDual.CharacterSpace.compContinuousMap α φ)
        ((gelfandStarTransform B).symm (f.comp p)) =
      f (p (WeakDual.CharacterSpace.compContinuousMap α φ)) at hleft
  change
    φ ((gelfandStarTransform B).symm ((f.comp d).comp p)) =
      f (d (p φ)) at hright
  calc
    _ = f (p (WeakDual.CharacterSpace.compContinuousMap α φ)) := hleft
    _ = f (d (p φ)) := congrArg f (hp φ)
    _ = _ := hright.symm

end

noncomputable
section

open scoped InnerProduct

universe u

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `positiveVectorState` construction used in the Connes rigidity formalization.
-/
def positiveVectorState (x : V) : (V →L[ℂ] V) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ V) x)).restrictScalars ℝ)

theorem positiveVectorState_star_mul_self (x : V) (T : V →L[ℂ] V) :
    positiveVectorState x (star T * T) = ‖T x‖ ^ 2 := by
  change (inner ℂ x ((star T) (T x))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)

omit [CompleteSpace V] in
@[simp] theorem positiveVectorState_one (x : V) :
    positiveVectorState x (1 : V →L[ℂ] V) = ‖x‖ ^ 2 := by
  change (inner ℂ x x).re = _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

end

noncomputable
section

open Connes MeasureTheory
open scoped CompactlySupported

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}

theorem dualCharacterAction_mul
    (action : H →* Multiplicative (AddAut A)) (g h : H)
    (χ : DiscreteCharacterSpace A) :
    dualCharacterAction action (g * h) χ =
      dualCharacterAction action g (dualCharacterAction action h χ) := by
  apply ContinuousMonoidHom.ext
  intro a
  change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action (g * h)⁻¹))
        (Multiplicative.toAdd a))) =
    χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹))
        ((Multiplicative.toAdd (action g⁻¹)) (Multiplicative.toAdd a))))
  rw [mul_inv_rev, map_mul]
  rfl

@[simp] theorem dualCharacterAction_one
    (action : H →* Multiplicative (AddAut A))
    (χ : DiscreteCharacterSpace A) :
    dualCharacterAction action (1 : H) χ = χ := by
  apply ContinuousMonoidHom.ext
  intro a
  change χ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (action 1⁻¹))
      (Multiplicative.toAdd a))) = χ a
  rw [inv_one, map_one]
  rfl

/--
The `dualCharacterHomeomorph` construction used in the Connes rigidity formalization.
-/
def dualCharacterHomeomorph
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    DiscreteCharacterSpace A ≃ₜ DiscreteCharacterSpace A where
  toFun := dualCharacterAction action h
  invFun := dualCharacterAction action h⁻¹
  left_inv χ := by
    rw [← dualCharacterAction_mul, inv_mul_cancel, dualCharacterAction_one]
  right_inv χ := by
    rw [← dualCharacterAction_mul, mul_inv_cancel, dualCharacterAction_one]
  continuous_toFun := continuous_dualCharacterAction action h
  continuous_invFun := continuous_dualCharacterAction action h⁻¹

@[simp] theorem dualCharacterHomeomorph_apply
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (χ : DiscreteCharacterSpace A) :
    dualCharacterHomeomorph action h χ = dualCharacterAction action h χ := rfl

section Riesz

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/--
The `compactTestPrecomp` construction used in the Connes rigidity formalization.
-/
def compactTestPrecomp (e : X ≃ₜ X) (f : C_c(X, ℝ)) : C_c(X, ℝ) where
  toFun x := f (e x)
  continuous_toFun := f.continuous.comp e.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

theorem rieszMeasure_map_homeomorph
    (e : X ≃ₜ X)
    (Λ Λ' : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (hfunctional : ∀ f : C_c(X, ℝ),
      Λ (compactTestPrecomp e f) = Λ' f) :
    (RealRMK.rieszMeasure Λ).map e = RealRMK.rieszMeasure Λ' := by
  let mappedRegular : ((RealRMK.rieszMeasure Λ).map e).Regular :=
    Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (μ := RealRMK.rieszMeasure Λ) (φ := e)
    e.continuous.measurable.aemeasurable
    (f := fun x : X ↦ f x) f.continuous.aestronglyMeasurable]
  change (∫ x, compactTestPrecomp e f x ∂(RealRMK.rieszMeasure Λ)) =
    ∫ x, f x ∂(RealRMK.rieszMeasure Λ')
  rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
  exact hfunctional f

end Riesz

section DualRiesz

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

theorem rieszMeasure_dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (Λ Λ' : C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ)
    (hfunctional : ∀ f : C_c(DiscreteCharacterSpace A, ℝ),
      Λ (compactTestPrecomp (dualCharacterHomeomorph action h) f) = Λ' f) :
    (RealRMK.rieszMeasure Λ).map (dualCharacterAction action h) =
      RealRMK.rieszMeasure Λ' :=
  rieszMeasure_map_homeomorph
    (dualCharacterHomeomorph action h) Λ Λ' hfunctional

end DualRiesz

section VectorState

variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

theorem positiveVectorState_unitary_pullback
    (x : V) (U : unitary (V →L[ℂ] V)) (T : V →L[ℂ] V) :
    positiveVectorState x
        (star (U : V →L[ℂ] V) * T * (U : V →L[ℂ] V)) =
      positiveVectorState ((U : V →L[ℂ] V) x) T := by
  change (inner ℂ x
    ((star (U : V →L[ℂ] V)) (T ((U : V →L[ℂ] V) x)))).re =
      (inner ℂ ((U : V →L[ℂ] V) x)
        (T ((U : V →L[ℂ] V) x))).re
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

end VectorState

end

noncomputable
section

open Connes WeakDual

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `quotientOperatorConjugation` construction used in the Connes rigidity formalization.
-/
def quotientOperatorConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    (V →L[ℂ] V) ≃⋆ₐ[ℂ] (V →L[ℂ] V) :=
  Unitary.conjStarAlgAut ℂ (V →L[ℂ] V) (π (E.splitting h))

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem quotientOperatorConjugation_apply
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (T : V →L[ℂ] V) :
    quotientOperatorConjugation E π h T =
      (π (E.splitting h) : V →L[ℂ] V) * T *
        star (π (E.splitting h) : V →L[ℂ] V) := rfl

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem quotientOperatorConjugation_kernel
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (a : A) :
    quotientOperatorConjugation E π h
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) =
        (π (E.inclusion (Multiplicative.ofAdd
          ((Multiplicative.toAdd (E.action h)) a))) : V →L[ℂ] V) := by
  change
    (π (E.splitting h) : V →L[ℂ] V) *
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) *
      star (π (E.splitting h) : V →L[ℂ] V) = _
  rw [← Unitary.coe_star, Unitary.star_eq_inv, ← map_inv]
  change
    (↑(π (E.splitting h) *
      π (E.inclusion (Multiplicative.ofAdd a)) *
      π ((E.splitting h)⁻¹)) : V →L[ℂ] V) = _
  rw [← map_mul, ← map_mul, E.conjugation]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem quotientOperatorConjugation_generators_image
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    quotientOperatorConjugation E π h '' spectralOperatorGenerators E π =
      spectralOperatorGenerators E π := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨(Multiplicative.toAdd (E.action h)) a,
      (quotientOperatorConjugation_kernel E π h a).symm⟩
  · rintro _ ⟨a, rfl⟩
    let b : A := (Multiplicative.toAdd (E.action h⁻¹)) a
    refine ⟨(π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V),
      ⟨b, rfl⟩, ?_⟩
    rw [quotientOperatorConjugation_kernel]
    congr 3
    change (Multiplicative.toAdd (E.action h * E.action h⁻¹)) a = a
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one, toAdd_one, AddAut.zero_apply]

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem quotientOperatorConjugation_mem
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    {T : V →L[ℂ] V} (hT : T ∈ spectralOperatorAlgebra E π) :
    quotientOperatorConjugation E π h T ∈ spectralOperatorAlgebra E π := by
  let F : (V →L[ℂ] V) →⋆ₐ[ℂ] (V →L[ℂ] V) :=
    (quotientOperatorConjugation E π h).toStarAlgHom
  have hcontinuous : Continuous F := by
    change Continuous (fun T : V →L[ℂ] V ↦
      (π (E.splitting h) : V →L[ℂ] V) * T *
        star (π (E.splitting h) : V →L[ℂ] V))
    fun_prop
  have hadjoin :
      (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)).map F =
        StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π) := by
    rw [StarAlgHom.map_adjoin]
    exact congrArg (StarAlgebra.adjoin ℂ)
      (quotientOperatorConjugation_generators_image E π h)
  have hmap := StarSubalgebra.map_topologicalClosure_le
    (StarAlgebra.adjoin ℂ (spectralOperatorGenerators E π)) F hcontinuous
  rw [hadjoin] at hmap
  exact hmap ⟨T, hT, rfl⟩

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem quotientOperatorConjugation_inv
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    quotientOperatorConjugation E π h⁻¹ =
      (quotientOperatorConjugation E π h).symm := by
  change Unitary.conjStarAlgAut ℂ (V →L[ℂ] V)
      (π (E.splitting h⁻¹)) = _
  rw [map_inv, map_inv]
  exact map_inv (Unitary.conjStarAlgAut ℂ (V →L[ℂ] V)) _

/--
The `quotientSpectralOperatorConjugation` construction used in the Connes rigidity formalization.
-/
def quotientSpectralOperatorConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) :
    spectralOperatorAlgebra E π ≃⋆ₐ[ℂ]
      spectralOperatorAlgebra E π where
  toFun T := ⟨quotientOperatorConjugation E π h T,
    quotientOperatorConjugation_mem E π h T.property⟩
  invFun T := ⟨quotientOperatorConjugation E π h⁻¹ T,
    quotientOperatorConjugation_mem E π h⁻¹ T.property⟩
  left_inv T := by
    apply Subtype.ext
    change quotientOperatorConjugation E π h⁻¹
      (quotientOperatorConjugation E π h (T : V →L[ℂ] V)) =
        (T : V →L[ℂ] V)
    rw [quotientOperatorConjugation_inv]
    exact (quotientOperatorConjugation E π h).symm_apply_apply T
  right_inv T := by
    apply Subtype.ext
    change quotientOperatorConjugation E π h
      (quotientOperatorConjugation E π h⁻¹ (T : V →L[ℂ] V)) =
        (T : V →L[ℂ] V)
    rw [quotientOperatorConjugation_inv]
    exact (quotientOperatorConjugation E π h).apply_symm_apply T
  map_mul' S T := by
    apply Subtype.ext
    exact map_mul (quotientOperatorConjugation E π h)
      (S : V →L[ℂ] V) (T : V →L[ℂ] V)
  map_add' S T := by
    apply Subtype.ext
    exact map_add (quotientOperatorConjugation E π h)
      (S : V →L[ℂ] V) (T : V →L[ℂ] V)
  map_star' T := by
    apply Subtype.ext
    exact StarHomClass.map_star
      (quotientOperatorConjugation E π h).toStarAlgHom
      (T : V →L[ℂ] V)
  map_smul' c T := by
    apply Subtype.ext
    exact map_smul (quotientOperatorConjugation E π h) c
      (T : V →L[ℂ] V)

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem quotientSpectralOperatorConjugation_coe
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    (T : spectralOperatorAlgebra E π) :
    ((quotientSpectralOperatorConjugation E π h T :
      spectralOperatorAlgebra E π) : V →L[ℂ] V) =
      quotientOperatorConjugation E π h (T : V →L[ℂ] V) := rfl

omit [TopologicalSpace A] [DiscreteTopology A] in
@[simp] theorem quotientSpectralOperatorConjugation_kernel
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H) (a : A) :
    quotientSpectralOperatorConjugation E π h
      (spectralKernelOperator E π a) =
      spectralKernelOperator E π
        ((Multiplicative.toAdd (E.action h)) a) := by
  apply Subtype.ext
  exact quotientOperatorConjugation_kernel E π h a

theorem spectralCharacter_quotientConjugation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    (φ : characterSpace ℂ (spectralOperatorAlgebra E π)) :
    spectralCharacter E π
        (CharacterSpace.compContinuousMap
          (quotientSpectralOperatorConjugation E π h).toStarAlgHom φ) =
      dualCharacterAction E.action h⁻¹ (spectralCharacter E π φ) := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Circle.ext
  change
    φ ((quotientSpectralOperatorConjugation E π h)
      (spectralKernelOperator E π (Multiplicative.toAdd a))) =
      φ (spectralKernelOperator E π
        ((Multiplicative.toAdd (E.action (h⁻¹)⁻¹))
          (Multiplicative.toAdd a)))
  rw [quotientSpectralOperatorConjugation_kernel, inv_inv]

/--
The `dualCharacterActionContinuousMap` construction used in the Connes rigidity formalization.
-/
def dualCharacterActionContinuousMap
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    C(DiscreteCharacterSpace A, DiscreteCharacterSpace A) :=
  ⟨dualCharacterAction action h, continuous_dualCharacterAction action h⟩

@[simp] theorem dualCharacterActionContinuousMap_apply
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (χ : DiscreteCharacterSpace A) :
    dualCharacterActionContinuousMap action h χ =
      dualCharacterAction action h χ := rfl


theorem jointFunctionalCalculus_quotient_covariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (h : H)
    (f : C(DiscreteCharacterSpace A, ℂ)) :
    ((jointFunctionalCalculus E π
        (f.comp (dualCharacterActionContinuousMap E.action h)) :
      spectralOperatorAlgebra E π) : V →L[ℂ] V) =
      star (π (E.splitting h) : V →L[ℂ] V) *
        ((jointFunctionalCalculus E π f : spectralOperatorAlgebra E π) :
          V →L[ℂ] V) *
        (π (E.splitting h) : V →L[ℂ] V) := by
  let α : spectralOperatorAlgebra E π →⋆ₐ[ℂ]
      spectralOperatorAlgebra E π :=
    (quotientSpectralOperatorConjugation E π h⁻¹).toStarAlgHom
  let d : C(DiscreteCharacterSpace A, DiscreteCharacterSpace A) :=
    dualCharacterActionContinuousMap E.action h
  have hp : ∀ φ : characterSpace ℂ (spectralOperatorAlgebra E π),
      spectralCharacterMap E π
        (CharacterSpace.compContinuousMap α φ) =
      d (spectralCharacterMap E π φ) := by
    intro φ
    change spectralCharacter E π
      (CharacterSpace.compContinuousMap
        (quotientSpectralOperatorConjugation E π h⁻¹).toStarAlgHom φ) =
      dualCharacterAction E.action h (spectralCharacter E π φ)
    simpa only [CharacterSpace.compContinuousMap_apply,
      inv_inv] using spectralCharacter_quotientConjugation E π h⁻¹ φ
  have hnaturality := inverseGelfand_naturality α
    (spectralCharacterMap E π) d hp f
  change
    (((gelfandStarTransform (spectralOperatorAlgebra E π)).symm
      ((f.comp d).comp (spectralCharacterMap E π)) :
      spectralOperatorAlgebra E π) : V →L[ℂ] V) = _
  rw [← hnaturality]
  change
    quotientOperatorConjugation E π h⁻¹
      ((jointFunctionalCalculus E π f : spectralOperatorAlgebra E π) :
        V →L[ℂ] V) = _
  rw [quotientOperatorConjugation_apply, map_inv, map_inv]
  rw [← Unitary.star_eq_inv, Unitary.coe_star, star_star]

end

noncomputable
section

open Connes MeasureTheory
open scoped CompactlySupported

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {V : Type v} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `characterRealComplexification` construction used in the Connes rigidity formalization.
-/
def characterRealComplexification
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp] theorem characterRealComplexification_apply
    (f : C_c(X, ℝ)) (y : X) :
    characterRealComplexification f y = (f y : ℂ) := rfl

@[simp] theorem characterRealComplexification_add
    (f g : C_c(X, ℝ)) :
    characterRealComplexification (f + g) =
      characterRealComplexification f + characterRealComplexification g := by
  ext y
  simp only [characterRealComplexification, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
    Complex.ofReal_add, ContinuousMap.coe_mk, ContinuousMap.add_apply]

@[simp] theorem characterRealComplexification_smul
    (r : ℝ) (f : C_c(X, ℝ)) :
    characterRealComplexification (r • f) =
      (r : ℂ) • characterRealComplexification f := by
  ext y
  simp only [characterRealComplexification, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, ContinuousMap.coe_mk, ContinuousMap.coe_smul]

variable [CompactSpace X]

/--
The `characterRealSqrt` construction used in the Connes rigidity formalization.
-/
def characterRealSqrt (f : C_c(X, ℝ)) : C_c(X, ℝ) where
  toFun y := Real.sqrt (f y)
  continuous_toFun := Real.continuous_sqrt.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

@[simp] theorem characterRealSqrt_apply
    (f : C_c(X, ℝ)) (y : X) :
    characterRealSqrt f y = Real.sqrt (f y) := rfl

theorem characterRealComplexification_eq_star_mul_sqrt
    (f : C_c(X, ℝ)) (hf : ∀ y : X, 0 ≤ f y) :
    characterRealComplexification f =
      star (characterRealComplexification (characterRealSqrt f)) *
        characterRealComplexification (characterRealSqrt f) := by
  ext y
  simp only [characterRealComplexification, ContinuousMap.coe_mk, characterRealSqrt,
    CompactlySupportedContinuousMap.coe_mk, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj]
  exact (Real.mul_self_sqrt (hf y)).symm

/--
The `characterVectorFunctionalLinear` construction used in the Connes rigidity formalization.
-/
def characterVectorFunctionalLinear
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f :=
    (inner ℂ x ((calculus (characterRealComplexification f)) x)).re
  map_add' f g := by
    simp only [characterRealComplexification_add, map_add, add_apply, CStarModule.inner_add_right,
      Complex.add_re]
  map_smul' r f := by
    rw [characterRealComplexification_smul, map_smul]
    change
      (inner ℂ x ((r : ℂ) •
        ((calculus (characterRealComplexification f)) x))).re =
        r * (inner ℂ x
          ((calculus (characterRealComplexification f)) x)).re
    rw [inner_smul_right, Complex.re_ofReal_mul]

omit [CompactSpace X] in
@[simp] theorem characterVectorFunctionalLinear_apply
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) :
    characterVectorFunctionalLinear calculus x f =
      (inner ℂ x ((calculus (characterRealComplexification f)) x)).re := rfl

theorem characterVectorFunctionalLinear_nonneg
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (hf : ∀ y : X, 0 ≤ f y) :
    0 ≤ characterVectorFunctionalLinear calculus x f := by
  let g : C(X, ℂ) := characterRealComplexification (characterRealSqrt f)
  have hfactor : characterRealComplexification f = star g * g :=
    characterRealComplexification_eq_star_mul_sqrt f hf
  change 0 ≤ (inner ℂ x ((calculus (characterRealComplexification f)) x)).re
  rw [hfactor, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
  change 0 ≤ (inner ℂ x
    (((calculus g).adjoint.comp (calculus g)) x)).re
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact @inner_self_nonneg ℂ V _ _ _ ((calculus g) x)

/--
The `characterVectorFunctional` construction used in the Connes rigidity formalization.
-/
def characterVectorFunctional
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := characterVectorFunctionalLinear calculus x
  monotone' := by
    intro f g hfg
    have hnonneg : ∀ y : X, 0 ≤ (g - f) y := by
      intro y
      exact sub_nonneg.mpr (hfg y)
    have hpositive := characterVectorFunctionalLinear_nonneg
      calculus x (g - f) hnonneg
    change
      characterVectorFunctionalLinear calculus x f ≤
        characterVectorFunctionalLinear calculus x g
    rw [map_sub] at hpositive
    linarith

@[simp] theorem characterVectorFunctional_apply
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) :
    characterVectorFunctional calculus x f =
      (inner ℂ x ((calculus (characterRealComplexification f)) x)).re := rfl

theorem characterVectorFunctional_one
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (hf : ∀ y : X, f y = 1) :
    characterVectorFunctional calculus x f = ‖x‖ ^ 2 := by
  have hcomplex : characterRealComplexification f =
      (1 : C(X, ℂ)) := by
    ext y
    simp only [characterRealComplexification, ContinuousMap.coe_mk, hf y, Complex.ofReal_one,
      ContinuousMap.one_apply]
  change positiveVectorState x
    (calculus (characterRealComplexification f)) = ‖x‖ ^ 2
  rw [hcomplex, map_one, positiveVectorState_one]

theorem characterVectorFunctional_energy_of_operator
    (calculus : C(X, ℂ) →⋆ₐ[ℂ] (V →L[ℂ] V))
    (x : V) (f : C_c(X, ℝ)) (T : V →L[ℂ] V)
    (hf : calculus (characterRealComplexification f) =
      star (T - 1) * (T - 1)) :
    characterVectorFunctional calculus x f = ‖T x - x‖ ^ 2 := by
  change positiveVectorState x
    (calculus (characterRealComplexification f)) = ‖T x - x‖ ^ 2
  rw [hf, positiveVectorState_star_mul_self]
  simp only [sub_apply, one_apply_eq_self]

section PontryaginCharacter

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

theorem characterEnergy_complexification
    (a : A) (evaluation : C(DiscreteCharacterSpace A, ℂ))
    (hevaluation : ∀ χ : DiscreteCharacterSpace A,
      evaluation χ =
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ)) :
    characterRealComplexification (spectralEnergyTest a) =
      star (evaluation - 1) * (evaluation - 1) := by
  ext χ
  change
    ((‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2 : ℝ) : ℂ) =
      star (evaluation χ - 1) * (evaluation χ - 1)
  rw [hevaluation]
  simpa only [Complex.ofReal_pow, star_sub, RCLike.star_def, star_one, Complex.normSq_eq_norm_sq,
    map_sub, map_one] using
    (Complex.normSq_eq_conj_mul_self
      (z := ((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1))

theorem characterVectorFunctional_spectralEnergy
    (calculus : C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      (V →L[ℂ] V))
    (x : V) (a : A) (evaluation : C(DiscreteCharacterSpace A, ℂ))
    (hevaluation : ∀ χ : DiscreteCharacterSpace A,
      evaluation χ =
        ((χ (Multiplicative.ofAdd a) : Circle) : ℂ))
    (T : V →L[ℂ] V) (hT : calculus evaluation = T) :
    characterVectorFunctional calculus x (spectralEnergyTest a) =
      ‖T x - x‖ ^ 2 := by
  apply characterVectorFunctional_energy_of_operator calculus x
    (spectralEnergyTest a) T
  rw [characterEnergy_complexification a evaluation hevaluation,
    map_mul, map_star, map_sub, map_one, hT]

theorem characterVectorFunctional_spectralUnit
    (calculus : C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ]
      (V →L[ℂ] V)) (x : V) :
    characterVectorFunctional calculus x (spectralUnitTest A) =
      ‖x‖ ^ 2 :=
  characterVectorFunctional_one calculus x (spectralUnitTest A)
    (fun _ ↦ rfl)

end PontryaginCharacter

section JointCharacterFunctional

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]

/--
The `jointFunctionalCalculusOperator` construction used in the Connes rigidity formalization.
-/
def jointFunctionalCalculusOperator
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) :
    C(DiscreteCharacterSpace A, ℂ) →⋆ₐ[ℂ] (W →L[ℂ] W) :=
  (spectralOperatorAlgebra E π).subtype.comp
    (jointFunctionalCalculus E π)

@[simp] theorem jointFunctionalCalculusOperator_characterEvaluation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (a : A) :
    jointFunctionalCalculusOperator E π (spectralCharacterEvaluation a) =
      (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) := by
  change ((jointFunctionalCalculus E π
    (spectralCharacterEvaluation a) : spectralOperatorAlgebra E π) :
      W →L[ℂ] W) = _
  rw [jointFunctionalCalculus_characterEvaluation]
  rfl

/--
The `jointCharacterFunctional` construction used in the Connes rigidity formalization.
-/
def jointCharacterFunctional
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) :
    C_c(DiscreteCharacterSpace A, ℝ) →ₚ[ℝ] ℝ :=
  characterVectorFunctional (jointFunctionalCalculusOperator E π) x

@[simp] theorem jointCharacterFunctional_apply
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W)
    (f : C_c(DiscreteCharacterSpace A, ℝ)) :
    jointCharacterFunctional E π x f =
      (inner ℂ x
        ((jointFunctionalCalculusOperator E π
          (characterRealComplexification f)) x)).re := rfl

theorem jointCharacterFunctional_normalization
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) :
    jointCharacterFunctional E π x (spectralUnitTest A) = ‖x‖ ^ 2 :=
  characterVectorFunctional_spectralUnit
    (jointFunctionalCalculusOperator E π) x

theorem jointCharacterFunctional_energy
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (x : W) (a : A) :
    jointCharacterFunctional E π x (spectralEnergyTest a) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x - x‖ ^ 2 := by
  exact characterVectorFunctional_spectralEnergy
    (jointFunctionalCalculusOperator E π) x a
    (spectralCharacterEvaluation a) (fun _ ↦ rfl)
    (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W)
    (jointFunctionalCalculusOperator_characterEvaluation E π a)

theorem jointCharacterFunctional_pullback_of_operatorCovariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (h : H)
    (hcovariance : ∀ f : C(DiscreteCharacterSpace A, ℂ),
      jointFunctionalCalculusOperator E π
          (f.comp
            ⟨dualCharacterHomeomorph E.action h,
              (dualCharacterHomeomorph E.action h).continuous⟩) =
        star (π (E.splitting h) : W →L[ℂ] W) *
          jointFunctionalCalculusOperator E π f *
          (π (E.splitting h) : W →L[ℂ] W))
    (x : W) (f : C_c(DiscreteCharacterSpace A, ℝ)) :
    jointCharacterFunctional E π x
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f) =
      jointCharacterFunctional E π
        ((π (E.splitting h) : W →L[ℂ] W) x) f := by
  have hpullback :
      characterRealComplexification
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f) =
        (characterRealComplexification f).comp
          ⟨dualCharacterHomeomorph E.action h,
            (dualCharacterHomeomorph E.action h).continuous⟩ := by
    ext χ
    rfl
  change positiveVectorState x
    (jointFunctionalCalculusOperator E π
      (characterRealComplexification
        (compactTestPrecomp (dualCharacterHomeomorph E.action h) f))) =
    positiveVectorState
      ((π (E.splitting h) : W →L[ℂ] W) x)
      (jointFunctionalCalculusOperator E π
        (characterRealComplexification f))
  rw [hpullback, hcovariance]
  exact positiveVectorState_unitary_pullback x (π (E.splitting h))
    (jointFunctionalCalculusOperator E π
      (characterRealComplexification f))

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

theorem jointCharacterFunctional_riesz_covariance_of_operatorCovariance
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W) (h : H)
    (hcovariance : ∀ f : C(DiscreteCharacterSpace A, ℂ),
      jointFunctionalCalculusOperator E π
          (f.comp
            ⟨dualCharacterHomeomorph E.action h,
              (dualCharacterHomeomorph E.action h).continuous⟩) =
        star (π (E.splitting h) : W →L[ℂ] W) *
          jointFunctionalCalculusOperator E π f *
          (π (E.splitting h) : W →L[ℂ] W))
    (x : W) :
    (RealRMK.rieszMeasure (jointCharacterFunctional E π x)).map
        (dualCharacterAction E.action h) =
      RealRMK.rieszMeasure
        (jointCharacterFunctional E π
          ((π (E.splitting h) : W →L[ℂ] W) x)) := by
  apply rieszMeasure_dualCharacterAction E.action h
  exact jointCharacterFunctional_pullback_of_operatorCovariance
    E π h hcovariance x

end JointCharacterFunctional

end

noncomputable
section

open Connes InnerProductSpace

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `kernelUnitaryOrbit` construction used in the Connes rigidity formalization.
-/
def kernelUnitaryOrbit
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) : Set V :=
  Set.range fun a : A =>
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x

/--
The `kernelOrbitClosedConvexHull` construction used in the Connes rigidity formalization.
-/
def kernelOrbitClosedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) : Set V :=
  closedConvexHull ℝ (kernelUnitaryOrbit E π x)

theorem mem_kernelOrbitClosedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    x ∈ kernelOrbitClosedConvexHull E π x := by
  apply subset_closedConvexHull
  refine ⟨0, ?_⟩
  simp only [ofAdd_zero, map_one, OneMemClass.coe_one, one_apply_eq_self]

theorem kernelUnitary_preserves_closedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) (a : A) :
    ∀ y ∈ kernelOrbitClosedConvexHull E π x,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y ∈
        kernelOrbitClosedConvexHull E π x := by
  let orbit : Set V := kernelUnitaryOrbit E π x
  let U : V →L[ℝ] V :=
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V).restrictScalars ℝ
  have horbit : U '' orbit ⊆ orbit := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨a + b, ?_⟩
    change
      (π (E.inclusion (Multiplicative.ofAdd (a + b))) : V →L[ℂ] V) x =
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
          ((π (E.inclusion (Multiplicative.ofAdd b)) : V →L[ℂ] V) x)
    change
      (π (E.inclusion
        (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) : V →L[ℂ] V) x =
        ((↑(π (E.inclusion (Multiplicative.ofAdd a)) *
            π (E.inclusion (Multiplicative.ofAdd b))) : V →L[ℂ] V)) x
    rw [E.inclusion.map_mul, map_mul]
  have hhull : U '' convexHull ℝ orbit ⊆ convexHull ℝ orbit := by
    change U.toLinearMap '' convexHull ℝ orbit ⊆ convexHull ℝ orbit
    rw [LinearMap.image_convexHull]
    exact convexHull_mono horbit
  have hclosure : U '' closure (convexHull ℝ orbit) ⊆
      closure (convexHull ℝ orbit) :=
    (image_closure_subset_closure_image U.continuous).trans
      (closure_mono hhull)
  intro y hy
  have hy' : y ∈ closure (convexHull ℝ orbit) := by
    change y ∈ closedConvexHull ℝ orbit at hy
    rwa [closedConvexHull_eq_closure_convexHull] at hy
  have hUy : U y ∈ closure (convexHull ℝ orbit) :=
    hclosure ⟨y, hy', rfl⟩
  change U y ∈ closedConvexHull ℝ orbit
  rwa [closedConvexHull_eq_closure_convexHull]

private theorem spectralOrbit_norm_minimizer_fixed
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {S : Set W} (hconvex : Convex ℝ S)
    (U : W → W) (hUnorm : ∀ z, ‖U z‖ = ‖z‖)
    {y : W} (hy : y ∈ S)
    (hymin : ‖(0 : W) - y‖ = ⨅ z : S, ‖(0 : W) - z‖)
    (hU : ∀ z ∈ S, U z ∈ S) : U y = y := by
  have hinner :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hy).mp hymin
      (U y) (hU y hy)
  have hlower : ‖y‖ ^ 2 ≤ @inner ℝ W _ (U y) y := by
    rw [zero_sub, inner_neg_left, inner_sub_right,
      real_inner_self_eq_norm_sq] at hinner
    have hcomm : @inner ℝ W _ (U y) y = @inner ℝ W _ y (U y) :=
      real_inner_comm _ _
    rw [hcomm]
    linarith
  have hupper := real_inner_le_norm (U y) y
  rw [hUnorm] at hupper
  have heq : @inner ℝ W _ (U y) y = ‖y‖ ^ 2 := by
    linarith
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
  · exact le_of_eq (hUnorm y)
  · simpa only [RCLike.re_to_real] using heq

theorem exists_kernel_fixed_norm_minimizer
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    ∃ y ∈ kernelOrbitClosedConvexHull E π x,
      (∀ z ∈ kernelOrbitClosedConvexHull E π x, ‖y‖ ≤ ‖z‖) ∧
        ∀ a : A,
          (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y = y := by
  let S : Set V := kernelOrbitClosedConvexHull E π x
  have hnonempty : S.Nonempty :=
    ⟨x, mem_kernelOrbitClosedConvexHull E π x⟩
  have hclosed : IsClosed S :=
    isClosed_closedConvexHull
  have hconvex : Convex ℝ S :=
    convex_closedConvexHull
  let realInnerProduct : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  obtain ⟨y, hy, hnorm⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hnonempty hclosed.isComplete hconvex (0 : V)
  have hnorm' : ‖y‖ = ⨅ z : S, ‖(z : V)‖ := by
    simpa only [zero_sub, norm_neg] using hnorm
  have hminimal : ∀ z ∈ S, ‖y‖ ≤ ‖z‖ := by
    intro z hz
    rw [hnorm']
    have hbounded :
        BddBelow (Set.range fun w : S => ‖(w : V)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbounded (⟨z, hz⟩ : S)
  refine ⟨y, hy, hminimal, ?_⟩
  intro a
  exact spectralOrbit_norm_minimizer_fixed hconvex
    (fun z =>
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) z)
    (fun z =>
      (Unitary.linearIsometryEquiv
        (π (E.inclusion (Multiplicative.ofAdd a)))).norm_map z)
    hy hnorm (kernelUnitary_preserves_closedConvexHull E π x a)

theorem exists_kernel_fixed_mem_closedConvexHull
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) (x : V) :
    ∃ y ∈ kernelOrbitClosedConvexHull E π x,
      ∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) y = y := by
  obtain ⟨y, hy, _, hfixed⟩ :=
    exists_kernel_fixed_norm_minimizer E π x
  exact ⟨y, hy, hfixed⟩

end

section

open Connes

noncomputable
section

universe u

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}
variable (E : SplitAbelianExtension A G H)
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]
variable (π : UnitaryRepresentation G V)

theorem kernelOrbit_closedConvexHull_projection_eq_zero
    (x : V) (hx : trivialCharacterProjection E π x = 0) :
    ∀ y ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x),
      trivialCharacterProjection E π y = 0 := by
  let P : V →L[ℝ] V :=
    (trivialCharacterProjection E π).restrictScalars ℝ
  have horbit :
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) ⊆
      (LinearMap.ker P.toLinearMap : Set V) := by
    rintro _ ⟨a, rfl⟩
    change trivialCharacterProjection E π
      ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) = 0
    rw [trivialCharacterProjection_kernel_orbit, hx]
  have hclosed : IsClosed (LinearMap.ker P.toLinearMap : Set V) :=
    P.isClosed_ker
  have hsubset :=
    closedConvexHull_min horbit (LinearMap.ker P.toLinearMap).convex hclosed
  intro y hy
  exact hsubset hy

theorem kernel_fixed_inner_eq_zero_of_mem_closedConvexHull
    (x v y : V) (hx : trivialCharacterProjection E π x = 0)
    (hvfixed : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) v = v)
    (hy : y ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)) :
    inner ℂ v y = 0 := by
  have hprojection : trivialCharacterProjection E π y = 0 :=
    kernelOrbit_closedConvexHull_projection_eq_zero E π x hx y hy
  have horthogonal : y ∈ (kernelFixedSubmodule E π)ᗮ := by
    apply (Submodule.starProjection_apply_eq_zero_iff
      (kernelFixedSubmodule E π)).mp
    exact hprojection
  exact (Submodule.mem_orthogonal (kernelFixedSubmodule E π) y).mp
    horthogonal v ((mem_kernelFixedSubmodule E π v).mpr hvfixed)

theorem kernel_fixed_eq_zero_of_mem_closedConvexHull
    (x v : V) (hx : trivialCharacterProjection E π x = 0)
    (hv : v ∈ closedConvexHull ℝ
      (Set.range fun a : A =>
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x))
    (hvfixed : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) v = v) :
    v = 0 := by
  exact inner_self_eq_zero.mp
    (kernel_fixed_inner_eq_zero_of_mem_closedConvexHull
      E π x v v hx hvfixed hv)

end

end

noncomputable
section

open Connes

universe u v

theorem exists_finset_affineCombination_approx_of_mem_closedConvexHull
    {I : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (orbit : I → V) {y : V}
    (hy : y ∈ closedConvexHull ℝ (Set.range orbit))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset I) (w : I → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      ‖(∑ i ∈ s, w i • orbit i) - y‖ < ε := by
  rw [closedConvexHull_eq_closure_convexHull] at hy
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hy ε hε
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_ofPred_eq] at hz
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hz
  refine ⟨s, w, hw, hsum, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination s orbit w hsum] at hcomb
  rw [hcomb]
  simpa only [dist_eq_norm] using
    (show dist z y < ε by simpa only [dist_comm] using hdist)

theorem exists_finset_affineCombination_norm_lt_of_zero_mem_closedConvexHull
    {I : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (orbit : I → V)
    (hzero : (0 : V) ∈ closedConvexHull ℝ (Set.range orbit))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset I) (w : I → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      ‖∑ i ∈ s, w i • orbit i‖ < ε := by
  simpa only [sub_zero] using
    exists_finset_affineCombination_approx_of_mem_closedConvexHull
      orbit hzero hε

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}

theorem kernelOrbit_exists_finset_affineCombination_norm_lt
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V)
    (hzero : (0 : V) ∈ closedConvexHull ℝ
      (Set.range fun a : A ↦
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset A) (w : A → ℝ),
      (∀ a ∈ s, 0 ≤ w a) ∧
      (∑ a ∈ s, w a) = 1 ∧
      ‖∑ a ∈ s, w a •
        ((π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)‖ < ε :=
  exists_finset_affineCombination_norm_lt_of_zero_mem_closedConvexHull
    (fun a : A ↦
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x)
    hzero hε

end

noncomputable
section

open Connes

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem zero_mem_kernelOrbitClosedConvexHull_of_projection_eq_zero
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (x : V)
    (hx : trivialCharacterProjection E π x = 0) :
    (0 : V) ∈ kernelOrbitClosedConvexHull E π x := by
  obtain ⟨y, hy, hfixed⟩ :=
    exists_kernel_fixed_mem_closedConvexHull E π x
  have hzero : y = 0 := by
    apply kernel_fixed_eq_zero_of_mem_closedConvexHull E π x y hx
    · exact hy
    · exact hfixed
  simpa only [hzero] using hy

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
theorem kernelOrbitAffineApproximation
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) :
    HasKernelOrbitAffineApproximation E π := by
  intro x hx ε hε
  have hzero : (0 : V) ∈ closedConvexHull ℝ
      (Set.range fun a : A ↦
        (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) x) :=
    zero_mem_kernelOrbitClosedConvexHull_of_projection_eq_zero E π x hx
  obtain ⟨s, w, _, hw, hnorm⟩ :=
    kernelOrbit_exists_finset_affineCombination_norm_lt E π x hzero hε
  exact ⟨s, w, hw, hnorm⟩

theorem spectral_criterion_of_positive_functional_unconditional
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (functional : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (π : UnitaryRepresentation G V),
        PositiveSpectralFunctional E V π) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion_of_positive_functional_and_orbitApproximation
    E hH J hc hdetection functional
  exact fun V _ _ _ π ↦ kernelOrbitAffineApproximation E π

end

noncomputable
section

open Connes MeasureTheory

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/--
The `jointPositiveSpectralFunctional` construction used in the Connes rigidity formalization.
-/
def jointPositiveSpectralFunctional
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G V) :
    PositiveSpectralFunctional E V π where
  functional x := jointCharacterFunctional E π x
  normalization x := jointCharacterFunctional_normalization E π x
  energy x a := jointCharacterFunctional_energy E π x a
  covariance h x := by
    apply jointCharacterFunctional_riesz_covariance_of_operatorCovariance
      E π h ?_ x
    intro f
    simpa only [jointFunctionalCalculusOperator, dualCharacterHomeomorph,
      Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, StarAlgHom.comp_apply,
      StarSubalgebra.coe_subtype, dualCharacterActionContinuousMap] using
      jointFunctionalCalculus_quotient_covariance E π h f

/--
Zhou's §4 spectral criterion with no analytic input left as a hypothesis.
For a split extension with property-(T) quotient, a positive finite detector on
the dual of the abelian kernel implies property-(T) of the total group.
-/
theorem spectral_criterion_unconditional
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c) :
    HasKazhdanPropertyT G := by
  apply spectral_criterion_of_positive_functional_unconditional
    E hH J hc hdetection
  exact fun W _ _ _ π => jointPositiveSpectralFunctional E π

end

end Connes
