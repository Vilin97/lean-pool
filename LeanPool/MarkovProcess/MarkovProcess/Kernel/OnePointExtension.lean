/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Metrizable.Urysohn
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ResolventGeneration

/-!
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/

noncomputable section PortComputability

open Filter Set Topology TopologicalSpace

section

namespace OnePoint

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

private def basis : Set (Set (OnePoint X)) :=
  ((fun s : Set X => ((↑) '' s : Set (OnePoint X))) '' TopologicalSpace.countableBasis X) ∪
    Set.range (fun n : ℕ => OnePoint.opensOfCompl
      (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n))

private theorem basis_countable : (basis (X := X)).Countable := by
  apply Set.Countable.union
  · exact (TopologicalSpace.countable_countableBasis X).image _
  · exact Set.countable_range _

private theorem basis_isOpen (s : Set (OnePoint X)) (hs : s ∈ basis (X := X)) : IsOpen s := by
  rcases hs with hs | hs
  · rcases hs with ⟨u, hu, rfl⟩
    exact OnePoint.isOpen_image_coe.mpr
      ((TopologicalSpace.isBasis_countableBasis X).isOpen hu)
  · rcases hs with ⟨n, rfl⟩
    exact (OnePoint.opensOfCompl (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n)).is_open'

private theorem basis_isTopologicalBasis : IsTopologicalBasis (basis (X := X)) := by
  apply isTopologicalBasis_of_isOpen_of_nhds basis_isOpen
  intro z u hzu hu
  induction z using OnePoint.rec with
  | infty =>
    have hu_inf : OnePoint.infty ∈ u := hzu
    rw [OnePoint.isOpen_iff_of_mem hu_inf] at hu
    obtain ⟨n, hn⟩ := (CompactExhaustion.choice X).exists_superset_of_isCompact hu.2
    refine ⟨OnePoint.opensOfCompl (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n), ?_, ?_, ?_⟩
    · exact Or.inr ⟨n, rfl⟩
    · exact OnePoint.infty_mem_opensOfCompl _ _
    · intro z hz
      induction z using OnePoint.rec with
      | infty => exact hu_inf
      | coe x =>
        change (x : OnePoint X) ∈
          (((↑) '' (CompactExhaustion.choice X n)) : Set (OnePoint X))ᶜ at hz
        have hx : x ∈ ((CompactExhaustion.choice X n) : Set X)ᶜ := by
          simpa only [Set.mem_compl_iff, Set.mem_image, OnePoint.coe_eq_coe,
            exists_eq_right] using hz
        have hxpre : x ∈ ((↑) ⁻¹' u : Set X) := by
          by_contra hxnot
          exact hx (hn hxnot)
        exact hxpre
  | coe x =>
    have hx : x ∈ ((↑) ⁻¹' u : Set X) := hzu
    have hopen : IsOpen (((↑) ⁻¹' u : Set X)) :=
      OnePoint.continuous_coe.isOpen_preimage _ hu
    obtain ⟨v, hvbasis, hxv, hvu⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hx hopen
    refine ⟨((↑) '' v : Set (OnePoint X)), ?_, ⟨x, hxv, rfl⟩, ?_⟩
    · exact Or.inl ⟨v, hvbasis, rfl⟩
    · rintro _ ⟨y, hyv, rfl⟩
      exact hvu hyv

/-- The one-point compactification of a second-countable locally compact Hausdorff space is
second countable. -/
noncomputable instance instSecondCountableTopology : SecondCountableTopology (OnePoint X) :=
  (basis_isTopologicalBasis (X := X)).secondCountableTopology (basis_countable (X := X))

/-- The canonical measurable structure on a one-point compactification is its Borel structure. -/
instance instMeasurableSpace : MeasurableSpace (OnePoint X) :=
  borel (OnePoint X)

/-- The canonical measurable structure on a one-point compactification is Borel. -/
instance instBorelSpace : BorelSpace (OnePoint X) :=
  ⟨rfl⟩

end OnePoint

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- The part of a function on the one-point compactification which vanishes at infinity. -/
noncomputable def onePointRemainder (g : C₀(OnePoint X, ℝ)) : C₀(X, ℝ) where
  toFun x := g (x : OnePoint X) - g OnePoint.infty
  continuous_toFun :=
    (g.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hg := (OnePoint.continuous_iff (g : OnePoint X → ℝ)).mp g.continuous
    rw [← Filter.coclosedCompact_eq_cocompact]
    simpa only [Function.comp_apply, sub_self] using hg.1.sub_const (g OnePoint.infty)

/-- Reassemble a vanishing function and its value at infinity. -/
noncomputable def onePointAssemble (f : C₀(X, ℝ)) (c : ℝ) : C₀(OnePoint X, ℝ) :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
    (OnePoint.continuousMapMk (f.toContinuousMap + ContinuousMap.const X c) c (by
      rw [Filter.coclosedCompact_eq_cocompact]
      simpa only [ContinuousMap.coe_add, ContinuousMap.coe_const, Pi.add_apply, zero_add]
        using! (zero_at_infty f).add_const c))

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The remainder of a compactified observable, unfolded. -/
@[simp] theorem onePointRemainder_apply (g : C₀(OnePoint X, ℝ)) (x : X) :
    onePointRemainder g x = g (x : OnePoint X) - g OnePoint.infty := rfl

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The assembled observable at a live point. -/
@[simp] theorem onePointAssemble_coe (f : C₀(X, ℝ)) (c : ℝ) (x : X) :
    onePointAssemble f c (x : OnePoint X) = f x + c := by
  rfl

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The assembled observable at the added point. -/
@[simp] theorem onePointAssemble_infty (f : C₀(X, ℝ)) (c : ℝ) :
    onePointAssemble f c OnePoint.infty = c := by
  rfl

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Assembling an observable and taking the remainder returns it. -/
@[simp] theorem onePointRemainder_assemble (f : C₀(X, ℝ)) (c : ℝ) :
    onePointRemainder (onePointAssemble f c) = f := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [onePointRemainder_apply, onePointAssemble_coe, onePointAssemble_infty,
    add_sub_cancel_right]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Taking the remainder and reassembling at the value at infinity returns the observable. -/
@[simp] theorem onePointAssemble_remainder (g : C₀(OnePoint X, ℝ)) :
    onePointAssemble (onePointRemainder g) (g OnePoint.infty) = g := by
  apply ZeroAtInftyContinuousMap.ext
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp only [onePointAssemble_coe, onePointRemainder_apply, sub_add_cancel]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The remainder is additive. -/
@[simp] theorem onePointRemainder_add (g h : C₀(OnePoint X, ℝ)) :
    onePointRemainder (g + h) = onePointRemainder g + onePointRemainder h := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [onePointRemainder_apply, ZeroAtInftyContinuousMap.add_apply]
  ring

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The remainder commutes with scalar multiplication. -/
@[simp] theorem onePointRemainder_smul (c : ℝ) (g : C₀(OnePoint X, ℝ)) :
    onePointRemainder (c • g) = c • onePointRemainder g := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [onePointRemainder_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

private noncomputable def onePointRemainderLinearMap :
    C₀(OnePoint X, ℝ) →ₗ[ℝ] C₀(X, ℝ) where
  toFun := onePointRemainder
  map_add' := onePointRemainder_add
  map_smul' := onePointRemainder_smul

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
private theorem norm_onePointRemainder_le (g : C₀(OnePoint X, ℝ)) :
    ‖onePointRemainder g‖ ≤ 2 * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (by norm_num) (norm_nonneg g))).2 fun x ↦ ?_
  change ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤ 2 * ‖g‖
  calc
    ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤
        ‖g (x : OnePoint X)‖ + ‖g OnePoint.infty‖ := norm_sub_le _ _
    _ ≤ ‖g‖ + ‖g‖ := add_le_add
      (g.toBCF.norm_coe_le_norm (x : OnePoint X))
      (g.toBCF.norm_coe_le_norm OnePoint.infty)
    _ = 2 * ‖g‖ := by ring

private noncomputable def onePointRemainderCLM :
    C₀(OnePoint X, ℝ) →L[ℝ] C₀(X, ℝ) :=
  onePointRemainderLinearMap.mkContinuous 2 norm_onePointRemainder_le

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
@[simp] private theorem onePointRemainderCLM_apply (g : C₀(OnePoint X, ℝ)) :
    onePointRemainderCLM g = onePointRemainder g := rfl

variable [MeasurableSpace X] [BorelSpace X]

variable (R : PositiveC0ContractiveResolvent X)

/-- Extend the generated semigroup action by fixing the value at infinity. -/
noncomputable def onePointSemigroupAction (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    C₀(OnePoint X, ℝ) :=
  onePointAssemble
    (R.toContractiveResolvent.generatedSemigroup t (onePointRemainder g))
    (g OnePoint.infty)

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The extended action fixes the value of an observable at the added point. -/
@[simp] theorem onePointSemigroupAction_infty (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    R.onePointSemigroupAction t g OnePoint.infty = g OnePoint.infty := by
  rw [onePointSemigroupAction, onePointAssemble_infty]

/-- At a live point, the extended semigroup integrates over the original transition law and
assigns its missing mass to the value of the observable at infinity. -/
theorem onePointSemigroupAction_coe (t : NNReal) (g : C₀(OnePoint X, ℝ)) (x : X) :
    R.onePointSemigroupAction t g (x : OnePoint X) =
      ∫ y, g (y : OnePoint X) ∂R.kernelSemigroup t x +
        (1 - (R.kernelSemigroup t x).real Set.univ) * g OnePoint.infty := by
  rw [onePointSemigroupAction, onePointAssemble_coe,
    ← R.integral_kernelSemigroup t (onePointRemainder g) x]
  let μ := R.kernelSemigroup t x
  have hmassE := R.kernelSemigroup.measure_univ_le_one t x
  have hfin : μ Set.univ < ⊤ :=
    lt_of_le_of_lt hmassE ENNReal.one_lt_top
  let : IsFiniteMeasure μ := ⟨hfin⟩
  let gc : X →ᵇ ℝ := g.toBCF.compContinuous
    ⟨fun x : X ↦ (x : OnePoint X), OnePoint.continuous_coe⟩
  have hg : Integrable (fun y : X ↦ g (y : OnePoint X)) μ := gc.integrable μ
  rw [show (∫ y, onePointRemainder g y ∂μ) =
      ∫ y, (g (y : OnePoint X) - g OnePoint.infty) ∂μ by rfl,
    integral_sub hg (integrable_const _), integral_const]
  change (∫ y, g (y : OnePoint X) ∂μ) - μ.real Set.univ * g OnePoint.infty +
      g OnePoint.infty = _
  ring

private theorem norm_onePointSemigroupAction_le (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    ‖R.onePointSemigroupAction t g‖ ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun z ↦ ?_
  induction z using OnePoint.rec with
  | infty =>
      change ‖R.onePointSemigroupAction t g OnePoint.infty‖ ≤ ‖g‖
      rw [onePointSemigroupAction_infty]
      exact g.toBCF.norm_coe_le_norm OnePoint.infty
  | coe x =>
      change ‖R.onePointSemigroupAction t g (x : OnePoint X)‖ ≤ ‖g‖
      rw [Real.norm_eq_abs, onePointSemigroupAction_coe]
      let μ := R.kernelSemigroup t x
      have hmassE : μ Set.univ ≤ 1 := R.kernelSemigroup.measure_univ_le_one t x
      have hfin : μ Set.univ < ⊤ := lt_of_le_of_lt hmassE ENNReal.one_lt_top
      let : IsFiniteMeasure μ := ⟨hfin⟩
      have hmass0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
      have hmass1 : μ.real Set.univ ≤ 1 := by
        rw [measureReal_def]
        simpa only [ENNReal.toReal_one] using
          (ENNReal.toReal_le_toReal hfin.ne ENNReal.one_ne_top).mpr hmassE
      have hint : |∫ y, g (y : OnePoint X) ∂μ| ≤ ‖g‖ * μ.real Set.univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const
          (ae_of_all μ fun y ↦ g.toBCF.norm_coe_le_norm (y : OnePoint X))
      calc
        |∫ y, g (y : OnePoint X) ∂μ +
            (1 - μ.real Set.univ) * g OnePoint.infty| ≤
            |∫ y, g (y : OnePoint X) ∂μ| +
              |(1 - μ.real Set.univ) * g OnePoint.infty| := abs_add_le _ _
        _ ≤ ‖g‖ * μ.real Set.univ +
              (1 - μ.real Set.univ) * ‖g‖ := by
          refine add_le_add hint ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hmass1)]
          exact mul_le_mul_of_nonneg_left
            (g.toBCF.norm_coe_le_norm OnePoint.infty) (sub_nonneg.mpr hmass1)
        _ = ‖g‖ := by ring

private noncomputable def onePointSemigroupLinearMap (t : NNReal) :
    C₀(OnePoint X, ℝ) →ₗ[ℝ] C₀(OnePoint X, ℝ) where
  toFun := R.onePointSemigroupAction t
  map_add' g h := by
    apply ZeroAtInftyContinuousMap.ext
    intro z
    induction z using OnePoint.rec with
    | infty => simp only [onePointSemigroupAction_infty, ZeroAtInftyContinuousMap.add_apply]
    | coe x =>
      simp only [onePointSemigroupAction, onePointAssemble_coe, onePointRemainder_add,
        ZeroAtInftyContinuousMap.add_apply, map_add]
      abel
  map_smul' c g := by
    apply ZeroAtInftyContinuousMap.ext
    intro z
    induction z using OnePoint.rec with
    | infty => simp only [onePointSemigroupAction_infty, ZeroAtInftyContinuousMap.smul_apply,
        RingHom.id_apply]
    | coe x =>
      simp only [onePointSemigroupAction, onePointAssemble_coe, onePointRemainder_smul,
        ZeroAtInftyContinuousMap.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul]
      ring

/-- The contraction on the compactified function space induced at time `t`. -/
noncomputable def onePointSemigroupOperator (t : NNReal) :
    C₀(OnePoint X, ℝ) →L[ℝ] C₀(OnePoint X, ℝ) :=
  (R.onePointSemigroupLinearMap t).mkContinuous 1 fun g ↦ by
    simpa only [one_mul] using! R.norm_onePointSemigroupAction_le t g

/-- The bundled extended operator acts by the extended semigroup action. -/
@[simp] theorem onePointSemigroupOperator_apply (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    R.onePointSemigroupOperator t g = R.onePointSemigroupAction t g := rfl

private noncomputable def onePointEmbedLinearMap : C₀(X, ℝ) →ₗ[ℝ] C₀(OnePoint X, ℝ) where
  toFun := fun f ↦ onePointAssemble f 0
  map_add' f g := by
    apply ZeroAtInftyContinuousMap.ext
    intro z
    induction z using OnePoint.rec with
    | infty => simp only [onePointAssemble_infty, ZeroAtInftyContinuousMap.add_apply, add_zero]
    | coe x => simp only [onePointAssemble_coe, ZeroAtInftyContinuousMap.add_apply, add_zero]
  map_smul' c f := by
    apply ZeroAtInftyContinuousMap.ext
    intro z
    induction z using OnePoint.rec with
    | infty => simp only [onePointAssemble_infty, ZeroAtInftyContinuousMap.smul_apply,
        smul_zero, RingHom.id_apply]
    | coe x => simp only [onePointAssemble_coe, ZeroAtInftyContinuousMap.smul_apply,
        add_zero, smul_eq_mul, RingHom.id_apply]

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
private theorem norm_onePointEmbed_le (f : C₀(X, ℝ)) :
    ‖onePointAssemble f 0‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun z ↦ ?_
  induction z using OnePoint.rec with
  | infty =>
      change ‖onePointAssemble f 0 OnePoint.infty‖ ≤ ‖f‖
      rw [onePointAssemble_infty, norm_zero]
      exact norm_nonneg f
  | coe x =>
      change ‖onePointAssemble f 0 (x : OnePoint X)‖ ≤ ‖f‖
      rw [onePointAssemble_coe, add_zero]
      exact f.toBCF.norm_coe_le_norm x

private noncomputable def onePointEmbed : C₀(X, ℝ) →L[ℝ] C₀(OnePoint X, ℝ) :=
  onePointEmbedLinearMap.mkContinuous 1 fun f ↦ by
    simpa only [one_mul] using! norm_onePointEmbed_le f

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
@[simp] private theorem onePointEmbed_apply (f : C₀(X, ℝ)) :
    onePointEmbed f = onePointAssemble f 0 := rfl

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
private theorem onePointSemigroupAction_eq (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    R.onePointSemigroupAction t g =
      onePointEmbed (R.toContractiveResolvent.generatedSemigroup t (onePointRemainder g)) +
        onePointAssemble 0 (g OnePoint.infty) := by
  apply ZeroAtInftyContinuousMap.ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      simp only [onePointSemigroupAction_infty, onePointEmbed_apply,
        ZeroAtInftyContinuousMap.add_apply, onePointAssemble_infty, zero_add]
  | coe x =>
      simp only [onePointSemigroupAction, onePointAssemble_coe,
        onePointEmbed_apply, ZeroAtInftyContinuousMap.add_apply,
        ZeroAtInftyContinuousMap.zero_apply]
      ring

/-- The generated semigroup on the one-point compactification. -/
noncomputable def onePointSemigroup :
    Semigroup.StronglyContinuousContractionSemigroup C₀(OnePoint X, ℝ) where
  operator := R.onePointSemigroupOperator
  operator_zero := by
    apply ContinuousLinearMap.ext
    intro g
    rw [onePointSemigroupOperator_apply, onePointSemigroupAction,
      R.toContractiveResolvent.generatedSemigroup.zero_apply,
      onePointAssemble_remainder]
    rfl
  operator_add s t := by
    apply ContinuousLinearMap.ext
    intro g
    change R.onePointSemigroupAction (s + t) g =
      R.onePointSemigroupAction s (R.onePointSemigroupAction t g)
    rw [onePointSemigroupAction, onePointSemigroupAction,
      onePointSemigroupAction, onePointRemainder_assemble,
      R.toContractiveResolvent.generatedSemigroup.add_apply]
    rfl
  opNorm_le_one t := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    rw [onePointSemigroupOperator_apply, one_mul]
    exact R.norm_onePointSemigroupAction_le t g
  continuous_orbit g := by
    rw [show (fun t ↦ R.onePointSemigroupOperator t g) = fun t ↦
        onePointEmbed (R.toContractiveResolvent.generatedSemigroup t (onePointRemainder g)) +
          onePointAssemble 0 (g OnePoint.infty) by
      funext t
      rw [onePointSemigroupOperator_apply, onePointSemigroupAction_eq]]
    exact (onePointEmbed.continuous.comp
      (R.toContractiveResolvent.generatedSemigroup.continuous (onePointRemainder g))).add
        continuous_const

/-- The compactified semigroup acts by the extended semigroup action. -/
@[simp] theorem onePointSemigroup_apply (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    R.onePointSemigroup t g = R.onePointSemigroupAction t g := rfl

/-- The compactified semigroup preserves pointwise nonnegative functions. -/
theorem isPositive_onePointSemigroup (t : NNReal) :
    PositiveC0OperatorMeasure.IsPositive (R.onePointSemigroup t) := by
  intro g hg z
  induction z using OnePoint.rec with
  | infty =>
      rw [onePointSemigroup_apply, onePointSemigroupAction_infty]
      exact hg OnePoint.infty
  | coe x =>
      rw [onePointSemigroup_apply, onePointSemigroupAction_coe]
      apply add_nonneg
      · exact integral_nonneg fun y ↦ hg (y : OnePoint X)
      · apply mul_nonneg
        · have hmassE := R.kernelSemigroup.measure_univ_le_one t x
          have hfin : (R.kernelSemigroup t x) Set.univ ≠ ⊤ :=
            (lt_of_le_of_lt hmassE ENNReal.one_lt_top).ne
          rw [sub_nonneg, measureReal_def]
          simpa only [ENNReal.toReal_one] using
            (ENNReal.toReal_le_toReal hfin ENNReal.one_ne_top).mpr hmassE
        · exact hg OnePoint.infty

private noncomputable def onePointEvaluation (z : OnePoint X) :
    C₀(OnePoint X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ g z
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun g ↦ by
      rw [one_mul]
      exact g.toBCF.norm_coe_le_norm z

private theorem isPositive_onePointResolventOperator (mu : Semigroup.PositiveShift) :
    PositiveC0OperatorMeasure.IsPositive (R.onePointSemigroup.resolvent mu) := by
  intro g hg z
  change 0 ≤ (R.onePointSemigroup.resolvent mu g) z
  rw [Semigroup.StronglyContinuousContractionSemigroup.resolvent]
  change 0 ≤ onePointEvaluation z
    (∫ t in Set.Ioi (0 : ℝ), R.onePointSemigroup.laplaceIntegrand mu g t)
  rw [← (onePointEvaluation z).integral_comp_comm
    (R.onePointSemigroup.integrableOn_laplaceIntegrand mu.property g)]
  apply integral_nonneg_of_ae
  filter_upwards with t
  change 0 ≤ Real.exp (-(mu : ℝ) * t) *
    R.onePointSemigroup (Real.toNNReal t) g z
  exact mul_nonneg (Real.exp_pos _).le (R.isPositive_onePointSemigroup _ g hg z)

/-- The positive contractive resolvent on the genuine one-point compactification. -/
noncomputable def onePointResolvent : PositiveC0ContractiveResolvent (OnePoint X) where
  toContractiveResolvent := R.onePointSemigroup.toContractiveResolvent
  isPositive := R.isPositive_onePointResolventOperator

/-- The semigroup generated by the compactified resolvent is the compactified semigroup. -/
theorem generatedSemigroup_onePointResolvent :
    R.onePointResolvent.toContractiveResolvent.generatedSemigroup = R.onePointSemigroup :=
  R.onePointSemigroup.generatedSemigroup_toContractiveResolvent

private theorem onePointResolvent_remainder (mu : Semigroup.PositiveShift)
    (g : C₀(OnePoint X, ℝ)) :
    onePointRemainder (R.onePointResolvent.toContractiveResolvent.operator mu g) =
      R.toContractiveResolvent.operator mu (onePointRemainder g) := by
  change onePointRemainder (R.onePointSemigroup.resolvent mu g) = _
  rw [Semigroup.StronglyContinuousContractionSemigroup.resolvent]
  change onePointRemainderCLM
      (∫ t in Set.Ioi (0 : ℝ), R.onePointSemigroup.laplaceIntegrand mu g t) = _
  rw [← onePointRemainderCLM.integral_comp_comm
    (R.onePointSemigroup.integrableOn_laplaceIntegrand mu.property g)]
  rw [← R.toContractiveResolvent.resolvent_generatedSemigroup mu]
  change (∫ t in Set.Ioi (0 : ℝ), onePointRemainderCLM
      (R.onePointSemigroup.laplaceIntegrand mu g t)) =
    ∫ t in Set.Ioi (0 : ℝ),
      R.toContractiveResolvent.generatedSemigroup.laplaceIntegrand mu
        (onePointRemainder g) t
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
    map_smul, onePointRemainderCLM_apply, onePointSemigroup_apply,
    onePointSemigroupAction, onePointRemainder_assemble]

private theorem onePointResolvent_infty (mu : Semigroup.PositiveShift)
    (g : C₀(OnePoint X, ℝ)) :
    R.onePointResolvent.toContractiveResolvent.operator mu g OnePoint.infty =
      (mu : ℝ)⁻¹ * g OnePoint.infty := by
  change R.onePointSemigroup.resolvent mu g OnePoint.infty = _
  rw [Semigroup.StronglyContinuousContractionSemigroup.resolvent]
  change onePointEvaluation OnePoint.infty
      (∫ t in Set.Ioi (0 : ℝ), R.onePointSemigroup.laplaceIntegrand mu g t) = _
  rw [← (onePointEvaluation OnePoint.infty).integral_comp_comm
    (R.onePointSemigroup.integrableOn_laplaceIntegrand mu.property g)]
  change (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(mu : ℝ) * t) * g OnePoint.infty) = _
  rw [integral_mul_const,
    Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero mu.property]

/-- The compactified resolvent evolves the vanishing remainder and divides the value at infinity
by the shift. -/
theorem onePointResolvent_operator (mu : Semigroup.PositiveShift)
    (g : C₀(OnePoint X, ℝ)) :
    R.onePointResolvent.toContractiveResolvent.operator mu g =
      onePointAssemble
        (R.toContractiveResolvent.operator mu (onePointRemainder g))
        ((mu : ℝ)⁻¹ * g OnePoint.infty) := by
  rw [← R.onePointResolvent_remainder mu g, ← R.onePointResolvent_infty mu g]
  exact (onePointAssemble_remainder _).symm

/-- The Feller kernel semigroup represented by the compactified resolvent. -/
noncomputable def onePointKernelSemigroup : SubMarkovKernelSemigroup (OnePoint X) :=
  R.onePointResolvent.kernelSemigroup

/-- The represented compactified kernel semigroup is Feller. -/
theorem isFellerKernelSemigroup_onePointKernelSemigroup :
    R.onePointKernelSemigroup.IsFellerKernelSemigroup :=
  R.onePointResolvent.isFellerKernelSemigroup_kernelSemigroup

/-- The compactified kernel semigroup acts on continuous functions by the compactified
semigroup. -/
theorem integral_onePointKernelSemigroup (t : NNReal) (g : C₀(OnePoint X, ℝ))
    (z : OnePoint X) :
    ∫ w, g w ∂R.onePointKernelSemigroup t z = R.onePointSemigroup t g z := by
  rw [onePointKernelSemigroup, R.onePointResolvent.integral_kernelSemigroup,
    R.generatedSemigroup_onePointResolvent]

private noncomputable def onePointConstant (c : ℝ) : C₀(OnePoint X, ℝ) :=
  onePointAssemble 0 c

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
@[simp] private theorem onePointConstant_apply (c : ℝ) (z : OnePoint X) :
    onePointConstant c z = c := by
  induction z using OnePoint.rec with
  | infty => exact onePointAssemble_infty 0 c
  | coe x => simp only [onePointConstant, onePointAssemble_coe,
      ZeroAtInftyContinuousMap.zero_apply, zero_add]

/-- The compactified semigroup fixes the constants. -/
theorem onePointSemigroup_constant (t : NNReal) (c : ℝ) :
    R.onePointSemigroup t (onePointConstant c) = onePointConstant c := by
  rw [onePointSemigroup_apply, onePointSemigroupAction, onePointConstant,
    onePointRemainder_assemble]
  simp only [map_zero, onePointAssemble_infty]

/-- The represented compactified semigroup is conservative. -/
theorem isConservative_onePointKernelSemigroup :
    R.onePointKernelSemigroup.IsConservative := by
  intro t z
  have h := R.integral_onePointKernelSemigroup t (onePointConstant 1) z
  rw [R.onePointSemigroup_constant] at h
  simp only [onePointConstant_apply, integral_const, smul_eq_mul, mul_one] at h
  rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h
  exact h

/-- The added point is absorbing for every transition kernel of the compactified semigroup. -/
theorem onePointKernelSemigroup_absorbing (t : NNReal) :
    R.onePointKernelSemigroup t OnePoint.infty = Measure.dirac OnePoint.infty := by
  rw [onePointKernelSemigroup, PositiveC0ContractiveResolvent.kernelSemigroup,
    PositiveC0SemigroupKernel.kernelSemigroup_apply,
    PositiveC0OperatorKernel.kernel_apply]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let f₀ : C₀(OnePoint X, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have h := R.integral_onePointKernelSemigroup t f₀ OnePoint.infty
  rw [onePointSemigroup_apply, onePointSemigroupAction_infty] at h
  change (∫ x, f x ∂R.onePointKernelSemigroup t OnePoint.infty) = f OnePoint.infty at h
  simpa only [integral_dirac] using! h


end MarkovProcess.PositiveC0ContractiveResolvent

end

end PortComputability
