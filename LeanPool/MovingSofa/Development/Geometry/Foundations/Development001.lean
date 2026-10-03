/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.MinMax
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Moving sofa: related mathematical developments

* `Infrastructure.Analysis.Foundations.Development001`.
* `Infrastructure.Geometry.Foundations.Development001`.
* `Infrastructure.MathlibExtensions.Foundations.Development001`.
* `Infrastructure.Geometry.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.BoundedDensity`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Bounded Density
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace MovingSofa

theorem boundedDensity_of_domination (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (q : ℝ → ℝ) (hq : Measurable q)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hq_bound : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, q t ≤ C)
    (hdom : ∀ E : Set ℝ, MeasurableSet E →
      μ E ≤ ENNReal.ofReal (∫ t in E, q t ∂volume.restrict (Set.Icc a b))) :
    ∃ r : ℝ → ℝ, Measurable r ∧ Integrable r (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), 0 ≤ r t ∧ r t ≤ q t) ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ ENNReal.ofReal (r t)) ∧
      (∃ C : ℝ, ∀ᵐ t ∂volume.restrict (Set.Icc a b), |r t| ≤ C) := by
  classical
  obtain ⟨C, hC⟩ := hq_bound
  let lam : Measure ℝ := volume.restrict (Set.Icc a b)
  let nu : Measure ℝ := lam.withDensity (fun t ↦ ENNReal.ofReal (q t))
  have hq_ae : 0 ≤ᵐ[lam] q := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hq_nonneg t ht
  have hq_bound_ae : ∀ᵐ t ∂lam, ‖q t‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg t ht)]
    exact le_max_of_le_left (hC t ht)
  have hq_int : Integrable q lam := by
    exact Measure.integrableOn_of_bounded (μ := volume)
      (s := Set.Icc a b) (M := max C 0) (by simp) hq.aestronglyMeasurable hq_bound_ae
  have hν_apply : ∀ E : Set ℝ, MeasurableSet E →
      nu E = ENNReal.ofReal (∫ t in E, q t ∂lam) := by
    intro E hE
    change (lam.withDensity (fun t ↦ ENNReal.ofReal (q t))) E = _
    rw [withDensity_apply _ hE]
    exact (ofReal_integral_eq_lintegral_ofReal
      (μ := lam.restrict E) hq_int.integrableOn
      (ae_restrict_of_ae hq_ae)).symm
  have hμν : μ ≤ nu := by
    rw [Measure.le_iff]
    intro E hE
    rw [hν_apply E hE]
    exact hdom E hE
  have hνlam : nu.AbsolutelyContinuous lam :=
    withDensity_absolutelyContinuous lam _
  have hμlam : μ.AbsolutelyContinuous lam :=
    (Measure.absolutelyContinuous_of_le hμν).trans hνlam
  let r : ℝ → ℝ := fun t ↦ (μ.rnDeriv lam t).toReal
  have hr_meas : Measurable r := by
    exact (Measure.measurable_rnDeriv μ lam).ennreal_toReal
  have hr_int : Integrable r lam := by
    simpa [r] using
      (Measure.integrableOn_toReal_rnDeriv
        (μ := μ) (ν := lam) (s := Set.univ) (by simp))
  have hr_eq : lam.withDensity (fun t ↦ μ.rnDeriv lam t) = μ :=
    Measure.withDensity_rnDeriv_eq μ lam hμlam
  have hr_le_q_enn : μ.rnDeriv lam ≤ᵐ[lam] (fun t ↦ ENNReal.ofReal (q t)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Measure.measurable_rnDeriv μ lam)
    intro E hE hEfin
    rw [Measure.setLIntegral_rnDeriv hμlam E]
    calc
      μ E ≤ nu E := hμν E
      _ = ∫⁻ t in E, ENNReal.ofReal (q t) ∂lam := by
        exact withDensity_apply' _ _
  have hr_bounds : ∀ᵐ t ∂lam, 0 ≤ r t ∧ r t ≤ q t := by
    filter_upwards [hr_le_q_enn, Measure.rnDeriv_ne_top μ lam,
      ae_restrict_mem measurableSet_Icc] with t hle htop ht
    constructor
    · exact ENNReal.toReal_nonneg
    · have hto := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mpr hle
      simpa [r, ENNReal.toReal_ofReal (hq_nonneg t ht)] using hto
  have hfun : (fun t ↦ ENNReal.ofReal (r t)) =ᵐ[lam] μ.rnDeriv lam := by
    filter_upwards [Measure.rnDeriv_ne_top μ lam] with t htop
    simpa [r] using ENNReal.ofReal_toReal htop
  have hr_eq' : lam.withDensity (fun t ↦ ENNReal.ofReal (r t)) = μ := by
    rw [← hr_eq]
    exact withDensity_congr_ae hfun
  have hr_bound : ∃ K : ℝ, ∀ᵐ t ∂lam, |r t| ≤ K := by
    refine ⟨max C 0, ?_⟩
    filter_upwards [hr_bounds, ae_restrict_mem measurableSet_Icc] with t ⟨h₀, hq⟩ ht
    rw [abs_of_nonneg h₀]
    exact hq.trans ((hC t ht).trans (le_max_left _ _))
  refine ⟨r, hr_meas, hr_int, hr_bounds, ?_, hr_bound⟩
  simpa [lam] using hr_eq'.symm

/-- A finite measure carried by `Set.Icc a b` and dominated on that interval by the integral of
a bounded, almost everywhere strongly measurable nonnegative function `f` has an integrable real
density with respect to the Lebesgue measure on `Set.Icc a b`, and that density is bounded above
by `f` almost everywhere. -/
theorem exists_density_le_of_domination {a b : ℝ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ, Measurable r ∧ IntegrableOn r (Set.Icc a b) volume ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), 0 ≤ r t ∧ r t ≤ f t) ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ ENNReal.ofReal (r t)) := by
  classical
  obtain ⟨g, hg, hgf⟩ := hf
  set q : ℝ → ℝ := fun t ↦ max 0 (min M (g t)) with hq
  have hq_meas : Measurable q := measurable_const.max (measurable_const.min hg.measurable)
  have hq_nonneg : ∀ t, 0 ≤ q t := fun t ↦ le_max_left _ _
  have hq_bound : ∀ t, q t ≤ max M 0 := fun t ↦
    max_le (le_max_right M 0) ((min_le_left _ _).trans (le_max_left _ _))
  have hqf : f =ᵐ[volume.restrict (Set.Icc a b)] q := by
    filter_upwards [hgf, ae_restrict_mem measurableSet_Icc] with t hgt ht
    simp only [hq, ← hgt, min_eq_right (hf_bound t ht), max_eq_right (hf_nonneg t ht)]
  have hdom' : ∀ E : Set ℝ, MeasurableSet E →
      μ E ≤ ENNReal.ofReal (∫ t in E, q t ∂volume.restrict (Set.Icc a b)) := by
    intro E hE
    have hnull : μ (E \ Set.Icc a b) = 0 := measure_mono_null (fun x hx ↦ hx.2) hμ
    have hEsub : μ E ≤ μ (E ∩ Set.Icc a b) :=
      calc μ E ≤ μ (E ∩ Set.Icc a b) + μ (E \ Set.Icc a b) := measure_le_inter_add_sdiff μ E _
        _ = μ (E ∩ Set.Icc a b) := by rw [hnull, add_zero]
    refine hEsub.trans ((hdom _ (hE.inter measurableSet_Icc) Set.inter_subset_right).trans ?_)
    rw [Measure.restrict_restrict hE]
    exact le_of_eq (congrArg ENNReal.ofReal (integral_congr_ae
      (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hqf)))
  obtain ⟨r, hr_meas, hr_int, hr_bounds, hr_eq, -⟩ :=
    boundedDensity_of_domination a b μ q hq_meas (fun t _ ↦ hq_nonneg t)
      ⟨max M 0, fun t _ ↦ hq_bound t⟩ hdom'
  refine ⟨r, hr_meas, hr_int, ?_, hr_eq⟩
  filter_upwards [hr_bounds, hqf] with t ht htq
  exact ⟨ht.1, htq ▸ ht.2⟩

/-- A finite measure carried by `Set.Icc a b` and dominated on that interval by the integral of
a bounded, almost everywhere strongly measurable nonnegative function has a measurable
`ℝ≥0`-valued density with respect to the Lebesgue measure on `Set.Icc a b`. -/
theorem exists_nnreal_density_of_domination {a b : ℝ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ (r t : ℝ≥0∞)) := by
  obtain ⟨r, hr_meas, -, -, hr_eq⟩ :=
    exists_density_le_of_domination μ hμ f hf hf_nonneg hf_bound hdom
  exact ⟨fun t ↦ (r t).toNNReal, hr_meas.real_toNNReal, hr_eq⟩

end MovingSofa

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Classical.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Classical.Area`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Planar area

The real-valued Lebesgue area of a planar set, and its invariance under translation.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa.ClassicalResults

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The real-valued Lebesgue area of a planar set. -/
@[expose]
def area (s : Set Plane) : ℝ := (volume s).toReal

/-- Planar area is invariant under translation. -/
theorem area_image_add (S : Set Plane) (v : Plane) :
    area ((fun p ↦ p + v) '' S) = area S := by
  change (MeasureTheory.volume ((fun p ↦ p + v) '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [Set.image_add_right]
  have hf : (fun x : Plane ↦ x + -v) = fun x ↦ -v + x := by
    funext x
    exact add_comm x (-v)
  rw [hf, MeasureTheory.measure_preimage_add]

end MovingSofa.ClassicalResults

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Algebra.Foundations.Development001`.
* `ForMathlib.Analysis.Foundations.Development001`.
* `ForMathlib.BoundedVariation.Foundations.Development001`.
* `ForMathlib.Convex.Foundations.Development001`.
* `ForMathlib.Geometry.Foundations.Development001`.
* `ForMathlib.MeasureTheory.Foundations.Development001`.
* `ForMathlib.Order.Foundations.Development001`.
* `ForMathlib.Topology.Foundations.Development001`.
* `ForMathlib.MeasureTheory.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Algebra.BigOperators.Triangle`.
* `ForMathlib.Algebra.Order.Fin`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Triangular rearrangement of a double sum over a `Finset`

A double sum over `s ×ˢ s` splits into the closed lower triangle `{(u, t) | u ≤ t}` and its
transpose. The two pieces overlap exactly on the diagonal, so for a kernel vanishing there the
lower-triangular sum plus its transpose recovers the whole double sum.

`Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag` is the `Fintype` and `LocallyFiniteOrder` analogue,
and `Fin.sum_sum_eq_sum_triangle_add` the `Fin` analogue; neither applies to a general `Finset`
of a plain `LinearOrder`.
-/

public section

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]

/-- For a kernel vanishing on the diagonal, the closed lower-triangular double sum plus the same
sum with the two arguments swapped is the full double sum. -/
theorem sum_filter_le_add_sum_filter_le_swap (s : Finset ι) (f : ι → ι → M)
    (hdiag : ∀ x, f x x = 0) :
    ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
        ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  calc ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u)
      = (∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ t < u), f t u) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u := by
        rw [Finset.sum_comm' (t' := s) (s' := fun u ↦ s.filter (fun t ↦ u ≤ t))
          (by simp; tauto)]
        refine congrArg₂ _ (Finset.sum_congr rfl fun t _ ↦ (Finset.sum_subset
          (monotone_filter_right _ fun _ _ ↦ le_of_lt) fun u hu hu' ↦ ?_).symm) rfl
        simp only [mem_filter, not_and, not_lt] at hu hu'
        rw [le_antisymm (hu' hu.1) hu.2, hdiag]
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y := by
        rw [add_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by
          simpa using Finset.sum_filter_add_sum_filter_not s (· ≤ x) (f x)

end Finset

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Algebra / Order / Fin
-/

public section

noncomputable section

namespace Fin

/-- A finite sequence is bounded by its final value plus its positive backward increments. -/
theorem apply_le_last_add_sum_max_sub {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    f i ≤ f (Fin.last n) + ∑ j : Fin n, max (f j.castSucc - f j.succ) 0 := by
  induction n with
  | zero => fin_cases i; simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail (k : Fin (n + 1)) := ih (fun j ↦ f j.succ) k
    have hnonneg : 0 ≤ max (f 0 - f (Fin.succ 0)) 0 := le_max_right _ _
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · have h := htail 0
      have hmax := le_max_left (f 0 - f (Fin.succ 0)) 0
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f 0 ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)
    · have h := htail k
      simpa only [Fin.succ_last, Fin.succ_castSucc, Fin.castSucc_zero] using
        (show f k.succ ≤ f (Fin.last (n + 1)) +
          (max (f 0 - f (Fin.succ 0)) 0 +
            ∑ j : Fin n, max (f j.castSucc.succ - f j.succ.succ) 0) by
          simp only [Fin.succ_last] at h
          linarith)

end Fin

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Analysis.Calculus.Deriv.Shift`.
* `ForMathlib.Analysis.Calculus.FirstReturn`.
* `ForMathlib.Analysis.Calculus.Interval`.
* `ForMathlib.Analysis.Calculus.LocalExtr.OneSided`.
* `ForMathlib.Analysis.Complex.DiskIntegral`.
* `ForMathlib.Analysis.Convex.Basic`.
* `ForMathlib.Analysis.Convex.Deriv`.
* `ForMathlib.Analysis.Convex.Gauge`.
* `ForMathlib.Analysis.Convex.GaugeRescale`.
* `ForMathlib.Analysis.Convex.Radial`.
* `ForMathlib.Analysis.FiniteEnvelope`.
* `ForMathlib.Analysis.InnerProductSpace.Box`.
* `ForMathlib.Analysis.InnerProductSpace.Linear`.
* `ForMathlib.Analysis.Normed.Affine.ContinuousAffineMap`.
* `ForMathlib.Analysis.SpecialFunctions.Angle`.
* `ForMathlib.Analysis.SpecialFunctions.AngleLift`.
* `ForMathlib.Analysis.SpecialFunctions.Arctan`.
* `ForMathlib.Analysis.SpecificLimits.AlternatingBracket`.
* `ForMathlib.Analysis.SpecialFunctions.Trigonometric`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Shifting the base point of a derivative

`HasDerivAt.comp_add_const` transports a derivative at a shifted base point to the shifted
function; this file records the converse implication, packaged as an `Iff`.
-/

public section

/-- A derivative at a shifted base point is the derivative of the shifted function. -/
theorem hasDerivAt_comp_add_const_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} (x a : 𝕜) :
    HasDerivAt (fun u ↦ f (u + a)) f' x ↔ HasDerivAt f f' (x + a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_add_const x a⟩
  have h' : HasDerivAt (fun u ↦ f (u + a)) f' (x + a + -a) := by simpa using h
  simpa using h'.comp_add_const (x + a) (-a)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# First return to a level

A continuous real function that starts strictly below a level and reaches it has a smallest
time at which it attains that level, and its derivative there is nonnegative.
-/

public section

/-- A continuous function below a level at the left end has a first return to that level. -/
theorem exists_first_return {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b)) (hga : g a < c) (hgb : c ≤ g b) :
    ∃ t ∈ Set.Ioc a b, g t = c ∧ ∀ u ∈ Set.Ico a t, g u < c := by
  set E : Set ℝ := Set.Icc a b ∩ g ⁻¹' Set.Ici c with hE
  have hEcl : IsClosed E := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hEne : E.Nonempty := ⟨b, ⟨hab.le, le_refl b⟩, hgb⟩
  have hEbdd : BddBelow E := ⟨a, fun u hu => hu.1.1⟩
  set t : ℝ := sInf E with ht
  have htE : t ∈ E := hEcl.csInf_mem hEne hEbdd
  have htlb : ∀ u ∈ E, t ≤ u := fun u hu => csInf_le hEbdd hu
  have hta : a < t := by
    rcases eq_or_lt_of_le htE.1.1 with h | h
    · exact absurd htE.2 (by rw [← h]; exact not_le.mpr hga)
    · exact h
  have hleft : ∀ u ∈ Set.Ico a t, g u < c := by
    intro u hu
    by_contra hcc
    push Not at hcc
    exact absurd (htlb u ⟨⟨hu.1, le_trans hu.2.le htE.1.2⟩, hcc⟩) (not_le.mpr hu.2)
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hta
  have hsub : Set.Ico a t ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2.le htE.1.2⟩
  have htend : Filter.Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (g t)) :=
    ((hcont t htE.1).mono hsub).tendsto.mono_left (nhdsWithin_le_of_mem hIco)
  refine ⟨t, ⟨hta, htE.1.2⟩, le_antisymm ?_ htE.2, hleft⟩
  exact le_of_tendsto htend (Filter.eventually_of_mem hIco fun u hu => (hleft u hu).le)

/-- At a first return from below, the derivative is nonnegative. -/
theorem nonneg_of_first_return {g : ℝ → ℝ} {a t c d : ℝ} (hat : a < t)
    (hd : HasDerivAt g d t) (hgt : g t = c) (hleft : ∀ u ∈ Set.Ico a t, g u < c) :
    0 ≤ d := by
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hat
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono t (fun x hx => ne_of_lt hx) :
      nhdsWithin t (Set.Iio t) ≤ nhdsWithin t {t}ᶜ)
  refine ge_of_tendsto hsl (Filter.eventually_of_mem hIco fun u hu => ?_)
  rw [slope_def_field, hgt]
  exact le_of_lt (div_pos_of_neg_of_neg (by linarith only [hleft u hu])
    (by linarith only [hu.2]))

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Calculus / Interval
-/

public section

open Set

/-- Glue one-sided derivatives on a closed interval, including its endpoints. -/
theorem hasDerivWithinAt_Icc_of_oneSided {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {f : ℝ → E} {d : E}
    (hr : t < b → HasDerivWithinAt f d (Ici t) t)
    (hl : a < t → HasDerivWithinAt f d (Iic t) t) :
    HasDerivWithinAt f d (Icc a b) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact (hr hab).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · have h := (hl hat).union (hr htb)
      rw [Iic_union_Ici] at h
      exact h.mono (subset_univ _)
    · exact (hl hat).mono Icc_subset_Iic_self

/-- A continuous derivative field on a uniquely differentiable set gives order-one regularity. -/
theorem contDiffOn_one_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (f : ℝ → E) (d : s → E) (hd : Continuous d)
    (hf : ∀ t : s, HasDerivWithinAt f (d t) s t) : ContDiffOn ℝ 1 f s := by
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht ↦ (hf ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hd.congr
  intro t
  exact ((hf t).derivWithin (hs t t.property)).symm

/-- Glue two everywhere differentiable functions along the switch `{s ≤ c}`.  If the values
and the derivatives agree at `c`, the glued function is differentiable everywhere and its
derivative is the analogous glue of the two derivative fields.  At `c` itself the statement
is genuine two-sided differentiability, obtained from the two one-sided derivatives. -/
theorem hasDerivAt_if_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hfg' : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ c then f s else g s) (if t ≤ c then f' t else g' t) t := by
  rcases lt_trichotomy t c with ht | ht | ht
  · rw [ite_eq_left ht.le]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact ite_eq_left (le_of_lt hs)
  · subst ht
    rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Iic t) t :=
      (hf t).hasDerivWithinAt.congr (fun _ hs => ite_eq_left hs) (ite_eq_left le_rfl)
    have hr : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Ici t) t := by
      rw [hfg']
      refine (hg t).hasDerivWithinAt.congr (fun s hs => ?_) (by rw [ite_eq_left le_rfl, hfg])
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with rfl | hlt
      · rw [ite_eq_left le_rfl, hfg]
      · rw [ite_eq_right (not_le.mpr hlt)]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · rw [ite_eq_right (not_le.mpr ht)]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ite_eq_right (not_le.mpr hs)

/-- A globally defined continuous derivative field witnesses continuous differentiability. -/
theorem contDiff_one_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ContDiff ℝ 1 f :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hf t).differentiableAt, deriv_eq hf ▸ hf'⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Fermat's theorem for one-sided derivatives on the real line

`IsLocalMinOn.hasFDerivWithinAt_nonneg` signs a derivative within a set against the positive
tangent cone of that set.  On the real line the positive tangent cones of the two half-lines
at `a` are generated by `1` and by `-1`, which turns that statement into the two familiar
one-sided derivative tests at a one-sided minimum.
-/

public section

/-- The forward direction belongs to the positive tangent cone of a right half-line. -/
theorem one_mem_posTangentConeAt_Ici (a : ℝ) : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Ici a).segment_subset (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith)))

/-- The backward direction belongs to the positive tangent cone of a left half-line. -/
theorem neg_one_mem_posTangentConeAt_Iic (a : ℝ) :
    (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Iic a).segment_subset (Set.mem_Iic.2 le_rfl) (Set.mem_Iic.2 (by linarith)))

/-- A right derivative at a minimum over a right half-line is nonnegative. -/
theorem IsLocalMinOn.hasDerivWithinAt_Ici_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by
  simpa using h.hasFDerivWithinAt_nonneg hf (one_mem_posTangentConeAt_Ici a)

/-- A left derivative at a minimum over a left half-line is nonpositive. -/
theorem IsLocalMinOn.hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 :=
  neg_nonneg.1 <| by
    simpa using h.hasFDerivWithinAt_nonneg hf (neg_one_mem_posTangentConeAt_Iic a)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Complex / Disk Integral
-/

public section

noncomputable section

open MeasureTheory

namespace Complex

private theorem integrableOn_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (hg : Integrable g) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • g (polarCoord.symm p))
      polarCoord.target := by
  have hinj : Set.InjOn (polarCoord.symm : ℝ × ℝ → ℝ × ℝ)
      polarCoord.target := by
    rw [← polarCoord.symm_source]
    exact polarCoord.symm.injOn
  have himage : polarCoord.symm '' polarCoord.target =
      polarCoord.source := by
    rw [← polarCoord.symm_source, ← polarCoord.symm_target]
    exact polarCoord.symm.image_source_eq_target
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (s := polarCoord.target) volume polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    hinj g).mp (by
      rw [himage]
      exact hg.integrableOn)
  refine hj.congr_fun ?_ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]

private theorem integrableOn_complex_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  let g : ℝ × ℝ → F := f ∘ Complex.measurableEquivRealProd.symm
  have hg : Integrable g :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  have h := integrableOn_polarCoord_target g hg
  change IntegrableOn
    (fun p ↦ p.1 • (f ∘ Complex.measurableEquivRealProd.symm)
      (polarCoord.symm p)) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) at h
  simpa only [Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply] using h

private theorem integral_circleMap_Ioo_eq_circleAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi), smul_smul]
  have hp : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [hp, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun θ ↦ f (circleMap 0 r θ)) (a := 0) (b := 2 * Real.pi) (-Real.pi)
  simpa [two_mul] using hshift.symm

/-- The radial profile of the inverse distance truncated to a disk of radius `S`. -/
private def invNormCutoff (S r : ℝ) : ℝ := if r < S then r⁻¹ else 0

private theorem indicator_ball_inv_norm_eq (S : ℝ) :
    (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
      fun p ↦ invNormCutoff S ‖p‖ := by
  funext p
  rw [Set.indicator]
  simp only [Metric.mem_ball, dist_zero_right, invNormCutoff]

private theorem radial_invNormCutoff_ae (S : ℝ) :
    (fun y : ℝ ↦ y ^ (Module.finrank ℝ ℂ - 1) • invNormCutoff S y)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (Set.Iio S).indicator (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp [invNormCutoff, Set.indicator, smul_eq_mul, hy0]

/-- Inverse distance from zero is integrable on a complex disk centred at zero. -/
theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : ℂ ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  change Integrable (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p)
  rw [indicator_ball_inv_norm_eq,
    MeasureTheory.integrable_fun_norm_addHaar volume (f := invNormCutoff S)]
  refine IntegrableOn.congr_fun_ae ?_ (radial_invNormCutoff_ae S).symm
  rw [integrableOn_indicator_iff measurableSet_Iio, Set.Iio_inter_Ioi]
  exact integrableOn_const (by simp)

/-- The integral of inverse distance from zero over a complex disk centred at zero. -/
theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : ℂ in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : ℂ ↦ ‖p‖⁻¹) measurableSet_ball,
    indicator_ball_inv_norm_eq,
    MeasureTheory.integral_fun_norm_addHaar volume (invNormCutoff S),
    integral_congr_ae (radial_invNormCutoff_ae S),
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  simp [hS.le, Measure.real, Complex.volume_ball, mul_assoc]

private theorem integrableOn_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    IntegrableOn (fun q : ℂ ↦ (a - q)⁻¹) (Metric.ball 0 R) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  let g : ℂ → ℝ :=
    (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹)
  have hg : Integrable g := by
    have hcenter : (fun q : ℂ ↦
        (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q) =
        fun q ↦ (Metric.ball 0 (2 * R)).indicator (fun w ↦ ‖w‖⁻¹) (a - q) := by
      funext q
      have hm : q ∈ Metric.ball a (2 * R) ↔ a - q ∈ Metric.ball 0 (2 * R) := by
        simp only [Metric.mem_ball, dist_eq_norm]
        simp [sub_zero, norm_sub_rev]
      by_cases hq : q ∈ Metric.ball a (2 * R)
      · simp [hq, hm.mp hq]
      · simp [hq, mt hm.mpr hq]
    change Integrable (fun q : ℂ ↦
      (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q)
    rw [hcenter, MeasureTheory.integrable_comp_sub_left]
    exact (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_inv_norm_ball (2 * R))
  refine Integrable.mono' hg ?_ ?_
  · exact ((measurable_const.sub measurable_id).inv.indicator
      measurableSet_ball).aestronglyMeasurable
  · filter_upwards with q
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · have hqa : q ∈ Metric.ball a (2 * R) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hqR : ‖q‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hq
        calc
          ‖q - a‖ ≤ ‖q‖ + ‖a‖ := norm_sub_le q a
          _ < R + R := add_lt_add hqR ha
          _ = 2 * R := by ring
      simp only [Set.indicator_of_mem hq, norm_inv]
      simp [g, hqa]
    · simp only [Set.indicator, hq, ↓reduceIte, norm_zero]
      exact Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem circleAverage_inv_sub_eq_inv_of_radius_lt_norm
    (a : ℂ) (r : ℝ) (hr : 0 ≤ r) (hout : r < ‖a‖) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = a⁻¹ := by
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) |r|, a - w ≠ 0 := by
    intro w hw hwa
    have hwa' : w = a := (sub_eq_zero.mp hwa).symm
    subst a
    have : ‖w‖ ≤ r := by simpa [abs_of_nonneg hr, dist_eq_norm] using hw
    linarith
  have hcont : ContinuousOn (fun w : ℂ ↦ (a - w)⁻¹) (Metric.closedBall 0 |r|) :=
    ((continuous_const.sub continuous_id).continuousOn).inv₀ hne
  have hdiff : DiffContOnCl ℂ (fun w : ℂ ↦ (a - w)⁻¹) (Metric.ball 0 |r|) :=
    DiffContOnCl.mk_ball
      (fun w hw ↦ (((differentiableAt_const a).sub differentiableAt_id).inv
        (hne w (Metric.ball_subset_closedBall hw))).differentiableWithinAt) hcont
  simpa using hdiff.circleAverage

private theorem partialFraction_circleIntegral_congr (a : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : a ≠ 0) (hra : ‖a‖ ≠ r) :
    (∮ w in C(0, r), (w - 0)⁻¹ * (a - w)⁻¹) =
      ∮ w in C(0, r), a⁻¹ * ((w - 0)⁻¹ - (w - a)⁻¹) := by
  refine circleIntegral.integral_congr hr.le fun w hw ↦ ?_
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    have hz : (0 : ℝ) = r := by simpa using (Metric.mem_sphere.mp hw)
    linarith
  have hwa : w ≠ a := by
    intro h
    subst w
    exact hra (by simpa [dist_eq_norm] using (Metric.mem_sphere.mp hw))
  field_simp
  ring

private theorem circleIntegrable_sub_inv_of_norm_ne (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hra : ‖a‖ ≠ r) : CircleIntegrable (fun w : ℂ ↦ (w - a)⁻¹) 0 r :=
  circleIntegrable_sub_inv_iff.mpr (Or.inr fun h ↦
    hra (by simpa [dist_eq_norm, abs_of_pos hr] using (Metric.mem_sphere.mp h)))

private theorem circleAverage_inv_sub_eq_zero_of_norm_lt_radius
    (a : ℂ) (r : ℝ) (hr : 0 < r) (ha : a ≠ 0) (hinner : ‖a‖ < r) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = 0 := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne']
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∮ z in C(0, r), (z - 0)⁻¹ * (a - z)⁻¹) = 0
  have hmem : a ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hinner
  rw [partialFraction_circleIntegral_congr a r hr ha hinner.ne,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub
      (circleIntegrable_sub_inv_of_norm_ne 0 r hr (by simpa using hr.ne))
      (circleIntegrable_sub_inv_of_norm_ne a r hr hinner.ne),
    circleIntegral.integral_sub_center_inv 0 hr.ne',
    circleIntegral.integral_sub_inv_of_mem_ball hmem]
  simp

private theorem setIntegral_inv_sub_ball_of_ne_zero (R : ℝ) (a : ℂ) (ha0 : a ≠ 0)
    (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hf : Integrable f :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_sub_ball R a ha)
  have hpInt := integrableOn_complex_polarCoord_target f hf
  have hpolar := Complex.integral_comp_polarCoord_symm f
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • f (Complex.polarCoord.symm p)) =
        ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ)) := by
    change (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • f (Complex.polarCoord.symm p)) = _
    exact setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod ℝ ℝ]
      simpa only [Complex.polarCoord_target] using hpInt)
  rw [← integral_indicator measurableSet_ball]
  change (∫ q, f q) = _
  rw [← hpolar, hprod]
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ))) =
        if r < R then r • ((2 * Real.pi) •
          Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0 := by
    intro r hr
    have hr0 : 0 < r := hr
    have hpoint : ∀ θ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
      intro θ
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
      simp
    by_cases hrR : r < R
    · simp only [hrR, ↓reduceIte]
      have hmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) R := by
        intro θ
        rw [hpoint]
        simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hrR
      simp_rw [f, Set.indicator_of_mem (hmem _), hpoint]
      rw [integral_smul]
      rw [integral_circleMap_Ioo_eq_circleAverage (fun q ↦ (a - q)⁻¹) r]
    · simp only [hrR, ↓reduceIte]
      have hnotmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) R := by
        intro θ hθ
        rw [hpoint] at hθ
        have : r < R := by
          simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hθ
        exact hrR this
      simp_rw [f, Set.indicator, hnotmem]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have hradial :
      (fun r : ℝ ↦ if r < R then r • ((2 * Real.pi) •
        Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0)
        =ᵐ[volume.restrict (Set.Ioi 0)]
      fun r ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (Measure.ae_ne volume ‖a‖)] with r hr hra
    have hr0 : 0 < r := hr
    by_cases hra' : r < ‖a‖
    · have hrR : r < R := hra'.trans ha
      simp only [hrR, hra', ↓reduceIte]
      rw [circleAverage_inv_sub_eq_inv_of_radius_lt_norm a r hr0.le hra']
    · have har : ‖a‖ < r := lt_of_le_of_ne (le_of_not_gt hra') (Ne.symm hra)
      by_cases hrR : r < R
      · simp only [hrR, hra', ↓reduceIte]
        rw [circleAverage_inv_sub_eq_zero_of_norm_lt_radius a r hr0 ha0 har, smul_zero]
        simp
      · simp only [hrR, hra', ↓reduceIte]
  rw [integral_congr_ae hradial]
  rw [show (fun r : ℝ ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0) =
      (Set.Iio ‖a‖).indicator (fun r ↦ r • ((2 * Real.pi) • a⁻¹)) by
    funext r
    simp [Set.indicator]]
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (norm_nonneg a)]
  rw [intervalIntegral.integral_smul_const]
  rw [integral_id]
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, Complex.normSq_eq_norm_sq, Complex.real_smul]
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hnormc : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  push_cast
  field_simp [hnormc]
  ring

private theorem setIntegral_inv_sub_ball_zero (R : ℝ) :
    (∫ q in Metric.ball 0 R, ((0 : ℂ) - q)⁻¹) = 0 := by
  rw [← integral_indicator (f := fun q : ℂ ↦ ((0 : ℂ) - q)⁻¹) measurableSet_ball]
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ ((0 : ℂ) - q)⁻¹)
  have hodd : ∀ q, f (-q) = -f q := by
    intro q
    have hm : -q ∈ Metric.ball (0 : ℂ) R ↔ q ∈ Metric.ball 0 R := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · simp [f, hq, hm.mpr hq]
    · simp [f, hq, mt hm.mp hq]
  have hneg : (∫ q, f (-q)) = -(∫ q, f q) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hodd), integral_neg]
  have hself : (∫ q, f q) = -(∫ q, f q) :=
    (MeasureTheory.integral_neg_eq_self f volume).symm.trans hneg
  have ht : (2 : ℝ) • (∫ q, f q) = 0 := by
    rw [two_smul]
    calc
      (∫ q, f q) + ∫ q, f q = -(∫ q, f q) + ∫ q, f q :=
        congrArg (fun x ↦ x + ∫ q, f q) hself
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The integral of `q ↦ (a - q)⁻¹` over a disk centred at zero containing `a`. -/
theorem setIntegral_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  by_cases ha0 : a = 0
  · subst a
    simpa using setIntegral_inv_sub_ball_zero R
  · exact setIntegral_inv_sub_ball_of_ne_zero R a ha0 ha

end Complex

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Basic
-/

public section

namespace Convex

/-- Every nonnegative scalar between zero and a known scalar multiple stays in a convex set. -/
theorem smul_mem_of_nonneg_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {v : E} {x a : ℝ}
    (hzero : (0 : E) ∈ s) (ha : a • v ∈ s) (hx : 0 ≤ x) (hxa : x ≤ a) :
    x • v ∈ s := by
  by_cases ha0 : a = 0
  · have hx0 : x = 0 := by linarith
    simpa [hx0] using hzero
  · have hapos : 0 < a := lt_of_le_of_ne (hx.trans hxa) (Ne.symm ha0)
    have hratio : x / a ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx hapos.le, (div_le_one hapos).2 hxa⟩
    have hmem := hs.smul_mem_of_zero_mem hzero ha hratio
    simpa only [smul_smul, div_mul_cancel₀ x ha0] using hmem

end Convex

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Deriv
-/

public section

open Filter Set
open scoped Topology

namespace ConcaveOn

/-- A differentiable concave real function lies below its tangent line. -/
theorem le_add_deriv_mul_sub {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ g x) {y : ℝ} (hy : y ∈ s) :
    g y ≤ g x + deriv g x * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope := hg.deriv_le_slope hy hx hyx hdiff
    rw [slope] at hslope
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hs : deriv g x * (x - y) ≤ g x - g y := by
      apply (le_div_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    nlinarith
  · simp
  · have hslope := hg.slope_le_of_hasDerivAt hx hy hxy hdiff.hasDerivAt
    rw [slope] at hslope
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hs : g y - g x ≤ deriv g x * (y - x) := by
      apply (div_le_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    linarith

/-- Pointwise convergence of concave functions forces derivative convergence at a common
differentiability point in the interior of an interval. -/
theorem tendsto_deriv_of_tendsto_Ioo {ι : Type*} {F : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hf : ∀ᶠ n in F, ConcaveOn ℝ (Ioo a b) (f n))
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun n ↦ f n y) F (𝓝 (g y)))
    (hdf : ∀ᶠ n in F, DifferentiableAt ℝ (f n) x)
    (hdg : DifferentiableAt ℝ g x) :
    Tendsto (fun n ↦ deriv (f n) x) F (𝓝 (deriv g x)) := by
  have hslope (y : ℝ) (hy : y ∈ Ioo a b) :
      Tendsto (fun n ↦ slope (f n) x y) F (𝓝 (slope g x y)) := by
    simpa only [slope, smul_eq_mul, vsub_eq_sub] using
      ((hlim y hy).sub (hlim x hx)).const_mul (y - x)⁻¹
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b := isOpen_Ioo.mem_nhds hx
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hright := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo a b ∧ x < y ∧ l < slope g x y := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hright.eventually (lt_mem_nhds hl)] with y hy hxy hsy
      exact ⟨hy, hxy, hsy⟩
    obtain ⟨y, hy, hxy, hly⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (lt_mem_nhds hly)] with n hfn hdn hn
    exact hn.trans_le (hfn.slope_le_of_hasDerivAt hx hy hxy hdn.hasDerivAt)
  · intro u hu
    have hleft := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo a b ∧ y < x ∧ slope g x y < u := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hleft.eventually (gt_mem_nhds hu)] with y hy hyx hsy
      exact ⟨hy, hyx, hsy⟩
    obtain ⟨y, hy, hyx, hyu⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (gt_mem_nhds hyu)] with n hfn hdn hn
    have hle := hfn.deriv_le_slope hy hx hyx hdn
    rw [slope_comm] at hle
    exact hle.trans_lt hn

end ConcaveOn

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Gauge
-/

public section

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A direction of positive gauge has a unique positive multiple on the frontier. -/
lemma Convex.existsUnique_pos_smul_mem_frontier_of_gauge_pos {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {u : E} (hu : 0 < gauge s u) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s := by
  refine ⟨(gauge s u)⁻¹, ⟨inv_pos.mpr hu, ?_⟩, ?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hs h₀).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hu.le), smul_eq_mul, inv_mul_cancel₀ hu.ne']
  · intro r hr
    have h := (gauge_eq_one_iff_mem_frontier hs h₀).mpr hr.2
    rw [gauge_smul_of_nonneg hr.1.le, smul_eq_mul] at h
    simpa only [one_div] using (eq_div_iff hu.ne').mpr h

/-- Every nonzero direction has a unique positive multiple on the frontier of a bounded convex
neighborhood of zero. -/
lemma Convex.existsUnique_pos_smul_mem_frontier {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) {u : E} (hu : u ≠ 0) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s :=
  hs.existsUnique_pos_smul_mem_frontier_of_gauge_pos h₀
    ((gauge_pos (absorbent_nhds_zero h₀) hb).mpr hu)

/-- Reciprocation is Lipschitz on real numbers bounded below by a positive constant. -/
lemma Real.dist_inv_le_of_pos_lower_bound {a b c : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    dist a⁻¹ b⁻¹ ≤ c⁻¹ ^ 2 * dist a b := by
  have ha₀ := hc.trans_le ha
  have hb₀ := hc.trans_le hb
  rw [dist_inv_inv₀ ha₀.ne' hb₀.ne', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha₀, abs_of_pos hb₀]
  calc
    dist a b / (a * b) ≤ dist a b / (c * c) := by gcongr
    _ = c⁻¹ ^ 2 * dist a b := by ring

/-- The reciprocal of a positive uniformly bounded-below Lipschitz function is Lipschitz. -/
lemma LipschitzWith.inv_of_pos_lower_bound {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ x, c ≤ f x) :
    LipschitzWith (Real.toNNReal (c⁻¹ ^ 2) * K) (fun x ↦ (f x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x)⁻¹ (f y)⁻¹ ≤ c⁻¹ ^ 2 * dist (f x) (f y) :=
      Real.dist_inv_le_of_pos_lower_bound hc (hbound x) (hbound y)
    _ ≤ c⁻¹ ^ 2 * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (sq_nonneg _)
    _ = _ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
      ring

/-- The reciprocal gauge is Lipschitz on the unit sphere of a bounded convex neighborhood of zero.
-/
lemma Convex.exists_lipschitzWith_inv_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹) := by
  obtain ⟨K, hK⟩ := hs.lipschitz_gauge h₀
  have hf : LipschitzWith K (fun u : {u : E | ‖u‖ = 1} ↦ gauge s u.val) :=
    by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      exact hK.dist_le_mul u.val v.val
  have hlower (u : {u : E | ‖u‖ = 1}) : 1 / R ≤ gauge s u.val := by
    have hu : ‖(u : E)‖ = 1 := u.property
    calc
      1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
      _ ≤ gauge s u.val :=
        le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
  exact ⟨_, hf.inv_of_pos_lower_bound (one_div_pos.mpr hR) hlower⟩

/-- Radial gauge rescaling is Lipschitz on the unit sphere. -/
lemma Convex.exists_lipschitzWith_radial_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C
      (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹ • u.val) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_inv_gauge_sphere h₀ hR hbound
  have hr (u : {u : E | ‖u‖ = 1}) : 0 ≤ (gauge s u.val)⁻¹ ∧
      (gauge s u.val)⁻¹ ≤ R := by
    have hu : ‖u.val‖ = 1 := u.property
    have hlower : 1 / R ≤ gauge s u.val := by
      calc
        1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
        _ ≤ _ := le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
    refine ⟨inv_nonneg.mpr (gauge_nonneg _), ?_⟩
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (one_div_pos.mpr hR) hlower
  refine ⟨Real.toNNReal R + C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  have hv : ‖v.val‖ = 1 := v.property
  calc
    dist ((gauge s u.val)⁻¹ • u.val) ((gauge s v.val)⁻¹ • v.val) ≤
        dist ((gauge s u.val)⁻¹ • u.val) ((gauge s u.val)⁻¹ • v.val) +
        dist ((gauge s u.val)⁻¹ • v.val) ((gauge s v.val)⁻¹ • v.val) :=
      dist_triangle _ _ _
    _ = (gauge s u.val)⁻¹ * dist u v +
        dist (gauge s u.val)⁻¹ (gauge s v.val)⁻¹ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (hr u).1]
      congr 1
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, dist_eq_norm]
    _ ≤ R * dist u v + (C : ℝ) * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_right (hr u).2 dist_nonneg) (hC.dist_le_mul u v)
    _ = _ := by rw [NNReal.coe_add, Real.coe_toNNReal _ hR.le]; ring

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Gauge Rescale
-/

public section

open Set
open scoped Topology NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gauge rescaling identifies the unit sphere with the frontier of a bounded convex neighborhood.
-/
noncomputable def radialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s) := by
  let e := gaugeRescaleHomeomorph (Metric.ball (0 : E) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds _ (by norm_num))
    (NormedSpace.isVonNBounded_ball ℝ E 1) hs h₀ hb
  have he : e '' frontier (Metric.ball (0 : E) 1) = frontier s := by
    rw [← closure_sdiff_interior, Set.image_sdiff e.injective]
    rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    exact closure_sdiff_interior s
  have hunit : {u : E | ‖u‖ = 1} = frontier (Metric.ball (0 : E) 1) := by
    rw [frontier_ball _ one_ne_zero]
    ext u
    simp
  exact (Homeomorph.setCongr hunit).trans ((e.image _).trans (Homeomorph.setCongr he))

/-- The radial gauge homeomorphism sends a unit vector to its reciprocal-gauge multiple. -/
lemma radialGaugeHomeomorph_apply {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (u : {u : E | ‖u‖ = 1}) :
    (radialGaugeHomeomorph hs h₀ hb u : E) = (gauge s u.val)⁻¹ • u.val := by
  change (gauge (Metric.ball (0 : E) 1) u.val / gauge s u.val) • u.val = _
  rw [gauge_ball (by norm_num), div_one]
  have hu : ‖u.val‖ = 1 := u.property
  rw [hu, one_div]

open scoped Pointwise

/-- Translate the radial gauge homeomorphism by a fixed vector. -/
noncomputable def translatedRadialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier (o +ᵥ s)) := by
  let e : E ≃ₜ E := Homeomorph.addLeft o
  have he : e '' frontier s = frontier (o +ᵥ s) := by
    rw [e.image_frontier]
    rfl
  exact (radialGaugeHomeomorph hs h₀ hb).trans
    ((e.image _).trans (Homeomorph.setCongr he))

/-- The translated radial gauge homeomorphism has the expected affine formula. -/
lemma translatedRadialGaugeHomeomorph_apply {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) (u : {u : E | ‖u‖ = 1}) :
    (translatedRadialGaugeHomeomorph hs h₀ hb o u : E) =
      o + (gauge s u.val)⁻¹ • u.val := by
  change o + (radialGaugeHomeomorph hs h₀ hb u : E) = _
  rw [radialGaugeHomeomorph_apply]

/-- The translated radial gauge homeomorphism is Lipschitz on the unit sphere. -/
lemma exists_lipschitzWith_translatedRadialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u ↦ (translatedRadialGaugeHomeomorph hs h₀ hb o u : E)) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_radial_gauge_sphere h₀ hR hbound
  refine ⟨C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  rw [translatedRadialGaugeHomeomorph_apply, translatedRadialGaugeHomeomorph_apply,
    dist_add_left]
  exact hC.dist_le_mul u v

/-- A bounded convex set with an interior basepoint admits a positive Lipschitz radial
parametrization of its frontier. -/
lemma exists_radial_homeomorph {s : Set E}
    (hs : Convex ℝ s) (hb : Bornology.IsBounded s) (o : E) (ho : o ∈ interior s) :
    ∃ (ρ : E → ℝ) (e : {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s)) (C : NNReal),
      (∀ u, ‖u‖ = 1 → 0 < ρ u ∧ o + ρ u • u ∈ frontier s ∧
        ∀ r : ℝ, 0 < r → o + r • u ∈ frontier s → r = ρ u) ∧
      (∀ u, (e u : E) = o + ρ u.val • u.val) ∧
      LipschitzWith C (fun u ↦ (e u : E)) := by
  let t : Set E := -o +ᵥ s
  have htconv : Convex ℝ t := hs.vadd (-o)
  have htzero : t ∈ nhds (0 : E) := by
    simpa [t, ← mem_interior_iff_mem_nhds, interior_vadd,
      mem_vadd_set_iff_neg_vadd_mem] using ho
  have htbound : Bornology.IsBounded t := hb.vadd (-o)
  have htbounded := NormedSpace.isVonNBounded_of_isBounded ℝ htbound
  have htranslate : o +ᵥ t = s := by simp [t]
  let e := (translatedRadialGaugeHomeomorph htconv htzero htbounded o).trans
    (Homeomorph.setCongr (congrArg frontier htranslate))
  obtain ⟨R, hR, hnorm⟩ := htbound.exists_pos_norm_le
  have hball : t ⊆ Metric.closedBall 0 R := by
    intro x hx
    simpa using hnorm x hx
  obtain ⟨C, hC⟩ := exists_lipschitzWith_translatedRadialGaugeHomeomorph
    htconv htzero htbounded o hR hball
  refine ⟨fun u ↦ (gauge t u)⁻¹, e, C, ?_, ?_, ?_⟩
  · intro u hu
    have hune : u ≠ 0 := by intro h; simp [h] at hu
    have hg := (gauge_pos (absorbent_nhds_zero htzero) htbounded).mpr hune
    refine ⟨inv_pos.mpr hg, ?_, ?_⟩
    · have hm := (e ⟨u, hu⟩).property
      change (translatedRadialGaugeHomeomorph htconv htzero htbounded o ⟨u, hu⟩ : E)
        ∈ frontier s at hm
      rwa [translatedRadialGaugeHomeomorph_apply] at hm
    · intro r hr hru
      have hz : r • u ∈ frontier t := by
        change r • u ∈ frontier (-o +ᵥ s)
        rw [frontier, closure_vadd, interior_vadd]
        simpa only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
          using hru
      have hgauge := (gauge_eq_one_iff_mem_frontier htconv htzero).mpr hz
      rw [gauge_smul_of_nonneg hr.le, smul_eq_mul] at hgauge
      simpa only [one_div] using (eq_div_iff hg.ne').mpr hgauge
  · intro u
    exact translatedRadialGaugeHomeomorph_apply htconv htzero htbounded o u
  · exact hC

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Radial exit points of a convex set

From an interior base point of a compact convex set, every point of the set lies on a segment
ending at a boundary point, and that boundary point is unique. These are the facts behind a
radial decomposition of a convex body into cones over its boundary.
-/

public section

open Set
open scoped Topology Pointwise

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point lying a fixed fraction of the way, less than all of it, from an interior point of a
convex set towards a point of the set is itself an interior point. -/
theorem Convex.mem_interior_of_sub_eq_smul_sub {s : Set E} (hs : Convex ℝ s) {o w z : E}
    {γ : ℝ} (ho : o ∈ interior s) (hw : w ∈ s) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (h : z - o = γ • (w - o)) : z ∈ interior s := by
  have hz : z = (1 - γ) • o + γ • w := by
    have hzo : z = o + γ • (w - o) := by rw [← h]; abel
    rw [hzo, smul_sub, sub_smul, one_smul]
    abel
  rw [hz]
  exact hs.combo_interior_closure_mem_interior ho (subset_closure hw) (by linarith) hγ₀ (by ring)

/-- From an interior base point, every point of a compact convex set lies on a segment ending at
a boundary point: the radial exit point of its direction. -/
theorem Convex.exists_mem_frontier_mem_segment [Nontrivial E] {s : Set E} (hs : Convex ℝ s)
    (hcomp : IsCompact s) {o : E} (ho : o ∈ interior s) {x : E} (hx : x ∈ s) :
    ∃ p ∈ frontier s, x ∈ segment ℝ o p := by
  have himage : ((-o) +ᵥ s) = (fun z : E ↦ -o + z) '' s := (Set.image_vadd).symm
  have hsconv : Convex ℝ ((-o) +ᵥ s) := by
    rw [himage]; exact hs.translate (-o)
  have hscompact : IsCompact ((-o) +ᵥ s) := by
    rw [himage]; exact hcomp.image (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ interior ((-o) +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨o, ho, by simp only [vadd_eq_add]; abel⟩
  have hnhds : ((-o) +ᵥ s) ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
  have hgbound := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
  have hfrontier : ∀ {z : E}, z ∈ frontier ((-o) +ᵥ s) → o + z ∈ frontier s := by
    intro z hz
    have hzs : z ∈ ((-o) +ᵥ s) := by
      have h := frontier_subset_closure hz
      rwa [hscompact.isClosed.closure_eq] at h
    obtain ⟨k, hk, hkeq⟩ := hzs
    have hok : o + z = k := by rw [← hkeq]; simp only [vadd_eq_add]; abel
    rw [hok, mem_frontier_iff_notMem_interior hk]
    intro hkint
    exact hz.2 (by rw [interior_vadd]; exact ⟨k, hkint, hkeq⟩)
  by_cases hxo : x = o
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    obtain ⟨r, hr, -⟩ := hsconv.existsUnique_pos_smul_mem_frontier hnhds hgbound hu
    exact ⟨o + r • u, hfrontier hr.2, hxo ▸ left_mem_segment ℝ o _⟩
  have hxs : x - o ∈ ((-o) +ᵥ s) := ⟨x, hx, by simp only [vadd_eq_add]; abel⟩
  have hgpos : 0 < gauge ((-o) +ᵥ s) (x - o) :=
    (gauge_pos (absorbent_nhds_zero hnhds) hgbound).mpr (sub_ne_zero.mpr hxo)
  have hgle : gauge ((-o) +ᵥ s) (x - o) ≤ 1 := gauge_le_one_of_mem hxs
  have hfr : (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) ∈ frontier ((-o) +ᵥ s) := by
    apply (gauge_eq_one_iff_mem_frontier hsconv hnhds).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le), smul_eq_mul, inv_mul_cancel₀ hgpos.ne']
  refine ⟨o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o), hfrontier hfr, ?_⟩
  rw [segment_eq_image']
  refine ⟨gauge ((-o) +ᵥ s) (x - o), ⟨hgpos.le, hgle⟩, ?_⟩
  change o + gauge ((-o) +ᵥ s) (x - o) • (o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) - o) = x
  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  abel

/-- The radial exit point from an interior base point is unique. -/
theorem Convex.eq_of_mem_frontier_of_mem_segment {s : Set E} (hs : Convex ℝ s)
    (hclosed : IsClosed s) {o x z w : E} (ho : o ∈ interior s) (hxo : x ≠ o)
    (hz : z ∈ frontier s) (hw : w ∈ frontier s) (hxz : x ∈ segment ℝ o z)
    (hxw : x ∈ segment ℝ o w) : z = w := by
  have hzs : z ∈ s := hclosed.frontier_subset hz
  have hws : w ∈ s := hclosed.frontier_subset hw
  have hzint : z ∉ interior s := (mem_frontier_iff_notMem_interior hzs).mp hz
  have hwint : w ∉ interior s := (mem_frontier_iff_notMem_interior hws).mp hw
  rw [segment_eq_image'] at hxz hxw
  obtain ⟨α, hα, hxα⟩ := hxz
  obtain ⟨β, hβ, hxβ⟩ := hxw
  have hxα' : o + α • (z - o) = x := hxα
  have hxβ' : o + β • (w - o) = x := hxβ
  have hαpos : 0 < α := hα.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxα', ← h]; simp)
  have hβpos : 0 < β := hβ.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxβ', ← h]; simp)
  have hkey : α • (z - o) = β • (w - o) := add_left_cancel (hxα'.trans hxβ'.symm)
  have hzw : z - o = (α⁻¹ * β) • (w - o) := by
    rw [mul_smul, ← hkey, smul_smul, inv_mul_cancel₀ hαpos.ne', one_smul]
  have hwz : w - o = (α⁻¹ * β)⁻¹ • (z - o) := by
    rw [hzw, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rcases lt_trichotomy (α⁻¹ * β) 1 with hlt | heq | hgt
  · exact absurd (hs.mem_interior_of_sub_eq_smul_sub ho hws (by positivity) hlt hzw) hzint
  · have hzo : z - o = w - o := by rw [hzw, heq, one_smul]
    simpa using congrArg (fun p : E ↦ p + o) hzo
  · refine absurd (hs.mem_interior_of_sub_eq_smul_sub ho hzs (by positivity) ?_ hwz) hwint
    rw [inv_lt_one_iff₀]
    exact Or.inr hgt

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Finite Envelope
-/

public section

noncomputable section

namespace List

open Filter Topology

lemma abs_foldr_min_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ min (f x) s) r -
        l.foldr (fun f s ↦ min (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma abs_foldr_max_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ max (f x) s) r -
        l.foldr (fun f s ↦ max (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma le_foldr_min_apply_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    y ≤ l.foldr (fun f s ↦ min (f x) s) r ↔ y ≤ r ∧ ∀ f ∈ l, y ≤ f x := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

lemma foldr_max_apply_le_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    l.foldr (fun f s ↦ max (f x) s) r ≤ y ↔ r ≤ y ∧ ∀ f ∈ l, f x ≤ y := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

end List

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Inner Product Space / Box
-/

public section

namespace EuclideanSpace

/-- A rectangle with finite coordinate bounds is bounded in the Euclidean plane. -/
theorem isBounded_coordinate_rectangle (l r a b : ℝ) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | l ≤ p 0 ∧ p 0 ≤ r ∧ a ≤ p 1 ∧ p 1 ≤ b} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(|l| + |r|) + (|a| + |b|), ?_⟩
  rintro p ⟨hl, hr, ha, hb⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr
    ⟨by linarith [neg_abs_le l, abs_nonneg r],
      by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy : |p 1| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg (p 1)) (by positivity)).mpr hy
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|)
    (by positivity : 0 ≤ |a| + |b|), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg a, abs_nonneg b]

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Linearity of a real inner product in its left argument

`Mathlib.Analysis.InnerProductSpace.Basic` provides the continuous linear map
`innerSL ℝ v = fun x ↦ ⟪v, x⟫`; the bundled form of the symmetric slot is what the
half-space convexity lemmas `convex_halfSpace_le` and `convex_halfSpace_ge` consume.
-/

public section

/-- `x ↦ ⟪x, v⟫` is a linear map of a real inner product space. -/
theorem isLinearMap_inner_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : IsLinearMap ℝ fun x : E ↦ inner ℝ x v :=
  ⟨fun a b ↦ inner_add_left a b v, fun c a ↦ real_inner_smul_left a v c⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Normed / Affine / Continuous Affine Map
-/

public section

namespace ContinuousAffineMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Precomposition by a fixed continuous affine map is continuous. -/
theorem continuous_comp_right (g : E →ᴬ[ℝ] F) :
    Continuous (fun f : F →ᴬ[ℝ] G ↦ f.comp g) := by
  let C : NNReal := ⟨‖g‖ + 1, by positivity⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) fun f h ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have heq : f.comp g - h.comp g = (f - h).comp g := by
    ext x
    simp
  rw [heq]
  calc
    ‖(f - h).comp g‖ ≤ ‖f - h‖ * ‖g‖ + ‖(f - h) 0‖ :=
      ContinuousAffineMap.norm_comp_le _ _
    _ ≤ ‖f - h‖ * ‖g‖ + ‖f - h‖ := by
      gcongr
      exact ContinuousAffineMap.norm_image_zero_le _
    _ = (C : ℝ) * ‖f - h‖ := by
      change _ = (‖g‖ + 1) * ‖f - h‖
      ring

end ContinuousAffineMap

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Angle
-/

public section

namespace Real.Angle

/-- Distinct reals at distance less than a full turn have distinct angles. -/
theorem coe_ne_coe_of_abs_sub_lt {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 2 * Real.pi) :
    ((x : ℝ) : Real.Angle) ≠ ((y : ℝ) : Real.Angle) := by
  intro he
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at he
  obtain ⟨k, hk⟩ := he
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith [h.1]
  · simp only [Int.cast_zero, mul_zero] at hk
    exact hne (by linarith)
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    nlinarith [h.2]

end Real.Angle

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Angle Lift
-/

public section

namespace Real

/-- Continuous real angle lifts of the same circle-valued map differ by a constant. -/
theorem sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin {X : Type*} [TopologicalSpace X] [PreconnectedSpace
  X]
    {θ ψ : X → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ x, Real.cos (θ x) = Real.cos (ψ x))
    (hsin : ∀ x, Real.sin (θ x) = Real.sin (ψ x)) (x y : X) :
    θ x - ψ x = θ y - ψ y := by
  have hsub : Set.range (fun z ↦ θ z - ψ z) ⊆ Set.range (fun n : ℤ ↦ 2 * Real.pi * n) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (hcos z) (hsin z))
    exact ⟨n, hn.symm⟩
  have hconst := (Set.countable_range (fun n : ℤ ↦ 2 * Real.pi * n)).isTotallyDisconnected
    _ hsub (isPreconnected_range (hθ.sub hψ))
  exact hconst (Set.mem_range_self x) (Set.mem_range_self y)

end Real

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# A cubic remainder bound for the arctangent

`Real.abs_arctan_sub_self_le` complements `Real.abs_arctan_le_abs` by quantifying the
first-order approximation `arctan s ≈ s` near the origin.
-/

public section

namespace Real

/-- The arctangent differs from the identity by at most a cubic error. -/
theorem abs_arctan_sub_self_le (s : ℝ) : |arctan s - s| ≤ |s| ^ 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivWithinAt (fun u : ℝ ↦ arctan u - u) (1 / (1 + u ^ 2) - 1)
        (Set.uIcc (0 : ℝ) s) u := fun u _ ↦
    ((hasDerivAt_arctan u).sub (hasDerivAt_id u)).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.uIcc (0 : ℝ) s, ‖1 / (1 + u ^ 2) - 1‖ ≤ s ^ 2 := by
    intro u hu
    have hu' : |u| ≤ |s| := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases abs_cases u with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rcases abs_cases s with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> linarith
    have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have heq : 1 / (1 + u ^ 2) - 1 = -(u ^ 2 / (1 + u ^ 2)) := by field_simp; ring
    rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    nlinarith [sq_abs u, sq_abs s, abs_nonneg u, abs_nonneg s, sq_nonneg u]
  have hmain := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hmain' : |arctan s - s| ≤ s ^ 2 * |s| := by simpa using hmain
  calc |arctan s - s| ≤ s ^ 2 * |s| := hmain'
    _ = |s| ^ 3 := by rw [← sq_abs s]; ring

/-- First-order angle estimate. If `W = (w0, w1)` has norm `nw > 0` and the displacement
`d = (d0, d1)` has norm `nd` with `2 * nd ≤ nw`, then the principal angle between `W` and
`W + d`, in the arctangent form given by their cross and dot products, differs from its
linearization `(w0 * d1 - w1 * d0) / nw ^ 2` by at most `6 * nd ^ 2 / nw ^ 2`. -/
theorem abs_arctan_div_sub_le_of_small {w0 w1 d0 d1 nw nd : ℝ}
    (hnw : 0 < nw) (hnw2 : nw ^ 2 = w0 ^ 2 + w1 ^ 2)
    (hnd : 0 ≤ nd) (hnd2 : nd ^ 2 = d0 ^ 2 + d1 ^ 2)
    (hsmall : 2 * nd ≤ nw) :
    |arctan ((w0 * d1 - w1 * d0) / (nw ^ 2 + (w0 * d0 + w1 * d1))) -
        (w0 * d1 - w1 * d0) / nw ^ 2| ≤ 6 * nd ^ 2 / nw ^ 2 := by
  set N := w0 * d1 - w1 * d0 with hN
  set P := w0 * d0 + w1 * d1 with hP
  have hlag : N ^ 2 + P ^ 2 = nw ^ 2 * nd ^ 2 := by
    rw [hN, hP, hnw2, hnd2]; ring
  have hprod : 0 ≤ nw * nd := mul_nonneg hnw.le hnd
  have hCS : |N| ≤ nw * nd := by
    nlinarith [sq_abs N, abs_nonneg N, sq_nonneg P]
  have hCS' : |P| ≤ nw * nd := by
    nlinarith [sq_abs P, abs_nonneg P, sq_nonneg N]
  set D := nw ^ 2 + P with hD
  have hPlow : -(nw * nd) ≤ P := neg_le_of_abs_le hCS'
  have hDlow : nw ^ 2 / 2 ≤ D := by nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  set s := N / D with hs
  have hsle : |s| ≤ 2 * nd / nw := by
    rw [hs, abs_div, abs_of_pos hD0, div_le_div_iff₀ hD0 hnw]
    nlinarith [abs_nonneg N]
  have hs1 : |s| ≤ 1 := by
    refine hsle.trans ?_
    rw [div_le_one hnw]
    linarith
  have h1 : |arctan s - s| ≤ 4 * nd ^ 2 / nw ^ 2 := by
    refine (abs_arctan_sub_self_le s).trans ?_
    have hstep : |s| ^ 3 ≤ (2 * nd / nw) ^ 2 := by
      nlinarith [abs_nonneg s, hsle, hs1, sq_nonneg (|s|)]
    refine hstep.trans_eq ?_
    field_simp
    ring
  have h2 : |s - N / nw ^ 2| ≤ 2 * nd ^ 2 / nw ^ 2 := by
    have heq : s - N / nw ^ 2 = -(N * P) / (D * nw ^ 2) := by
      rw [hs, hD]
      rw [div_sub_div _ _ (ne_of_gt hD0) (by positivity : (nw : ℝ) ^ 2 ≠ 0)]
      rw [hD]
      ring_nf
    rw [heq, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D * nw ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < nw ^ 2)]
    nlinarith [mul_le_mul hCS hCS' (abs_nonneg P) hprod, abs_nonneg N, abs_nonneg P,
      mul_nonneg (abs_nonneg N) (abs_nonneg P), sq_nonneg nd, sq_nonneg nw]
  calc |arctan s - N / nw ^ 2| ≤ |arctan s - s| + |s - N / nw ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ 4 * nd ^ 2 / nw ^ 2 + 2 * nd ^ 2 / nw ^ 2 := add_le_add h1 h2
    _ = 6 * nd ^ 2 / nw ^ 2 := by ring

end Real

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Two-sided bracketing of an alternating series with an antitone tail

`alternating_series_bracket_of_antitone_shift` upgrades the one-sided Leibniz estimates
`Antitone.alternating_series_le_tendsto` and `Antitone.tendsto_le_alternating_series` to a
two-sided bracket for an alternating series whose term magnitudes are antitone only from an
even index `2 * N` onwards: the sum then lies between the partial sums of `2 * N` and of
`2 * N + 1` terms.  `antitone_pow_div_factorial_two_mul_add` is the antitonicity criterion
for the stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` that the Taylor
series of the trigonometric functions produce.
-/

public section

/-- The stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` are antitone as soon
as `x ^ 2 ≤ (a + 1) * (a + 2)`, i.e. as soon as the first term ratio is at most one. -/
theorem antitone_pow_div_factorial_two_mul_add {x : ℝ} (hx0 : 0 ≤ x) {a : ℕ}
    (hx : x ^ 2 ≤ ((a + 1) * (a + 2) : ℕ)) :
    Antitone fun n : ℕ ↦ x ^ (2 * n + a) / (Nat.factorial (2 * n + a) : ℝ) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  set m := 2 * n + a with hm
  have ham : a ≤ m := by omega
  have hstep : 2 * (n + 1) + a = m + 1 + 1 := by omega
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hle : x ^ 2 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    refine hx.trans ?_
    have hcast : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    push_cast
    nlinarith
  have hpow : x ^ (m + 1 + 1) = x ^ m * x * x := by ring
  rw [hstep, Nat.factorial_succ, Nat.factorial_succ, hpow,
    div_le_div_iff₀ (by positivity) hfac]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hx0 m) hfac.le) (sub_nonneg.2 hle)]

/-- Leibniz bracketing for an alternating series whose term magnitudes are antitone only
from index `2 * N` onwards: the limit lies between the partial sums of `2 * N` and of
`2 * N + 1` terms. -/
theorem alternating_series_bracket_of_antitone_shift {f : ℕ → ℝ} {l : ℝ} (N : ℕ)
    (hfl : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l))
    (hfa : Antitone fun n ↦ f (2 * N + n)) :
    (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i) ≤ l ∧
      l ≤ ∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i := by
  set S := ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i with hS
  have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      = (∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i) - S := by
    intro n
    rw [hS, Finset.sum_range_add]
    simp [pow_add, pow_mul]
  have hshift : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l) := by
    have h := hfl.comp (Filter.tendsto_add_atTop_nat (2 * N))
    simpa [Function.comp_def, Nat.add_comm] using h
  have htend : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      Filter.atTop (nhds (l - S)) := by
    simp only [key]
    exact hshift.sub_const S
  have hlow := Antitone.alternating_series_le_tendsto htend hfa 0
  have hhigh := Antitone.tendsto_le_alternating_series htend hfa 0
  simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, Nat.zero_add,
    Finset.sum_range_one, pow_zero, one_mul, Nat.add_zero] at hlow hhigh
  refine ⟨by linarith, ?_⟩
  rw [Finset.sum_range_succ, ← hS, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Trigonometric
-/

public section

/-- The tangent of half a complementary angle is secant minus tangent on the first quadrant. -/
theorem Real.tan_pi_div_two_sub_div_two (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  let u := (Real.pi / 2 - ω) / 2
  have hu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2], by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2]⟩
  have hw : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1, hω.2], hω.2⟩
  have h2 : 2 * u = Real.pi / 2 - ω := by
    dsimp [u]
    ring
  have hs : 2 * Real.sin u * Real.cos u = Real.cos ω := by
    rw [← Real.sin_two_mul, h2, Real.sin_pi_div_two_sub]
  have hc : 2 * Real.cos u ^ 2 - 1 = Real.sin ω := by
    rw [← Real.cos_two_mul, h2, Real.cos_pi_div_two_sub]
  change Real.tan u = _
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hu.ne', hw.ne']
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- Cotangent is antitone between its consecutive poles at negative pi and zero. -/
theorem Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero :
    AntitoneOn (fun x : ℝ ↦ Real.cos x / Real.sin x) (Set.Ioo (-Real.pi) 0) := by
  intro x hx y hy hxy
  have hxsin := Real.sin_neg_of_neg_of_neg_pi_lt hx.2 hx.1
  have hysin := Real.sin_neg_of_neg_of_neg_pi_lt hy.2 hy.1
  change Real.cos y / Real.sin y ≤ Real.cos x / Real.sin x
  rw [← neg_div_neg_eq (Real.cos y) (Real.sin y),
    ← neg_div_neg_eq (Real.cos x) (Real.sin x)]
  apply (div_le_div_iff₀ (neg_pos.mpr hysin) (neg_pos.mpr hxsin)).mpr
  have hsin : 0 ≤ Real.sin (y - x) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hsin
  nlinarith

/-- A cubic upper bound for the tangent on `[0, 1]`, companion to `Real.sin_gt_sub_cube`. -/
theorem Real.tan_le_self_add_cube {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.tan x ≤ x + 4 / 3 * x ^ 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcl : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hs : Real.sin x ≤ x := Real.sin_le hx
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos]
  have h1 : (0 : ℝ) ≤ x + 4 / 3 * x ^ 3 := by positivity
  have h2 : (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) ≤ (x + 4 / 3 * x ^ 3) * Real.cos x :=
    mul_le_mul_of_nonneg_left hcl h1
  have h3 : x ≤ (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) := by
    nlinarith [mul_nonneg (pow_nonneg hx 3) (show (0 : ℝ) ≤ 5 / 6 - 2 / 3 * x ^ 2 by nlinarith)]
  linarith

/-- Leibniz bracketing of the sine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 2) * (4 * N + 3)` the value `Real.sin x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.sin_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 2) * (4 * N + 3) : ℕ)) :
    Real.sin x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      Filter.atTop (nhds (Real.sin x)) := by
    have h := (Real.hasSum_sin x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n) + 1) / (Nat.factorial (2 * (2 * N + n) + 1) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) + 1 = 2 * n + (4 * N + 1) := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N + 1) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Leibniz bracketing of the cosine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 1) * (4 * N + 2)` the value `Real.cos x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.cos_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 1) * (4 * N + 2) : ℕ)) :
    Real.cos x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      Filter.atTop (nhds (Real.cos x)) := by
    have h := (Real.hasSum_cos x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n)) / (Nat.factorial (2 * (2 * N + n)) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) = 2 * n + 4 * N := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.BoundedVariation`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Bounded Variation
-/

public section

/-- The variation of a sum is at most the sum of the variations. -/
theorem eVariationOn.add_le {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- A sum of two functions of bounded variation has bounded variation. -/
theorem BoundedVariationOn.add {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  exact eVariationOn.add_le f g s

/-- Variation bounds the increments along a finite monotone partition. -/
theorem eVariationOn.sum_edist_fin_le {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f : α → E} {s : Set α} {n : ℕ} (u : Fin (n + 1) → α)
    (hu : Monotone u) (hus : ∀ i, u i ∈ s) :
    ∑ i : Fin n, edist (f (u i.succ)) (f (u i.castSucc)) ≤ eVariationOn f s := by
  let v : ℕ → α := fun k ↦ u ⟨min k n, by omega⟩
  have hv : Monotone v := fun i j hij ↦ hu (min_le_min_right n hij)
  have h := eVariationOn.sum_le (f := f) (n := n) hv
    (fun k ↦ hus ⟨min k n, by omega⟩)
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [v]
  have h₁ : min (i.val + 1) n = i.val + 1 := Nat.min_eq_left (by omega)
  have h₀ : min i.val n = i.val := Nat.min_eq_left (by omega)
  congr 2 <;> apply congrArg u <;> apply Fin.ext
  · exact h₁.symm
  · exact h₀.symm

/-- Total variation bounds the sum of norms of increments on a finite partition. -/
theorem BoundedVariationOn.sum_norm_sub_fin_le {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s) :
    ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ (eVariationOn f s).toReal := by
  have h := ENNReal.toReal_mono hf (eVariationOn.sum_edist_fin_le u hu hus)
  rw [ENNReal.toReal_sum (fun i _ ↦ edist_ne_top _ _)] at h
  simpa only [edist_dist, dist_eq_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using h

/-- Squared increments are bounded by the largest increment times the total variation. -/
theorem BoundedVariationOn.sum_norm_sub_sq_fin_le {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ δ) :
    ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 ≤ δ * (eVariationOn f s).toReal := by
  calc
    _ ≤ ∑ i : Fin n, δ * ‖f (u i.succ) - f (u i.castSucc)‖ := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hbound i, norm_nonneg (f (u i.succ) - f (u i.castSucc))]
    _ = δ * ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf.sum_norm_sub_fin_le u hu hus) hδ

/-- A telescoping sum of increments with quadratic remainders is controlled by the
largest increment times the total variation. -/
theorem BoundedVariationOn.abs_sub_sum_le_of_param_quadratic_remainder
    {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    {n : ℕ} (u : Fin (n + 1) → α) (hu : Monotone u) (hus : ∀ i, u i ∈ s)
    (A : α → ℝ) (L : Fin n → ℝ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hbound : ∀ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ≤ δ)
    (herror : ∀ i : Fin n,
      |A (u i.succ) - A (u i.castSucc) - L i| ≤
        C * ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2) :
    |A (u (Fin.last n)) - A (u 0) - ∑ i, L i| ≤ C * δ * (eVariationOn f s).toReal := by
  have htel : ∑ i : Fin n, (A (u i.succ) - A (u i.castSucc)) =
      A (u (Fin.last n)) - A (u 0) := by
    have hfirst := Fin.sum_univ_succ (fun i ↦ A (u i))
    have hlast := Fin.sum_univ_castSucc (fun i ↦ A (u i))
    rw [Finset.sum_sub_distrib]
    linarith
  rw [← htel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, |A (u i.succ) - A (u i.castSucc) - L i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, C * ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ herror i)
    _ = C * ∑ i : Fin n, ‖f (u i.succ) - f (u i.castSucc)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ C * (δ * (eVariationOn f s).toReal) :=
      mul_le_mul_of_nonneg_left (hf.sum_norm_sub_sq_fin_le u hu hus hδ hbound) hC
    _ = _ := by ring

/-- If the increments of a real function `A` agree with a linear functional of the
increments of a bounded variation path up to a quadratic remainder on all parameter
pairs closer than a fixed positive threshold, then the linear sums along any family of
partitions whose mesh tends to zero converge to the endpoint increment of `A`. -/
theorem BoundedVariationOn.tendsto_sum_of_local_quadratic_remainder
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    {f : Set.Icc a b → E} (hf : BoundedVariationOn f Set.univ) (hfc : Continuous f)
    (A : Set.Icc a b → ℝ) (L : Set.Icc a b → E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (herror : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
      |A u - A t - L t (f u - f t)| ≤ C * ‖f u - f t‖ ^ 2)
    (N : ℕ → ℕ) (cuts : ∀ k, Fin (N k + 1) → Set.Icc a b)
    (hcuts : ∀ k, Monotone (cuts k))
    (hzero : ∀ k, (cuts k 0 : ℝ) = a)
    (hlast : ∀ k, (cuts k (Fin.last (N k)) : ℝ) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (N k),
      (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ) :
    Filter.Tendsto (fun k ↦ ∑ i : Fin (N k),
      L (cuts k i.castSucc) (f (cuts k i.succ) - f (cuts k i.castSucc)))
      Filter.atTop (nhds (A ⟨b, hab, le_rfl⟩ - A ⟨a, le_rfl, hab⟩)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (eVariationOn f Set.univ).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set η := ε / (C * V + 1) with hηdef
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hfc) η hη
  filter_upwards [hmesh (min δ δ₀) (lt_min hδ hδ₀)] with k hk
  have hinc (i : Fin (N k)) :
      ‖f (cuts k i.succ) - f (cuts k i.castSucc)‖ ≤ η := by
    have hle : (cuts k i.castSucc : ℝ) ≤ (cuts k i.succ : ℝ) :=
      hcuts k (Fin.castSucc_le_succ i)
    have hd : dist (cuts k i.succ) (cuts k i.castSucc) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
      exact lt_of_lt_of_le (hk i) (min_le_left _ _)
    simpa only [dist_eq_norm] using (hmod hd).le
  have hbound := hf.abs_sub_sum_le_of_param_quadratic_remainder (cuts k) (hcuts k)
    (fun _ ↦ Set.mem_univ _) A
    (fun i ↦ L (cuts k i.castSucc) (f (cuts k i.succ) - f (cuts k i.castSucc)))
    hC hη.le hinc
    (fun i ↦ herror (cuts k i.castSucc) (cuts k i.succ) (hcuts k (Fin.castSucc_le_succ i))
      (lt_of_lt_of_le (hk i) (min_le_right _ _)))
  have hleft : cuts k 0 = ⟨a, le_rfl, hab⟩ := Subtype.ext (hzero k)
  have hright : cuts k (Fin.last (N k)) = ⟨b, hab, le_rfl⟩ := Subtype.ext (hlast k)
  rw [hleft, hright] at hbound
  rw [Real.dist_eq, abs_sub_comm]
  apply hbound.trans_lt
  have hcancel : η * (C * V + 1) = ε := div_mul_cancel₀ ε (by positivity)
  change C * η * V < ε
  nlinarith

/-- Bounded variation on two adjacent closed intervals gives bounded variation on their
union. -/
theorem BoundedVariationOn.Icc_union_Icc {α E : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] {f : α → E} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : BoundedVariationOn f (Set.Icc a b)) (h₂ : BoundedVariationOn f (Set.Icc b c)) :
    BoundedVariationOn f (Set.Icc a c) := by
  have h := eVariationOn.Icc_add_Icc f hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at h
  change eVariationOn f (Set.Icc a c) ≠ ⊤
  rw [← h]
  exact ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩

/-- A function on the order subtype `Set.Icc a b` has bounded variation everywhere as soon as
it has bounded variation on the closed interval between the two endpoints of that subtype. -/
theorem BoundedVariationOn.univ_of_Icc_endpoints {α E : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] {a b : α} (hab : a ≤ b) {g : Set.Icc a b → E}
    (h : BoundedVariationOn g (Set.Icc ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩)) :
    BoundedVariationOn g Set.univ := by
  have huniv : Set.Icc (⟨a, le_rfl, hab⟩ : Set.Icc a b) ⟨b, hab, le_rfl⟩ = Set.univ := by
    ext x
    simp only [Set.mem_Icc, Set.mem_univ, iff_true]
    exact ⟨x.2.1, x.2.2⟩
  rwa [huniv] at h

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Convex.Body.BoundaryMeasure`.
* `ForMathlib.Convex.Body.Hausdorff`.
* `ForMathlib.Convex.Collinear`.
* `ForMathlib.Convex.Body.Segment`.
* `ForMathlib.Convex.Function`.
* `ForMathlib.Convex.Hausdorff`.
* `ForMathlib.Convex.Support`.
* `ForMathlib.Convex.Translation`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Body / Boundary Measure
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Topology

namespace ConvexBody

private abbrev Plane_m58ecd66 := EuclideanSpace ℝ (Fin 2)

private def unitCircleParam (t : ℝ) : Plane_m58ecd66 :=
  WithLp.toLp 2 (![Real.cos t, Real.sin t] : Fin 2 → ℝ)

private theorem lipschitzWith_unitCircleParam :
    LipschitzWith 2 unitCircleParam := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_eq_norm]
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [unitCircleParam, PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : |Real.cos x - Real.cos y| ≤ |x - y| := by
    exact Real.abs_cos_sub_cos_le x y
  have hs : |Real.sin x - Real.sin y| ≤ |x - y| := by
    exact Real.abs_sin_sub_sin_le x y
  have hxy : 0 ≤ |x - y| := abs_nonneg _
  have hc_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hc
  have hs_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hs
  norm_num
  nlinarith [sq_abs (Real.cos x - Real.cos y), sq_abs (Real.sin x - Real.sin y)]

private theorem hausdorffMeasure_one_sphere_lt_top :
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane_m58ecd66) 1) < ⊤ := by
  have hsphere : Metric.sphere (0 : Plane_m58ecd66) 1 ⊆
      unitCircleParam '' Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    have hnorm : ‖p‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp
    let z : ℂ := ⟨p 0, p 1⟩
    have hzNorm : ‖z‖ = 1 := by
      rw [Complex.norm_def, show Complex.normSq z = ‖p‖ ^ 2 by
        rw [EuclideanSpace.norm_sq_eq]
        simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
      simp [hnorm]
    have hz : z ≠ 0 := by
      intro hz
      simp [hz] at hzNorm
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    ext i
    fin_cases i
    · simpa [unitCircleParam, z, hzNorm] using Complex.cos_arg hz
    · simpa [unitCircleParam, z, hzNorm] using Complex.sin_arg z
  calc
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane_m58ecd66) 1) ≤
        Measure.hausdorffMeasure 1 (unitCircleParam '' Set.Icc (-Real.pi) Real.pi) :=
      measure_mono hsphere
    _ ≤ ((2 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (Set.Icc (-Real.pi) Real.pi) :=
      lipschitzWith_unitCircleParam.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      finiteness

private theorem image_gaugeRescale_unitSphere_eq_frontier {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hbounded : Bornology.IsBounded s)
    (hclosed : IsClosed s) :
    gaugeRescale (Metric.ball 0 1) s '' Metric.sphere 0 1 = frontier s := by
  have hvnb : Bornology.IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hbounded
  let h := gaugeRescaleHomeomorph (Metric.ball (0 : Plane_m58ecd66) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (NormedSpace.isVonNBounded_ball ℝ Plane_m58ecd66 1) hconv h₀ hvnb
  change h '' Metric.sphere 0 1 = frontier s
  rw [← frontier_ball, ← closure_sdiff_interior, Set.image_sdiff h.injective]
  · rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    rw [hclosed.closure_eq]
    simpa [hclosed.closure_eq] using closure_sdiff_interior s
  · norm_num

private theorem exists_lipschitzOnWith_gaugeRescale_unitSphere {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hbounded : Bornology.IsBounded s) :
    ∃ C, LipschitzOnWith C (gaugeRescale (Metric.ball 0 1) s) (Metric.sphere 0 1) := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp h₀
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  let R : ℝ := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsR : s ⊆ Metric.closedBall (0 : Plane_m58ecd66) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hB x hx).trans (by dsimp [R]; linarith [le_abs_self B])
  have habs : Absorbent ℝ s := absorbent_nhds_zero h₀
  let rn : NNReal := ⟨r, hr.le⟩
  have hg : LipschitzWith rn⁻¹ (gauge s) := hconv.lipschitzWith_gauge hr hrs
  let C : NNReal := ⟨R + (rn⁻¹ : ℝ) * R ^ 2, by positivity⟩
  refine ⟨C, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hnx : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hny : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  have hgx : 1 / R ≤ gauge s x := by
    simpa [hnx] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖x‖ / R ≤ gauge s x)
  have hgy : 1 / R ≤ gauge s y := by
    simpa [hny] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖y‖ / R ≤ gauge s y)
  have hgxpos : 0 < gauge s x := (div_pos one_pos hR).trans_le hgx
  have hgypos : 0 < gauge s y := (div_pos one_pos hR).trans_le hgy
  have hinvx : (gauge s x)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgxpos hR]
    simpa [div_eq_inv_mul] using hgx
  have hinvy : (gauge s y)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgypos hR]
    simpa [div_eq_inv_mul] using hgy
  have hginv : dist (gauge s x)⁻¹ (gauge s y)⁻¹ ≤
      (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by
    rw [dist_inv_inv₀ hgxpos.ne' hgypos.ne']
    have hdist := hg.dist_le_mul x y
    have hprod : 1 / R ^ 2 ≤ ‖gauge s x‖ * ‖gauge s y‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgxpos, abs_of_pos hgypos]
      calc
        1 / R ^ 2 = (1 / R) * (1 / R) := by ring_nf
        _ ≤ gauge s x * gauge s y :=
          mul_le_mul hgx hgy (div_nonneg one_pos.le hR.le) hgxpos.le
    calc
      dist (gauge s x) (gauge s y) / (‖gauge s x‖ * ‖gauge s y‖) ≤
          dist (gauge s x) (gauge s y) / (1 / R ^ 2) := by
        exact div_le_div_of_nonneg_left (dist_nonneg) (by positivity) hprod
      _ ≤ ((rn⁻¹ : ℝ) * dist x y) / (1 / R ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa [NNReal.coe_inv] using hdist
      _ = (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by field_simp
  change dist ((gauge (Metric.ball 0 1) x / gauge s x) • x)
      ((gauge (Metric.ball 0 1) y / gauge s y) • y) ≤ (C : ℝ) * dist x y
  simp_rw [gauge_ball (by positivity : (0 : ℝ) ≤ 1)]
  rw [hnx, hny]
  simp only [inv_one, one_div]
  rw [dist_eq_norm]
  calc
    ‖(gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y‖ ≤
        ‖(gauge s x)⁻¹ • (x - y)‖ +
          ‖((gauge s x)⁻¹ - (gauge s y)⁻¹) • y‖ := by
      have heq : (gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y =
          (gauge s x)⁻¹ • (x - y) +
            ((gauge s x)⁻¹ - (gauge s y)⁻¹) • y := by module
      rw [heq]
      exact norm_add_le _ _
    _ ≤ R * dist x y + ((rn⁻¹ : ℝ) * R ^ 2 * dist x y) := by
      simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
      have hix : |(gauge s x)⁻¹| ≤ R := by rw [abs_of_pos (inv_pos.mpr hgxpos)]; exact hinvx
      have hid : |(gauge s x)⁻¹ - (gauge s y)⁻¹| ≤
          (rn⁻¹ : ℝ) * R ^ 2 * ‖x - y‖ := by simpa [dist_eq_norm] using hginv
      rw [hny, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hix (norm_nonneg _)) hid
    _ = (C : ℝ) * dist x y := by
      change _ = (R + (rn⁻¹ : ℝ) * R ^ 2) * dist x y
      ring

private theorem hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero {s : Set Plane_m58ecd66}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane_m58ecd66)) (hcompact : IsCompact s) :
    Measure.hausdorffMeasure 1 (frontier s) < ⊤ := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzOnWith_gaugeRescale_unitSphere hconv h₀ hcompact.isBounded
  rw [← image_gaugeRescale_unitSphere_eq_frontier hconv h₀ hcompact.isBounded hcompact.isClosed]
  refine (hC.hausdorffMeasure_image_le (by positivity)).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hausdorffMeasure_one_sphere_lt_top

/-- The frontier of a planar convex body with nonempty interior has finite
one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_frontier_lt_top
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hint : (interior (K : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set (EuclideanSpace ℝ (Fin 2)))) < ⊤ := by
  obtain ⟨c, hc⟩ := hint
  let s : Set Plane_m58ecd66 := -c +ᵥ (K : Set Plane_m58ecd66)
  have hsconv : Convex ℝ s := K.convex.vadd (-c)
  have hscompact : IsCompact s := by
    change IsCompact ((fun x : Plane_m58ecd66 ↦ -c + x) '' (K : Set Plane_m58ecd66))
    exact K.isCompact.image (continuous_const.add continuous_id)
  have hs₀ : s ∈ nhds (0 : Plane_m58ecd66) := by
    rw [← mem_interior_iff_mem_nhds]
    change (0 : Plane_m58ecd66) ∈ interior (-c +ᵥ (K : Set Plane_m58ecd66))
    rw [interior_vadd]
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hc
  have hsfinite := hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero hsconv hs₀ hscompact
  have himage : (fun z : Plane_m58ecd66 ↦ c + z) '' frontier s = frontier (K : Set Plane_m58ecd66)
    := by
    calc
      (fun z : Plane_m58ecd66 ↦ c + z) '' frontier s =
          frontier ((fun z : Plane_m58ecd66 ↦ c + z) '' s) :=
        (Homeomorph.addLeft c).image_frontier s
      _ = frontier (K : Set Plane_m58ecd66) := by
        congr 1
        ext x
        simp [s, Set.mem_vadd_set_iff_neg_vadd_mem]
  have hisom : Isometry (fun z : Plane_m58ecd66 ↦ c + z) := by
    intro x y
    simp
  rw [← himage, hisom.hausdorffMeasure_image (Or.inl zero_le_one)]
  exact hsfinite

end ConvexBody

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Body / Hausdorff
-/

public section

open Filter
open scoped Topology

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eventual membership persists in a Hausdorff limit of convex bodies. -/
theorem mem_of_tendsto_hausdorffDist (q : E) (K : ℕ → ConvexBody E) (L : ConvexBody E)
    (hev : ∀ᶠ n in atTop, q ∈ (K n : Set E))
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E))
      atTop (𝓝 0)) : q ∈ (L : Set E) := by
  have hle : (fun _ : ℕ ↦ Metric.infDist q (L : Set E)) ≤ᶠ[atTop]
      (fun n ↦ Metric.hausdorffDist (K n : Set E) (L : Set E)) := by
    filter_upwards [hev] with n hn
    exact Metric.infDist_le_hausdorffDist_of_mem hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
  have hz : Metric.infDist q (L : Set E) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  exact (IsClosed.mem_iff_infDist_zero L.isClosed L.nonempty).mpr
    (le_antisymm hz Metric.infDist_nonneg)

end ConvexBody

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Collinear
-/

public section

open Module

/-- A convex set with empty interior in dimension at most two is collinear. -/
theorem Convex.collinear_of_interior_eq_empty {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hdim : finrank ℝ E ≤ 2)
    (hint : interior s = ∅) : Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact collinear_empty ℝ E
  have hspan : vectorSpan ℝ s ≠ ⊤ := by
    intro h
    have ha : affineSpan ℝ s = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty
        (hne.mono (subset_affineSpan ℝ s))).mp (by simpa only [direction_affineSpan] using h)
    have hi := hs.interior_nonempty_iff_affineSpan_eq_top.mpr ha
    simp [hint] at hi
  apply collinear_iff_finrank_le_one.mpr
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hspan)
  simp only [finrank_top] at hlt
  omega

/-- A separating linear functional orders points on a line into a segment. -/
theorem Collinear.mem_segment_of_apply_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Collinear ℝ s) {a p x : E}
    (ha : a ∈ s) (hp : p ∈ s) (hx : x ∈ s) (f : E →ₗ[ℝ] ℝ)
    (hpos : 0 < f (p - a)) (hle : f p ≤ f x) : p ∈ segment ℝ a x := by
  have hne : a ≠ p := by
    intro h
    simp [h] at hpos
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hs.mem_affineSpan_of_mem_of_ne ha hp hx hne)
  have hrle : 1 ≤ r := by
    rw [← hr, AffineMap.lineMap_apply_module', map_add, map_smul] at hle
    have hsub := f.map_sub p a
    change f p ≤ r * f (p - a) + f a at hle
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrle
  have hinv : r⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hrpos.le, inv_le_one_of_one_le₀ hrle⟩
  have hmem := lineMap_mem_segment ℝ a x hinv
  rw [← hr, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hrpos.ne',
    AffineMap.lineMap_apply_one] at hmem
  simpa only [hr] using hmem

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Body / Segment
-/

public section

noncomputable section

open scoped Pointwise

namespace ConvexBody

private abbrev Plane_mea511e5 := EuclideanSpace ℝ (Fin 2)

/-- A nonsingleton planar convex body with empty interior is a nontrivial segment. -/
theorem exists_eq_segment_of_interior_empty
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hsub : ¬(K : Set (EuclideanSpace ℝ (Fin 2))).Subsingleton)
    (hint : interior (K : Set (EuclideanSpace ℝ (Fin 2))) = ∅) :
    ∃ a b, a ≠ b ∧
      (K : Set (EuclideanSpace ℝ (Fin 2))) = segment ℝ a b := by
  have hcol : Collinear ℝ (K : Set Plane_mea511e5) :=
    K.convex.collinear_of_interior_eq_empty
      (by simp) hint
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd
    (k := ℝ) (K : Set Plane_mea511e5)).mp hcol
  have hv₀ : v ≠ 0 := by
    intro hz
    apply hsub
    intro p hp q hq
    obtain ⟨r, hr⟩ := hv p hp
    obtain ⟨s, hs⟩ := hv q hq
    simpa [hz] using hr.trans (by simpa [hz] using hs.symm)
  let f : Plane_mea511e5 → ℝ := fun p ↦ inner ℝ v (p - p₀) / inner ℝ v v
  have hvv : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hv₀
  have hrepr : ∀ p ∈ (K : Set Plane_mea511e5), p = f p • v + p₀ := by
    intro p hp
    obtain ⟨r, rfl⟩ := hv p hp
    have hf : f (r • v + p₀) = r := by
      dsimp [f]
      rw [add_sub_cancel_right, inner_smul_right]
      field_simp [hvv]
    change r • v + p₀ = f (r • v + p₀) • v + p₀
    rw [hf]
  have hfcont : Continuous f := by fun_prop
  obtain ⟨a, ha, hamin⟩ := K.isCompact.exists_isMinOn K.nonempty hfcont.continuousOn
  obtain ⟨b, hb, hbmax⟩ := K.isCompact.exists_isMaxOn K.nonempty hfcont.continuousOn
  have habf : f a < f b := by
    apply lt_of_le_of_ne (hamin hb)
    intro heq
    apply hsub
    intro p hp q hq
    rw [hrepr p hp, hrepr q hq]
    have hpfa : f p = f a :=
      le_antisymm ((hbmax hp).trans_eq heq.symm) (hamin hp)
    have hqfa : f q = f a :=
      le_antisymm ((hbmax hq).trans_eq heq.symm) (hamin hq)
    rw [hpfa, hqfa]
  refine ⟨a, b, ?_, Set.Subset.antisymm ?_ ?_⟩
  · intro hab
    rw [hab] at habf
    exact habf.false
  · intro p hp
    rw [segment_eq_image']
    let t := (f p - f a) / (f b - f a)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨
      div_nonneg (sub_nonneg.mpr (hamin hp)) (sub_nonneg.mpr habf.le),
      (div_le_one (sub_pos.mpr habf)).mpr (sub_le_sub_right (hbmax hp) _)⟩
    refine ⟨t, ht, ?_⟩
    rw [hrepr p hp, hrepr a ha, hrepr b hb]
    have hden : f b - f a ≠ 0 := sub_ne_zero.mpr habf.ne'
    have htalg : f a + t * (f b - f a) = f p := by
      dsimp [t]
      field_simp [hden]
      ring
    rw [← htalg]
    module
  · exact K.convex.segment_subset ha hb

end ConvexBody

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Function
-/

public section

/-- A convex function stays below a bound before the right endpoint if the left
endpoint is strictly below the bound and the right endpoint is at most the bound. -/
theorem ConvexOn.lt_on_Ico_of_lt_of_le {f : ℝ → ℝ} {a b t c : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (ha : f a < c) (hb : f b ≤ c)
    (hat : a ≤ t) (htb : t < b) : f t < c := by
  have hab : a < b := lt_of_le_of_lt hat htb
  let u := (b - t) / (b - a)
  let v := (t - a) / (b - a)
  have hu : 0 < u := div_pos (sub_pos.mpr htb) (sub_pos.mpr hab)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hab.le)
  have huv : u + v = 1 := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have ht : u * a + v * b = t := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have h := hf.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hu.le hv huv
  simp only [smul_eq_mul, ht] at h
  have hleft : u * f a < u * c := mul_lt_mul_of_pos_left ha hu
  have hright : v * f b ≤ v * c := mul_le_mul_of_nonneg_left hb hv
  calc
    f t ≤ u * f a + v * f b := h
    _ < u * c + v * c := add_lt_add_of_lt_of_le hleft hright
    _ = c := by rw [← add_mul, huv, one_mul]

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Hausdorff
-/

public section

open Filter TopologicalSpace
open scoped Topology

/-- Hausdorff limits of nonempty compact convex sets are convex. -/
theorem TopologicalSpace.NonemptyCompacts.convex_of_tendsto {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} [l.NeBot] {K : ι → NonemptyCompacts E} {L : NonemptyCompacts E}
    (hK : ∀ n, Convex ℝ (K n : Set E)) (hlim : Tendsto K l (𝓝 L)) :
    Convex ℝ (L : Set E) := by
  have happrox : ∀ x ∈ (L : Set E), ∃ p : ι → E,
      (∀ n, p n ∈ (K n : Set E)) ∧ Tendsto p l (𝓝 x) := by
    intro x hx
    choose p hp hd using fun n ↦ (K n).isCompact.exists_infDist_eq_dist (K n).nonempty x
    refine ⟨p, hp, ?_⟩
    have hinf := (NonemptyCompacts.lipschitz_infDist_const x).continuous.tendsto L |>.comp hlim
    have hz : Metric.infDist x (L : Set E) = 0 := Metric.infDist_zero_of_mem hx
    rw [hz] at hinf
    change Tendsto (fun n ↦ Metric.infDist x (K n : Set E)) l (𝓝 0) at hinf
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Function.comp_apply, hd, dist_comm] using hinf
  intro x hx y hy a b ha hb hab
  obtain ⟨p, hp, hpx⟩ := happrox x hx
  obtain ⟨q, hq, hqy⟩ := happrox y hy
  have hz := (hpx.const_smul a).add (hqy.const_smul b)
  have hi := NonemptyCompacts.uniformContinuous_infDist.continuous.tendsto
    (a • x + b • y, L) |>.comp (hz.prodMk_nhds hlim)
  have hzero : (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E)) = fun _ ↦ 0 := by
    funext n
    exact Metric.infDist_zero_of_mem (hK n (hp n) (hq n) ha hb hab)
  change Tendsto (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E))
    l (𝓝 (Metric.infDist (a • x + b • y) (L : Set E))) at hi
  rw [hzero] at hi
  exact (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    (tendsto_nhds_unique hi tendsto_const_nhds)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Support
-/

public section

open scoped ENNReal

/-- Support values of compact sets differ by at most their Hausdorff distance times the norm of
the direction. -/
theorem IsCompact.abs_csSup_inner_sub_le_hausdorffDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S T : Set E} (hS : IsCompact S) (hneS : S.Nonempty)
    (hT : IsCompact T) (hneT : T.Nonempty) (u : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x u) '' T)| ≤
      Metric.hausdorffDist S T * ‖u‖ := by
  obtain ⟨x, hxS, hx, hxmax⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyT, hy⟩ := hT.exists_infDist_eq_dist hneT x
  obtain ⟨z, hzT, hz, hzmax⟩ := hT.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneT
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hfin : Metric.hausdorffEDist S T ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneS hneT
      hS.isBounded hT.isBounded
  have hdist : ‖x - y‖ ≤ Metric.hausdorffDist S T := by
    calc
      ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
      _ = Metric.infDist x T := hy.symm
      _ ≤ Metric.hausdorffDist S T := Metric.infDist_le_hausdorffDist_of_mem hxS hfin
  have hupper : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' T) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    rw [hx, hz]
    calc
      inner ℝ x u - inner ℝ z u ≤ inner ℝ x u - inner ℝ y u :=
        sub_le_sub_left (hzmax y hyT) _
      _ = inner ℝ (x - y) u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (x - y) u| := le_abs_self _
      _ ≤ ‖x - y‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (x - y) u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  have hreverse : sSup ((fun x ↦ inner ℝ x u) '' T) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    have hfin' : Metric.hausdorffEDist T S ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneT hneS
        hT.isBounded hS.isBounded
    obtain ⟨x', hx'S, hx'⟩ := hS.exists_infDist_eq_dist hneS z
    have hdist' : ‖z - x'‖ ≤ Metric.hausdorffDist S T := by
      calc
        ‖z - x'‖ = dist z x' := (dist_eq_norm z x').symm
        _ = Metric.infDist z S := hx'.symm
        _ ≤ Metric.hausdorffDist T S :=
          Metric.infDist_le_hausdorffDist_of_mem hzT hfin'
        _ = Metric.hausdorffDist S T := Metric.hausdorffDist_comm
    rw [hz, hx]
    calc
      inner ℝ z u - inner ℝ x u ≤ inner ℝ z u - inner ℝ x' u :=
        sub_le_sub_left (hxmax x' hx'S) _
      _ = inner ℝ (z - x') u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (z - x') u| := le_abs_self _
      _ ≤ ‖z - x'‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (z - x') u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- The support values of a compact set are Lipschitz in the direction, with constant equal to the
maximum norm of a point in the set. -/
theorem IsCompact.abs_csSup_inner_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} (hS : IsCompact S) (hneS : S.Nonempty) (u v : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x v) '' S)| ≤
      sSup (norm '' S) * ‖u - v‖ := by
  obtain ⟨x, hxS, hxu, hxu'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyS, hyv, hyv'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x v) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hbound (z : E) (hz : z ∈ S) (w : E) :
      |inner ℝ z w| ≤ sSup (norm '' S) * ‖w‖ := by
    calc
      |inner ℝ z w| ≤ ‖z‖ * ‖w‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) z w
      _ ≤ sSup (norm '' S) * ‖w‖ := by
        gcongr
        exact le_csSup (hS.bddAbove_image continuous_norm.continuousOn) ⟨z, hz, rfl⟩
  have huv : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x v) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hxu, hyv]
    calc
      inner ℝ x u - inner ℝ y v ≤ inner ℝ x u - inner ℝ x v :=
        sub_le_sub_left (hyv' x hxS) _
      _ = inner ℝ x (u - v) := by rw [inner_sub_right]
      _ ≤ |inner ℝ x (u - v)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖u - v‖ := hbound x hxS (u - v)
  have hvu : sSup ((fun x ↦ inner ℝ x v) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hyv, hxu]
    calc
      inner ℝ y v - inner ℝ x u ≤ inner ℝ y v - inner ℝ y u :=
        sub_le_sub_left (hxu' y hyS) _
      _ = inner ℝ y (v - u) := by rw [inner_sub_right]
      _ ≤ |inner ℝ y (v - u)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖v - u‖ := hbound y hyS (v - u)
      _ = sSup (norm '' S) * ‖u - v‖ := by rw [norm_sub_rev]
  rw [abs_le]
  constructor <;> linarith

/-- A convex body in a real inner product space is the intersection of its supporting
half-spaces. -/
theorem ConvexBody.eq_iInter_halfSpaces
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : ConvexBody E) :
    (K : Set E) = ⋂ u ∈ {u : E | ‖u‖ = 1},
      {p : E | inner ℝ p u ≤ sSup ((fun x ↦ inner ℝ x u) '' (K : Set E))} := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro u _
    obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : E ↦ inner ℝ x u) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    rw [hxmax]
    exact hmax p hp
  · intro p hp
    by_contra hpK
    obtain ⟨q, hq, hqmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex p
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ hpK (h ▸ hq))
    let u : E := ‖p - q‖⁻¹ • (p - q)
    have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hpq
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm.ne']
    have hproj : ∀ y ∈ (K : Set E), inner ℝ (p - q) (y - q) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero K.convex hq).mp hqmin
    have hqmax : sSup ((fun x ↦ inner ℝ x u) '' (K : Set E)) = inner ℝ q u := by
      obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
        (f := fun x : E ↦ inner ℝ x u) K.nonempty
        (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
      rw [hxmax]
      apply le_antisymm
      · dsimp [u]
        rw [inner_smul_right, inner_smul_right]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnorm.le)
        have h := hproj x hx
        have h' : inner ℝ (x - q) (p - q) ≤ 0 := by rwa [real_inner_comm]
        rw [inner_sub_left] at h'
        linarith
      · exact hmax q hq
    have hpu := Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    rw [hqmax] at hpu
    have hstrict : inner ℝ q u < inner ℝ p u := by
      dsimp [u]
      rw [inner_smul_right, inner_smul_right]
      have hself : 0 < inner ℝ (p - q) (p - q) := by
        rw [real_inner_self_eq_norm_sq]
        positivity
      rw [← sub_pos, ← mul_sub, ← inner_sub_left]
      exact mul_pos (inv_pos.mpr hnorm) hself
    exact (not_lt_of_ge hpu) hstrict

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Convex / Translation
-/

public section

/-- Translation of a convex body by a vector. -/
@[expose]
def ConvexBody.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun p ↦ p + v) '' (K : Set E)
  convex' := by simpa only [add_comm] using K.convex.translate v
  isCompact' := K.isCompact.image (continuous_id.add continuous_const)
  nonempty' := K.nonempty.image _

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Geometry.Euclidean.Segment`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Geometry / Euclidean / Segment
-/

public section

open MeasureTheory

namespace EuclideanGeometry

/-- Two unit vectors perpendicular to the same nonzero planar vector agree up to sign. -/
theorem eq_or_eq_neg_of_unit_orthogonal
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
    {v n m : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hvn : inner ℝ v n = 0) (hvm : inner ℝ v m = 0) : n = m ∨ n = -m := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
    ⟨by simp [finrank_euclideanSpace]⟩
  obtain ⟨r, hr⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp hvn).resolve_left hv
  obtain ⟨s, hs⟩ :=
    ((o.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two).mp hvm).resolve_left hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrabs : |r| * ‖v‖ = 1 := by
    calc
      |r| * ‖v‖ = ‖r • o.rotation (Real.pi / 2 : ℝ) v‖ := by simp [norm_smul]
      _ = ‖n‖ := congrArg norm hr
      _ = 1 := hn
  have hsabs : |s| * ‖v‖ = 1 := by
    calc
      |s| * ‖v‖ = ‖s • o.rotation (Real.pi / 2 : ℝ) v‖ := by simp [norm_smul]
      _ = ‖m‖ := congrArg norm hs
      _ = 1 := hm
  have habs : |r| = |s| := mul_right_cancel₀ (ne_of_gt hvnorm) (hrabs.trans hsabs.symm)
  rcases (abs_eq_abs.mp habs) with hrs | hrs
  · left
    rw [← hr, ← hs, hrs]
  · right
    rw [← hr, ← hs, hrs, neg_smul]

/-- Equal segments have the same orthogonal directions. -/
theorem inner_direction_eq_zero_of_segment_eq
    {a b c d n : (EuclideanSpace ℝ (Fin 2))} (hseg : segment ℝ a b = segment ℝ c d)
    (hcdn : inner ℝ (d - c) n = 0) : inner ℝ (b - a) n = 0 := by
  have ha : a ∈ segment ℝ c d := hseg ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := hseg ▸ right_mem_segment ℝ a b
  rw [segment_eq_image'] at ha hb
  obtain ⟨r, _, hr⟩ := ha
  obtain ⟨s, _, hs⟩ := hb
  rw [← hr, ← hs]
  have heq : c + s • (d - c) - (c + r • (d - c)) = (s - r) • (d - c) := by
    module
  rw [heq]
  rw [inner_smul_left, hcdn, mul_zero]

/-- Equal segments have equal endpoint distances. -/
theorem dist_eq_of_segment_eq {a b c d : (EuclideanSpace ℝ (Fin 2))}
    (hseg : segment ℝ a b = segment ℝ c d) : dist a b = dist c d := by
  have h := congrArg (Measure.hausdorffMeasure 1) hseg
  simpa only [MeasureTheory.hausdorffMeasure_segment, edist_dist,
    ENNReal.ofReal_eq_ofReal_iff, dist_nonneg] using h

/-- A segment transverse to a hyperplane meets it in at most one point. -/
lemma segment_inter_hyperplane_subsingleton {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (h : inner ℝ (b - a) n ≠ 0) :
    (segment ℝ a b ∩ {q | inner ℝ q n = c}).Subsingleton := by
  rintro x ⟨hx, hxc⟩ y ⟨hy, hyc⟩
  rw [segment_eq_image'] at hx hy
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨s, hs, rfl⟩ := hy
  have heq : r * inner ℝ (b - a) n = s * inner ℝ (b - a) n := by
    have hx : inner ℝ a n + r * inner ℝ (b - a) n = c := by
      simpa only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] using hxc
    have hy : inner ℝ a n + s * inner ℝ (b - a) n = c := by
      simpa only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] using hyc
    linarith
  rw [mul_right_cancel₀ h heq]

/-- A transverse segment has zero length on a hyperplane. -/
lemma hausdorffMeasure_segment_inter_hyperplane_eq_zero {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (h : inner ℝ (b - a) n ≠ 0) :
    Measure.hausdorffMeasure 1 (segment ℝ a b ∩ {q | inner ℝ q n = c}) = 0 := by
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num : (0 : ℝ) <
    1)
  exact (segment_inter_hyperplane_subsingleton h).countable.measure_zero _

/-- A segment not contained in a hyperplane meets it in at most one point. -/
lemma segment_inter_hyperplane_subsingleton_of_not_subset {a b n : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hnot : ¬ segment ℝ a b ⊆ {q | inner ℝ q n = c}) :
    (segment ℝ a b ∩ {q | inner ℝ q n = c}).Subsingleton := by
  by_cases hdir : inner ℝ (b - a) n = 0
  · intro x hx y hy
    exfalso
    apply hnot
    have hconstant {q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ segment ℝ a b) :
        inner ℝ q n = inner ℝ a n := by
      rw [segment_eq_image'] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      simp only [inner_add_left, real_inner_smul_left, hdir, mul_zero, add_zero]
    intro q hq
    exact (hconstant hq).trans ((hconstant hx.1).symm.trans hx.2)
  · exact segment_inter_hyperplane_subsingleton hdir

/-- A nondegenerate segment covered by finitely many hyperplanes lies in one of them. -/
lemma exists_segment_subset_hyperplane_of_finite_cover {ι : Type*}
    (I : Finset ι) (n : ι → EuclideanSpace ℝ (Fin 2)) (c : ι → ℝ) {a b : EuclideanSpace ℝ (Fin 2)}
      (hab : a ≠ b)
    (hcover : segment ℝ a b ⊆ ⋃ i ∈ I, {q | inner ℝ q (n i) = c i}) :
    ∃ i ∈ I, segment ℝ a b ⊆ {q | inner ℝ q (n i) = c i} := by
  classical
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num : (0 : ℝ) <
    1)
  by_contra hnot
  push Not at hnot
  have hnull (i : ι) (hi : i ∈ I) :
      Measure.hausdorffMeasure 1 (segment ℝ a b ∩ {q | inner ℝ q (n i) = c i}) = 0 :=
    (segment_inter_hyperplane_subsingleton_of_not_subset (hnot i hi)).countable.measure_zero _
  have hsub : segment ℝ a b ⊆
      ⋃ i ∈ I, segment ℝ a b ∩ {q | inner ℝ q (n i) = c i} := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp (hcover hq)
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hq, hqi⟩
  have hm := measure_mono_null hsub
    ((measure_biUnion_null_iff I.finite_toSet.countable).mpr hnull)
  rw [hausdorffMeasure_segment] at hm
  exact hab (edist_eq_zero.mp hm)

end EuclideanGeometry

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.MeasureTheory.EuclideanSpace`.
* `ForMathlib.MeasureTheory.FiniteMeasure.Portmanteau`.
* `ForMathlib.MeasureTheory.FiniteMeasure.Restriction`.
* `ForMathlib.MeasureTheory.Angle`.
* `ForMathlib.MeasureTheory.Hausdorff.Arclength`.
* `ForMathlib.MeasureTheory.Hausdorff.Graph`.
* `ForMathlib.MeasureTheory.Hausdorff.PlanarGraph`.
* `ForMathlib.MeasureTheory.Integral.AtomicBounds`.
* `ForMathlib.MeasureTheory.Integral.IntervalExhaustion`.
* `ForMathlib.MeasureTheory.Integral.MovingIntervals`.
* `ForMathlib.MeasureTheory.Integral.Translation`.
* `ForMathlib.MeasureTheory.Measure.Atoms`.
* `ForMathlib.MeasureTheory.Measure.HaarNullSets`.
* `ForMathlib.MeasureTheory.Measure.Map`.
* `ForMathlib.MeasureTheory.Measure.WithDensity`.
* `ForMathlib.MeasureTheory.RegionBetween`.
* `ForMathlib.MeasureTheory.Measure.PlanarTrapezoid`.
* `ForMathlib.MeasureTheory.Measure.PlanarTriangle`.
* `ForMathlib.MeasureTheory.StieltjesDensity`.
* `ForMathlib.MeasureTheory.VectorMeasure.Interval`.
* `ForMathlib.MeasureTheory.VectorMeasure.WithDensity`.
* `ForMathlib.MeasureTheory.Volume`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Euclidean Space
-/

public section

open MeasureTheory

namespace EuclideanSpace

theorem volume_preserving_finTwoCoordinates :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

/-- The volume of a closed coordinate box of the Euclidean plane. -/
theorem volume_setOf_apply_mem_Icc (l r b t : ℝ) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet :
      NullMeasurableSet (Set.Icc l r ×ˢ Set.Icc b t) (volume : Measure (ℝ × ℝ)))
  calc
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
        volume (Set.Icc l r ×ˢ Set.Icc b t) := by
      convert h using 1
      congr 1
    _ = _ := by rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- The coordinates of a point of the Euclidean plane, listed second coordinate first. -/
def finTwoCoordinatesSwap (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (p 1, p 0)

/-- Reading the plane coordinates in the reversed order is measure preserving. -/
theorem volume_preserving_finTwoCoordinatesSwap :
    MeasurePreserving finTwoCoordinatesSwap volume
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  convert hswap.comp volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Portmanteau for finite measures: the open-set inequality

Mathlib proves the open-set portmanteau inequality
`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto` for probability measures and
only the closed-set inequality `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`
for finite measures. This file supplies the missing open-set inequality for finite measures, by
combining the closed-set inequality on the complement with the convergence of the total masses.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory.FiniteMeasure

/-- Portmanteau for finite measures: weak convergence bounds the mass of an open set by the
lower limit of the approximating masses. -/
theorem le_liminf_measure_open_of_tendsto
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω} {μs : ι → FiniteMeasure Ω}
    (hlim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (hG : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf (fun i ↦ (μs i : Measure Ω) G) := by
  have hclosed := MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim
    hG.isClosed_compl
  rw [le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
  intro y hy
  have hμGtop : (μ : Measure Ω) G ≠ ⊤ := measure_ne_top _ _
  have hyTop : y ≠ ⊤ := ne_top_of_lt (hy.trans_le (le_top))
  have hyR : y.toReal < ((μ : Measure Ω) G).toReal :=
    (ENNReal.toReal_lt_toReal hyTop hμGtop).mpr hy
  let d : ℝ := (((μ : Measure Ω) G).toReal - y.toReal) / 3
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hmass : Tendsto (fun i ↦ ((μs i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto μ.mass).comp
      (MeasureTheory.FiniteMeasure.continuous_mass.tendsto μ |>.comp hlim)
  have hevmass : ∀ᶠ i in L, (μ.mass : ℝ) - d < ((μs i).mass : ℝ) :=
    hmass.eventually_const_lt (sub_lt_self _ hd)
  let q : ENNReal := ENNReal.ofReal (((μ : Measure Ω) Gᶜ).toReal + d)
  have hqd : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal + d := by
    have hcR : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal := ENNReal.toReal_nonneg
    linarith
  have hcompq : (μ : Measure Ω) Gᶜ < q := by
    rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hqd]
    linarith
  have hlsq : L.limsup (fun i ↦ (μs i : Measure Ω) Gᶜ) < q :=
    hclosed.trans_lt hcompq
  have hevcomp : ∀ᶠ i in L, (μs i : Measure Ω) Gᶜ < q :=
    eventually_lt_of_limsup_lt hlsq
  filter_upwards [hevmass, hevcomp] with i him hic
  have hmassEq : ((μs i : Measure Ω) univ).toReal = ((μs i).mass : ℝ) := by
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  have hcompR : ((μs i : Measure Ω) Gᶜ).toReal <
      ((μ : Measure Ω) Gᶜ).toReal + d := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr hic
    simpa [q, ENNReal.toReal_ofReal hqd] using h
  have hsplit : ((μs i : Measure Ω) G).toReal =
      ((μs i).mass : ℝ) - ((μs i : Measure Ω) Gᶜ).toReal := by
    rw [show (μs i : Measure Ω) G = (μs i : Measure Ω) univ -
      (μs i : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _), hmassEq]
  have hμsplit : ((μ : Measure Ω) G).toReal =
      (μ.mass : ℝ) - ((μ : Measure Ω) Gᶜ).toReal := by
    rw [show (μ : Measure Ω) G = (μ : Measure Ω) univ -
      (μ : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _)]
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  apply (ENNReal.toReal_lt_toReal hyTop (measure_ne_top _ _)).mp
  rw [hsplit]
  dsimp [d] at him hcompR hd
  linarith [hyR, hμsplit]

end MeasureTheory.FiniteMeasure

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Finite Measure / Restriction
-/

public section

noncomputable section

open Filter Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace MeasureTheory.FiniteMeasure

/-- Weak convergence of finite measures and their restrictions implies weak
convergence of the complementary restrictions. -/
theorem tendsto_restrict_compl_of_tendsto_restrict
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hsμ : Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s))) :
    Tendsto (fun n ↦ (μs n).restrict sᶜ) F (𝓝 (μ.restrict sᶜ)) := by
  apply tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi (ν : FiniteMeasure X) :
      (∫ x, f x ∂(ν.restrict sᶜ : Measure X)) =
        (∫ x, f x ∂(ν : Measure X)) - (∫ x, f x ∂(ν.restrict s : Measure X)) := by
    have h := integral_add_compl hs (f.integrable (μ := (ν : Measure X)))
    change (∫ x in sᶜ, f x ∂(ν : Measure X)) =
      (∫ x, f x ∂(ν : Measure X)) - (∫ x in s, f x ∂(ν : Measure X))
    linarith
  simpa only [hi] using
    ((tendsto_iff_forall_integral_tendsto.mp hμ) f).sub
      ((tendsto_iff_forall_integral_tendsto.mp hsμ) f)

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.FiniteMeasure

/-- A continuity set has convergent masses under weak convergence of finite measures. -/
theorem tendsto_apply_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hμ : Tendsto μs F (𝓝 μ)) (hs : μ (frontier s) = 0) :
    Tendsto (fun n ↦ μs n s) F (𝓝 (μ s)) := by
  by_cases hzero : μ = 0
  · subst μ
    have hm := hμ.mass
    simp only [zero_mass] at hm
    have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) F (𝓝 0)) hm
      (fun _ ↦ zero_le) (fun n ↦ (μs n).apply_le_mass s)
    simpa using hlim
  · have hn := μ.tendsto_normalize_of_tendsto hμ hzero
    have hs' : μ.normalize (frontier s) = 0 := by
      rw [μ.normalize_eq_of_nonzero hzero, hs, mul_zero]
    have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hs'
    simpa only [← self_eq_mass_mul_normalize] using hμ.mass.mul hset

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.Measure

/-- Equal atoms on a finite set give equal restrictions to that set. -/
theorem restrict_finset_eq_of_singleton_eq
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ ν : Measure X} (s : Finset X) (h : ∀ x ∈ s, μ {x} = ν {x}) :
    μ.restrict (s : Set X) = ν.restrict (s : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hd : Disjoint ({a} : Set X) (s : Set X) := by simpa using ha
    have heq := ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
    rw [Finset.coe_insert, ← Set.singleton_union]
    rw [restrict_union hd s.measurableSet, restrict_union hd s.measurableSet]
    rw [restrict_singleton, restrict_singleton, h a (Finset.mem_insert_self _ _), heq]

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

/-- Removing finitely many fixed atoms preserves weak convergence. -/
theorem tendsto_restrict_compl_finset_of_singleton_eq
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSingletonClass X] {F : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} (s : Finset X)
    (hμ : Tendsto μs F (𝓝 μ))
    (h : ∀ n x, x ∈ s → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict (s : Set X)ᶜ) F
      (𝓝 (μ.restrict (s : Set X)ᶜ)) := by
  apply tendsto_restrict_compl_of_tendsto_restrict s.measurableSet hμ
  have heq (n : ι) : (μs n).restrict (s : Set X) = μ.restrict (s : Set X) :=
    Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq s (h n))
  simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ι ↦ μ.restrict (s : Set X)) F
      (𝓝 (μ.restrict (s : Set X))))

/-- A finite measure weighted by a bounded continuous nonnegative function. -/
private def withDensityNN {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : FiniteMeasure X) (g : X →ᵇ ℝ≥0) : FiniteMeasure X :=
  ⟨(μ : Measure X).withDensity (fun x ↦ g x),
    isFiniteMeasure_withDensity (g.lintegral_lt_top_of_nnreal μ).ne⟩

/-- Weighting by a fixed bounded continuous nonnegative function preserves weak convergence. -/
private theorem tendsto_withDensityNN
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs F (𝓝 μ)) (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n ↦ withDensityNN (μs n) g) F (𝓝 (withDensityNN μ g)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  have hprod := (tendsto_iff_forall_lintegral_tendsto.mp hμ) (g * f)
  have h_lintegral (ν : FiniteMeasure X) :
      (∫⁻ x, (f x : ℝ≥0∞) ∂(withDensityNN ν g : Measure X)) =
        ∫⁻ x, ((g * f) x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [withDensityNN, toMeasure_mk, lintegral_withDensity_eq_lintegral_mul]
    · simp
    · exact (ENNReal.continuous_coe.comp g.continuous).measurable
    · exact (ENNReal.continuous_coe.comp f.continuous).measurable
  simpa only [h_lintegral] using hprod

/-- Weak convergence is preserved by restriction to a measurable continuity set. -/
theorem tendsto_restrict_of_null_frontier
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (hμ : Tendsto μs F (𝓝 μ))
    (hfrontier : μ (frontier s) = 0) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  apply tendsto_iff_forall_lintegral_tendsto.mpr
  intro g
  have hweighted := tendsto_withDensityNN hμ g
  have hfrontier' : (withDensityNN μ g) (frontier s) = 0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [ennreal_coeFn_eq_coeFn_toMeasure]
    apply withDensity_absolutelyContinuous (μ : Measure X) (fun x ↦ g x)
    simpa only [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_zero] using
      congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hfrontier
  have hmass := tendsto_apply_of_null_frontier hweighted hfrontier'
  have hmass_ennreal := (ENNReal.continuous_coe.tendsto _).comp hmass
  change Tendsto (fun n ↦ (withDensityNN (μs n) g s : ℝ≥0∞)) F
    (𝓝 (withDensityNN μ g s : ℝ≥0∞)) at hmass_ennreal
  have h_lintegral (ν : FiniteMeasure X) :
      (withDensityNN ν g s : ℝ≥0∞) =
        ∫⁻ x in s, (g x : ℝ≥0∞) ∂(ν : Measure X) := by
    rw [ennreal_coeFn_eq_coeFn_toMeasure, withDensityNN, toMeasure_mk, withDensity_apply _ hs]
  simpa only [h_lintegral, restrict_measure_eq] using hmass_ennreal

/-- Fixed atoms on a finite set containing the frontier allow weak restriction convergence. -/
theorem tendsto_restrict_of_frontier_subset_finset
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Nonempty X] [MeasurableSingletonClass X]
    {F : Filter ι} {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X} {s : Set X}
    (hs : MeasurableSet s) (t : Finset X) (hfrontier : frontier s ⊆ (t : Set X))
    (hμ : Tendsto μs F (𝓝 μ))
    (hatoms : ∀ n x, x ∈ t → (μs n : Measure X) {x} = (μ : Measure X) {x}) :
    Tendsto (fun n ↦ (μs n).restrict s) F (𝓝 (μ.restrict s)) := by
  have hremoved := tendsto_restrict_compl_finset_of_singleton_eq t hμ hatoms
  have hzero : (μ.restrict (t : Set X)ᶜ) (frontier s) = 0 := by
    apply (null_iff_toMeasure_null _ _).mpr
    rw [restrict_measure_eq, Measure.restrict_apply measurableSet_frontier]
    have he : frontier s ∩ (t : Set X)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2 (hfrontier hx.1)
    rw [he, measure_empty]
  have hrestricted := tendsto_restrict_of_null_frontier hs hremoved hzero
  have hfixed (n : ι) : ((μs n).restrict (t : Set X)).restrict s =
      (μ.restrict (t : Set X)).restrict s := by
    congr 1
    exact Subtype.ext (Measure.restrict_finset_eq_of_singleton_eq t (hatoms n))
  have hsplit (ν : FiniteMeasure X) : ν.restrict s =
      (ν.restrict (t : Set X)ᶜ).restrict s + (ν.restrict (t : Set X)).restrict s := by
    apply Subtype.ext
    change (ν : Measure X).restrict s =
      ((ν : Measure X).restrict (t : Set X)ᶜ).restrict s +
        ((ν : Measure X).restrict (t : Set X)).restrict s
    rw [← Measure.restrict_add]
    congr 1
    rw [add_comm, Measure.restrict_add_restrict_compl t.measurableSet]
  have hconst : Tendsto (fun n ↦ ((μs n).restrict (t : Set X)).restrict s) F
      (𝓝 ((μ.restrict (t : Set X)).restrict s)) := by
    simpa only [hfixed] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (μ.restrict (t : Set X)).restrict s) F _)
  simpa only [← hsplit] using hrestricted.add hconst

end MeasureTheory.FiniteMeasure

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Angle
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace Real.Angle

/-- A half-open interval of at most one turn has distinct angular representatives. -/
theorem injOn_coe_Ioc {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Set.InjOn (fun t : ℝ ↦ (t : Angle)) (Ioc a b) := by
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    ⟨hx.1, hx.2.trans h⟩ ⟨hy.1, hy.2.trans h⟩).mp hxy

/-- Every fibre of the angular projection is countable, being a full residue class. -/
theorem countable_preimage_coe_singleton (x : Angle) :
    ((fun s : ℝ ↦ (s : Angle)) ⁻¹' {x}).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_range fun k : ℤ ↦ x.toReal + 2 * Real.pi * (k : ℝ))
  intro y hy
  have hy' : ((y : ℝ) : Angle) = ((x.toReal : ℝ) : Angle) := by
    rw [mem_preimage, mem_singleton_iff] at hy
    rw [hy, coe_toReal]
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp hy'
  exact ⟨k, by linarith [hk]⟩

/-- The quotient map sends an open real interval to an open angular arc. -/
theorem isOpen_image_Ioo (a b : ℝ) :
    IsOpen ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) := by
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The frontier of an angular arc is contained in its two endpoint angles. -/
theorem frontier_image_Ioo_subset (a b : ℝ) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) ⊆
      {(a : Angle), (b : Angle)} := by
  intro x hx
  have hc : IsClosed ((fun t : ℝ ↦ (t : Angle)) '' Icc a b) :=
    (isCompact_Icc.image continuous_coe).isClosed
  have hx' : x ∈ (fun t : ℝ ↦ (t : Angle)) '' Icc a b :=
    closure_minimal (image_mono Ioo_subset_Icc_self) hc hx.1
  obtain ⟨t, ht, rfl⟩ := hx'
  have hout : (t : Angle) ∉ (fun t : ℝ ↦ (t : Angle)) '' Ioo a b := by
    simpa only [(isOpen_image_Ioo a b).interior_eq] using hx.2
  have hends : t = a ∨ t = b := by
    by_contra h
    push Not at h
    exact hout ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1),
      lt_of_le_of_ne ht.2 h.2⟩, rfl⟩
  rcases hends with rfl | rfl <;> simp

/-- A nonempty half-open arc consists of its open arc and its terminal angle. -/
theorem image_Ioc_eq_image_Ioo_union {a b : ℝ} (hab : a < b) :
    (fun t : ℝ ↦ (t : Angle)) '' Ioc a b =
      (fun t : ℝ ↦ (t : Angle)) '' Ioo a b ∪ {(b : Angle)} := by
  rw [← Ioo_union_right hab, image_union, image_singleton]

/-- The frontier of a nonempty half-open angular arc lies in its two endpoint angles. -/
theorem frontier_image_Ioc_subset {a b : ℝ} (hab : a < b) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) ⊆
      {(a : Angle), (b : Angle)} := by
  rw [image_Ioc_eq_image_Ioo_union hab]
  refine (frontier_union_subset _ _).trans ?_
  refine union_subset ?_ ?_
  · exact inter_subset_left.trans (frontier_image_Ioo_subset a b)
  · refine inter_subset_right.trans (frontier_subset_closure.trans ?_)
    simp

/-- Half-open real intervals have measurable angular images. -/
theorem measurableSet_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle] (a b : ℝ) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) := by
  by_cases hab : a < b
  · rw [image_Ioc_eq_image_Ioo_union hab]
    exact (isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton _)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab)]

/-- A Borel subset of a real interval of at most one turn has a Borel angular image. -/
theorem measurableSet_image_of_subset_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    {a b : ℝ} (hab : b ≤ a + 2 * Real.pi) {E : Set ℝ} (hE : MeasurableSet E)
    (hEab : E ⊆ Ioc a b) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' E) :=
  hE.image_of_continuousOn_injOn continuous_coe.continuousOn ((injOn_coe_Ioc hab).mono hEab)

/-- The preimage of an open angular arc under the half-turn shift is the shifted arc. -/
theorem preimage_sub_pi_image_Ioo (a b : ℝ) :
    (fun t : Angle ↦ t - ((Real.pi : ℝ) : Angle)) ⁻¹'
        ((fun s : ℝ ↦ (s : Angle)) '' Ioo a b) =
      (fun s : ℝ ↦ (s : Angle)) '' Ioo (a + Real.pi) (b + Real.pi) := by
  ext x
  simp only [mem_preimage, mem_image, mem_Ioo]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s + Real.pi, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [coe_add, hsx]
    abel
  · rintro ⟨r, hr, hrx⟩
    refine ⟨r - Real.pi, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [coe_sub, hrx]

/-- The terminal atom is disjoint from the open arc, even for a full turn. -/
theorem disjoint_image_Ioo_singleton {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Disjoint ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) {(b : Angle)} := by
  rw [Set.disjoint_singleton_right]
  rintro ⟨t, ht, heq⟩
  have htb := injOn_coe_Ioc h ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans ht.2, le_rfl⟩ heq
  exact ht.2.ne htb

/-- Passing from an open arc to a half-open arc restores exactly its terminal atom. -/
theorem integral_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    (μ : MeasureTheory.FiniteMeasure Angle) (f : Angle →ᵇ ℝ)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : MeasureTheory.Measure Angle)) =
      (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioo a b, f x ∂(μ : MeasureTheory.Measure Angle)) +
        (μ : MeasureTheory.Measure Angle).real {(b : Angle)} * f (b : Angle) := by
  rw [image_Ioc_eq_image_Ioo_union hab, MeasureTheory.setIntegral_union
    (disjoint_image_Ioo_singleton hturn) (measurableSet_singleton _)
    (f.integrable (μ := (μ : Measure Angle))).integrableOn
    (f.integrable (μ := (μ : Measure Angle))).integrableOn]
  rw [MeasureTheory.integral_singleton]
  rfl

/-- Weak convergence with fixed endpoint atoms preserves integrals on half-open angular arcs. -/
theorem tendsto_integral_image_Ioc_of_fixed_endpoint_atoms
    [MeasurableSpace Angle] [BorelSpace Angle]
    {ι : Type*} {F : Filter ι} {μs : ι → FiniteMeasure Angle} {μ : FiniteMeasure Angle}
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hμ : Tendsto μs F (𝓝 μ))
    (ha : ∀ n, (μs n : Measure Angle) {(a : Angle)} = (μ : Measure Angle) {(a : Angle)})
    (hb : ∀ n, (μs n : Measure Angle) {(b : Angle)} = (μ : Measure Angle) {(b : Angle)})
    (f : Angle →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b,
      f x ∂(μs n : Measure Angle)) F
      (𝓝 (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : Measure Angle))) := by
  classical
  have hatoms : ∀ n x, x ∈ ({(a : Angle), (b : Angle)} : Finset Angle) →
      (μs n : Measure Angle) {x} = (μ : Measure Angle) {x} := by
    intro n x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha n
    · exact hb n
  have hres := FiniteMeasure.tendsto_restrict_of_frontier_subset_finset
    (isOpen_image_Ioo a b).measurableSet ({(a : Angle), (b : Angle)} : Finset Angle)
    (by simpa using frontier_image_Ioo_subset a b) hμ hatoms
  have hint := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hres f
  have hatom (n : ι) : (μs n : Measure Angle).real {(b : Angle)} =
      (μ : Measure Angle).real {(b : Angle)} := by
    exact congrArg ENNReal.toReal (hb n)
  simpa only [integral_image_Ioc _ _ hab hturn, hatom,
    FiniteMeasure.restrict_measure_eq] using
      hint.add (tendsto_const_nhds (x := (μ : Measure Angle).real {(b : Angle)} * f (b : Angle)))

/-! ### Integration over the circle of directions -/

/-- A continuous function of a direction is integrable for every finite angular measure, the
circle of directions being compact. -/
theorem integrable_of_continuous [MeasurableSpace Angle] [BorelSpace Angle] {E : Type*}
    [NormedAddCommGroup E] {μ : Measure Angle} [IsFiniteMeasure μ] {f : Angle → E}
    (hf : Continuous f) : Integrable f μ := by
  have : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  have : CompactSpace Angle := inferInstanceAs (CompactSpace (AddCircle (2 * Real.pi)))
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ### Angular measures reading a real density -/

/-- On a real window of at most one turn, the pushforward of a weighted measure along the
angular projection gives the angular image of a measurable subset the integral of the weight
over that subset. -/
theorem map_coe_withDensity_image_eq_setLIntegral [MeasurableSpace Angle] [BorelSpace Angle]
    {ν : Measure ℝ} {w : ℝ → ENNReal} {S T : Set ℝ} {a b : ℝ}
    (hturn : b ≤ a + 2 * Real.pi) (hS : S ⊆ Ioc a b) (hT : MeasurableSet T) (hTS : T ⊆ S) :
    Measure.map (fun t : ℝ ↦ (t : Angle)) ((ν.restrict S).withDensity w)
        ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ν := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  have himage : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' T) :=
    measurableSet_image_of_subset_Ioc hturn hT (hTS.trans hS)
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹'
      ((fun t : ℝ ↦ (t : Angle)) '' T)) := himage.preimage hmeas
  have hback : (fun t : ℝ ↦ (t : Angle)) ⁻¹' ((fun t : ℝ ↦ (t : Angle)) '' T) ∩ S = T := by
    refine Subset.antisymm ?_ fun x hx ↦ ⟨mem_image_of_mem _ hx, hTS hx⟩
    rintro x ⟨⟨y, hy, hxy⟩, hxS⟩
    exact injOn_coe_Ioc hturn (hS (hTS hy)) (hS hxS) hxy ▸ hy
  rw [Measure.map_apply hmeas himage, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
    hback]

/-- Two angular measures that agree on the angular image of every measurable subset of a real
window agree after restriction to that window's angular image. -/
theorem measure_restrict_image_congr [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {J : Set ℝ} (hJ : MeasurableSet J)
    (h : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ν ((fun t : ℝ ↦ (t : Angle)) '' T)) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹' A) := hA.preimage hmeas
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, inter_comm,
    ← image_inter_preimage, h _ (hJ.inter hpre) inter_subset_left]

/-- Two angular measures reading extended-real weights on a real window agree after restriction
to its angular image as soon as the weights agree almost everywhere on the window. -/
theorem measure_restrict_image_congr_of_ae_eq [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {ρ : Measure ℝ} {w w' : ℝ → ENNReal} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ρ)
    (hν : ∀ T, MeasurableSet T → T ⊆ J →
      ν ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w' t ∂ρ)
    (hw : ∀ᵐ t ∂ρ.restrict J, w t = w' t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  rw [hμ T hT hTJ, hν T hT hTJ]
  exact lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hTJ hw)

/-- An angular measure reading a real density on a window agrees, after restriction to the
window's angular image, with a sum of two angular measures whose densities add up to it almost
everywhere. -/
theorem measure_restrict_image_congr_add [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν₁ ν₂ : Measure Angle} {ρ : Measure ℝ} {f g h : ℝ → ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (h t) ∂ρ)
    (hν₁ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₁ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (f t) ∂ρ)
    (hν₂ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₂ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (g t) ∂ρ)
    (hf : AEMeasurable f (ρ.restrict J)) (hf0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ f t)
    (hg0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ g t) (hfg : ∀ᵐ t ∂ρ.restrict J, h t = f t + g t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      (ν₁ + ν₂).restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  have hsplit : ∀ᵐ t ∂ρ.restrict T,
      ENNReal.ofReal (h t) = ENNReal.ofReal (f t) + ENNReal.ofReal (g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTJ hf0,
      ae_restrict_of_ae_restrict_of_subset hTJ hg0,
      ae_restrict_of_ae_restrict_of_subset hTJ hfg] with t h1 h2 h3
    rw [h3, ENNReal.ofReal_add h1 h2]
  have hfT : AEMeasurable (fun t ↦ ENNReal.ofReal (f t)) (ρ.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hf.mono_measure (Measure.restrict_mono hTJ le_rfl))
  rw [hμ T hT hTJ, Measure.add_apply, hν₁ T hT hTJ, hν₂ T hT hTJ, lintegral_congr_ae hsplit,
    lintegral_add_left' hfT]

end Real.Angle

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Arclength
-/

public section

noncomputable section

open Filter
open scoped Topology

open MeasureTheory

namespace MeasureTheory

private theorem dist_le_hausdorffMeasure_image_Icc_of_continuousOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Set.Icc a
      b)) :
    ENNReal.ofReal (dist (γ a) (γ b)) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  by_cases heq : γ a = γ b
  · simp [heq]
  let n : (EuclideanSpace ℝ (Fin 2)) := ‖γ b - γ a‖⁻¹ • (γ b - γ a)
  let f : (EuclideanSpace ℝ (Fin 2)) → ℝ := fun p ↦ inner ℝ (p - γ a) n
  have hnorm : ‖n‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq)))]
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    change |inner ℝ (p - γ a) n - inner ℝ (q - γ a) n| ≤ dist p q
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm ((p - γ a) - (q - γ a)) n
    rw [hnorm, mul_one, show (p - γ a) - (q - γ a) = p - q by module,
      ← dist_eq_norm] at h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hfa : f (γ a) = 0 := by simp [f]
  have hfb : f (γ b) = dist (γ a) (γ b) := by
    dsimp only [f, n]
    rw [inner_smul_right, real_inner_self_eq_norm_sq, dist_eq_norm, inv_mul_eq_div,
      norm_sub_rev]
    field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq))]
  have hinterval : Set.Icc 0 (dist (γ a) (γ b)) ⊆ f '' (γ '' Set.Icc a b) := by
    rw [← hfa, ← hfb]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab (hf.continuous.comp_continuousOn hγ) hy
    exact ⟨γ x, ⟨x, hx, rfl⟩, hxy⟩
  calc
    ENNReal.ofReal (dist (γ a) (γ b)) =
        Measure.hausdorffMeasure 1 (Set.Icc 0 (dist (γ a) (γ b))) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ Measure.hausdorffMeasure 1 (f '' (γ '' Set.Icc a b)) := measure_mono hinterval
    _ ≤ ((1 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      hf.hausdorffMeasure_image_le (by norm_num) _
    _ = Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by simp

private theorem hausdorffMeasure_image_Icc_add_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a c) +
        Measure.hausdorffMeasure 1 (γ '' Set.Icc c b) := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := Measure.hausdorffMeasure 1
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hcb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hac
  have hinter : γ '' Set.Icc a c ∩ γ '' Set.Icc c b ⊆ {γ c} := by
    rintro p ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hxeq : x = y := hinj (hleft hx) (hright hy) hxy.symm
    have : x = c := le_antisymm hx.2 (hxeq ▸ hy.1)
    simp [this]
  have hnull : μ (γ '' Set.Icc a c ∩ γ '' Set.Icc c b) = 0 := by
    let _ := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2))
      (by norm_num : (0 : ℝ) < 1)
    exact measure_mono_null hinter (measure_singleton (γ c))
  have hmeas : MeasurableSet (γ '' Set.Icc c b) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono hright)).measurableSet
  have hunion : γ '' Set.Icc a b = γ '' Set.Icc a c ∪ γ '' Set.Icc c b := by
    rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc hac hcb]
  rw [hunion]
  exact measure_union₀ hmeas.nullMeasurableSet hnull

private theorem hausdorff_partition_sum_le (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (u : ℕ → ℝ) (n : ℕ)
    (hu : Monotone u) (hγ : ContinuousOn γ (Set.Icc (u 0) (u n)))
    (hinj : Set.InjOn γ (Set.Icc (u 0) (u n))) :
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      let v : ℕ → ℝ := fun i ↦ u (i + 1)
      have huv : u 0 ≤ u 1 := hu (Nat.zero_le 1)
      have hvn : u 1 ≤ u (n + 1) := hu (Nat.succ_le_succ (Nat.zero_le n))
      have hwhole : u 0 ≤ u (n + 1) := huv.trans hvn
      have hleft : Set.Icc (u 0) (u 1) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_right hvn
      have hright : Set.Icc (u 1) (u (n + 1)) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_left huv
      rw [Finset.sum_range_succ']
      have htail : (∑ i ∈ Finset.range n,
          edist (γ (u (i + 1 + 1))) (γ (u (i + 1)))) ≤
          Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 1) (u (n + 1))) := by
        simpa [v, Nat.add_assoc] using ih v (fun _ _ hij ↦ hu (Nat.add_le_add_right hij 1))
          (hγ.mono hright) (hinj.mono hright)
      have hfirst := dist_le_hausdorffMeasure_image_Icc_of_continuousOn γ huv
        (hγ.mono hleft)
      rw [edist_dist]
      rw [hausdorffMeasure_image_Icc_add_of_injectiveOn γ huv hvn hγ hinj]
      simpa [add_comm, dist_comm] using add_le_add htail hfirst

private theorem eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hu0 := hus 0
  have hun := hus n
  have hsub : Set.Icc (u 0) (u n) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hu0.1 hun.2
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) :=
      hausdorff_partition_sum_le γ u n hu (hγ.mono hsub) (hinj.mono hsub)
    _ ≤ Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      measure_mono (Set.image_mono hsub)

private theorem hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≤
      eVariationOn γ (Set.Icc a b) := by
  let ℓ : ℝ → ℝ := variationOnFromTo γ (Set.Icc a b) a
  have hℓstrict : StrictMonoOn ℓ (Set.Icc a b) := by
    intro x hx y hy hxy
    have hnonneg : 0 ≤ variationOnFromTo γ (Set.Icc a b) x y :=
      variationOnFromTo.nonneg_of_le γ _ hxy.le
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hle : ℓ x ≤ ℓ y := by dsimp only [ℓ]; linarith
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hzero : variationOnFromTo γ (Set.Icc a b) x y = 0 := by
      dsimp only [ℓ] at heq
      linarith
    have hed := variationOnFromTo.edist_zero_of_eq_zero hBV.locallyBoundedVariationOn
      hx hy hzero
    have hxy' : γ x = γ y := edist_eq_zero.mp hed
    exact hxy.ne (hinj hx hy hxy')
  let iso := hℓstrict.orderIso ℓ (Set.Icc a b)
  let Γ : (ℓ '' Set.Icc a b) → (EuclideanSpace ℝ (Fin 2)) := fun z ↦ γ (iso.symm z)
  have hΓle : ∀ z w : (ℓ '' Set.Icc a b), z ≤ w →
      dist (Γ z) (Γ w) ≤ dist z w := by
    intro z w hzw
    have hxy : (iso.symm z : ℝ) ≤ iso.symm w := iso.symm.monotone hzw
    have hvar : dist (γ (iso.symm z)) (γ (iso.symm w)) ≤
        variationOnFromTo γ (Set.Icc a b) (iso.symm z) (iso.symm w) := by
      rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
      apply ENNReal.toReal_mono
        (hBV.locallyBoundedVariationOn _ _ (iso.symm z).property (iso.symm w).property)
      exact eVariationOn.edist_le γ
        ⟨(iso.symm z).property, le_rfl, hxy⟩
        ⟨(iso.symm w).property, hxy, le_rfl⟩
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) (iso.symm z).property (iso.symm w).property
    change dist (γ (iso.symm z)) (γ (iso.symm w)) ≤ dist (z : ℝ) (w : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (z : ℝ) ≤ (w : ℝ) from hzw))]
    have hz : ℓ (iso.symm z) = z := congrArg Subtype.val (iso.apply_symm_apply z)
    have hw : ℓ (iso.symm w) = w := congrArg Subtype.val (iso.apply_symm_apply w)
    dsimp only [ℓ] at hz hw
    linarith
  have hΓ : LipschitzWith 1 Γ := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    rcases le_total z w with hzw | hwz
    · exact hΓle z w hzw
    · simpa only [dist_comm] using hΓle w z hwz
  have himage : Γ '' Set.univ = γ '' Set.Icc a b := by
    ext p
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨iso.symm z, (iso.symm z).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨iso ⟨x, hx⟩, Set.mem_univ _, ?_⟩
      simp [Γ]
  have hval : (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) '' Set.univ =
      ℓ '' Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨z, _, rfl⟩; exact z.property
    · intro hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hdom : Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) =
      Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := by
    conv_rhs => rw [← hval]
    have hi : Isometry (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) := fun _ _ ↦ rfl
    exact (hi.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) _).symm
  have hsub : ℓ '' Set.Icc a b ⊆
      Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨variationOnFromTo.nonneg_of_le γ _ hx.1,
      (le_abs_self _).trans (variationOnFromTo.abs_le_eVariationOn hBV)⟩
  calc
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
        Measure.hausdorffMeasure 1 (Γ '' Set.univ) := congrArg _ himage.symm
    _ ≤ Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) := by
      simpa using hΓ.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) Set.univ
    _ = Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := hdom
    _ ≤ Measure.hausdorffMeasure 1
        (Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal) := measure_mono hsub
    _ = eVariationOn γ (Set.Icc a b) := by
      rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hBV]

/-- Hausdorff length of a continuous injective arc is its total variation. -/
theorem hausdorffMeasure_image_Icc_eq_eVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      eVariationOn γ (Set.Icc a b) :=
  le_antisymm (hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn γ hab hinj hBV)
    (eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn γ hγ hinj)

private theorem eVariationOn_Icc_le_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ C * ENNReal.ofReal (b - a) := by
  simpa using hγ.comp_eVariationOn_le (g := id) (s := Set.Icc a b) (fun _ hx ↦ hx)

/-- Accumulated variation preserves a curve's Lipschitz bound. -/
private theorem lipschitzOnWith_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a) (Set.Icc a b) := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  have hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      dist (ℓ x) (ℓ y) ≤ C * dist x y := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have hvar := eVariationOn_Icc_le_of_lipschitzOn (hγ.mono hsub)
    have hreal := ENNReal.toReal_mono (by finiteness) hvar
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hreal
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy hxy
    rw [variationOnFromTo.eq_of_le _ _ hxy, Set.inter_eq_right.mpr hsub] at hadd
    change dist (variationOnFromTo γ (Set.Icc a b) a x)
      (variationOnFromTo γ (Set.Icc a b) a y) ≤ _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hbound x hx y hy hxy
  · simpa only [dist_comm] using hbound y hy x hx hyx

/-- Total variation of a Lipschitz curve is the integral of its accumulated variation derivative. -/
private theorem integral_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv (variationOnFromTo γ (Set.Icc a b) a) x) =
      (eVariationOn γ (Set.Icc a b)).toReal := by
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a)
    (Set.uIcc a b) by simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  rw [hAC.integral_deriv_eq_sub, variationOnFromTo.self,
    variationOnFromTo.eq_of_le _ _ hab, Set.inter_self, sub_zero]

private theorem norm_deriv_le_abs_deriv_of_eventually_dist_le
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {ℓ : ℝ → ℝ} {x : ℝ}
    (hγ : DifferentiableAt ℝ γ x) (hℓ : DifferentiableAt ℝ ℓ x)
    (hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤ dist (ℓ y) (ℓ x)) :
    ‖deriv γ x‖ ≤ |deriv ℓ x| := by
  have hγlim := hγ.hasDerivAt.tendsto_slope.norm
  have hℓlim := hℓ.hasDerivAt.tendsto_slope.norm
  change Filter.Tendsto _ _ (nhds |deriv ℓ x|) at hℓlim
  apply le_of_tendsto_of_tendsto hγlim hℓlim
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, norm_smul]
  rw [dist_eq_norm, dist_eq_norm] at hy
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

private theorem dist_le_dist_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x y : ℝ} (hab : a ≤ b)
    (hBV : BoundedVariationOn γ (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    dist (γ x) (γ y) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a x)
        (variationOnFromTo γ (Set.Icc a b) a y) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this hy hx (le_of_not_ge hxy)
  have hvar : dist (γ x) (γ y) ≤ variationOnFromTo γ (Set.Icc a b) x y := by
    rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
    apply ENNReal.toReal_mono (hBV.locallyBoundedVariationOn _ _ hx hy)
    exact eVariationOn.edist_le γ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy hxy
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm)]
  linarith

/-- The derivative norm of a curve is bounded by the derivative of accumulated variation. -/
private theorem norm_deriv_le_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x : ℝ}
    (hBV : BoundedVariationOn γ (Set.Icc a b)) (hx : x ∈ Set.Ioo a b)
    (hγ : DifferentiableAt ℝ γ x)
    (hℓ : DifferentiableAt ℝ (variationOnFromTo γ (Set.Icc a b) a) x) :
    ‖deriv γ x‖ ≤ deriv (variationOnFromTo γ (Set.Icc a b) a) x := by
  have hab := hx.1.le.trans hx.2.le
  have hnhds := Icc_mem_nhds hx.1 hx.2
  have hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a y)
        (variationOnFromTo γ (Set.Icc a b) a x) := by
    filter_upwards [hnhds] with y hy
    exact dist_le_dist_variationOnFromTo hab hBV hy ⟨hx.1.le, hx.2.le⟩
  have h := norm_deriv_le_abs_deriv_of_eventually_dist_le hγ hℓ hbound
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab)
  have hnonneg := hm.derivWithin_nonneg (x := x)
  rw [derivWithin_of_mem_nhds hnhds] at hnonneg
  rwa [abs_of_nonneg hnonneg] at h

/-- The derivative of a planar Lipschitz curve is integrable on its interval. -/
theorem integrableOn_deriv_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    IntegrableOn (deriv γ) (Set.Icc a b) := by
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  apply (integrable_const (C : ℝ)).mono' (aestronglyMeasurable_deriv γ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hγ

/-- The integral of speed is bounded by the total variation of a Lipschitz curve. -/
private theorem integral_norm_deriv_le_eVariationOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, ‖deriv γ x‖) ≤ (eVariationOn γ (Set.Icc a b)).toReal := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C ℓ (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [← integral_deriv_variationOnFromTo hab hγ]
  apply intervalIntegral.integral_mono_ae_restrict hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm) hAC.intervalIntegrable_deriv
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    hL.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff, measure_singleton],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hxγ hxL hxa hxb hx
  have hx' : x ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hxcc : x ∈ Set.Icc a b := ⟨hx'.1.le, hx'.2.le⟩
  exact norm_deriv_le_deriv_variationOnFromTo hBV hx'
    ((hxγ hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))
    ((hxL hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))

/-- Fundamental theorem of calculus for a planar Lipschitz curve. -/
private theorem integral_deriv_eq_sub_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv γ x) = γ b - γ a := by
  have hint : IntervalIntegrable (deriv γ) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ)
  ext i
  let L : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i
  have hcoord := L.lipschitzWith.comp_lipschitzOnWith hγ
  have hAC := (show LipschitzOnWith _ (fun x ↦ L (γ x)) (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab, LipschitzOnWith, Function.comp_apply] using
      hcoord).absolutelyContinuousOnInterval
  change L (∫ x in a..b, deriv γ x) = L (γ b - γ a)
  rw [← L.intervalIntegral_comp_comm hint, map_sub, ← hAC.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hx hxb hxI
  have hx' : x ∈ Set.Ioo a b := by
    rw [Set.uIoc_of_le hab] at hxI
    exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hd := (hx ⟨hx'.1.le, hx'.2.le⟩).differentiableAt (Icc_mem_nhds hx'.1 hx'.2)
  exact ((L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv).symm

private theorem edist_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    edist (γ b) (γ a) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [edist_dist, dist_eq_norm, ← integral_deriv_eq_sub_of_lipschitzOn hab hγ]
  exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hab)

/-- Total variation is bounded by the integral of speed for a Lipschitz curve. -/
private theorem eVariationOn_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  have hint : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hsub (i : ℕ) : Set.Icc (u i) (u (i + 1)) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  have hints (i : ℕ) : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume (u i) (u (i + 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hu (Nat.le_succ i))).mpr
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm (hsub i))
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ x in u i..u (i + 1), ‖deriv γ x‖) :=
      Finset.sum_le_sum fun i _ ↦
        edist_le_ofReal_integral_norm_deriv (hu (Nat.le_succ i)) (hγ.mono (hsub i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖deriv γ x‖) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun i _ ↦
        intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ ↦ norm_nonneg _)
    _ = ENNReal.ofReal (∫ x in u 0..u n, ‖deriv γ x‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ ↦ hints i)]
    _ ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hint

/-- Total variation of a planar Lipschitz curve is the integral of its speed. -/
theorem eVariationOn_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  apply le_antisymm (eVariationOn_le_ofReal_integral_norm_deriv hab hγ)
  have hBV : eVariationOn γ (Set.Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [ENNReal.ofReal_le_iff_le_toReal hBV]
  exact integral_norm_deriv_le_eVariationOn hab hγ

/-- Hausdorff length of a planar injective Lipschitz curve is the integral of its speed. -/
theorem hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ.continuousOn hinj
    (ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)),
    eVariationOn_eq_ofReal_integral_norm_deriv hab hγ]

/-- The image of a continuous injective planar arc of bounded variation is Lebesgue null. -/
theorem volume_image_Icc_eq_zero_of_boundedVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    volume (γ '' Set.Icc a b) = 0 := by
  have hlength : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ hinj hBV]
    exact hBV
  have harea : Measure.hausdorffMeasure 2 (γ '' Set.Icc a b) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) _).resolve_right hlength
  have habs := MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))))
  apply habs
  simpa [finrank_euclideanSpace_fin] using harea

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Graph
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

private theorem map_firstCoordinate_restrict_curve_Icc
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (a b c d : ℝ)
    (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) (Set.Icc c d) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (max a c) (min b d)) := by
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  rw [Measure.map_apply hm measurableSet_Icc,
    Measure.restrict_apply (hm measurableSet_Icc)]
  congr 1
  ext p
  constructor
  · rintro ⟨hp, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change γ x 0 ∈ Set.Icc c d at hp
    rw [hcoord x hx] at hp
    exact ⟨max_le hx.1 hp.1, le_min hx.2 hp.2⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x, ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, rfl⟩
    change γ x 0 ∈ Set.Icc c d
    rw [hcoord x ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩]
    exact ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩

/-- Projected Hausdorff measure on a Lipschitz graph has speed as its density. -/
theorem map_firstCoordinate_restrict_curve_eq_withDensity
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x) :
    Measure.map (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0)
      ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      (volume.restrict (Set.Icc a b)).withDensity (fun x ↦ ENNReal.ofReal ‖deriv γ x‖) := by
  have hinj : Set.InjOn γ (Set.Icc a b) := by
    intro x hx y hy hxy
    simpa only [hcoord x hx, hcoord y hy] using congrArg (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p
      0) hxy
  have hfinite : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hab hγ hinj]
    exact ENNReal.ofReal_ne_top
  let _ : IsFiniteMeasure ((Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) :=
    (isFiniteMeasure_restrict).mpr hfinite
  apply Measure.ext_of_Icc
  intro c d _
  rw [map_firstCoordinate_restrict_curve_Icc γ a b c d hcoord,
    withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hinter : Set.Icc c d ∩ Set.Icc a b = Set.Icc (max a c) (min b d) := by
    rw [Set.Icc_inter_Icc]
    simp only [max_comm, min_comm]
  rw [hinter]
  by_cases hcd : max a c ≤ min b d
  · have hsub : Set.Icc (max a c) (min b d) ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    rw [hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv hcd
      (hγ.mono hsub) (hinj.mono hsub)]
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm hsub)
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
    simp

/-- Weighted arclength formula for a planar Lipschitz graph on a compact interval. -/
theorem integral_restrict_curve_eq_integral_norm_deriv_mul
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hcoord : ∀ x ∈ Set.Icc a b, γ x 0 = x)
    {φ : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)) =
      ∫ x in a..b, ‖deriv γ x‖ * φ (γ x) := by
  let γc : ℝ → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ γ (max a (min x b))
  have hc : Continuous γc := hγ.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x ↦ ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hceq (x : ℝ) (hx : x ∈ Set.Icc a b) : γc x = γ x := by
    simp only [γc, min_eq_left hx.2, max_eq_right hx.1]
  have hm : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)) ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hset : MeasurableSet (γ '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hγ.continuousOn).measurableSet
  have heq : (fun p ↦ φ (γc (p 0))) =ᵐ[
      (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b)] φ := by
    filter_upwards [ae_restrict_mem hset] with p hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [hcoord x hx, hceq x hx]
  rw [← integral_congr_ae heq,
    ← integral_map (μ := (Measure.hausdorffMeasure 1).restrict (γ '' Set.Icc a b))
      (f := fun x : ℝ ↦ φ (γc x)) hm.aemeasurable
      (hφ.comp hc.measurable).aestronglyMeasurable,
    map_firstCoordinate_restrict_curve_eq_withDensity hab hγ hcoord,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_deriv γ |>.norm |>.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [hceq x hx]

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Hausdorff / Planar Graph
-/

public section

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

private theorem lipschitzOnWith_planarGraph {g : ℝ → ℝ} {s : Set ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g s) :
    LipschitzOnWith (C + 1) (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hgxy := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
  have hxy : dist x y = |x - y| := Real.dist_eq x y
  have hgy : |g x - g y| ≤ (C : ℝ) * |x - y| := by
    simpa [Real.dist_eq] using hgxy
  have hnonneg : 0 ≤ ((C : ℝ) + 1) * |x - y| := mul_nonneg (by positivity) (abs_nonneg _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_add, NNReal.coe_one,
    Real.dist_eq]
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · have hsq := mul_self_le_mul_self (abs_nonneg (g x - g y)) hgy
    nlinarith [sq_nonneg ((C : ℝ) * |x - y|), NNReal.coe_nonneg C]

private theorem hausdorffMeasure_planarGraph_eq_zero {g : ℝ → ℝ} {s t : Set ℝ}
    {C : NNReal} (hg : LipschitzOnWith C g s) (hts : t ⊆ s) (ht : volume t = 0) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) = 0 := by
  have hgraph := (lipschitzOnWith_planarGraph hg).mono hts
  apply le_zero_iff.mp
  calc
    Measure.hausdorffMeasure 1
        ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) ≤
        ((C + 1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1 t :=
      hgraph.hausdorffMeasure_image_le (by positivity)
    _ = 0 := by rw [MeasureTheory.hausdorffMeasure_real, ht, mul_zero]

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g (Set.Icc a b)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Icc a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  apply hausdorffMeasure_planarGraph_eq_zero hg (by
    intro x hx
    exact hx.1)
  rcases le_total a b with hab | hba
  · rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    have hBV := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    have hdiff := hBV.ae_differentiableAt_of_mem_uIcc
    rw [Set.uIcc_of_le hab] at hdiff
    filter_upwards [hdiff] with x hx hbad
    exact hbad.2 (hx hbad.1)
  · rcases hba.eq_or_lt with rfl | hba
    · apply measure_mono_null (by aesop) (MeasureTheory.measure_singleton b)
    · rw [Set.Icc_eq_empty (not_le_of_gt hba)]
      simp

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / (n + 1 : ℝ)) (b - 1 / (n + 1 : ℝ))
  let bad : ℕ → Set ℝ := fun n ↦ {x | x ∈ s n ∧ ¬ DifferentiableAt ℝ g x}
  have hs (n : ℕ) : s n ⊆ Set.Ioo a b := by
    intro x hx
    dsimp only [s] at hx
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a hpos) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b hpos)⟩
  have hzero (n : ℕ) : Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) = 0 := by
    obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc (hg.mono (hs n))
    exact hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero hC
  apply measure_mono_null
    (t := ⋃ n, (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) ?_
    (MeasureTheory.measure_iUnion_null hzero)
  rintro p ⟨x, hx, rfl⟩
  have hδ : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx.1.1) (sub_pos.mpr hx.1.2)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  rw [Set.mem_iUnion]
  refine ⟨n, x, ?_, rfl⟩
  refine ⟨?_, hx.2⟩
  dsimp only [s]
  constructor <;> linarith [lt_of_lt_of_le hn (min_le_left _ _),
    lt_of_lt_of_le hn (min_le_right _ _)]

/-- The graph image of the nondifferentiability set of a locally Lipschitz real
function has zero one-dimensional Hausdorff measure, in isometric coordinates. -/
theorem hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g)
    (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, g x]) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let graph : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  let transform : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p ↦ o + e.symm p
  have htransform : LipschitzWith 1 transform := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [transform, NNReal.coe_one, one_mul, dist_add_left]
    rw [e.symm.dist_map]
  have hzero := hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero hg
  apply le_zero_iff.mp
  rw [show (fun x ↦ o + e.symm !₂[x, g x]) ''
      {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x} =
      transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) by
    simp only [transform, graph, Set.image_image]]
  calc
    Measure.hausdorffMeasure 1
        (transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x})) ≤
      ((1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1
        (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) :=
      htransform.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [hzero, mul_zero]

private theorem norm_coordinateGraph_deriv (g : ℝ → ℝ) (x : ℝ) :
    ‖(!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (1 + (deriv g x) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]

private theorem hasDerivAt_coordinateGraph {g : ℝ → ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2))
      !₂[1, deriv g x] x := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap
  have hpi : HasDerivAt (fun y i ↦ !₂[y, g y].ofLp i)
      (fun i ↦ !₂[1, deriv g x].ofLp i) x := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_id x
    · exact hg.hasDerivAt
  have hcomp := L.hasFDerivAt.comp x hpi
  have hfun : (L ∘ fun y i ↦ !₂[y, g y].ofLp i) =
      (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2)) := rfl
  have hder : L.comp (ContinuousLinearMap.toSpanSingleton ℝ
      (fun i ↦ !₂[1, deriv g x].ofLp i)) =
      ContinuousLinearMap.toSpanSingleton ℝ
        (!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2)) := by
    apply ContinuousLinearMap.ext
    intro r
    rw [WithLp.ext_iff]
    funext i
    fin_cases i <;> simp [L, ContinuousLinearMap.comp_apply]
  rw [hfun, hder] at hcomp
  exact hcomp

private theorem integral_restrict_planarGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ !₂[x, g x] := by
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  rw [MeasureTheory.integral_restrict_curve_eq_integral_norm_deriv_mul hab
    (lipschitzOnWith_planarGraph hg) (fun _ _ ↦ rfl) hφ]
  apply intervalIntegral.integral_congr_ae
  have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hg
  have hdiff := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    |>.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff] with x hx hxi
  have hderiv := (hasDerivAt_coordinateGraph (hx ⟨le_of_lt hxi.1, hxi.2⟩)).deriv
  rw [hderiv, norm_coordinateGraph_deriv]

/-- Weighted Hausdorff integration over an isometric planar graph equals the
parameter integral weighted by its almost-everywhere speed. -/
theorem integral_restrict_coordinateGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b)) (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ (o + e.symm !₂[x, g x]) := by
  let F : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) :=
    e.symm.toIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst (V := EuclideanSpace ℝ (Fin 2))
        (P := EuclideanSpace ℝ (Fin 2)) ℝ o).toIsometryEquiv
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  have hF : ∀ p, F p = o + e.symm p := by
    intro p
    simp [F, add_comm]
  rw [show (fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b =
      F '' (γ '' Set.Icc a b) by
    rw [Set.image_image]
    congr 1
    funext x
    exact (hF _).symm]
  rw [(F.measurePreserving_hausdorffMeasure 1).setIntegral_image_emb
    F.toHomeomorph.measurableEmbedding φ (γ '' Set.Icc a b)]
  have hbase := integral_restrict_planarGraph_eq_integral_sqrt_mul hab hg
    (hφ.comp F.continuous.measurable)
  simpa only [γ, Function.comp_apply, hF] using hbase

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Atomic Bounds
-/

public section

noncomputable section

namespace MeasureTheory

/-- A finite sum of atomic contributions is bounded by the integral of a nonnegative function. -/
theorem sum_measureReal_mul_le_setIntegral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : MeasureTheory.Measure α) (D : Finset α)
    {E : Set α} {f : α → ℝ} (hE : MeasurableSet E)
    (hDE : (D : Set α) ⊆ E) (hf : MeasureTheory.IntegrableOn f E μ)
    (hnonneg : ∀ x ∈ E, 0 ≤ f x) :
    ∑ x ∈ D, (μ {x}).toReal * f x ≤ ∫ x in E, f x ∂μ := by
  have hfinite := MeasureTheory.setIntegral_finset D (hf.mono_set hDE)
  simp only [smul_eq_mul, MeasureTheory.measureReal_def] at hfinite
  rw [← hfinite]
  apply MeasureTheory.setIntegral_mono_set hf
  · exact (MeasureTheory.ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hnonneg)
  · exact Filter.Eventually.of_forall hDE

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Interval Exhaustion
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

/-- Every interior point eventually belongs to the standard inner exhaustion of an interval. -/
theorem eventually_mem_innerIcc_of_mem_Ioo {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) :
    ∀ᶠ n : ℕ in atTop,
      x ∈ Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) := by
  have hleft := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.1))
  have hright := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (sub_pos.mpr hx.2))
  exact (hleft.and hright).mono fun n hn ↦ by
    constructor <;> linarith [hn.1, hn.2]

/-- Each interval in the standard inner exhaustion lies in the open interval. -/
theorem innerIcc_subset_Ioo (a b : ℝ) (n : ℕ) :
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) ⊆
      Set.Ioo a b := by
  intro x hx
  have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  constructor <;> linarith [hx.1, hx.2]

/-- Integrals over compact intervals exhausting the interior converge to the
integral over the full compact interval. -/
theorem tendsto_integral_innerIcc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hf : Integrable f (volume.restrict (Set.Icc a b))) :
    Tendsto (fun n : ℕ ↦ ∫ x in Set.Icc (a + 1 / ((n : ℝ) + 1))
        (b - 1 / ((n : ℝ) + 1)), f x)
      atTop (nhds (∫ x in Set.Icc a b, f x)) := by
  let t := Set.Icc a b
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1))
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_Icc
  have hft : Integrable (t.indicator f) volume :=
    IntegrableOn.integrable_indicator hf measurableSet_Icc
  have hmeas (n : ℕ) : AEStronglyMeasurable ((s n).indicator f) volume := by
    apply (hft.1.indicator (hs n)).congr
    filter_upwards [] with x
    by_cases hx : x ∈ s n
    · have hxi := innerIcc_subset_Ioo a b n hx
      have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
      simp [Set.indicator, hx, hxt]
    · simp [Set.indicator, hx]
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖(s n).indicator f x‖ ≤ ‖t.indicator f x‖ :=
    Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s n
      · have hxi := innerIcc_subset_Ioo a b n hx
        have hxt : x ∈ t := ⟨hxi.1.le, hxi.2.le⟩
        simp [Set.indicator, hx, hxt]
      · simp only [Set.indicator, hx, ↓reduceIte, norm_zero]
        exact norm_nonneg _
  have hIooVolume : Set.Ioo a b =ᵐ[volume] Set.Icc a b := Ioo_ae_eq_Icc
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ (s n).indicator f x)
      atTop (nhds (t.indicator f x)) := by
    filter_upwards [hIooVolume] with x hxeq
    by_cases hx : x ∈ Set.Ioo a b
    · have hev := eventually_mem_innerIcc_of_mem_Ioo hx
      apply tendsto_const_nhds.congr'
      exact hev.mono fun n hn ↦
        (Set.indicator_of_mem (hxeq.mp hx) f).trans
          (Set.indicator_of_mem hn f).symm
    · have hxt : x ∉ t := fun h ↦ hx (hxeq.mpr h)
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hxn : x ∉ s n := fun h ↦ by
        have hxi := innerIcc_subset_Ioo a b n h
        exact hxt ⟨hxi.1.le, hxi.2.le⟩
      simp only [Set.indicator, hxn, hxt, ↓reduceIte]
  have ht := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun x ↦ ‖t.indicator f x‖) hmeas hft.norm hbound hlim
  simpa only [s, t, integral_indicator, hs, measurableSet_Icc] using ht

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Moving Intervals
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Moving interval cutoffs preserve almost-everywhere convergence on the limiting interior. -/
theorem ae_tendsto_indicator_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] {a b : ℕ → ℝ} {c d : ℝ}
    {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂volume, Tendsto (fun n ↦ (Icc (a n) (b n)).indicator (f n) x)
      atTop (𝓝 ((Icc c d).indicator g x)) := by
  have hne (y : ℝ) : ∀ᵐ x ∂volume, x ≠ y := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp (measure_singleton y :
      volume ({y} : Set ℝ) = 0))
  filter_upwards [hf, hne c, hne d] with x hx hxc hxd
  by_cases hmem : x ∈ Icc c d
  · have hxi : x ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxc), lt_of_le_of_ne hmem.2 hxd⟩
    rw [indicator_of_mem hmem]
    apply (hx hxi).congr'
    filter_upwards [ha.eventually (gt_mem_nhds hxi.1),
      hb.eventually (lt_mem_nhds hxi.2)] with n hn hn'
    exact (indicator_of_mem (show x ∈ Icc (a n) (b n) from ⟨hn.le, hn'.le⟩) _).symm
  · rw [indicator_of_notMem hmem]
    apply tendsto_const_nhds.congr'
    have hout : x < c ∨ d < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hmem
    rcases hout with hleft | hright
    · filter_upwards [ha.eventually (lt_mem_nhds hleft)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.1) _).symm
    · filter_upwards [hb.eventually (gt_mem_nhds hright)] with n hn
      exact (indicator_of_notMem (show x ∉ Icc (a n) (b n) from
        fun h ↦ (not_le.mpr hn) h.2) _).symm

/-- Dominated convergence on intervals whose endpoints converge, using convergence
only in the interior of the limiting interval. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} {c d : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E} {bound : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hbound : Integrable bound) (hbound_nonneg : ∀ᵐ x ∂volume, 0 ≤ bound x)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ bound x)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  have hm : ∀ᶠ n in atTop,
      AEStronglyMeasurable ((Icc (a n) (b n)).indicator (f n)) volume := by
    filter_upwards [hmeas] with n hn
    exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hn
  have hd : ∀ᶠ n in atTop, ∀ᵐ x ∂volume,
      ‖(Icc (a n) (b n)).indicator (f n) x‖ ≤ bound x := by
    filter_upwards [hdom] with n hn
    filter_upwards [hn, hbound_nonneg] with x hx hnonneg
    by_cases hmem : x ∈ Icc (a n) (b n)
    · simpa only [indicator_of_mem hmem] using hx hmem
    · simpa only [indicator_of_notMem hmem, norm_zero] using hnonneg
  have h := tendsto_integral_filter_of_dominated_convergence bound hm hd hbound
    (ae_tendsto_indicator_Icc_of_tendsto_endpoints ha hb hf)
  simpa only [integral_indicator measurableSet_Icc] using h

/-- A uniform bound on moving finite intervals suffices for dominated convergence. -/
theorem tendsto_integral_Icc_of_tendsto_endpoints_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} {c d M : ℝ} {f : ℕ → ℝ → E} {g : ℝ → E}
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 d))
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Icc (a n) (b n))))
    (hM : 0 ≤ M)
    (hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, x ∈ Icc (a n) (b n) → ‖f n x‖ ≤ M)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo c d → Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ ∫ x in Icc (a n) (b n), f n x) atTop
      (𝓝 (∫ x in Icc c d, g x)) := by
  let s := Icc (c - 1) (d + 1)
  have hs : MeasurableSet s := measurableSet_Icc
  have hi : Integrable (s.indicator (fun _ : ℝ ↦ M)) volume := by
    apply IntegrableOn.integrable_indicator _ hs
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  apply tendsto_integral_Icc_of_tendsto_endpoints ha hb hmeas hi
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ s <;> simp [indicator, hx, hM]
  · filter_upwards [hdom, ha.eventually (lt_mem_nhds (show c - 1 < c by linarith)),
      hb.eventually (gt_mem_nhds (show d < d + 1 by linarith))] with n hn hna hnb
    filter_upwards [hn] with x hx
    intro hmem
    have hxs : x ∈ s := ⟨hna.le.trans hmem.1, hmem.2.trans hnb.le⟩
    simpa only [indicator_of_mem hxs] using hx hmem
  · exact hf

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Integral / Translation
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- Translation of a measurable real set preserves integrals. -/
theorem integral_image_add_right_eq (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    (∫ y in (fun x : ℝ ↦ x + c) '' E, f y) = ∫ x in E, f (x + c) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact (hr.integral_comp hφ f).symm

/-- Translating both endpoints of a closed real interval translates the integrand. -/
theorem integral_Icc_const_add_eq (c a b : ℝ) (f : ℝ → ℝ) :
    (∫ y in Icc (c + a) (c + b), f y) = ∫ x in Icc a b, f (x + c) := by
  rw [show c + a = a + c from add_comm c a, show c + b = b + c from add_comm c b,
    ← Set.image_add_const_Icc, integral_image_add_right_eq c _ measurableSet_Icc]

/-- Integrability on a translated measurable set is preserved by translation. -/
theorem integrableOn_comp_add_right_iff (c : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (f : ℝ → ℝ) :
    IntegrableOn (fun x ↦ f (x + c)) E ↔
      IntegrableOn f ((fun x : ℝ ↦ x + c) '' E) := by
  let φ : ℝ → ℝ := fun x ↦ x + c
  have hφ : MeasurableEmbedding φ :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving φ volume volume :=
    ⟨hφ.measurable, map_add_right_eq_self volume c⟩
  have himage : MeasurableSet (φ '' E) := hφ.measurableSet_image' hE
  have hpre : φ ⁻¹' (φ '' E) = E := Set.preimage_image_eq E hφ.injective
  have hr := hpres.restrict_preimage himage
  rw [hpre] at hr
  exact hr.integrable_comp_emb hφ

/-- A lower Lebesgue integral of a right-translated function is the integral of the function
itself over the translated set. -/
theorem setLIntegral_comp_sub_right (w : ℝ → ℝ≥0∞) (c : ℝ) (A : Set ℝ) :
    ∫⁻ u in A, w (u - c) = ∫⁻ t in (fun t : ℝ ↦ t + c) ⁻¹' A, w t := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  simpa using ((measurePreserving_add_right (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    hemb (fun u ↦ w (u - c)) A).symm

/-- Pushing a weighted restriction of Lebesgue measure forward along `t ↦ t + c` translates both
the set and the weight. -/
theorem map_add_right_restrict_withDensity (c : ℝ) (S : Set ℝ) (w : ℝ → ℝ≥0∞) :
    Measure.map (fun t : ℝ ↦ t + c) ((volume.restrict S).withDensity w) =
      (volume.restrict ((fun t : ℝ ↦ t + c) '' S)).withDensity (fun u ↦ w (u - c)) := by
  have hemb : MeasurableEmbedding fun t : ℝ ↦ t + c :=
    (MeasurableEquiv.addRight c).measurableEmbedding
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ t + c) ⁻¹' A) := hA.preimage hemb.measurable
  rw [Measure.map_apply hemb.measurable hA, withDensity_apply _ hpre,
    Measure.restrict_restrict hpre, withDensity_apply _ hA, Measure.restrict_restrict hA,
    setLIntegral_comp_sub_right, Set.preimage_inter, hemb.injective.preimage_image]

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / Atoms
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- A membership that fails only on a countable set holds almost everywhere on the restriction
of a measure with null singletons. -/
theorem ae_restrict_mem_of_countable_diff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NullSingletonClass μ] {S A N : Set α} (hS : MeasurableSet S) (hN : N.Countable)
    (hsub : S \ A ⊆ N) : ∀ᵐ x ∂μ.restrict S, x ∈ A := by
  rw [ae_iff, Measure.restrict_apply' hS]
  exact measure_mono_null (fun x hx ↦ hsub ⟨hx.2, hx.1⟩) (hN.measure_zero μ)

/-- Along an injective parametrization, a finite-measure atom occurs only almost nowhere. -/
theorem ae_measure_singleton_comp_eq_zero_of_injOn
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [SFinite μ] {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → X} (hf : Set.InjOn f s) :
    ∀ᵐ t ∂volume.restrict s, μ {f t} = 0 := by
  let A : Set X := {x | 0 < μ {x}}
  have hA : A.Countable := μ.countable_meas_level_set_pos measurable_id
  let B : Set ℝ := {t | t ∈ s ∧ f t ∈ A}
  have hmaps : MapsTo f B A := fun _ h ↦ h.2
  have hB : B.Countable := hmaps.countable_of_injOn (hf.mono fun _ h ↦ h.1) hA
  filter_upwards [ae_restrict_mem hs, hB.ae_notMem (volume.restrict s)] with t hts htB
  by_contra hne
  exact htB ⟨hts, pos_iff_ne_zero.mpr hne⟩

/-- A measure carried by a finite set is the sum of its atomic contributions. -/
theorem measure_eq_sum_singleton_inter_of_compl_eq_zero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S : Finset α) (hS : μ (S : Set α)ᶜ = 0)
    (E : Set α) (hE : MeasurableSet E) :
    μ E = ∑ x ∈ S, μ ({x} ∩ E) := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∈ (S : Set α) := by
    rw [ae_iff]
    exact hS
  have hrestrict : μ.restrict (S : Set α) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hinter : μ E = μ (E ∩ (S : Set α)) := by
    calc
      μ E = (μ.restrict (S : Set α)) E := by rw [hrestrict]
      _ = μ (E ∩ (S : Set α)) := Measure.restrict_apply hE
  rw [hinter]
  have heq : E ∩ (S : Set α) = ⋃ x ∈ S, ({x} ∩ E : Set α) := by
    ext x
    simp [and_comm]
  rw [heq, measure_biUnion_finset]
  · intro i _ j _ hij
    simp only [Set.disjoint_left]
    intro x hxi hxj
    exact hij (hxi.1.symm.trans hxj.1)
  · intro b _
    exact (measurableSet_singleton b).inter hE

/-- A measure carried by the image of a finite index set is bounded by the sum of atomic bounds
over any index subset containing every index whose atom meets the measured set. -/
theorem measure_le_sum_of_measure_compl_image_eq_zero
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (S S' : Finset ι) (f : ι → α) (b : ι → ENNReal)
    (hf : Set.InjOn f (S : Set ι)) (hS : μ (f '' (S : Set ι))ᶜ = 0)
    (hb : ∀ i ∈ S, μ {f i} ≤ b i) (E : Set α) (hE : MeasurableSet E)
    (hactive : ∀ i ∈ S, f i ∈ E → i ∈ S') :
    μ E ≤ ∑ i ∈ S', b i := by
  classical
  have himage : ((S.image f : Finset α) : Set α) = f '' (S : Set ι) := by
    ext x
    simp
  rw [measure_eq_sum_singleton_inter_of_compl_eq_zero μ (S.image f)
    (by rw [himage]; exact hS) E hE]
  calc
    ∑ x ∈ S.image f, μ ({x} ∩ E) = ∑ i ∈ S, μ ({f i} ∩ E) :=
      Finset.sum_image fun i hi j hj h ↦ hf (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) h
    _ ≤ ∑ i ∈ S, (if f i ∈ E then b i else 0) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      by_cases hfi : f i ∈ E
      · have hinter : ({f i} : Set α) ∩ E = {f i} := by
          ext y
          simp [hfi]
        simp only [hinter, hfi, ite_true]
        exact hb i hi
      · have hinter : ({f i} : Set α) ∩ E = ∅ := by
          ext y
          simp [hfi]
        simp [hinter, hfi]
    _ = ∑ i ∈ S.filter (fun i ↦ f i ∈ E), b i := (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ S', b i := by
      refine Finset.sum_le_sum_of_subset fun i hi ↦ ?_
      obtain ⟨hiS, hiE⟩ := Finset.mem_filter.1 hi
      exact hactive i hiS hiE

/-! ### Almost every point of a half-open interval is interior -/

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ico_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ico (countable_singleton a)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h ↦ hx' ⟨h, hx.2⟩) hx.1)

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in the
corresponding open interval. -/
theorem ae_restrict_Ioc_mem_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a b), t ∈ Ioo a b :=
  ae_restrict_mem_of_countable_diff measurableSet_Ioc (countable_singleton b)
    fun _ ⟨hx, hx'⟩ ↦ mem_singleton_iff.2 (le_antisymm hx.2 (not_lt.1 fun h ↦ hx' ⟨hx.1, h⟩))

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ico_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ico a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ico
    ((countable_singleton b).insert a) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact Or.inl (le_antisymm (not_lt.1 fun hlt ↦ hx' (Or.inl ⟨hlt, h⟩)) hx.1)
  · exact Or.inr (mem_singleton_iff.2 h)
  · exact absurd (Or.inr ⟨h, hx.2⟩) hx'

/-- Almost every point of a half-open interval, for a measure with null singletons, lies in one
of the two open intervals cut out by an arbitrary intermediate point. -/
theorem ae_restrict_Ioc_mem_Ioo_union_Ioo {μ : Measure ℝ} [NullSingletonClass μ] (a b c : ℝ) :
    ∀ᵐ t ∂μ.restrict (Ioc a c), t ∈ Ioo a b ∪ Ioo b c := by
  refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
    ((countable_singleton c).insert b) ?_
  rintro x ⟨hx, hx'⟩
  rcases lt_trichotomy x b with h | h | h
  · exact absurd (Or.inl ⟨hx.1, h⟩) hx'
  · exact Or.inl h
  · exact Or.inr (mem_singleton_iff.2
      (le_antisymm hx.2 (not_lt.1 fun hlt ↦ hx' (Or.inr ⟨h, hlt⟩))))

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Haar-null lines and inner-product level sets

Lines and hyperplanes of a finite-dimensional real normed space carry no additive Haar mass.
This file records the two convenient forms used when a planar region is exhausted by triangles
up to the rays through finitely many vertices.
-/

public section

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A line through the origin is a proper subspace once the ambient dimension exceeds one. -/
theorem Submodule.span_singleton_ne_top (h : 1 < Module.finrank ℝ E) (v : E) :
    (ℝ ∙ v) ≠ ⊤ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    rw [Submodule.span_zero_singleton]
    exact bot_ne_top
  · intro htop
    have hfin : Module.finrank ℝ E = 1 := (finrank_eq_one_iff_of_nonzero v hv).2 htop
    omega

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Any line in a space of dimension at least two is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_vadd_span_singleton (μ : Measure E)
    [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o v : E) :
    μ (o +ᵥ (ℝ ∙ v : Set E)) = 0 := by
  rw [measure_vadd]
  exact μ.addHaar_submodule _ (Submodule.span_singleton_ne_top h v)

/-- A countable union of lines through a common point is null. -/
theorem MeasureTheory.Measure.addHaar_iUnion_vadd_span_singleton {ι : Type*} [Countable ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o : E) (v : ι → E) :
    μ (⋃ i, o +ᵥ (ℝ ∙ v i : Set E)) = 0 :=
  measure_iUnion_null fun i ↦ μ.addHaar_vadd_span_singleton h o (v i)

/-- A level set of a nonzero inner-product functional is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_setOf_real_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {u : F} (hu : u ≠ 0) (c : ℝ) :
    μ {p : F | inner ℝ p u = c} = 0 := by
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  set f : F →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap with hf
  set A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f with hA
  have hAset : (A : Set F) = {p : F | inner ℝ p u = c} := by
    ext p
    simp [hA, hf, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hAset]
  refine μ.addHaar_affineSubspace _ fun htop ↦ ?_
  have hp : ((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hAset, Set.mem_ofPred_eq] at hp
  have : inner ℝ (((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u) u = c + ‖u‖ ^ 2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [this] at hp
  linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / Map
-/

public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

/-- If `g` is almost everywhere a left inverse of `f`, then pushing a measure forward along `f`
and then along `g` recovers it. This is the almost-everywhere form of
`MeasurableEquiv.map_symm_map`. -/
theorem map_map_of_ae_leftInverse {f : α → β} (hf : Measurable f) {g : β → α}
    (hg : Measurable g) (h : ∀ᵐ a ∂μ, g (f a) = a) :
    (μ.map f).map g = μ := by
  rw [map_map hg hf, show μ.map (g ∘ f) = μ.map id from map_congr h, map_id]

end MeasureTheory.Measure

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Measure / With Density
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- An injective image of a weighted restriction preserves null singleton masses. -/
theorem map_restrict_withDensity_singleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [NullSingletonClass μ] (f : α → β) (hf : Measurable f)
    (s : Set α) (hinj : Set.InjOn f s) (w : α → ℝ≥0∞) {x : α} (hx : x ∈ s) :
    Measure.map f ((μ.restrict s).withDensity w) {f x} = 0 := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (hf (measurableSet_singleton _))]
  have heq : f ⁻¹' {f x} ∩ s = {x} := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ hinj h.2 hx h.1, fun h ↦ by subst y; exact ⟨rfl, hx⟩⟩
  rw [heq, measure_singleton]

/-- Pushing a weighted measure forward along a measurable map is linear in the weight: if `w` is
the pointwise combination `a * w₁ + b * w₂`, then the pushforward of `μ.withDensity w` is the
same combination of the pushforwards of `μ.withDensity w₁` and `μ.withDensity w₂`. -/
theorem map_withDensity_eq_smul_add_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (a b : ℝ≥0∞) {w w₁ w₂ : α → ℝ≥0∞}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂) (hw : ∀ x, w x = a * w₁ x + b * w₂ x) :
    Measure.map φ (μ.withDensity w) =
      a • Measure.map φ (μ.withDensity w₁) + b • Measure.map φ (μ.withDensity w₂) := by
  have hwfun : w = a • w₁ + b • w₂ := funext hw
  rw [hwfun, withDensity_add_left (h₁.const_smul a), withDensity_smul _ h₁,
    withDensity_smul _ h₂, Measure.map_add _ _ hφ, Measure.map_smul _ hφ.aemeasurable,
    Measure.map_smul _ hφ.aemeasurable]

end MeasureTheory.Measure

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Region Between
-/

public section

open EuclideanSpace MeasureTheory Set

theorem volume_setOf_mem_Icc_eq_volume_regionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

theorem volume_regionBetween_triangle {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    volume (regionBetween (fun _ : ℝ ↦ 0) (fun x ↦ h - h / b * x) (Ioc 0 b)) =
      ENNReal.ofReal (b * h / 2) := by
  have hc : Continuous (fun x : ℝ ↦ h - h / b * x) := by fun_prop
  have hi := hc.intervalIntegrable (μ := volume) 0 b
  have hz := (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ))).intervalIntegrable
    (μ := volume) 0 b
  change (volume.prod volume) _ = _
  rw [volume_regionBetween_eq_integral
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hz)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hi) measurableSet_Ioc]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [← intervalIntegral.integral_of_le hb.le]
    have hm : IntervalIntegrable (fun x : ℝ ↦ h / b * x) volume 0 b :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 b
    have hh' : IntervalIntegrable (fun _ : ℝ ↦ h) volume 0 b :=
      continuous_const.intervalIntegrable 0 b
    rw [intervalIntegral.integral_sub hh' hm,
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  · intro x hx
    have := mul_le_mul_of_nonneg_left hx.2 (div_nonneg hh hb.le)
    have heq : h / b * b = h := div_mul_cancel₀ h hb.ne'
    linarith

theorem volume_setOf_mem_Ioc_eq_volume_regionBetween
    {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_oc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Ioc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Ioc, Real.volume_Ioo]
  · simp [regionBetween, hx]

/-- The planar volume of the horizontal band between the graphs of `f` and `g` over `s`,
where the first coordinate is the one squeezed between the two graphs. -/
theorem volume_horizontalIcc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_cc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- The half-open variant of `volume_horizontalIcc`. -/
theorem volume_horizontalIoc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_oc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Ioc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- A planar set whose second coordinate lies in `[0, 1]` and whose first coordinate is
squeezed between a continuous graph and its horizontal translate by `c` has volume at
most `c`. Only the upper bound is asserted, so no measurability of the set is needed. -/
theorem volume_le_of_subset_horizontalBand {X : Set (EuclideanSpace ℝ (Fin 2))}
    {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) (hc : 0 ≤ c)
    (hX : ∀ p ∈ X, (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ f (p 1) ≤ p 0 ∧ p 0 ≤ f (p 1) + c) :
    volume X ≤ ENNReal.ofReal c := by
  have hg : Continuous (fun y ↦ f y + c) := hf.add continuous_const
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hf.intervalIntegrable 0 1)
  have hgi : IntegrableOn (fun y ↦ f y + c) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hg.intervalIntegrable 0 1)
  have key := volume_horizontalIcc (f := f) (g := fun y ↦ f y + c)
    (s := Icc (0 : ℝ) 1) hf.measurable hg.measurable measurableSet_Icc hfi hgi
    (fun x _ ↦ by simp [hc])
  have hint : ∫ x in Icc (0 : ℝ) 1, ((fun y ↦ f y + c) - f) x = c := by
    have hdiff : ((fun y ↦ f y + c) - f) = fun _ ↦ c := by funext y; simp
    rw [hdiff, setIntegral_const]
    simp
  rw [hint] at key
  refine le_trans (measure_mono ?_) key.le
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hX p hp
  exact ⟨h1, h2, h3⟩

/-- The horizontal unit strip meets the band `c ≤ a * x + b * y ≤ c + 1` in a
parallelogram of area `1 / |a|`. Only the upper bound is asserted. -/
theorem volume_horizontalBand_inter_le (a b c : ℝ) (ha : a ≠ 0) :
    volume {p : EuclideanSpace ℝ (Fin 2) | (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (c ≤ a * p 0 + b * p 1 ∧ a * p 0 + b * p 1 ≤ c + 1)} ≤
      ENNReal.ofReal (1 / |a|) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c + 1 - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff_of_neg hneg]
      linarith
    · have hrw : (c + 1 - b * p 1) / a + 1 / |a| = (c - b * p 1) / a := by
        rw [abs_of_neg hneg]
        field_simp
        ring
      rw [hrw, le_div_iff_of_neg hneg]
      linarith
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      linarith
    · have hrw : (c - b * p 1) / a + 1 / |a| = (c + 1 - b * p 1) / a := by
        rw [abs_of_pos hpos]
        field_simp
        ring
      rw [hrw, le_div_iff₀ hpos]
      linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Planar trapezoids with horizontal parallel sides
-/

public section

namespace EuclideanSpace

/-- A convex planar set containing the four vertices of a trapezoid whose parallel sides are
the horizontal segments at heights `0` and `1` contains the whole trapezoid. -/
theorem horizontalTrapezoid_subset_of_convex {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : Convex ℝ S) {l₀ r₀ l₁ r₁ : ℝ}
    (h₀l : (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₀r : (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁l : (!₂[l₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S)
    (h₁r : (!₂[r₁, 1] : EuclideanSpace ℝ (Fin 2)) ∈ S) :
    {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} ⊆ S := by
  rintro q ⟨⟨hy0, hy1⟩, hql, hqr⟩
  have hleft : ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) ∈ S :=
    hS h₀l h₁l (by linarith) hy0 (by ring)
  have hright : ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) ∈ S :=
    hS h₀r h₁r (by linarith) hy0 (by ring)
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      q 0 = (1 - s) * ((1 - q 1) * l₀ + q 1 * l₁) + s * ((1 - q 1) * r₀ + q 1 * r₁) := by
    rcases (hql.trans hqr).eq_or_lt with hLR | hLR
    · exact ⟨0, le_rfl, zero_le_one, by rw [sub_zero, one_mul, zero_mul, add_zero]; linarith⟩
    · have hne : (1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁) ≠ 0 := by linarith
      refine ⟨(q 0 - ((1 - q 1) * l₀ + q 1 * l₁)) /
          ((1 - q 1) * r₀ + q 1 * r₁ - ((1 - q 1) * l₀ + q 1 * l₁)),
        div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith, ?_⟩
      field_simp
      ring
  have hcoord : ∀ z w : EuclideanSpace ℝ (Fin 2), z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have heq : q = (1 - s) • ((1 - q 1) • (!₂[l₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[l₁, 1]) +
      s • ((1 - q 1) • (!₂[r₀, 0] : EuclideanSpace ℝ (Fin 2)) + q 1 • !₂[r₁, 1]) := by
    refine hcoord _ _ ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
      linear_combination hs
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
  rw [heq]
  exact hS hleft hright (by linarith) hs0 (by ring)

/-- The planar area of the trapezoid cut from the horizontal band `y₀ ≤ y ≤ y₁` by the two lines
`x = a + b * y` and `x = c + d * y`: the height of the band times the mean of the lengths of its
two horizontal sides. -/
theorem volume_horizontalTrapezoid_band {y₀ y₁ a b c d : ℝ} (hy : y₀ ≤ y₁)
    (h₀ : a + b * y₀ ≤ c + d * y₀) (h₁ : a + b * y₁ ≤ c + d * y₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc y₀ y₁ ∧
        q 0 ∈ Set.Icc (a + b * q 1) (c + d * q 1)} =
      ENNReal.ofReal ((y₁ - y₀) *
        ((c + d * y₀ - (a + b * y₀)) + (c + d * y₁ - (a + b * y₁))) / 2) := by
  have hfc : Continuous fun y : ℝ ↦ a + b * y := by fun_prop
  have hgc : Continuous fun y : ℝ ↦ c + d * y := by fun_prop
  rw [volume_horizontalIcc (f := fun y : ℝ ↦ a + b * y) (g := fun y : ℝ ↦ c + d * y)
    (s := Set.Icc y₀ y₁) hfc.measurable hgc.measurable measurableSet_Icc
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hfc.intervalIntegrable y₀ y₁))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mp (hgc.intervalIntegrable y₀ y₁))
    (fun y hy' ↦ by
      rcases hy.eq_or_lt with rfl | hylt
      · have : y = y₀ := le_antisymm hy'.2 hy'.1
        rw [this]
        exact h₀
      · have hcoef : (y₁ - y) * (c + d * y₀ - (a + b * y₀)) +
            (y - y₀) * (c + d * y₁ - (a + b * y₁)) =
            (y₁ - y₀) * (c + d * y - (a + b * y)) := by ring
        nlinarith [mul_nonneg (by linarith [hy'.2] : (0 : ℝ) ≤ y₁ - y) (by linarith : (0 : ℝ) ≤
            c + d * y₀ - (a + b * y₀)),
          mul_nonneg (by linarith [hy'.1] : (0 : ℝ) ≤ y - y₀) (by linarith : (0 : ℝ) ≤
            c + d * y₁ - (a + b * y₁))])]
  congr 1
  have hrw : ((fun y : ℝ ↦ c + d * y) - fun y : ℝ ↦ a + b * y) =
      fun y : ℝ ↦ (c - a) + (d - b) * y := by
    funext y
    simp only [Pi.sub_apply]
    ring
  have hii : IntervalIntegrable (fun x : ℝ ↦ (d - b) * x) MeasureTheory.volume y₀ y₁ :=
    (by fun_prop : Continuous fun x : ℝ ↦ (d - b) * x).intervalIntegrable y₀ y₁
  rw [hrw, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_add intervalIntegrable_const hii,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- The planar area of a trapezoid whose parallel sides are the horizontal segments
`[l₀, r₀] × {0}` and `[l₁, r₁] × {1}` is the mean of their lengths. -/
theorem volume_horizontalTrapezoid {l₀ r₀ l₁ r₁ : ℝ} (h₀ : l₀ ≤ r₀) (h₁ : l₁ ≤ r₁) :
    MeasureTheory.volume {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      ENNReal.ofReal ((r₀ - l₀ + (r₁ - l₁)) / 2) := by
  have hset : {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc ((1 - q 1) * l₀ + q 1 * l₁) ((1 - q 1) * r₀ + q 1 * r₁)} =
      {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
        q 0 ∈ Set.Icc (l₀ + (l₁ - l₀) * q 1) (r₀ + (r₁ - r₀) * q 1)} := by
    refine Set.ext fun q ↦ ?_
    simp only [Set.mem_ofPred_eq,
      show (1 - q 1) * l₀ + q 1 * l₁ = l₀ + (l₁ - l₀) * q 1 from by ring,
      show (1 - q 1) * r₀ + q 1 * r₁ = r₀ + (r₁ - r₀) * q 1 from by ring]
  rw [hset, volume_horizontalTrapezoid_band zero_le_one (by simpa using h₀) (by simpa using h₁)]
  congr 1
  ring

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The area of a planar triangle

The convex hull of three points of the Euclidean plane has area one half of the absolute
determinant of the two edge vectors emanating from the first point. The proof transports the
standard right triangle, whose area is computed by integration, along the linear map sending
the coordinate basis to the two edge vectors.
-/

public section

open MeasureTheory Set
open scoped Pointwise

namespace EuclideanSpace

private def standardTriangleProd : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}

private theorem measurableSet_standardTriangleProd : MeasurableSet standardTriangleProd := by
  have h : MeasurableSet {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ 1) ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 - p.1} :=
    ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst)))
  simpa only [standardTriangleProd, Set.mem_Ioc, Set.mem_Icc] using h

private theorem volume_standardTriangleProd :
    volume standardTriangleProd = ENNReal.ofReal (1 / 2) := by
  rw [show standardTriangleProd =
      {p : ℝ × ℝ | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc (0 : ℝ) (1 - p.1)} from rfl,
    volume_setOf_mem_Icc_eq_volume_regionBetween
      (f := fun _ : ℝ ↦ 0) (g := fun x ↦ 1 - x) (s := Ioc 0 1)
      measurable_const (measurable_const.sub measurable_id) measurableSet_Ioc]
  simpa using
    (volume_regionBetween_triangle (b := 1) (h := 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1))

private def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Ioc 0 1 ∧ p 1 ∈ Icc 0 (1 - p 0)}

private theorem volume_standardTriangle : volume standardTriangle = ENNReal.ofReal (1 / 2) := by
  have hpre := volume_preserving_finTwoCoordinates.measure_preimage
    measurableSet_standardTriangleProd.nullMeasurableSet
  rw [show (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) ⁻¹' standardTriangleProd =
      standardTriangle from rfl, volume_standardTriangleProd] at hpre
  exact hpre

private def closedStandardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 - p 0}

private theorem volume_closedStandardTriangle :
    volume closedStandardTriangle = ENNReal.ofReal (1 / 2) := by
  rw [← volume_standardTriangle]
  refine (measure_eq_measure_of_null_sdiff (μ := volume) ?_ ?_).symm
  · exact fun p hp ↦ ⟨hp.1.1.le, hp.2⟩
  · refine measure_mono_null
      (t := {p : EuclideanSpace ℝ (Fin 2) | inner ℝ p (EuclideanSpace.single 0 (1 : ℝ)) = 0})
      (fun p hp ↦ ?_) ?_
    · have hp0 : p 0 = 0 := by
        refine le_antisymm (le_of_not_gt fun hpos ↦ hp.2 ⟨⟨hpos, ?_⟩, hp.1.2⟩) hp.1.1
        linarith [hp.1.2.1, hp.1.2.2]
      simpa [EuclideanSpace.inner_single_right] using hp0
    · refine volume.addHaar_setOf_real_inner_eq (fun h ↦ ?_) 0
      have hone : (1 : ℝ) = 0 := by
        simpa [PiLp.single_apply] using congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0) h
      exact one_ne_zero hone

private def standardTriangleVertices : Set (EuclideanSpace ℝ (Fin 2)) :=
  {0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)}

private theorem convex_closedStandardTriangle : Convex ℝ closedStandardTriangle := by
  intro p hp q hq a b ha hb hab
  simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp hq ⊢
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith [hp.1, hq.1, hp.2.1, hq.2.1, hp.2.2, hq.2.2]

private theorem convexHull_standardTriangleVertices :
    convexHull ℝ standardTriangleVertices = closedStandardTriangle := by
  refine Set.Subset.antisymm (convexHull_min (fun p hp ↦ ?_) convex_closedStandardTriangle)
    (fun p hp ↦ ?_)
  · simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;>
      norm_num [closedStandardTriangle, PiLp.single_apply]
  · simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp
    refine mem_convexHull_of_exists_fintype ![1 - p 0 - p 1, p 0, p 1]
      ![0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [standardTriangleVertices]
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_succ]

private def triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := p 0 • u + p 1 • v
  map_add' p q := by
    ext i
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' c p := by
    ext i
    simp [mul_smul]

private theorem det_triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    LinearMap.det (triangleMap u v) = u 0 * v 1 - v 0 * u 1 := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, triangleMap,
    PiLp.basisFun_apply, Fin.isValue]
  norm_num

private theorem convexHull_triple_eq_image (u v : EuclideanSpace ℝ (Fin 2)) :
    convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) =
      triangleMap u v '' closedStandardTriangle := by
  have himage : triangleMap u v '' standardTriangleVertices =
      ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> simp [triangleMap]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp [standardTriangleVertices], by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 0 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 1 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
  rw [← himage, ← LinearMap.image_convexHull, convexHull_standardTriangleVertices]

/-- The triangle spanned by the origin and two vectors of the Euclidean plane has area one
half of the absolute determinant of their coordinates. -/
theorem volume_convexHull_zero_pair (u v : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|u 0 * v 1 - v 0 * u 1| / 2) := by
  rw [convexHull_triple_eq_image, Measure.addHaar_image_linearMap, det_triangleMap,
    volume_closedStandardTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- The area of a planar triangle is one half of the absolute coordinate determinant of its
two edge vectors. -/
theorem volume_convexHull_triple (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|(b - a) 0 * (c - a) 1 - (c - a) 0 * (b - a) 1| / 2) := by
  have hvertices : ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) =
      a +ᵥ ({0, b - a, c - a} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_vadd_set]
    constructor
    · intro hp
      rcases hp with hp | hp | hp
      · exact ⟨0, by simp, by simp [hp]⟩
      · refine ⟨b - a, by simp, ?_⟩
        rw [hp]
        change a + (b - a) = b
        abel
      · refine ⟨c - a, by simp, ?_⟩
        rw [hp]
        change a + (c - a) = c
        abel
    · rintro ⟨q, hq, hp⟩
      rcases hq with hq | hq | hq
      · subst hq
        simp only [vadd_eq_add, add_zero] at hp
        exact hp ▸ Or.inl rfl
      · refine Or.inr (Or.inl ?_)
        rw [← hp, hq]
        change a + (b - a) = b
        abel
      · refine Or.inr (Or.inr ?_)
        rw [← hp, hq]
        change a + (c - a) = c
        abel
  rw [hvertices, convexHull_vadd, measure_vadd, volume_convexHull_zero_pair]

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Stieltjes Density
-/

public section

open MeasureTheory Set

/-- Equality of interval increments identifies a continuous BV function's vector measure. -/
theorem BoundedVariationOn.vectorMeasure_eq_withDensity_of_integral_Icc
    {α E : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [CompactIccSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f r : α → E} {μ : Measure α} (hf : BoundedVariationOn f univ)
    (hcont : Continuous f) (hr : Integrable r μ)
    (hinc : ∀ a b, a ≤ b → f b - f a = ∫ x in Icc a b, r x ∂μ) :
    hf.vectorMeasure = μ.withDensityᵥ r := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, (hcont.continuousAt (x := b)).continuousWithinAt.rightLim_eq,
    (hcont.continuousAt (x := a)).continuousWithinAt.leftLim_eq,
    withDensityᵥ_apply hr measurableSet_Icc]
  exact hinc a b hab

/-- Integrating on a subtype and a measurable preimage agrees with restricting both sets. -/
theorem MeasureTheory.integral_subtype_preimage {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (f : α → E) :
    (∫ x in {x : s | (x : α) ∈ t}, f (x : α) ∂μ.comap Subtype.val) =
      ∫ x in t, f x ∂μ.restrict s := by
  have hpre : MeasurableSet {x : s | (x : α) ∈ t} := ht.preimage measurable_subtype_coe
  rw [← integral_indicator (μ := μ.comap (Subtype.val : s → α))
    (f := fun x : s ↦ f (x : α)) hpre]
  change (∫ x : s, (t.indicator f) (x : α) ∂μ.comap Subtype.val) = _
  rw [integral_subtype_comap hs, integral_indicator ht]

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Vector Measure / Interval
-/

public section

noncomputable section

open Set MeasureTheory

namespace MeasureTheory.VectorMeasure

/-- Agreement on half-open intervals and the whole space determines a vector measure. -/
theorem ext_of_Ioc {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] (μ ν : VectorMeasure α E)
    (h : ∀ a b, a < b → μ (Ioc a b) = ν (Ioc a b))
    (huniv : μ univ = ν univ) : μ = ν := by
  apply ext_of_generateFrom {s | ∃ a b, a < b ∧ Ioc a b = s} _
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc α))
    (isPiSystem_Ioc id id) huniv
  rintro s ⟨a, b, hab, rfl⟩
  exact h a b hab

end MeasureTheory.VectorMeasure

/-- Pulling an integrable density back along a measurable embedding gives its image integrals. -/
theorem MeasurableEmbedding.exists_vectorMeasure_image_integral
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure β) (g : β → E)
    (hg : Integrable g μ) :
    ∃ ν : VectorMeasure α E, ∀ s, MeasurableSet s → ν s = ∫ x in f '' s, g x ∂μ := by
  have hi : Integrable (fun x ↦ g (f x)) (μ.comap f) := by
    apply hf.integrable_map_iff.mp
    rw [hf.map_comap]
    exact hg.integrableOn
  refine ⟨(μ.comap f).withDensityᵥ (fun x ↦ g (f x)), ?_⟩
  intro s hs
  rw [withDensityᵥ_apply hi hs]
  have h := hf.setIntegral_map (μ := μ.comap f) g (f '' s)
  rw [hf.map_comap, hf.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  exact h.symm

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Vector Measure / With Density
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- Integrating a bounded function against a real signed density multiplies the ordinary
integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul_of_bounded
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {r q : X → ℝ}
    (hr : Integrable r μ) (hq : AEStronglyMeasurable q μ) (C : ℝ)
    (hq_bound : ∀ x, ‖q x‖ ≤ C) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hr]
  let μp := μ.withDensity fun x ↦ ENNReal.ofReal (r x)
  let μn := μ.withDensity fun x ↦ ENNReal.ofReal (-r x)
  let _ : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hr.2
  let _ : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hr.neg.2
  have hqp : (μp.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hqn : (μn.toSignedMeasure : SignedMeasure X).Integrable q := by
    rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound (hq.mono_ac (withDensity_absolutelyContinuous _ _)) C
      (ae_of_all _ hq_bound)
  have hmul : ContinuousLinearMap.mul ℝ ℝ =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext; simp
  change ∫ᵛ x, q x ∂[ContinuousLinearMap.mul ℝ ℝ;
      ((μp.toSignedMeasure : SignedMeasure X) - μn.toSignedMeasure).restrict E] = _
  rw [VectorMeasure.restrict_sub,
    VectorMeasure.integral_sub_vectorMeasure hqp.restrict hqn.restrict]
  have hp : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μp.toSignedMeasure]) =
      ∫ x in E, q x ∂μp := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hn : (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μn.toSignedMeasure]) =
      ∫ x in E, q x ∂μn := by
    rw [hmul]
    exact VectorMeasure.setIntegral_toSignedMeasure hE
  have hdp : ∫ x in E, q x ∂μp =
      ∫ x in E, (ENNReal.ofReal (r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  have hdn : ∫ x in E, q x ∂μn =
      ∫ x in E, (ENNReal.ofReal (-r x)).toReal • q x ∂μ := by
    apply setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    · exact hr.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
    · filter_upwards with x
      simp
    · exact hE
  rw [hp, hn, hdp, hdn]
  have hip : Integrable (fun x ↦ (ENNReal.ofReal (r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.pos_part.bdd_mul hq (ae_of_all _ hq_bound)
  have hin : Integrable (fun x ↦ (ENNReal.ofReal (-r x)).toReal • q x) μ := by
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm] using
      hr.neg_part.bdd_mul hq (ae_of_all _ hq_bound)
  rw [← MeasureTheory.integral_sub hip.integrableOn hin.integrableOn]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rcases le_total 0 (r x) with hx | hx
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    simp only [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

/-- Integrating a continuous real function on a compact space against a signed density
multiplies the ordinary integrand by that density. -/
theorem VectorMeasure.setIntegral_withDensity_mul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
    {μ : Measure X} {r q : X → ℝ}
    (hr : Integrable r μ) (hq : Continuous q) (E : Set X) (hE : MeasurableSet E) :
    (∫ᵛ x in E, q x ∂[ContinuousLinearMap.mul ℝ ℝ; μ.withDensityᵥ r]) =
      ∫ x in E, q x * r x ∂μ := by
  let q' : BoundedContinuousFunction X ℝ :=
    ContinuousMap.equivBoundedOfCompact X ℝ ⟨q, hq⟩
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hr hq.aestronglyMeasurable ‖q'‖
    (fun x ↦ BoundedContinuousFunction.norm_coe_le_norm q' x) E hE

end MeasureTheory

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Volume
-/

public section

open scoped Pointwise

namespace MeasureTheory

/-- The square root of planar volume scales linearly under nonnegative dilations. -/
theorem volume_smul_rpow_half (S : Set (EuclideanSpace ℝ (Fin 2))) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal a * volume S ^ (2 : ℝ)⁻¹ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) ha]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow ha]
  simpa using ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) (ENNReal.ofReal a)

end MeasureTheory

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Order.Infimum`.
* `ForMathlib.Order.IntervalPartition`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Order / Infimum
-/

public section

open Set

/-- Uniformly close real functions have uniformly close infima on a nonempty set. -/
theorem abs_sInf_image_sub_sInf_image_le {ι : Type*} {s : Set ι}
    (hs : s.Nonempty) (f g : ι → ℝ) (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s))
    {C : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ C) :
    |sInf (f '' s) - sInf (g '' s)| ≤ C := by
  have hfg : sInf (f '' s) - C ≤ sInf (g '' s) := by
    apply le_csInf (hs.image g)
    rintro _ ⟨x, hx, rfl⟩
    have hfx : sInf (f '' s) ≤ f x := csInf_le hf ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).2
    linarith
  have hgf : sInf (g '' s) - C ≤ sInf (f '' s) := by
    apply le_csInf (hs.image f)
    rintro _ ⟨x, hx, rfl⟩
    have hgx : sInf (g '' s) ≤ g x := csInf_le hg ⟨x, hx, rfl⟩
    have hpoint := (abs_le.mp (h x hx)).1
    linarith
  rw [abs_le]
  constructor <;> linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Order / Interval Partition
-/

public section

open Set

/-- Adjacent half-open intervals of a finite monotone sequence cover its endpoint interval. -/
theorem Monotone.iUnion_Ioc_fin {α : Type*} [LinearOrder α] {n : ℕ} (cuts : Fin (n + 1) → α)
    (hcuts : Monotone cuts) :
    (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Ioc (cuts 0) (cuts (Fin.last n)) := by
  rw [← hcuts.biUnion_Ico_Ioc_map_succ 0 (Fin.last n)]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i.castSucc, ⟨Fin.zero_le _, i.castSucc_lt_last⟩, ?_⟩
    simpa only [Fin.orderSucc_castSucc] using hi
  · rintro ⟨i, hi, hx⟩
    have hn : i.val < n := hi.2
    refine ⟨⟨i, hn⟩, ?_⟩
    change x ∈ Ioc (cuts (⟨i, hn⟩ : Fin n).castSucc)
      (cuts (Order.succ (⟨i, hn⟩ : Fin n).castSucc)) at hx
    simpa only [Fin.orderSucc_castSucc] using hx

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Topology.Angle`.
* `ForMathlib.Topology.Order.Compact`.
* `ForMathlib.Topology.Order.Concatenation`.
* `ForMathlib.Topology.Order.Interval`.
* `ForMathlib.Topology.Order.IntervalExtension`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Angle
-/

public section

open scoped unitInterval

namespace Real.Angle

/-- A continuous angle path starting at zero has a continuous real lift starting at zero. -/
theorem exists_continuous_lift_zero (θ : I → Real.Angle) (hθ : Continuous θ)
    (hzero : θ 0 = 0) :
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ ∀ t, (α t : Real.Angle) = θ t := by
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, hα0⟩ := hcov.exists_path_lifts
    (⟨θ, hθ⟩ : C(I, Real.Angle)) (0 : ℝ) (by simpa using hzero)
  exact ⟨α, α.continuous, hα0, fun t ↦ congrFun hα t⟩

end Real.Angle

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Compact
-/

public section

/-- A positive continuous function has a positive uniform lower bound on a nonempty compact set. -/
theorem IsCompact.exists_pos_forall_le {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ f x := by
  obtain ⟨x, hx, hxmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, hpos x hx, fun y hy ↦ hxmin hy⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Concatenation
-/

public section

namespace Function

/-- Concatenate two functions on `[0, 1]` on the interval `[0, 2]`. -/
@[expose]
noncomputable def concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (t : Set.Icc (0 : ℝ) 2) : E :=
  if (t : ℝ) ≤ 1 then x (Set.projIcc 0 1 (by norm_num) t)
  else y (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))

/-- Concatenation is continuous when the endpoint values agree. -/
theorem continuous_concatUnitIntervals {E : Type*} [TopologicalSpace E]
    {x y : Set.Icc (0 : ℝ) 1 → E} (hx : Continuous x) (hy : Continuous y)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Continuous (concatUnitIntervals x y) := by
  unfold concatUnitIntervals
  apply continuous_if_le continuous_subtype_val continuous_const
  · simpa only [Function.comp_def] using
      (hx.comp (continuous_projIcc.comp continuous_subtype_val)).continuousOn
  · simpa only [Function.comp_def, Pi.sub_apply] using
      (hy.comp
        (continuous_projIcc.comp (continuous_subtype_val.sub continuous_const))).continuousOn
  intro t ht
  simpa [ht] using hjoin

@[simp] theorem concatUnitIntervals_zero {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨0, by norm_num⟩ = x ⟨0, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_one {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨1, by norm_num⟩ = x ⟨1, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_two {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨2, by norm_num⟩ = y ⟨1, by norm_num⟩ := by
  norm_num [concatUnitIntervals]

/-- Joined paths have precisely the union of the two original ranges. -/
theorem range_concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Set.range (concatUnitIntervals x y) = Set.range x ∪ Set.range y := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    unfold concatUnitIntervals
    split_ifs
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · refine ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ?_⟩
      simp [concatUnitIntervals, t.property.2, Set.projIcc_of_mem (by norm_num) t.property]
    · by_cases ht : (t : ℝ) = 0
      · refine ⟨⟨1, by norm_num⟩, ?_⟩
        rw [concatUnitIntervals_one, hjoin]
        congr 1
        exact Subtype.ext ht.symm
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        refine ⟨⟨(t : ℝ) + 1, by constructor <;> linarith [t.property.1, t.property.2]⟩, ?_⟩
        have hnot : ¬(t : ℝ) + 1 ≤ 1 := by linarith
        simp [concatUnitIntervals, hnot, Set.projIcc_of_mem (by norm_num) t.property]

/-- A strict cyclic cut preserves injectivity away from the final endpoint. -/
theorem injOn_concatUnitIntervals_comp_of_cyclic_endpoints
    {E : Type*} {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → E}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b)
    (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    Set.InjOn (concatUnitIntervals (x ∘ φ) (x ∘ ψ)) {t | (t : ℝ) < 2} := by
  have hab' : a < b := has.trans hsb
  have hinj' : Set.InjOn x {t | a < (t : ℝ)} := by
    intro p hp q hq hpq
    by_cases hpb : (p : ℝ) < b
    · by_cases hqb : (q : ℝ) < b
      · exact hinj hpb hqb hpq
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        have hpa : p = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hpb hab'
          rw [hqeq] at hpq
          exact hpq.trans hclosed.symm
        exact False.elim ((ne_of_gt hp) (congrArg Subtype.val hpa))
    · have hpeq : p = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
        apply Subtype.ext
        exact le_antisymm p.property.2 (le_of_not_gt hpb)
      by_cases hqb : (q : ℝ) < b
      · have hqa : q = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hqb hab'
          rw [hpeq] at hpq
          exact hpq.symm.trans hclosed.symm
        exact False.elim ((ne_of_gt hq) (congrArg Subtype.val hqa))
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        exact hpeq.trans hqeq.symm
  intro u hu v hv huv
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hv0 : 0 ≤ (v : ℝ) := v.property.1
  have hu2 : (u : ℝ) < 2 := hu
  have hv2 : (v : ℝ) < 2 := hv
  by_cases hu1 : (u : ℝ) ≤ 1
  · let pu : Set.Icc (0 : ℝ) 1 := ⟨u, hu0, hu1⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (φ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) ⟨hu0, hu1⟩]
    have hφu : (s : ℝ) ≤ φ pu := by
      rw [← hφ₀]
      exact hφ.monotone pu.property.1
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : φ pu = φ pv := hinj' (has.trans_le hφu) (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      apply Subtype.ext
      simpa [pu, pv] using congrArg Subtype.val (hφ.injective hp)
    · have hv1' : 1 < (v : ℝ) := lt_of_not_ge hv1
      have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : φ pu = ψ pv := hinj' (has.trans_le hφu) hψvpos
        (hueval ▸ huv ▸ hveval)
      have hψvlt : (ψ pv : ℝ) < s := by
        have h := hψ (show pv < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (v : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψvlt) (hp ▸ hφu))
  · have hu1' : 1 < (u : ℝ) := lt_of_not_ge hu1
    have hup : 0 ≤ (u : ℝ) - 1 ∧ (u : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
    let pu : Set.Icc (0 : ℝ) 1 := ⟨(u : ℝ) - 1, hup⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (ψ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) hup]
    have hψupos : a < (ψ pu : ℝ) := by
      have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pu by
        change 0 < (u : ℝ) - 1
        linarith)
      rw [hψ₀] at h
      exact h
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : ψ pu = φ pv := hinj' hψupos (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      have hψult : (ψ pu : ℝ) < s := by
        have h := hψ (show pu < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (u : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψult) (hp ▸ hφv))
    · have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : ψ pu = ψ pv := hinj' hψupos hψvpos (hueval ▸ huv ▸ hveval)
      have hp' := congrArg Subtype.val (hψ.injective hp)
      apply Subtype.ext
      simp [pu, pv] at hp'
      linarith

end Function

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Interval
-/

public section

namespace Set

instance instCompactIccSpaceIcc (a b : ℝ) : CompactIccSpace (Icc a b) :=
  ⟨fun {_ _} ↦ isClosed_Icc.isCompact⟩

end Set

/-- Reverse a closed real interval about its midpoint. -/
@[expose]
def Set.Icc.reverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b → Set.Icc a b := fun t ↦
  ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩

/-- Interval reversal is continuous. -/
theorem Set.Icc.continuous_reverse {a b : ℝ} (hab : a ≤ b) :
    Continuous (Set.Icc.reverse hab) :=
  (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

/-- Interval reversal is antitone. -/
theorem Set.Icc.antitone_reverse {a b : ℝ} (hab : a ≤ b) :
    Antitone (Set.Icc.reverse hab) := by
  intro x y hxy
  have hxy' : (x : ℝ) ≤ y := hxy
  change a + b - (y : ℝ) ≤ a + b - (x : ℝ)
  linarith

/-- Reversing a closed interval twice is the identity. -/
theorem Set.Icc.involutive_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Involutive (Set.Icc.reverse hab) := by
  intro x
  apply Subtype.ext
  simp [Set.Icc.reverse]

/-- Interval reversal is surjective. -/
theorem Set.Icc.surjective_reverse {a b : ℝ} (hab : a ≤ b) :
    Function.Surjective (Set.Icc.reverse hab) :=
  (Set.Icc.involutive_reverse hab).surjective

open Set Filter
open scoped Topology

/-- Replace the terminal value of a one-sided continuous function by its left limit. -/
theorem continuousOn_replace_right_endpoint {E : Type*} [TopologicalSpace E]
    {a b : ℝ} (hab : a < b) (f : ℝ → E) (z : E)
    (hr : ∀ t ∈ Ico a b, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hl : ∀ t ∈ Ioo a b, Tendsto f (𝓝[<] t) (𝓝 (f t)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 z)) :
    ContinuousOn (fun t ↦ if t = b then z else f t) (Icc a b) := by
  let g : ℝ → E := fun t ↦ if t = b then z else f t
  have heql {t : ℝ} (ht : t ≤ b) : g =ᶠ[𝓝[<] t] f := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hne : u ≠ b := (lt_of_lt_of_le hu ht).ne
    simp [g, hne]
  have heqr {t : ℝ} (ht : t < b) : g =ᶠ[𝓝[>] t] f := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with u hu
    simp [g, (show u ≠ b from hu.ne)]
  intro t ht
  change ContinuousWithinAt g (Icc a b) t
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have h : ContinuousWithinAt g (Ioi a) a := by
      change Tendsto g _ _
      simpa only [g, ite_eq_right hab.ne] using (hr a ⟨le_rfl, hab⟩).congr' (heqr hab).symm
    exact (continuousWithinAt_Ioi_iff_Ici.mp h).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply ContinuousAt.continuousWithinAt
      apply continuousAt_iff_continuous_left'_right'.mpr
      constructor
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hl t ⟨hat, htb⟩).congr' (heql htb.le).symm
      · change Tendsto g _ _
        simpa only [g, ite_eq_right htb.ne] using (hr t ⟨hat.le, htb⟩).congr' (heqr htb).symm
    · have h : ContinuousWithinAt g (Iio t) t := by
        change Tendsto g _ _
        simpa only [g, ite_eq_left rfl] using hb.congr' (heql le_rfl).symm
      exact (continuousWithinAt_Iio_iff_Iic.mp h).mono Icc_subset_Iic_self

/-- Every compact real interval carries finite monotone partitions, with prescribed
endpoints, whose mesh eventually falls below any positive threshold. -/
theorem Set.Icc.exists_partitions_mesh_tendsto_zero {a b : ℝ} (hab : a ≤ b) :
    ∃ cuts : ∀ k : ℕ, Fin (k + 2) → Set.Icc a b,
      (∀ k, Monotone (cuts k)) ∧ (∀ k, (cuts k 0 : ℝ) = a) ∧
      (∀ k, (cuts k (Fin.last (k + 1)) : ℝ) = b) ∧
      ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (k + 1),
        (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ := by
  let cuts (k : ℕ) (i : Fin (k + 2)) : Set.Icc a b :=
    ⟨a + (b - a) * (i : ℝ) / (k + 1), by
      have hk : (0 : ℝ) < k + 1 := by positivity
      have hi : (i : ℝ) ≤ k + 1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      constructor
      · exact le_add_of_nonneg_right (div_nonneg
          (mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)) hk.le)
      · have hmul := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab)
        have hdiv : (b - a) * (i : ℝ) / (k + 1) ≤ b - a :=
          (div_le_iff₀ hk).mpr hmul
        linarith⟩
  refine ⟨cuts, ?_, ?_, ?_, ?_⟩
  · intro k i j hij
    change a + (b - a) * (i : ℝ) / (k + 1) ≤ a + (b - a) * (j : ℝ) / (k + 1)
    gcongr
    exact_mod_cast hij
  · intro k
    simp [cuts]
  · intro k
    dsimp [cuts]
    push_cast
    rw [mul_div_cancel_right₀ _ (by positivity)]
    ring
  · intro δ hδ
    have ht : Filter.Tendsto (fun k : ℕ ↦ (b - a) / (k + 1))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
    intro i
    convert hk using 1
    dsimp [cuts]
    push_cast
    ring

/-- The increasing affine surjection between two nondegenerate closed intervals. -/
theorem Set.Icc.exists_affine_monotone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = c + ((t : ℝ) - a) / (b - a) * (d - c) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hdc : (0 : ℝ) < d - c := by linarith
  have hfrac : ∀ t : Set.Icc a b,
      0 ≤ ((t : ℝ) - a) / (b - a) ∧ ((t : ℝ) - a) / (b - a) ≤ 1 := by
    intro t
    refine ⟨div_nonneg (by linarith [t.property.1]) hba.le, ?_⟩
    rw [div_le_one hba]
    linarith [t.property.2]
  refine ⟨fun t ↦ ⟨c + ((t : ℝ) - a) / (b - a) * (d - c), ?_, ?_⟩, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · nlinarith [(hfrac t).1]
  · nlinarith [(hfrac t).2]
  · exact Continuous.subtype_mk (by fun_prop) _
  · intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hdiv : ((s : ℝ) - a) / (b - a) ≤ ((t : ℝ) - a) / (b - a) := by gcongr
    change c + ((s : ℝ) - a) / (b - a) * (d - c) ≤ c + ((t : ℝ) - a) / (b - a) * (d - c)
    nlinarith
  · intro y
    have hyl : 0 ≤ ((y : ℝ) - c) / (d - c) := div_nonneg (by linarith [y.property.1]) hdc.le
    have hyr : ((y : ℝ) - c) / (d - c) ≤ 1 := by
      rw [div_le_one hdc]
      linarith [y.property.2]
    refine ⟨⟨a + ((y : ℝ) - c) / (d - c) * (b - a), by nlinarith, by nlinarith⟩, ?_⟩
    apply Subtype.ext
    change c + (a + ((y : ℝ) - c) / (d - c) * (b - a) - a) / (b - a) * (d - c) = (y : ℝ)
    field_simp
    ring

/-- The decreasing affine surjection between two nondegenerate closed intervals: the increasing
one reflected in the midpoint of its codomain. -/
theorem Set.Icc.exists_affine_antitone_surjection {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ φ : Set.Icc a b → Set.Icc c d, Continuous φ ∧ Antitone φ ∧ Function.Surjective φ ∧
      ∀ t : Set.Icc a b, (φ t : ℝ) = d - ((t : ℝ) - a) / (b - a) * (d - c) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ := Set.Icc.exists_affine_monotone_surjection hab hcd
  refine ⟨fun t ↦ ⟨c + d - (φ t : ℝ), ?_, ?_⟩, ?_, ?_, ?_, fun t ↦ ?_⟩
  · linarith [(φ t).property.2]
  · linarith [(φ t).property.1]
  · exact (continuous_const.sub (continuous_subtype_val.comp hφc)).subtype_mk _
  · intro s t hst
    exact Subtype.mk_le_mk.mpr (by linarith [show (φ s : ℝ) ≤ (φ t : ℝ) from hφm hst])
  · intro y
    have hy : c + d - (y : ℝ) ∈ Set.Icc c d :=
      ⟨by linarith [y.property.2], by linarith [y.property.1]⟩
    obtain ⟨t, ht⟩ := hφs ⟨c + d - (y : ℝ), hy⟩
    refine ⟨t, Subtype.ext ?_⟩
    change c + d - (φ t : ℝ) = (y : ℝ)
    rw [show (φ t : ℝ) = c + d - (y : ℝ) from congrArg Subtype.val ht]
    ring
  · change c + d - (φ t : ℝ) = _
    rw [hφv t]
    ring

/-- The translation of the unit interval onto a closed interval of length one. -/
theorem Set.Icc.exists_translation_surjection {c d : ℝ} (hcd : d = c + 1) :
    ∃ φ : Set.Icc (0 : ℝ) 1 → Set.Icc c d, Continuous φ ∧ Monotone φ ∧
      Function.Surjective φ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (φ u : ℝ) = c + (u : ℝ) := by
  obtain ⟨φ, hφc, hφm, hφs, hφv⟩ :=
    Set.Icc.exists_affine_monotone_surjection zero_lt_one (show c < d by rw [hcd]; linarith)
  exact ⟨φ, hφc, hφm, hφs, fun u ↦ by rw [hφv u, hcd]; ring⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Topology / Order / Interval Extension
-/

public section

noncomputable section
namespace OrderIso

/-- Extend an order isomorphism of open real intervals by matching the endpoints. -/
def extendIoo {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Icc a b) : Set.Icc c d :=
  if hxa : (x : ℝ) = a then ⟨c, le_rfl, hcd.le⟩
  else if hxb : (x : ℝ) = b then ⟨d, hcd.le, le_rfl⟩
  else let t := e ⟨x, lt_of_le_of_ne x.property.1 (Ne.symm hxa),
      lt_of_le_of_ne x.property.2 hxb⟩
    ⟨t, t.property.1.le, t.property.2.le⟩

/-- The extension maps the left endpoint to the left endpoint. -/
theorem extendIoo_left {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨a, le_rfl, hab.le⟩ = ⟨c, le_rfl, hcd.le⟩ := by
  simp [extendIoo]

/-- The extension maps the right endpoint to the right endpoint. -/
theorem extendIoo_right {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨b, hab.le, le_rfl⟩ = ⟨d, hcd.le, le_rfl⟩ := by
  simp [extendIoo, ne_of_gt hab]

/-- The extension agrees with the original order isomorphism on the interior. -/
theorem extendIoo_interior {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Ioo a b) :
    (extendIoo hcd e ⟨x, x.property.1.le, x.property.2.le⟩ : ℝ) = e x := by
  simp [extendIoo, ne_of_gt x.property.1, ne_of_lt x.property.2]

/-- The endpoint extension is monotone. -/
theorem monotone_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Monotone (extendIoo hcd e) := by
  intro x y hxy
  by_cases hx : (x : ℝ) = a
  · have he : x = ⟨a, le_rfl, hab.le⟩ := Subtype.ext hx
    rw [he, extendIoo_left hab]
    exact (extendIoo hcd e y).property.1
  by_cases hy : (y : ℝ) = b
  · have he : y = ⟨b, hab.le, le_rfl⟩ := Subtype.ext hy
    rw [he, extendIoo_right hab]
    exact (extendIoo hcd e x).property.2
  have hxlo : a < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
  have hyhi : (y : ℝ) < b := lt_of_le_of_ne y.property.2 hy
  have hxhi : (x : ℝ) < b := lt_of_le_of_lt hxy hyhi
  have hylo : a < (y : ℝ) := lt_of_lt_of_le hxlo hxy
  change (extendIoo hcd e x : ℝ) ≤ extendIoo hcd e y
  rw [extendIoo_interior hcd e ⟨x, hxlo, hxhi⟩,
    extendIoo_interior hcd e ⟨y, hylo, hyhi⟩]
  exact e.monotone hxy

/-- The endpoint extension is surjective. -/
theorem surjective_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Function.Surjective (extendIoo hcd e) := by
  intro y
  by_cases hyc : (y : ℝ) = c
  · refine ⟨⟨a, le_rfl, hab.le⟩, ?_⟩
    rw [extendIoo_left hab]
    exact Subtype.ext hyc.symm
  by_cases hyd : (y : ℝ) = d
  · refine ⟨⟨b, hab.le, le_rfl⟩, ?_⟩
    rw [extendIoo_right hab]
    exact Subtype.ext hyd.symm
  let y' : Set.Ioo c d := ⟨y, lt_of_le_of_ne y.property.1 (Ne.symm hyc),
    lt_of_le_of_ne y.property.2 hyd⟩
  let x := e.symm y'
  refine ⟨⟨x, x.property.1.le, x.property.2.le⟩, Subtype.ext ?_⟩
  rw [extendIoo_interior]
  exact congrArg Subtype.val (e.apply_symm_apply y')

/-- The endpoint extension is continuous. -/
theorem continuous_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Continuous (extendIoo hcd e) :=
  (monotone_extendIoo hab hcd e).continuous_of_surjective (surjective_extendIoo hab hcd e)

end OrderIso

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.MeasureTheory.StieltjesTransport`.
* `ForMathlib.MeasureTheory.VectorMeasure.LocallyConstant`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Stieltjes Transport
-/

public section

noncomputable section

open MeasureTheory Set

/-- A monotone surjection of compact intervals preserves bounded variation. -/
theorem BoundedVariationOn.comp_monotone_surjective_Icc
    {a b c d : ℝ} (_hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    {φ : Set.Icc c d → Set.Icc a b} (hφ : Monotone φ) (hφs : Function.Surjective φ) :
    BoundedVariationOn (f ∘ φ) Set.univ := by
  let _ : Fact (a ≤ b) := ⟨_hab⟩
  rw [BoundedVariationOn,
    eVariationOn.comp_eq_of_monotoneOn (t := Set.univ) f φ
      (fun _ _ _ _ hxy ↦ hφ hxy)]
  rw [Set.image_univ, hφs.range_eq]
  exact hf

/-- The Stieltjes measure is preserved by continuous monotone surjective reparametrization. -/
theorem BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) {φ : Set.Icc c d → Set.Icc a b} (hφc : Continuous φ)
    (hφ : Monotone φ) (hφs : Function.Surjective φ) :
    (BoundedVariationOn.comp_monotone_surjective_Icc hab hf hφ hφs).vectorMeasure.map φ =
      hf.vectorMeasure := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let _ : Fact (c ≤ d) := ⟨hcd⟩
  let hfφ := BoundedVariationOn.comp_monotone_surjective_Icc hab hf hφ hφs
  have fiberGreatest (y : Set.Icc a b) :
      ∃ x, IsGreatest (φ ⁻¹' {y}) x := by
    apply (isClosed_singleton.preimage hφc).isCompact.exists_isGreatest
    rcases hφs y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have preimage_Ioc (u v : Set.Icc a b) :
      ∃ x y, φ x = u ∧ φ y = v ∧ (u ≤ v → x ≤ y) ∧
        φ ⁻¹' Ioc u v = Ioc x y := by
    obtain ⟨x, hxmem, hxmax⟩ := fiberGreatest u
    obtain ⟨y, hymem, hymax⟩ := fiberGreatest v
    change φ x = u at hxmem
    change φ y = v at hymem
    have hxy : u ≤ v → x ≤ y := by
      intro huv
      by_contra hxy
      have hyx : y ≤ x := le_of_not_ge hxy
      have huv' : u = v := le_antisymm huv (hxmem ▸ hymem ▸ hφ hyx)
      exact hxy (hymax (by change φ x = v; rw [hxmem, huv']))
    refine ⟨x, y, hxmem, hymem, hxy, Set.ext fun z ↦ ?_⟩
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro hz
    · constructor
      · by_contra hzx
        have hzx' : z ≤ x := le_of_not_gt hzx
        exact (not_le_of_gt hz.1) (hxmem ▸ hφ hzx')
      · by_contra hyz
        have hyz' : y < z := lt_of_not_ge hyz
        have hvz : v ≤ φ z := hymem ▸ hφ hyz'.le
        have : φ z = v := le_antisymm hz.2 hvz
        exact (not_le_of_gt hyz') (hymax this)
    · constructor
      · have hux : u ≤ φ z := hxmem ▸ hφ hz.1.le
        exact hux.lt_of_ne fun hzu ↦ (not_le_of_gt hz.1) (hxmax hzu.symm)
      · exact hymem ▸ hφ hz.2
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hright_comp (x : Set.Icc c d) : (f ∘ φ).rightLim x = (f ∘ φ) x :=
    (hfc.comp hφc).continuousAt.continuousWithinAt.rightLim_eq
  have hinterval (u v : Set.Icc a b) (huv : u ≤ v) :
      (hfφ.vectorMeasure.map φ) (Ioc u v) = hf.vectorMeasure (Ioc u v) := by
    obtain ⟨x, y, hx, hy, hxy, hpre⟩ := preimage_Ioc u v
    rw [VectorMeasure.map_apply _ hφc.measurable measurableSet_Ioc, hpre,
      hfφ.vectorMeasure_Ioc (hxy huv), hf.vectorMeasure_Ioc huv, hright_comp, hright_comp,
      hright, hright, Function.comp_apply, Function.comp_apply, hx, hy]
  apply VectorMeasure.ext_of_generateFrom
      {s | ∃ u v : Set.Icc a b, u ≤ v ∧ s = Ioc u v}
  · rintro s ⟨u, v, huv, rfl⟩
    exact hinterval u v huv
  · exact BorelSpace.measurable_eq.trans <| by
      rw [borel_eq_generateFrom_Ioc_le]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
  · exact IsSetSemiring.isPiSystem IsSetSemiring.Ioc
  · have hφtop : φ ⊤ = ⊤ := by
      obtain ⟨x, hx⟩ := hφs ⊤
      exact top_unique (hx ▸ hφ le_top)
    have hφbot : φ ⊥ = ⊥ := by
      obtain ⟨x, hx⟩ := hφs ⊥
      exact bot_unique (hx ▸ hφ bot_le)
    have htopφ : Filter.atTop.limUnder (f ∘ φ) = (f ∘ φ) ⊤ := by
      apply tendsto_nhds_unique hfφ.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbotφ : Filter.atBot.limUnder (f ∘ φ) = (f ∘ φ) ⊥ := by
      apply tendsto_nhds_unique hfφ.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    have htop : Filter.atTop.limUnder f = f ⊤ := by
      apply tendsto_nhds_unique hf.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbot : Filter.atBot.limUnder f = f ⊥ := by
      apply tendsto_nhds_unique hf.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    rw [VectorMeasure.map_apply _ hφc.measurable MeasurableSet.univ, preimage_univ,
      hfφ.vectorMeasure_univ, hf.vectorMeasure_univ, htopφ, hbotφ, htop, hbot,
      Function.comp_apply, Function.comp_apply, hφtop, hφbot]

/-- The Stieltjes measure of a continuous BV function has no point masses. -/
theorem BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous
    {a b : ℝ} {f : Set.Icc a b → ℝ} (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) (x : Set.Icc a b) : hf.vectorMeasure {x} = 0 := by
  rw [hf.vectorMeasure_singleton,
    hfc.continuousAt.continuousWithinAt.rightLim_eq,
    hfc.continuousAt.continuousWithinAt.leftLim_eq, sub_self]

/-- The Stieltjes measure on a closed subinterval pushes forward to the half-open restriction. -/
theorem BoundedVariationOn.vectorMeasure_map_Icc_inclusion
    {a b : ℝ} {f : Set.Icc a b → ℝ} (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) (l u : Set.Icc a b) (hlu : l ≤ u) :
    let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hfr : BoundedVariationOn (f ∘ ι) Set.univ :=
      ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    hfr.vectorMeasure.map ι = hf.vectorMeasure.restrict (Ioc l u) := by
  dsimp only
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
    ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
  let hfr : BoundedVariationOn (f ∘ ι) Set.univ :=
    ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f ι
      (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
  let _ : Fact ((l : ℝ) ≤ u) := ⟨hlu⟩
  change hfr.vectorMeasure.map ι = hf.vectorMeasure.restrict (Ioc l u)
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hright_comp (x : Set.Icc (l : ℝ) u) : (f ∘ ι).rightLim x = (f ∘ ι) x :=
    (hfc.comp hι).continuousAt.continuousWithinAt.rightLim_eq
  have htop : Filter.atTop.limUnder (f ∘ ι) = (f ∘ ι) ⊤ := by
    apply tendsto_nhds_unique hfr.tendsto_atTop_limUnder
    rw [Filter.atTop_eq_pure_of_isTop isTop_top]
    exact tendsto_pure_nhds _ _
  have hbot : Filter.atBot.limUnder (f ∘ ι) = (f ∘ ι) ⊥ := by
    apply tendsto_nhds_unique hfr.tendsto_atBot_limUnder
    rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
    exact tendsto_pure_nhds _ _
  apply VectorMeasure.ext_of_generateFrom (Set.range Iic)
  · rintro s ⟨x, rfl⟩
    rw [VectorMeasure.map_apply _ hι.measurable measurableSet_Iic,
      VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic]
    by_cases hxl : x < l
    · have hp : ι ⁻¹' Iic x = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact (not_le_of_gt hxl) (le_trans y.property.1 hy)
      have hi : Iic x ∩ Ioc l u = ∅ := by ext y; simp; grind
      simp [hp, hi]
    · by_cases hxu : u ≤ x
      · have hp : ι ⁻¹' Iic x = Set.univ := by
          apply eq_univ_of_forall
          intro y
          exact le_trans y.property.2 hxu
        have hi : Iic x ∩ Ioc l u = Ioc l u := by ext y; simp; grind
        rw [hp, hi, hfr.vectorMeasure_univ, hf.vectorMeasure_Ioc hlu]
        rw [htop, hbot, hright, hright]
        rfl
      · have hlx : l ≤ x := le_of_not_gt hxl
        have hxu' : x ≤ u := le_of_not_ge hxu
        let y : Set.Icc (l : ℝ) u := ⟨x, hlx, hxu'⟩
        have hp : ι ⁻¹' Iic x = Iic y := by ext z; rfl
        have hi : Iic x ∩ Ioc l u = Ioc l x := by ext z; simp; grind
        rw [hp, hi, hfr.vectorMeasure_Iic, hf.vectorMeasure_Ioc hlx,
          hright_comp, hbot, hright, hright]
        rfl
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic _)
  · exact isPiSystem_Iic
  · rw [VectorMeasure.map_apply _ hι.measurable MeasurableSet.univ,
      preimage_univ, VectorMeasure.restrict_apply_univ,
      hfr.vectorMeasure_univ, hf.vectorMeasure_Ioc hlu, htop, hbot, hright, hright]
    rfl

/-- An antitone surjection of compact intervals preserves bounded variation. -/
theorem BoundedVariationOn.comp_antitone_surjective_Icc
    {a b c d : ℝ} (_hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    {φ : Set.Icc c d → Set.Icc a b} (hφ : Antitone φ)
    (hφs : Function.Surjective φ) :
    BoundedVariationOn (f ∘ φ) Set.univ := by
  let _ : Fact (a ≤ b) := ⟨_hab⟩
  rw [BoundedVariationOn,
    eVariationOn.comp_eq_of_antitoneOn (t := Set.univ) f φ
      (fun _ _ _ _ hxy ↦ hφ hxy)]
  rw [Set.image_univ, hφs.range_eq]
  exact hf

/-- Reversing a continuous BV function negates its transported Stieltjes measure. -/
theorem BoundedVariationOn.vectorMeasure_map_reverse_Icc
    {a b : ℝ} (hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ) (hfc : Continuous f) :
    let r := Set.Icc.reverse hab
    let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab hf
      (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
    hfr.vectorMeasure.map r = -hf.vectorMeasure := by
  dsimp only
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let r := Set.Icc.reverse hab
  let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab hf
    (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
  have hr : Continuous r := Set.Icc.continuous_reverse hab
  have hleft (x : Set.Icc a b) : f.leftLim x = f x :=
    hfc.continuousAt.continuousWithinAt.leftLim_eq
  have hleft_comp (x : Set.Icc a b) : (f ∘ r).leftLim x = (f ∘ r) x :=
    (hfc.comp hr).continuousAt.continuousWithinAt.leftLim_eq
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hpre (u v : Set.Icc a b) :
      r ⁻¹' Ioc u v = Ico (r v) (r u) := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    change (u : ℝ) < a + b - x ∧ a + b - x ≤ v ↔
      a + b - v ≤ x ∧ x < a + b - u
    constructor <;> intro hx <;> constructor <;> linarith
  have hinterval (u v : Set.Icc a b) (huv : u ≤ v) :
      (hfr.vectorMeasure.map r) (Ioc u v) = (-hf.vectorMeasure) (Ioc u v) := by
    rw [MeasureTheory.VectorMeasure.map_apply _ hr.measurable measurableSet_Ioc, hpre,
      hfr.vectorMeasure_Ico ((Set.Icc.antitone_reverse hab) huv)]
    change _ = -(hf.vectorMeasure (Ioc u v))
    rw [hf.vectorMeasure_Ioc huv, hleft_comp, hleft_comp, hright, hright]
    simp [r, Set.Icc.reverse, Function.comp_apply]
  apply MeasureTheory.VectorMeasure.ext_of_generateFrom
      {s | ∃ u v : Set.Icc a b, u ≤ v ∧ s = Ioc u v}
  · rintro s ⟨u, v, huv, rfl⟩
    exact hinterval u v huv
  · exact BorelSpace.measurable_eq.trans <| by
      rw [borel_eq_generateFrom_Ioc_le]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
  · exact IsSetSemiring.isPiSystem IsSetSemiring.Ioc
  · rw [MeasureTheory.VectorMeasure.map_apply _ hr.measurable MeasurableSet.univ,
      preimage_univ, hfr.vectorMeasure_univ]
    change _ = -(hf.vectorMeasure Set.univ)
    rw [hf.vectorMeasure_univ]
    have htop : Filter.atTop.limUnder (f ∘ r) = f ⊥ := by
      apply tendsto_nhds_unique hfr.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      convert tendsto_pure_nhds (f ∘ r) ⊤ using 1
      apply congrArg nhds
      apply congrArg f
      apply Subtype.ext
      change a = a + b - b
      ring
    have hbot : Filter.atBot.limUnder (f ∘ r) = f ⊤ := by
      apply tendsto_nhds_unique hfr.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      convert tendsto_pure_nhds (f ∘ r) ⊥ using 1
      apply congrArg nhds
      apply congrArg f
      apply Subtype.ext
      change b = a + b - a
      ring
    have htopf : Filter.atTop.limUnder f = f ⊤ := by
      apply tendsto_nhds_unique hf.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbotf : Filter.atBot.limUnder f = f ⊥ := by
      apply tendsto_nhds_unique hf.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    rw [htop, hbot, htopf, hbotf]
    simp

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Measure Theory / Vector Measure / Locally Constant
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Local constancy away from the initial endpoint gives a variation-null neighborhood. -/
theorem BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    {a b : ℝ} (hab : a < b) {g : Set.Icc a b → ℝ}
    (hg : BoundedVariationOn g Set.univ)
    (hr : ∀ y, ContinuousWithinAt g (Set.Ici y) y) (x : Set.Icc a b)
    (hxbot : a < (x : ℝ))
    (hx : g =ᶠ[𝓝 x] fun _ ↦ g x) :
    ∃ U ∈ 𝓝 x, hg.vectorMeasure.variation U = 0 := by
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hright (y : Set.Icc a b) : Function.rightLim g y = g y :=
    (hr y).rightLim_eq
  by_cases hxtop : x = ⊤
  · subst x
    obtain ⟨c, hc, hsub⟩ := (nhds_top_basis.mem_iff.mp hx)
    refine ⟨Set.Ioi c, nhds_top_basis.mem_iff.mpr ⟨c, hc, subset_rfl⟩, ?_⟩
    rw [hg.variation_vectorMeasure_Ioi]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm
  · have hxlt : x < ⊤ := lt_top_iff_ne_top.mpr hxtop
    have hxgt : ⊥ < x := hxbot
    obtain ⟨c, d, hxcd, hsub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨⊥, hxgt⟩ ⟨⊤, hxlt⟩).mp hx
    refine ⟨Set.Ioo c d, Ioo_mem_nhds hxcd.1 hxcd.2, ?_⟩
    rw [hg.variation_vectorMeasure_Ioo_right]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Foundations.Development001`.
* `Cap.Foundations.Development001`.
* `Polygon.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Plane`.
* `Geometry.Basic`.
* `Geometry.Frame`.
* `Geometry.NormalLines`.
* `Geometry.QuadrantBounds`.
* `Geometry.Subgraph`.
* `Geometry.Support`.
* `Geometry.Contacts`.
* `Geometry.FrameCalculus`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Plane
-/

public section

namespace MovingSofa

/-- The two-dimensional real Euclidean space used for sofa geometry. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The squared norm of a planar point in coordinates. -/
theorem Point.norm_sq_eq (z : Point) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Cauchy-Schwarz for the coordinate form of the planar inner product. -/
theorem Point.abs_inner_coords_le (w d : Point) :
    |w 0 * d 0 + w 1 * d 1| ≤ ‖w‖ * ‖d‖ := by
  have hinner : (inner ℝ w d : ℝ) = w 0 * d 0 + w 1 * d 1 := by
    simp [inner, Fin.sum_univ_two]
    ring
  rw [← hinner]
  exact abs_real_inner_le_norm w d

/-- Each coordinate of a planar point is bounded by its norm. -/
theorem Point.abs_apply_le_norm (z : Point) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa [PiLp.norm_single, EuclideanSpace.inner_single_right] using
    abs_real_inner_le_norm z (EuclideanSpace.single i (1 : ℝ))

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Basic
-/

public section

noncomputable section

namespace MovingSofa

/-- The normal and positively oriented tangent at an angular direction. -/
@[expose]
def frame (t : Real.Angle) : Point × Point :=
  (!₂[t.cos, t.sin], !₂[-t.sin, t.cos])

/-- The unit normal of the angular frame. -/
abbrev normalVector (t : Real.Angle) : Point := (frame t).1

/-- The counterclockwise unit tangent of the angular frame. -/
abbrev tangentVector (t : Real.Angle) : Point := (frame t).2

/-- The support value; geometric results require a nonempty compact set. -/
@[expose]
def supportValue (s : Set Point) (t : Real.Angle) : ℝ :=
  sSup ((fun p ↦ inner ℝ p (normalVector t)) '' s)

/-- The line with the given unit normal and signed offset. -/
@[expose]
def normalLine (t : Real.Angle) (h : ℝ) : Set Point :=
  {p | inner ℝ p (normalVector t) = h}

/-- A normal half-plane: `upper` chooses the greater side, `strict` its open version. -/
@[expose]
def normalHalfPlane (t : Real.Angle) (h : ℝ) (upper strict : Bool) : Set Point :=
  {p | if upper then
    if strict then h < inner ℝ p (normalVector t) else h ≤ inner ℝ p (normalVector t)
  else
    if strict then inner ℝ p (normalVector t) < h else inner ℝ p (normalVector t) ≤ h}

/-- Closed normal half-planes are closed, on either side of the boundary line. -/
theorem isClosed_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    IsClosed (normalHalfPlane t h upper false) := by
  cases upper
  · exact isClosed_le (continuous_id.inner continuous_const) continuous_const
  · exact isClosed_le continuous_const (continuous_id.inner continuous_const)

/-- Closed normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper false) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_le hlin h
  · exact convex_halfSpace_ge hlin h

/-- Open normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane_open (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper true) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_lt hlin h
  · exact convex_halfSpace_gt hlin h

/-- The supporting line and closed containing half-plane of a nonempty compact set. -/
@[expose]
def supportingLineHalfPlane (s : Set Point) (t : Real.Angle) : Set Point × Set Point :=
  (normalLine t (supportValue s t), normalHalfPlane t (supportValue s t) false false)

/-- A closed supporting half-plane, read through the opposite normal direction. -/
theorem supportingLineHalfPlane_snd_eq_normalHalfPlane {s : Set Point} {t u : Real.Angle}
    {h : ℝ} (hn : normalVector u = -normalVector t) (hs : supportValue s u = -h) :
    (supportingLineHalfPlane s u).2 = normalHalfPlane t h true false := by
  ext q
  change inner ℝ q (normalVector u) ≤ supportValue s u ↔ h ≤ inner ℝ q (normalVector t)
  rw [hn, inner_neg_right, hs]
  constructor <;> intro hq <;> linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Frame
-/

public section

noncomputable section

namespace MovingSofa

/-- Every unit vector is the normal vector of an angular frame. -/
theorem exists_angle_normalVector_eq {u : Point} (hu : ‖u‖ = 1) :
    ∃ t : Real.Angle, normalVector t = u := by
  let z : ℂ := ⟨u 0, u 1⟩
  have hzNorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, show Complex.normSq z = ‖u‖ ^ 2 by
      rw [EuclideanSpace.norm_sq_eq]
      simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
    simp [hu]
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at hzNorm
  refine ⟨(z.arg : ℝ), ?_⟩
  ext i
  fin_cases i
  · simpa [normalVector, frame, z, hzNorm] using Complex.cos_arg hz
  · simpa [normalVector, frame, z, hzNorm] using Complex.sin_arg z

theorem continuous_normalVector_real :
    Continuous (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  let c : ℝ → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases (Real.cos t) (fun _ ↦ Real.sin t) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos
    · exact Real.continuous_sin
  have heq : (fun t : ℝ ↦ normalVector (t : Real.Angle)) =
      (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

/-- Opposite real angles give opposite normal vectors. -/
theorem normalVector_add_pi (t : ℝ) :
    normalVector ((t + Real.pi : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- Opposite real angles give opposite tangent vectors. -/
theorem tangentVector_add_pi (t : ℝ) :
    tangentVector ((t + Real.pi : ℝ) : Real.Angle) = -tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- The projection onto the normal direction of a real angle, in coordinates. -/
theorem inner_normalVector_real (p : Point) (t : ℝ) :
    inner ℝ p (normalVector (t : Real.Angle)) = p 0 * Real.cos t + p 1 * Real.sin t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The projection onto the tangent direction of a real angle, in coordinates. -/
theorem inner_tangentVector_real (p : Point) (t : ℝ) :
    inner ℝ p (tangentVector (t : Real.Angle)) = -(p 0 * Real.sin t) + p 1 * Real.cos t := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The inner product of two unit normals is the cosine of their angle difference. -/
theorem inner_normalVector_normalVector (s t : ℝ) :
    inner ℝ (normalVector (s : Real.Angle)) (normalVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- A normal vector has squared length one. -/
theorem inner_normalVector_self (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
  rw [inner_normalVector_normalVector]
  simp

/-- A normal vector at an angle has squared length one. -/
theorem inner_normalVector_self_angle (t : Real.Angle) :
    inner ℝ (normalVector t) (normalVector t) = 1 := by
  induction t using Real.Angle.induction_on with
  | _ r => exact inner_normalVector_self r

/-- A normal vector at a real angle has length one. -/
theorem norm_normalVector_real (t : ℝ) : ‖normalVector (t : Real.Angle)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [normalVector, frame, Fin.sum_univ_two]

theorem inner_normalVector_smul_add_inner_tangentVector_smul (p : Point) (t : Real.Angle) :
    inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t = p := by
  ext i
  fin_cases i <;>
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun r : ℝ ↦ r * p 0) t.cos_sq_add_sin_sq,
      congrArg (fun r : ℝ ↦ r * p 1) t.cos_sq_add_sin_sq]

theorem normalVector_add_real (t δ : ℝ) :
    normalVector ((t + δ : ℝ) : Real.Angle) =
      Real.cos δ • normalVector (t : Real.Angle) +
      Real.sin δ • tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame, -Real.Angle.coe_add, Real.cos_add,
    Real.sin_add] <;> ring

theorem inner_normalVector_tangentVector (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
  simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem inner_tangentVector_self (t : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
  rw [PiLp.inner_apply]
  simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]

theorem tangentVector_add_pi_div_two (t : ℝ) :
    tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

/-- Adding pi to an angle reverses its normal vector. -/
theorem normalVector_add_pi_angle (a : Real.Angle) :
    normalVector (a + ((Real.pi : ℝ) : Real.Angle)) = -normalVector a := by
  induction a using Real.Angle.induction_on with
  | _ a => simpa only [Real.Angle.coe_add] using normalVector_add_pi a

/-- The sine convolution kernel is the negative normal projection of the moving tangent. -/
theorem sin_sub_eq_neg_inner_normalVector_tangentVector (t u : Real.Angle) :
    (u - t).sin = -inner ℝ (normalVector t) (tangentVector u) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    induction u using Real.Angle.induction_on with
    | _ u =>
      change Real.sin (u - t) = _
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.sin_sub]
      ring

/-- The normal projection of a tangent vector is the sine of the angle difference. -/
theorem inner_tangentVector_normalVector_real (t s : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (normalVector (s : Real.Angle)) =
      Real.sin (s - t) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
  ring

/-- The inner product of two unit tangents is the cosine of their angle difference. -/
theorem inner_tangentVector_tangentVector (s t : ℝ) :
    inner ℝ (tangentVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- The normal coordinate of a vector in the frame at another angle. -/
theorem inner_normalVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (normalVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.cos (s - t) -
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.sin (s - t) := by
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_normalVector, inner_tangentVector_normalVector_real,
    show t - s = -(s - t) by ring, Real.sin_neg]
  ring

/-- The tangent coordinate of a vector in the frame at another angle. -/
theorem inner_tangentVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (tangentVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.sin (s - t) +
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.cos (s - t) := by
  have hcross : inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.sin (s - t) := by
    rw [real_inner_comm]
    exact inner_tangentVector_normalVector_real t s
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, hcross]

/-- Two points whose normal coordinates agree at two transverse angles coincide. -/
theorem eq_of_inner_normalVector_eq {p q : Point} {s t : ℝ}
    (hst : Real.sin (s - t) ≠ 0)
    (hs : inner ℝ p (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) =
      inner ℝ q (normalVector (t : Real.Angle))) : p = q := by
  have hp := inner_normalVector_eq_frame_rotate p s t
  have hq := inner_normalVector_eq_frame_rotate q s t
  have hmul : (inner ℝ p (tangentVector (s : Real.Angle)) -
      inner ℝ q (tangentVector (s : Real.Angle))) * Real.sin (s - t) = 0 := by
    linear_combination hp - hq - ht + Real.cos (s - t) * hs
  have hv : inner ℝ p (tangentVector (s : Real.Angle)) =
      inner ℝ q (tangentVector (s : Real.Angle)) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hst)
  calc p = inner ℝ p (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ p (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) :=
        (inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)).symm
    _ = inner ℝ q (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ q (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) := by
        rw [hs, hv]
    _ = q := inner_normalVector_smul_add_inner_tangentVector_smul q (s : Real.Angle)

/-- Each coordinate of the frame tangent is continuous in the angle. -/
theorem continuous_tangentVector_coordinate (i : Fin 2) :
    Continuous fun u : Real.Angle ↦ tangentVector u i := by
  fin_cases i
  · exact Real.Angle.continuous_sin.neg
  · exact Real.Angle.continuous_cos

/-- The frame tangent is a unit vector. -/
theorem norm_tangentVector (t : Real.Angle) : ‖tangentVector t‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), Point.norm_sq_eq]
  simp [tangentVector, frame, add_comm]

/-- Each coordinate of the frame tangent is bounded by one. -/
theorem norm_tangentVector_coordinate_le_one (t : Real.Angle) (i : Fin 2) :
    ‖tangentVector t i‖ ≤ 1 := by
  simpa [Real.norm_eq_abs, norm_tangentVector t] using
    Point.abs_apply_le_norm (tangentVector t) i

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Normal Lines
-/

public section

noncomputable section

namespace MovingSofa

/-- A nontrivial segment has at most one normal direction strictly between zero and pi. -/
theorem eq_of_inner_sub_normalVector_eq_zero_of_ne {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a ≠ b)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hxprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hyprod : (b 1 - a 1) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.cos t * hs' - Real.cos s * ht'
  have hsin : Real.sin (s - t) = 0 := by
    by_contra hne
    have hx : b 0 = a 0 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hxprod).resolve_right hne)
    have hy : b 1 = a 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hyprod).resolve_right hne)
    apply hab
    ext i
    fin_cases i
    · exact hx.symm
    · exact hy.symm
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hsin
  linarith

/-- Normal lines with angles strictly between zero and pi agree exactly when their data agree. -/
theorem normalLine_eq_iff_of_mem_Ioo {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) :
    normalLine (s : Real.Angle) c = normalLine (t : Real.Angle) d ↔
      s = t ∧ c = d := by
  constructor
  · intro hline
    let p := c • normalVector (s : Real.Angle)
    let q := p + tangentVector (s : Real.Angle)
    have hp : p ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ p (normalVector (s : Real.Angle)) = c
      rw [show p = c • normalVector (s : Real.Angle) by rfl,
        real_inner_smul_left, inner_normalVector_self]
      simp
    have hq : q ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ q (normalVector (s : Real.Angle)) = c
      rw [show q = p + tangentVector (s : Real.Angle) by rfl, inner_add_left]
      rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp]
      rw [real_inner_comm, inner_normalVector_tangentVector, add_zero]
    have hp' : p ∈ normalLine (t : Real.Angle) d := hline ▸ hp
    have hq' : q ∈ normalLine (t : Real.Angle) d := hline ▸ hq
    have hv : tangentVector (s : Real.Angle) ≠ 0 := by
      intro hz
      have hinner := inner_tangentVector_self s
      rw [hz, inner_zero_left] at hinner
      norm_num at hinner
    have hsorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (s : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    have htorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [show tangentVector (s : Real.Angle) = q - p by simp [q]]
      rw [inner_sub_left, show inner ℝ q (normalVector (t : Real.Angle)) = d by exact hq',
        show inner ℝ p (normalVector (t : Real.Angle)) = d by exact hp', sub_self]
    have hst := eq_of_inner_sub_normalVector_eq_zero_of_ne
      (a := 0) (b := tangentVector (s : Real.Angle)) hs ht hv.symm
      (by simpa using hsorth) (by simpa using htorth)
    subst t
    refine ⟨rfl, ?_⟩
    change inner ℝ p (normalVector (s : Real.Angle)) = d at hp'
    rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp] at hp'
    exact hp'
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Opposite normal angles describe the same line with the opposite offset. -/
theorem normalLine_eq_of_cut {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) :
    normalLine ((b : ℝ) : Real.Angle) c = normalLine ((a : ℝ) : Real.Angle) (-c) := by
  rw [hab]
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith only [h]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Quadrant Bounds
-/

public section

namespace MovingSofa

/-- A horizontal lower bound cuts a first-quadrant pair of upper projection bounds to a bounded set.
-/
theorem isBounded_setOf_le_snd_and_inner_lt (a b c t : ℝ) (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Bornology.IsBounded {p : Point | a ≤ p 1 ∧
      inner ℝ p (normalVector (t : Real.Angle)) < b ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < c} := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  apply (EuclideanSpace.isBounded_coordinate_rectangle ((Real.cos t * a - c) / Real.sin t)
    ((b - Real.sin t * a) / Real.cos t) a (Real.sin t * b + Real.cos t * c)).subset
  rintro p ⟨hy, h₁, h₂⟩
  have hb : Real.cos t * p 0 + Real.sin t * p 1 < b := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using h₁
  have hd : -Real.sin t * p 0 + Real.cos t * p 1 < c := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add, -Real.Angle.coe_add, mul_comm] using h₂
  refine ⟨?_, ?_, hy, ?_⟩
  · apply (div_le_iff₀ hs).2
    nlinarith only [hd, mul_le_mul_of_nonneg_left hy hc.le]
  · apply (le_div_iff₀ hc).2
    nlinarith only [hb, mul_le_mul_of_nonneg_left hy hs.le]
  · have hyid : (Real.sin t ^ 2 + Real.cos t ^ 2) * p 1 = p 1 := by
      rw [Real.sin_sq_add_cos_sq, one_mul]
    have hb' := mul_lt_mul_of_pos_left hb hs
    have hd' := mul_lt_mul_of_pos_left hd hc
    nlinarith only [hyid, hb', hd']

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The planar region under the graph of a function

For `a b : ℝ` and `f : ℝ → ℝ` this file describes the three planar regions between the
horizontal axis and the graph of `f` over `[a, b]`: `closedSubgraph`, which contains both the
base segment and the graph, `strictSubgraph`, which contains the base but not the graph, and
`openSubgraph`, which contains neither.

For a function continuous on `[a, b]`, vanishing at `a` and `b` and positive in between, the
closed region is the closure of either smaller region (`closure_openSubgraph`,
`closure_strictSubgraph`) and the open region is its interior (`interior_closedSubgraph`).
-/

public section

noncomputable section

namespace MovingSofa

/-- A planar point is recovered from its two coordinates. -/
theorem Point.eq_vecNotation (z : Point) : z = !₂[z 0, z 1] := by
  ext i
  fin_cases i <;> simp

/-- The closed region between the base and the graph of `f` over `[a, b]`. -/
@[expose]
def closedSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 ≤ f (q 0)}

/-- The region under the graph of `f` over `[a, b]`, including the base but not the graph. -/
@[expose]
def strictSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 < f (q 0)}

/-- The open region strictly between the base and the graph of `f` over `(a, b)`. -/
@[expose]
def openSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a < q 0 ∧ q 0 < b ∧ 0 < q 1 ∧ q 1 < f (q 0)}

section Subgraph

variable {a b : ℝ} {f : ℝ → ℝ}

/-- The open subgraph omits the base, which the strict subgraph contains. -/
theorem openSubgraph_subset_strictSubgraph : openSubgraph a b f ⊆ strictSubgraph a b f :=
  fun _ h ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2⟩

/-- The strict subgraph omits the graph, which the closed subgraph contains. -/
theorem strictSubgraph_subset_closedSubgraph : strictSubgraph a b f ⊆ closedSubgraph a b f :=
  fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.le⟩

/-- The open subgraph is contained in the closed one. -/
theorem openSubgraph_subset_closedSubgraph : openSubgraph a b f ⊆ closedSubgraph a b f :=
  openSubgraph_subset_strictSubgraph.trans strictSubgraph_subset_closedSubgraph

/-- The vertical line through a fixed horizontal coordinate is continuous. -/
private theorem continuous_verticalLine (c : ℝ) :
    Continuous fun y : ℝ ↦ (!₂[c, y] : Point) :=
  (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
    (continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const))

/-- The closed subgraph of a function continuous on the base interval is closed. -/
theorem isClosed_closedSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsClosed (closedSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hSclosed : IsClosed {q : Point | q 0 ∈ Set.Icc a b} := isClosed_Icc.preimage hc0
  have hgS : ContinuousOn (fun q : Point ↦ f (q 0) - q 1) {q : Point | q 0 ∈ Set.Icc a b} :=
    (hf.comp hc0.continuousOn fun q hq ↦ hq).sub hc1.continuousOn
  have hone := hgS.preimage_isClosed_of_isClosed hSclosed (isClosed_Ici (a := (0 : ℝ)))
  have htwo : IsClosed {q : Point | 0 ≤ q 1} := isClosed_Ici.preimage hc1
  have hsplit : closedSubgraph a b f = ({q : Point | q 0 ∈ Set.Icc a b} ∩
      (fun q : Point ↦ f (q 0) - q 1) ⁻¹' Set.Ici 0) ∩ {q : Point | 0 ≤ q 1} := by
    ext q
    simp only [closedSubgraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      Set.mem_preimage, Set.mem_Ici, sub_nonneg]
    tauto
  rw [hsplit]
  exact hone.inter htwo

/-- The open subgraph of a function continuous on the base interval is open. -/
theorem isOpen_openSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsOpen (openSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h1, h2, h3, h4⟩
  have hfat : ContinuousAt f (p 0) :=
    (hf.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds h1 h2)
  have hgap : ContinuousAt (fun q : Point ↦ f (q 0) - q 1) p :=
    (ContinuousAt.comp (g := f) (f := fun q : Point ↦ q 0) (x := p) hfat
      hc0.continuousAt).sub hc1.continuousAt
  filter_upwards [hc0.continuousAt (isOpen_Ioo.mem_nhds (⟨h1, h2⟩ : p 0 ∈ Set.Ioo a b)),
    hc1.continuousAt (isOpen_Ioi.mem_nhds (show p 1 ∈ Set.Ioi (0 : ℝ) from h3)),
    hgap (isOpen_Ioi.mem_nhds (show f (p 0) - p 1 ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr h4))]
    with q hq1 hq2 hq3
  exact ⟨hq1.1, hq1.2, hq2, by simpa using sub_pos.mp hq3⟩

/-- The closed subgraph is the closure of the open one: interior graph points are limits from
below, base points at interior horizontal coordinates are limits from above, and the two
corners are limits of half-height points over the open base interval. -/
theorem closure_openSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (openSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm ((isClosed_closedSubgraph hf).closure_subset_iff.mpr ?_) ?_
  · rintro q ⟨h1, h2, h3, h4⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  · have hF : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (Set.Icc a b) :=
      (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
        (continuous_id.continuousOn.matrixVecCons
          ((hf.div_const 2).matrixVecCons continuousOn_const))
    have hFsub : (fun c ↦ (!₂[c, f c / 2] : Point)) '' Set.Ioo a b ⊆ openSubgraph a b f := by
      rintro _ ⟨c, hc, rfl⟩
      have hfc := hpos c hc
      exact ⟨by simpa using hc.1, by simpa using hc.2, by simpa using by linarith,
        by simpa using by linarith⟩
    have hcl : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
    have hF' : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (closure (Set.Ioo a b)) := by
      rw [hcl]; exact hF
    have hcorner : ∀ c ∈ Set.Icc a b, (!₂[c, f c / 2] : Point) ∈ closure (openSubgraph a b f) :=
      fun c hc ↦ closure_mono hFsub (hF'.image_closure ⟨c, by rw [hcl]; exact hc, rfl⟩)
    rintro q ⟨h1, h2, h3, h4⟩
    rcases eq_or_lt_of_le h1 with hqa | hqa
    · have : q 1 = 0 := le_antisymm (by rw [← hqa, ha] at h4; exact h4) h3
      have hq : q = !₂[a, f a / 2] := by
        rw [Point.eq_vecNotation q, ← hqa, this, ha]
        norm_num
      rw [hq]
      exact hcorner a ⟨le_rfl, hab.le⟩
    rcases eq_or_lt_of_le h2 with hqb | hqb
    · have : q 1 = 0 := le_antisymm (by rw [hqb, hb] at h4; exact h4) h3
      have hq : q = !₂[b, f b / 2] := by
        rw [Point.eq_vecNotation q, hqb, this, hb]
        norm_num
      rw [hq]
      exact hcorner b ⟨hab.le, le_rfl⟩
    · have hfc : 0 < f (q 0) := hpos _ ⟨hqa, hqb⟩
      have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioo 0 (f (q 0)) ⊆
          openSubgraph a b f := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨by simpa using hqa, by simpa using hqb, by simpa using hy.1,
          by simpa using hy.2⟩
      refine closure_mono hsub ?_
      have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
        (s := Set.Ioo 0 (f (q 0)))
        ⟨q 1, by rw [closure_Ioo hfc.ne]; exact ⟨h3, h4⟩, rfl⟩
      have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
      simpa only [heq] using this

/-- A point of the closed subgraph which is not in the open one lies on the base or on the
graph, hence is a limit of points outside the closed subgraph. -/
private theorem mem_closure_compl_closedSubgraph (ha : f a = 0) (hb : f b = 0)
    {q : Point} (hq : q ∈ closedSubgraph a b f)
    (hq' : q ∉ openSubgraph a b f) : q ∈ closure (closedSubgraph a b f)ᶜ := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hbelow : q 1 = 0 → q ∈ closure (closedSubgraph a b f)ᶜ := by
    intro hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Iio 0 ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0)) (s := Set.Iio 0)
      ⟨q 1, by rw [closure_Iio]; exact hz.le, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  rcases eq_or_lt_of_le h3 with hz | hz
  · exact hbelow hz.symm
  rcases eq_or_lt_of_le h4 with htop | htop
  · -- the point sits on the graph, which is strictly above the base here
    have hfpos : 0 < f (q 0) := htop ▸ hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioi (f (q 0)) ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
      (s := Set.Ioi (f (q 0))) ⟨q 1, by rw [closure_Ioi]; exact htop.ge, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  · -- strictly between base and graph: the horizontal coordinate must be interior
    exfalso
    have hfpos : 0 < f (q 0) := hz.trans htop
    have hqa : a < q 0 := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h, ha] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    have hqb : q 0 < b := by
      rcases eq_or_lt_of_le h2 with h | h
      · rw [h, hb] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    exact hq' ⟨hqa, hqb, hz, htop⟩

/-- The open subgraph is the interior of the closed one. -/
theorem interior_closedSubgraph (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    interior (closedSubgraph a b f) = openSubgraph a b f := by
  refine Set.Subset.antisymm ?_ (interior_maximal openSubgraph_subset_closedSubgraph
    (isOpen_openSubgraph hf))
  intro q hq
  by_contra hqU
  have h2 := mem_closure_compl_closedSubgraph ha hb (interior_subset hq) hqU
  rw [closure_compl] at h2
  exact h2 hq

/-- The closed subgraph is also the closure of the strict subgraph. -/
theorem closure_strictSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (strictSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm
    ((isClosed_closedSubgraph hf).closure_subset_iff.mpr
      strictSubgraph_subset_closedSubgraph) ?_
  rw [← closure_openSubgraph hab hf ha hb hpos]
  exact closure_mono openSubgraph_subset_strictSubgraph

end Subgraph

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Support
-/

public section

noncomputable section

namespace MovingSofa

/-- A compact convex body attains its support value in every normal direction. -/
theorem exists_mem_inner_eq_supportValue (K : ConvexBody Point) (t : Real.Angle) :
    ∃ p ∈ (K : Set Point), inner ℝ p (normalVector t) = supportValue K t := by
  obtain ⟨p, hp, hmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  exact ⟨p, hp, by simpa only [supportValue] using hmax.symm⟩

/-- Translating a nonempty compact set adds the normal component to its support value. -/
theorem supportValue_image_add_of_isCompact {s : Set Point}
    (hs : IsCompact s) (hne : s.Nonempty) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' s) t =
      supportValue s t + inner ℝ v (normalVector t) := by
  obtain ⟨x, hx, hmax, hbound⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨x + v, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [inner_add_left, supportValue] using congrArg
      (fun r ↦ r + inner ℝ v (normalVector t)) hmax.symm
  · rintro z ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    simp only [inner_add_left]
    simpa only [supportValue, hmax] using
      add_le_add (hbound p hp) (le_refl (inner ℝ v (normalVector t)))

/-- Translating a compact convex body adds the normal component of the translation to support. -/
theorem supportValue_image_add (K : ConvexBody Point) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' (K : Set Point)) t =
      supportValue K t + inner ℝ v (normalVector t) :=
  supportValue_image_add_of_isCompact K.isCompact K.nonempty v t

/-- Every point of a compact set lies below its support value. -/
theorem inner_le_supportValue_of_isCompact {s : Set Point}
    (hs : IsCompact s) {p : Point} (hp : p ∈ s) (a : Real.Angle) :
    inner ℝ p (normalVector a) ≤ supportValue s a := by
  apply le_csSup (hs.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
  exact ⟨p, hp, rfl⟩

/-- A point of a convex body lies below each supporting line. -/
theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t :=
  inner_le_supportValue_of_isCompact K.isCompact hp t

/-- Containment in a closed normal half-plane bounds the support value. -/
theorem supportValue_le_of_subset_normalHalfPlane (K : ConvexBody Point)
    (t : Real.Angle) (c : ℝ)
    (hK : (K : Set Point) ⊆ normalHalfPlane t c false false) :
    supportValue K t ≤ c := by
  apply csSup_le (K.nonempty.image _)
  rintro _ ⟨p, hp, rfl⟩
  exact hK hp

/-- Enlarging a nonempty set without increasing its directional upper bound preserves support. -/
theorem supportValue_eq_of_subset_of_inner_le {s u : Set Point}
    (hs : s.Nonempty) (hsu : s ⊆ u) (a : Real.Angle)
    (hu : ∀ p ∈ u, inner ℝ p (normalVector a) ≤ supportValue s a) :
    supportValue u a = supportValue s a := by
  have hbounded : BddAbove ((fun p ↦ inner ℝ p (normalVector a)) '' u) :=
    ⟨supportValue s a, by rintro _ ⟨p, hp, rfl⟩; exact hu p hp⟩
  apply le_antisymm
  · exact csSup_le ((hs.mono hsu).image _) (by rintro _ ⟨p, hp, rfl⟩; exact hu p hp)
  · exact csSup_le_csSup hbounded (hs.image _) (Set.image_mono hsu)

/-- A convex set meets every intermediate level of a linear functional. -/
theorem exists_mem_inner_eq_of_convex {s : Set Point} (hconv : Convex ℝ s)
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s) {u : Point} {c : ℝ}
    (hCle : inner ℝ C u ≤ c) (hAge : c ≤ inner ℝ A u) :
    ∃ q ∈ s, inner ℝ q u = c := by
  rcases eq_or_lt_of_le (hCle.trans hAge) with heq | hlt
  · exact ⟨C, hC, le_antisymm hCle (heq ▸ hAge)⟩
  · set d : ℝ := inner ℝ A u - inner ℝ C u with hd
    have hdpos : 0 < d := by simp only [hd]; linarith
    set lam : ℝ := (c - inner ℝ C u) / d with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hdpos.le
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hdpos]
      simp only [hd]; linarith
    refine ⟨lam • A + (1 - lam) • C, hconv hA hC hlam0 (by linarith) (by ring), ?_⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hlam]
    field_simp
    simp only [hd]
    ring

/-- Support bound in the direction opposite to a cut line lying below the set. -/
theorem supportValue_le_of_cut {s : Set Point} (hne : s.Nonempty) {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle))
    (hs : ∀ p ∈ s, c ≤ inner ℝ p (normalVector (a : Real.Angle))) :
    supportValue s ((b : ℝ) : Real.Angle) ≤ -c := by
  rw [hab]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨p, hp, rfl⟩
  dsimp only
  rw [normalVector_add_pi, inner_neg_right]
  linarith only [hs p hp]

/-- A contact point on a cut line attains the opposite support value. -/
theorem le_supportValue_of_cut {s : Set Point} (hcomp : IsCompact s) {a b c : ℝ} {p : Point}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) (hp : p ∈ s)
    (hpc : inner ℝ p (normalVector (a : Real.Angle)) = c) :
    -c ≤ supportValue s ((b : ℝ) : Real.Angle) := by
  rw [hab]
  have h := inner_le_supportValue_of_isCompact hcomp hp ((a + Real.pi : ℝ) : Real.Angle)
  rw [normalVector_add_pi, inner_neg_right, hpc] at h
  linarith only [h]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Contacts
-/

public section

noncomputable section

namespace MovingSofa

/-- The exposed edge at a normal direction, including singleton edges. -/
@[expose]
def exposedEdge (K : ConvexBody Point) (t : Real.Angle) : Set Point :=
  (K : Set Point) ∩ (supportingLineHalfPlane K t).1

/-- The positive and negative tangent endpoints of an exposed edge. -/
@[expose]
def edgeVertices (K : ConvexBody Point) (t : Real.Angle) : Point × Point :=
  let heights := (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
  (supportValue K t • normalVector t + sSup heights • tangentVector t,
    supportValue K t • normalVector t + sInf heights • tangentVector t)

/-- The intersection point of two supporting lines at nonparallel normal directions. -/
@[expose]
def supportingIntersection (K : ConvexBody Point) (a b : Real.Angle) : Point :=
  supportValue K a • normalVector a +
    ((supportValue K b - supportValue K a * (b - a).cos) / (b - a).sin) • tangentVector a

theorem exposedEdge_nonempty (K : ConvexBody Point) (t : Real.Angle) :
    (exposedEdge K t).Nonempty := by
  obtain ⟨x, hx, hxmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨x, hx, ?_⟩
  simpa [supportingLineHalfPlane, normalLine, supportValue] using hxmax.symm

theorem convex_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (exposedEdge K t) := by
  apply K.convex.inter
  intro x hx y hy a b ha hb hab
  change inner ℝ x (normalVector t) = supportValue K t at hx
  change inner ℝ y (normalVector t) = supportValue K t at hy
  change inner ℝ (a • x + b • y) (normalVector t) = supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left, hx, hy]
  simp only [RCLike.conj_to_real]
  rw [← add_mul, hab, one_mul]

theorem isConnected_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsConnected (exposedEdge K t) :=
  (convex_exposedEdge K t).isConnected (exposedEdge_nonempty K t)

theorem supportingIntersection_inner_left (K : ConvexBody Point) (s t : ℝ) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle) := by
  have htn : inner ℝ (tangentVector (s : Real.Angle)) (normalVector (s : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_self, htn, mul_one, mul_zero, add_zero]

theorem supportingIntersection_inner_right (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right,
    supportingIntersection_inner_left]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self, mul_zero, mul_one, zero_add,
    ← Real.Angle.coe_sub, Real.Angle.cos_coe, Real.Angle.sin_coe]
  field_simp
  ring

theorem supportingIntersection_comm (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportingIntersection K (t : Real.Angle) (s : Real.Angle) := by
  have h' : Real.sin (s - t) ≠ 0 := by
    rw [show s - t = -(t - s) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr h
  let p := supportingIntersection K (t : Real.Angle) (s : Real.Angle)
  have hp := supportingIntersection_inner_right K t s h'
  have hq := supportingIntersection_inner_left K t s
  change inner ℝ p (normalVector (s : Real.Angle)) = _ at hp
  change inner ℝ p (normalVector (t : Real.Angle)) = _ at hq
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right, hp] at hq
  have ht : inner ℝ p (tangentVector (s : Real.Angle)) =
      (supportValue K (t : Real.Angle) - supportValue K (s : Real.Angle) *
        Real.cos (t - s)) / Real.sin (t - s) := by
    apply (eq_div_iff h).mpr
    linarith
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)
  rw [hp, ht] at heq
  simpa only [p, supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe] using heq

/-- Every exposed edge of a compact convex body is compact. -/
theorem isCompact_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsCompact (exposedEdge K t) :=
  K.isCompact.inter_right (isClosed_eq
    (continuous_id.inner continuous_const) continuous_const)

/-- The positive tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_exposedEdge K t).exists_sSup_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).1 = p := by
    change supportValue K t • normalVector t +
      sSup ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmax, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- The negative tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_snd_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).2 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_exposedEdge K t).exists_sInf_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).2 = p := by
    change supportValue K t • normalVector t +
      sInf ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmin, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- A singleton exposed face is both of its tangent endpoints. -/
theorem edgeVertices_eq_of_exposedEdge_singleton {K : ConvexBody Point} {t : Real.Angle}
    {p : Point} (h : exposedEdge K t = {p}) : edgeVertices K t = (p, p) := by
  have h1 := edgeVertices_fst_mem K t
  have h2 := edgeVertices_snd_mem K t
  rw [h, Set.mem_singleton_iff] at h1 h2
  exact Prod.ext h1 h2

/-- The positive face vertex attains the largest tangent coordinate. -/
theorem inner_edgeVertices_fst_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).1 (tangentVector t) =
      sSup ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

/-- The negative face vertex attains the smallest tangent coordinate. -/
theorem inner_edgeVertices_snd_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).2 (tangentVector t) =
      sInf ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

private theorem exposedEdge_subset_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t ⊆ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  intro p hp
  let lo := (edgeVertices K t).2
  let hi := (edgeVertices K t).1
  let z := inner ℝ p (tangentVector t)
  let zlo := inner ℝ lo (tangentVector t)
  let zhi := inner ℝ hi (tangentVector t)
  have hbddBelow : BddBelow ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddBelow
  have hbddAbove : BddAbove ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddAbove
  have hzmem : z ∈ (fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t :=
    ⟨p, hp, rfl⟩
  have hzlo : zlo ≤ z := by
    dsimp only [zlo, z, lo]
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le hbddBelow hzmem
  have hzhi : z ≤ zhi := by
    dsimp only [zhi, z, hi]
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup hbddAbove hzmem
  by_cases hzh : zlo = zhi
  · have hz : z = zlo := le_antisymm (hzhi.trans_eq hzh.symm) hzlo
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hpl : p = lo := by
      rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
        ← inner_normalVector_smul_add_inner_tangentVector_smul lo t,
        hpnormal, hlonormal]
      change inner ℝ p (tangentVector t) = inner ℝ lo (tangentVector t) at hz
      rw [hz]
    simpa only [lo, hi, hpl] using left_mem_segment ℝ lo hi
  · have hlt : zlo < zhi := lt_of_le_of_ne (hzlo.trans hzhi) hzh
    let u := (z - zlo) / (zhi - zlo)
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hlt.le)
      · rw [div_le_one (sub_pos.mpr hlt)]
        linarith
    rw [segment_eq_image]
    refine ⟨u, hu, ?_⟩
    change (1 - u) • lo + u • hi = p
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hhinormal : inner ℝ hi (normalVector t) = supportValue K t :=
      (edgeVertices_fst_mem K t).2
    have hnormal : inner ℝ ((1 - u) • lo + u • hi) (normalVector t) =
        inner ℝ p (normalVector t) := by
      simp only [inner_add_left, real_inner_smul_left, hlonormal, hhinormal, hpnormal]
      ring
    have htangent : inner ℝ ((1 - u) • lo + u • hi) (tangentVector t) =
        inner ℝ p (tangentVector t) := by
      simp only [inner_add_left, real_inner_smul_left]
      change (1 - u) * zlo + u * zhi = z
      dsimp [u]
      field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]
      ring
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      ((1 - u) • lo + u • hi) t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      hnormal, htangent]

/-- An exposed face is the segment joining its two tangent-extreme vertices. -/
theorem exposedEdge_eq_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t = segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  apply Set.Subset.antisymm (exposedEdge_subset_segment_edgeVertices K t)
  exact (convex_exposedEdge K t).segment_subset
    (edgeVertices_snd_mem K t) (edgeVertices_fst_mem K t)

/-- An exposed face determines the support value and both of its endpoint vertices. -/
theorem edgeVertices_eq_of_exposedEdge_eq (K L : ConvexBody Point) (u : Real.Angle)
    (h : exposedEdge K u = exposedEdge L u) : edgeVertices K u = edgeVertices L u := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K u
  have hpL : p ∈ exposedEdge L u := h ▸ hp
  have hK : inner ℝ p (normalVector u) = supportValue K u := hp.2
  have hL : inner ℝ p (normalVector u) = supportValue L u := hpL.2
  simp only [edgeVertices, hK.symm.trans hL, h]

/-- A support-line intersection in the body is the negative endpoint at the later normal. -/
theorem supportingIntersection_eq_edgeVertices_snd_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (b : Real.Angle)).2 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (b : Real.Angle) := ⟨hp, hpb⟩
  have heedge := edgeVertices_snd_mem K (b : Real.Angle)
  have hen : inner ℝ e (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (b : Real.Angle)) =
      inner ℝ e (tangentVector (b : Real.Angle)) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm
    · apply le_csInf ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqa := inner_le_supportValue K hq.1 (a : Real.Angle)
      have hna : normalVector (a : Real.Angle) =
          Real.cos (a - b) • normalVector (b : Real.Angle) +
            Real.sin (a - b) • tangentVector (b : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
      rw [← hpa, hna] at hqa
      simp only [inner_add_right, inner_smul_right] at hqa
      rw [hpb, hq.2] at hqa
      nlinarith
    · exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨p, hpedge, rfl⟩
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (b : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (b : Real.Angle), hpb, hen,
    hpt]

/-- A support-line intersection in the body is the positive endpoint at the earlier normal. -/
theorem supportingIntersection_eq_edgeVertices_fst_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (a : Real.Angle)).1 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (a : Real.Angle) := ⟨hp, hpa⟩
  have heedge := edgeVertices_fst_mem K (a : Real.Angle)
  have hen : inner ℝ e (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (a : Real.Angle)) =
      inner ℝ e (tangentVector (a : Real.Angle)) := by
    rw [inner_edgeVertices_fst_tangent]
    apply le_antisymm
    · exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨p, hpedge, rfl⟩
    · apply csSup_le ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqb := inner_le_supportValue K hq.1 (b : Real.Angle)
      have hnb : normalVector (b : Real.Angle) =
          Real.cos (b - a) • normalVector (a : Real.Angle) +
            Real.sin (b - a) • tangentVector (a : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
      rw [← hpb, hnb] at hqb
      simp only [inner_add_right, inner_smul_right] at hqb
      rw [hpa, hq.2] at hqb
      nlinarith
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (a : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (a : Real.Angle), hpa, hen,
    hpt]

/-- The first endpoint reaches the adjacent supporting-line intersection along a positive
tangent ray. -/
theorem supportingIntersection_eq_fst_add_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (a : Real.Angle)).1 + d • tangentVector (a : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let P := (edgeVertices K (a : Real.Angle)).1
  let d := inner ℝ (O - P) (tangentVector (a : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hPn : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hnormal : inner ℝ (O - P) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hOn, hPn, sub_self]
  have hdir : O = P + d • tangentVector (a : Real.Angle) := by
    rw [show O = P + (O - P) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (O - P) (a : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
      supportingIntersection_inner_right K a b hsin.ne'
    have hPb := inner_le_supportValue K (edgeVertices_fst_mem K (a : Real.Angle)).1
      (b : Real.Angle)
    change inner ℝ P (normalVector (b : Real.Angle)) ≤ supportValue K b at hPb
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [← hOb, hdir, hnb, inner_add_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hPn] at hPb
    have htn : inner ℝ (tangentVector (a : Real.Angle))
        (normalVector (a : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hPb
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOP : O = P := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOP ▸ (edgeVertices_fst_mem K _).1
    have hOQ := supportingIntersection_eq_edgeVertices_snd_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-- The second endpoint reaches the adjacent supporting-line intersection against a positive
tangent ray. -/
theorem supportingIntersection_eq_snd_sub_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (b : Real.Angle)).2 - d • tangentVector (b : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let Q := (edgeVertices K (b : Real.Angle)).2
  let d := inner ℝ (Q - O) (tangentVector (b : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQn : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K (b : Real.Angle)).2
  have hnormal : inner ℝ (Q - O) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQn, hOn, sub_self]
  have hdir : O = Q - d • tangentVector (b : Real.Angle) := by
    rw [show O = Q - (Q - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - O) (b : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
      supportingIntersection_inner_left K a b
    have hQa := inner_le_supportValue K (edgeVertices_snd_mem K (b : Real.Angle)).1
      (a : Real.Angle)
    change inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a at hQa
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [← hOa, hdir, hna, inner_sub_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hQn] at hQa
    have htn : inner ℝ (tangentVector (b : Real.Angle))
        (normalVector (b : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hQa
    have hsneg : Real.sin (a - b) < 0 := by
      rw [show a - b = -(b - a) by ring, Real.sin_neg]
      exact neg_neg_of_pos hsin
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOQ : O = Q := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOQ ▸ (edgeVertices_snd_mem K _).1
    have hOP := supportingIntersection_eq_edgeVertices_fst_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-! ### Faces at a reversed normal direction -/

/-- A body bounded below in a normal direction, with the bound attained, has the opposite
support value in the reversed direction. -/
theorem supportValue_add_pi_eq_neg_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    supportValue L ((t + Real.pi : ℝ) : Real.Angle) = -c :=
  le_antisymm (supportValue_le_of_cut L.nonempty rfl hle)
    (le_supportValue_of_cut L.isCompact rfl hp hpc)

/-- The face at a reversed normal direction consists of the points attaining the attained
lower bound. -/
theorem exposedEdge_add_pi_eq_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) =
      {q | q ∈ (L : Set Point) ∧ inner ℝ q (normalVector (t : Real.Angle)) = c} := by
  have hsup := supportValue_add_pi_eq_neg_of_forall_le hle hp hpc
  ext q
  constructor
  · intro hq
    have h2 : inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) := hq.2
    rw [normalVector_add_pi, inner_neg_right, hsup] at h2
    exact ⟨hq.1, by linarith only [h2]⟩
  · rintro ⟨hqL, hqc⟩
    refine ⟨hqL, ?_⟩
    change inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) = _
    rw [normalVector_add_pi, inner_neg_right, hsup, hqc]

/-! ### Faces between two supporting normals with a common contact point -/

/-- A point on two transverse supporting lines is their intersection. -/
theorem eq_supportingIntersection_of_mem_exposedEdge {L : ConvexBody Point} {a b : ℝ}
    {p : Point} (hsin : Real.sin (a - b) ≠ 0) (hpa : p ∈ exposedEdge L (a : Real.Angle))
    (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    p = supportingIntersection L (a : Real.Angle) (b : Real.Angle) := by
  have hsin' : Real.sin (b - a) ≠ 0 := by
    rw [show b - a = -(a - b) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsin
  refine eq_of_inner_normalVector_eq hsin ?_ ?_
  · rw [supportingIntersection_inner_left]
    exact hpa.2
  · rw [supportingIntersection_inner_right L a b hsin']
    exact hpb.2

/-- Between two supporting normals less than a straight angle apart with a common contact
point, every intervening face is that point. -/
theorem exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo {L : ConvexBody Point}
    {a b s : ℝ} {p : Point} (hba : b < a + Real.pi) (hs : s ∈ Set.Ioo a b)
    (hpa : p ∈ exposedEdge L (a : Real.Angle)) (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    exposedEdge L (s : Real.Angle) = {p} := by
  have hab : a < b := hs.1.trans hs.2
  have hsba : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hab]) (by linarith only [hba])
  have hsbs : 0 < Real.sin (b - s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.2]) (by linarith only [hba, hs.1])
  have hssa : 0 < Real.sin (s - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.1]) (by linarith only [hba, hs.2])
  -- the positive combination of the two endpoint normals
  have hcomb : ∀ q : Point, Real.sin (b - s) * inner ℝ q (normalVector (a : Real.Angle)) +
      Real.sin (s - a) * inner ℝ q (normalVector (b : Real.Angle)) =
      Real.sin (b - a) * inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q
    rw [inner_normalVector_real, inner_normalVector_real, inner_normalVector_real,
      Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  have hqa : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (a : Real.Angle)) ≤
      inner ℝ p (normalVector (a : Real.Angle)) := by
    intro q hq
    rw [hpa.2]
    exact inner_le_supportValue L hq _
  have hqb : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (b : Real.Angle)) ≤
      inner ℝ p (normalVector (b : Real.Angle)) := by
    intro q hq
    rw [hpb.2]
    exact inner_le_supportValue L hq _
  have hps : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)) := by
    intro q hq
    have h1 := mul_le_mul_of_nonneg_left (hqa q hq) hsbs.le
    have h2 := mul_le_mul_of_nonneg_left (hqb q hq) hssa.le
    have h := add_le_add h1 h2
    rw [hcomb q, hcomb p] at h
    exact le_of_mul_le_mul_left (by linarith only [h]) hsba
  have hpsval : inner ℝ p (normalVector (s : Real.Angle)) = supportValue L (s : Real.Angle) :=
    le_antisymm (inner_le_supportValue L hpa.1 _) (csSup_le (L.nonempty.image _)
      (by rintro _ ⟨q, hq, rfl⟩; exact hps q hq))
  ext q
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ hq ▸ ⟨hpa.1, hpsval⟩⟩
  have hqs : inner ℝ q (normalVector (s : Real.Angle)) =
      inner ℝ p (normalVector (s : Real.Angle)) := by rw [hq.2, hpsval]
  have hsum : Real.sin (b - s) *
        (inner ℝ p (normalVector (a : Real.Angle)) - inner ℝ q (normalVector (a : Real.Angle))) +
      Real.sin (s - a) *
        (inner ℝ p (normalVector (b : Real.Angle)) - inner ℝ q (normalVector (b : Real.Angle)))
      = 0 := by
    have h1 := hcomb p
    have h2 := hcomb q
    rw [hqs] at h2
    linear_combination h1 - h2
  have hza : inner ℝ q (normalVector (a : Real.Angle)) =
      inner ℝ p (normalVector (a : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hzb : inner ℝ q (normalVector (b : Real.Angle)) =
      inner ℝ p (normalVector (b : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hsinab : Real.sin (a - b) ≠ 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsba.ne'
  exact eq_of_inner_normalVector_eq hsinab hza hzb

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Frame Calculus
-/

public section

noncomputable section

namespace MovingSofa

theorem hasDerivAt_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ normalVector (s : Real.Angle))
      (tangentVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      (![-Real.sin t, Real.cos t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ tangentVector (s : Real.Angle))
      (-normalVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![-Real.sin s, Real.cos s] : Fin 2 → ℝ))
      (![-Real.cos t, -Real.sin t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_sin t).neg
    · exact Real.hasDerivAt_cos t
  convert (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
    h using 1
  · rfl
  · ext i
    fin_cases i <;> rfl

/-- The angular unit-normal parametrization is one-Lipschitz. -/
theorem lipschitzWith_normalVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_normalVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_normalVector t).deriv]
  change ‖tangentVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_tangentVector]

/-- The angular unit-tangent parametrization is one-Lipschitz. -/
theorem lipschitzWith_tangentVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_tangentVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_tangentVector t).deriv]
  change ‖-normalVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_neg, norm_normalVector_real]

/-- A combination of the rotating frame whose coefficients are globally Lipschitz and bounded on a
set is Lipschitz on that set. -/
theorem lipschitzOnWith_frameCombination {f g : ℝ → ℝ} {C M : ℝ} {D : NNReal} {s : Set ℝ}
    (hD : 2 * (C + M) ≤ (D : ℝ)) (hM : 0 ≤ M)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ C * |x - y|) (hg : ∀ x y : ℝ, |g x - g y| ≤ C * |x - y|)
    (hfM : ∀ x ∈ s, |f x| ≤ M) (hgM : ∀ x ∈ s, |g x| ≤ M) :
    LipschitzOnWith D (fun x : ℝ ↦ f x • normalVector (x : Real.Angle) +
      g x • tangentVector (x : Real.Angle)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hframe (u v : ℝ) : dist (normalVector (u : Real.Angle)) (normalVector (v : Real.Angle)) ≤
      |u - v| ∧ dist (tangentVector (u : Real.Angle)) (tangentVector (v : Real.Angle)) ≤
        |u - v| := by
    constructor
    · simpa [Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul u v
    · simpa [Real.dist_eq] using lipschitzWith_tangentVector_real.dist_le_mul u v
  have hpair (p q : ℝ) (u w : Point) (hu : ‖u‖ = 1) (hq : |q| ≤ M)
      (huw : dist u w ≤ |x - y|) : dist (p • u) (q • w) ≤ |p - q| + M * |x - y| := by
    have h1 : dist (p • u) (q • u) ≤ |p - q| := by
      simpa [hu, Real.dist_eq] using dist_pair_smul p q u
    have h2 : dist (q • u) (q • w) ≤ M * |x - y| := by
      refine (dist_smul_pair q u w).trans ?_
      rw [Real.dist_eq, sub_zero]
      exact mul_le_mul hq huw dist_nonneg hM
    exact (dist_triangle _ _ _).trans (add_le_add h1 h2)
  have h1 := hpair (f x) (f y) (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (hfM y hy) (hframe x y).1
  have h2 := hpair (g x) (g y) (tangentVector (x : Real.Angle)) (tangentVector (y : Real.Angle))
    (norm_tangentVector _) (hgM y hy) (hframe x y).2
  have htri := dist_add_add_le (f x • normalVector (x : Real.Angle))
    (g x • tangentVector (x : Real.Angle)) (f y • normalVector (y : Real.Angle))
    (g y • tangentVector (y : Real.Angle))
  have hfxy := hf x y
  have hgxy := hg x y
  have hd : 2 * (C + M) * |x - y| ≤ (D : ℝ) * |x - y| :=
    mul_le_mul_of_nonneg_right hD (abs_nonneg _)
  rw [Real.dist_eq]
  linarith

/-- The angular derivative of a fixed normal projection is its tangent projection. -/
theorem hasDerivAt_inner_normalVector (A : Point) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ inner ℝ A (normalVector (u : Real.Angle)))
      (inner ℝ A (tangentVector (t : Real.Angle))) t := by
  simpa using (hasDerivAt_const t A).inner ℝ (hasDerivAt_normalVector t)

/-- A contact point in a normal direction has the support derivative as tangent coordinate. -/
theorem exists_contact_of_hasDerivAt {s : Set Point} (hcomp : IsCompact s)
    (hne : s.Nonempty) {t d : ℝ}
    (hd : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) d t) :
    ∃ A ∈ s, inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = d := by
  obtain ⟨A, hA, hmax, -⟩ := hcomp.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hAt : inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) := by
    simpa only [supportValue] using hmax.symm
  refine ⟨A, hA, hAt, ?_⟩
  set F : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ A (normalVector (u : Real.Angle)) with hF
  have hFmin : IsLocalMin F t := by
    filter_upwards with u
    have h1 : inner ℝ A (normalVector (u : Real.Angle)) ≤ supportValue s (u : Real.Angle) :=
      inner_le_supportValue_of_isCompact hcomp hA _
    simp only [hF, hAt, sub_self]
    linarith
  have hFderiv : HasDerivAt F (d - inner ℝ A (tangentVector (t : Real.Angle))) t :=
    hd.sub (hasDerivAt_inner_normalVector A t)
  have := hFmin.hasDerivAt_eq_zero hFderiv
  linarith
end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Cap.Basic`.
* `Cap.AngleDomain`.
* `Cap.Area`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Basic
-/

public section

noncomputable section

namespace MovingSofa

/-- The two real intervals of upper cap normals. -/
@[expose]
def capUpperAngles (ω : ℝ) : Set ℝ :=
  Set.Icc 0 ω ∪ Set.Icc (Real.pi / 2) (ω + Real.pi / 2)

/-- The normal directions of the two lower strip boundaries. -/
@[expose]
def capLowerNormals (ω : ℝ) : Set Real.Angle :=
  {((ω + Real.pi : ℝ) : Real.Angle), ((3 * Real.pi / 2 : ℝ) : Real.Angle)}

/-- A set represented by closed lower half-planes with allowed normal directions. -/
@[expose]
def HasHalfPlaneRepresentation (s : Set Point) (normals : Set Real.Angle) : Prop :=
  ∃ constraints : Set (Real.Angle × ℝ),
    (∀ c ∈ constraints, c.1 ∈ normals) ∧
      s = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false

/-- The normalized cap conditions, including its nonzero rotation-angle domain. -/
@[expose]
def IsCap (ω : ℝ) (K : ConvexBody Point) : Prop :=
  0 < ω ∧ ω ≤ Real.pi / 2 ∧
    supportValue K (ω : Real.Angle) = 1 ∧
    supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) = 1 ∧
    supportValue K ((ω + Real.pi : ℝ) : Real.Angle) = 0 ∧
    supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 ∧
    HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪ capLowerNormals ω)

/-- The space of caps at a fixed rotation angle. -/
@[expose]
def CapSpace (ω : ℝ) := {K : ConvexBody Point // IsCap ω K}

/-- A nonempty finite set of angles strictly between zero and its rotation angle. -/
structure AngleSet where
  /-- The terminal rotation angle of the polygonal approximation. -/
  angle : ℝ
  angle_pos : 0 < angle
  angle_le : angle ≤ Real.pi / 2
  /-- The finite nonempty set of interior wall directions. -/
  directions : Finset ℝ
  nonempty : directions.Nonempty
  interior : ∀ t ∈ directions, t ∈ Set.Ioo 0 angle

/-- The finite upper-normal domain associated with an angle set. -/
@[expose]
def angleDomain (Θ : AngleSet) : Set ℝ :=
  (Θ.directions : Set ℝ) ∪
    ((fun t ↦ t + Real.pi / 2) '' (Θ.directions : Set ℝ)) ∪
    {Θ.angle, Real.pi / 2}

/-- Polygon caps whose upper normals belong to the specified angle domain. -/
@[expose]
def PolygonCapSpace (Θ : AngleSet) :=
  {K : CapSpace Θ.angle // HasHalfPlaneRepresentation (K.1 : Set Point)
    (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle)}

/-- The fan above both lower strip boundaries. -/
@[expose]
def capFan (ω : ℝ) : Set Point :=
  normalHalfPlane (ω : Real.Angle) 0 true false ∩
    normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false

/-- The fan of a rotation angle is convex. -/
theorem convex_capFan (ω : ℝ) : Convex ℝ (capFan ω) :=
  (convex_normalHalfPlane _ _ _).inter (convex_normalHalfPlane _ _ _)

/-- The open inward quadrant of the supporting hallway, in support coordinates. -/
@[expose]
def innerQuadrant (s : Set Point) (t : ℝ) : Set Point :=
  normalHalfPlane (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true

/-- The open inward quadrant of a supporting hallway is convex. -/
theorem convex_innerQuadrant (s : Set Point) (t : ℝ) : Convex ℝ (innerQuadrant s t) :=
  (convex_normalHalfPlane_open _ _ _).inter (convex_normalHalfPlane_open _ _ _)

/-- The niche is the union of inward quadrants clipped by the fan. -/
@[expose]
def capNiche {ω : ℝ} (K : CapSpace ω) : Set Point :=
  capFan ω ∩ ⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (K.1 : Set Point) t

/-- The finite-angle niche uses the same fan clipping as the continuous niche. -/
@[expose]
def polygonNiche (Θ : AngleSet) (K : CapSpace Θ.angle) : Set Point :=
  capFan Θ.angle ∩ ⋃ t ∈ Θ.directions, innerQuadrant (K.1 : Set Point) t

/-- Avoiding an inward quadrant means lying above one of its two inner walls. -/
theorem notMem_innerQuadrant_iff (S : Set Point) (u : ℝ) (p : Point) :
    p ∉ innerQuadrant S u ↔
      p ∈ normalHalfPlane (u : Real.Angle) (supportValue S (u : Real.Angle) - 1) true false ∨
        p ∈ normalHalfPlane ((u + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false := by
  have h1 : (p ∈ innerQuadrant S u) ↔
      (inner ℝ p (normalVector (u : Real.Angle)) < supportValue S (u : Real.Angle) - 1 ∧
        inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle)) <
          supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) := Iff.rfl
  have h2 : (p ∈ normalHalfPlane (u : Real.Angle)
      (supportValue S (u : Real.Angle) - 1) true false) ↔
      (supportValue S (u : Real.Angle) - 1 ≤ inner ℝ p (normalVector (u : Real.Angle))) := Iff.rfl
  have h3 : (p ∈ normalHalfPlane ((u + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false) ↔
      (supportValue S ((u + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ p (normalVector ((u + Real.pi / 2 : ℝ) : Real.Angle))) := Iff.rfl
  rw [h1, h2, h3, not_and_or, not_lt, not_lt]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Angle Domain
-/

public section

noncomputable section

namespace MovingSofa

/-- Every upper normal of an angle set has strictly positive sine. -/
lemma angleDomain_subset_Ioo (Θ : AngleSet) : angleDomain Θ ⊆ Set.Ioo 0 Real.pi := by
  intro t ht
  rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
  · have h := Θ.interior t ht
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · have h := Θ.interior s hs
    constructor <;> linarith [h.1, h.2, Θ.angle_le, Real.pi_pos]
  · rcases ht with rfl | ht
    · constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · have ht : t = Real.pi / 2 := ht
      rw [ht]
      constructor <;> linarith [Real.pi_pos]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Area
-/

public section

noncomputable section

namespace MovingSofa

/-- Cap area minus niche area, with real Lebesgue area as in the classical interface. -/
@[expose]
def capAreaFunctional {ω : ℝ} (K : CapSpace ω) : ℝ :=
  ClassicalResults.area (K.1 : Set Point) - ClassicalResults.area (capNiche K)

/-- The cap space at a right angle. -/
abbrev RightAngleCapSpace := CapSpace (Real.pi / 2)

/-- The sofa area functional on the right-angle cap space. -/
@[expose]
def rightAngleAreaFunctional (K : RightAngleCapSpace) : ℝ := capAreaFunctional K

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Polygon.AngleSet`.
* `Polygon.BooleanFunctions`.
* `Polygon.Height.Space`.
* `Polygon.Height.Bounds`.
* `Polygon.Height.RaisedSupport`.
* `Polygon.Nef.Basic`.
* `Polygon.Nef.CapConstruction`.
* `Polygon.Nef.Cells`.
* `Polygon.Nef.Height`.
* `Polygon.PerturbationBounds`.
* `Polygon.Polyline.Basic`.
* `Polygon.Polyline.Displacement`.
* `Polygon.Polyline.Graph`.
* `Polygon.Polyline.Measure`.
* `Polygon.Polyline.Projection`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Angle Set
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The interior points of the uniform angular grid. -/
@[expose]
def uniformAngleSet (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (n : ℕ) (hn : 2 ≤ n) : AngleSet where
  angle := ω
  angle_pos := hω
  angle_le := hω'
  directions := (Finset.Ioo 0 n).image (fun i : ℕ ↦ (i : ℝ) / n * ω)
  nonempty := by
    apply Finset.Nonempty.image
    exact ⟨1, by simp; omega⟩
  interior := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hi, hin⟩ := Finset.mem_Ioo.mp hi
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have hin' : (i : ℝ) < n := by exact_mod_cast hin
    refine ⟨mul_pos (div_pos hi' hn') hω, ?_⟩
    exact (mul_lt_mul_of_pos_right ((div_lt_one hn').2 hin') hω).trans_eq (one_mul ω)

/-- A divisible grid refines the original grid. -/
theorem uniformAngleSet_directions_mono_of_dvd (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hmn : m ∣ n) :
    (uniformAngleSet ω hω hω' m hm).directions ⊆
      (uniformAngleSet ω hω hω' n hn).directions := by
  obtain ⟨k, rfl⟩ := hmn
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hj0, hjm⟩ := Finset.mem_Ioo.mp hj
  have hk : 0 < k := by nlinarith
  apply Finset.mem_image.mpr
  refine ⟨j * k, Finset.mem_Ioo.mpr ⟨Nat.mul_pos hj0 hk,
    Nat.mul_lt_mul_of_pos_right hjm hk⟩, ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [mul_div_mul_right _ _ hk']

/-- Monotone dyadic grids have nested directions. -/
theorem uniformAngleSet_directions_mono_of_dyadic (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : Monotone n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    {i j : ℕ} (hij : i ≤ j) :
    (uniformAngleSet ω hω hω' (n i) (hn i)).directions ⊆
      (uniformAngleSet ω hω hω' (n j) (hn j)).directions := by
  apply uniformAngleSet_directions_mono_of_dvd
  obtain ⟨a, ha⟩ := hdyadic i
  obtain ⟨b, hb⟩ := hdyadic j
  have hab : a ≤ b := by
    apply (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp
    simpa only [← ha, ← hb] using hmono hij
  rw [ha, hb]
  exact pow_dvd_pow 2 hab

/-- An interval longer than the mesh contains a grid direction. -/
theorem exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ) (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ ω) (hmesh : ω / n < b - a) :
    ∃ t ∈ (uniformAngleSet ω hω hω' n hn).directions, t ∈ Set.Ioo a b := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let j := ⌊a * n / ω⌋₊ + 1
  have hjpos : 0 < j := by dsimp [j]; omega
  have hfloor := Nat.floor_le (show 0 ≤ a * n / ω by positivity)
  have hfloor' := Nat.lt_floor_add_one (a * n / ω)
  have hjlo : a < (j : ℝ) / n * ω := by
    have h : a * n < (j : ℝ) * ω := by
      apply (div_lt_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one] using hfloor'
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hnpos).mpr h
  have hjhi : (j : ℝ) / n * ω ≤ a + ω / n := by
    have h : ((j : ℝ) - 1) * ω ≤ a * n := by
      apply (le_div_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hfloor
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    nlinarith
  have hjb : (j : ℝ) / n * ω < b := hjhi.trans_lt (by linarith)
  have hjn : j < n := by
    have h : (j : ℝ) / n < 1 := (mul_lt_mul_iff_left₀ hω).mp (by simpa using hjb.trans_le hb)
    exact_mod_cast (div_lt_one hnpos).mp h
  refine ⟨(j : ℝ) / n * ω, Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨hjpos, hjn⟩, rfl⟩,
    hjlo, hjb⟩

/-- An increasing sequence of grids eventually meets each interior open interval. -/
theorem eventually_exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ ω) :
    ∀ᶠ i in atTop, ∃ t ∈ (uniformAngleSet ω hω hω' (n i) (hn i)).directions,
      t ∈ Set.Ioo a b := by
  have hlim : Tendsto (fun i ↦ ω / (n i : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ω).comp hmono.tendsto_atTop
  filter_upwards [hlim.eventually_lt_const (sub_pos.mpr hab)] with i hi
  exact exists_uniformAngleSet_mem_Ioo ω hω hω' (n i) (hn i) ha hb hi

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Boolean Functions
-/

public section

namespace MovingSofa

/-- Boolean functions of finitely many Boolean variables. -/
abbrev BooleanFunction (n : ℕ) := (Fin n → Bool) → Bool

/-- Changing inputs from false to true cannot change a true output to false. -/
@[expose]
def IsMonotoneBooleanFunction {n : ℕ} (E : BooleanFunction n) : Prop :=
  ∀ P Q, (∀ i, P i = true → Q i = true) → E P = true → E Q = true

/-- Formulas built from variables using only conjunction and disjunction. -/
inductive PositiveBooleanFormula (n : ℕ) where
  | variable (i : Fin n)
  | conjunction (left right : PositiveBooleanFormula n)
  | disjunction (left right : PositiveBooleanFormula n)

/-- Evaluate a positive formula under a Boolean assignment. -/
def PositiveBooleanFormula.eval {n : ℕ} : PositiveBooleanFormula n → BooleanFunction n
  | .variable i => fun P ↦ P i
  | .conjunction left right => fun P ↦ left.eval P && right.eval P
  | .disjunction left right => fun P ↦ left.eval P || right.eval P

theorem positiveBooleanFormula_monotone {n : ℕ} (E : PositiveBooleanFormula n) :
    IsMonotoneBooleanFunction E.eval := by
  induction E <;>
    simp_all [IsMonotoneBooleanFunction, PositiveBooleanFormula.eval,
      Bool.and_eq_true, Bool.or_eq_true] <;>
    aesop

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Space
-/

public section

noncomputable section

namespace MovingSofa

/-- Point sets obtained by translating a polygonal cap with the fixed angle data. -/
@[expose]
def PolygonCapTranslateSpace (Θ : AngleSet) :=
  {S : Set Point // ∃ (K : PolygonCapSpace Θ) (q : Point),
    S = (fun p ↦ p + q) '' (K.val.val : Set Point)}

/-- Real wall heights indexed by the finite angle domain. -/
@[expose]
def PolygonHeightSpace (Θ : AngleSet) := angleDomain Θ → ℝ

/-- Extend a wall-height function by zero outside its angle domain. -/
@[expose]
def polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ angleDomain Θ then h ⟨t, ht⟩ else 0

/-- Intersect the two endpoint strips of unit width determined by the height data. -/
@[expose]
def polygonHeightParallelogram {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

/-- Cut the endpoint parallelogram by all upper wall half-planes. -/
@[expose]
def polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightParallelogram h ∩
    ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
      normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false

/-- Intersect the lower half-planes at the two endpoint directions. -/
@[expose]
def polygonHeightFan {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) true false

/-- Intersect the endpoint fan with the union of forbidden inner corners. -/
@[expose]
def polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set Point :=
  polygonHeightFan h ∩ ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue h t - 1) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue h (t + Real.pi / 2) - 1) false true

/-- The real area of the cap minus the real area of its niche. -/
@[expose]
def polygonHeightArea {Θ : AngleSet} (h : PolygonHeightSpace Θ) : ℝ :=
  ClassicalResults.area (polygonHeightCap h) - ClassicalResults.area (polygonHeightNiche h)

/-- Bundle the parallelogram, cap, fan, niche and area constructed from wall heights. -/
def polygonHeightExtensions {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Set Point × Set Point × Set Point × Set Point × ℝ :=
  (polygonHeightParallelogram h, polygonHeightCap h, polygonHeightFan h,
    polygonHeightNiche h, polygonHeightArea h)

/-- Take support values of a translated cap in the prescribed directions. -/
@[expose]
def polygonTranslateHeight {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    PolygonHeightSpace Θ := fun t ↦ supportValue K.val (t.val : Real.Angle)

/-- The niche and area functional associated with a translated cap. -/
@[expose]
def polygonTranslateExtensions {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    Set Point × ℝ :=
  (polygonHeightNiche (polygonTranslateHeight K), polygonHeightArea (polygonTranslateHeight K))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Bounds
-/

public section

namespace MovingSofa

/-- A height cap satisfies each selected upper half-plane constraint. -/
theorem polygonHeightCap_subset_normalHalfPlane {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightCap h ⊆ normalHalfPlane (t : Real.Angle)
      (polygonHeightValue h t) false false := by
  intro p hp
  rcases ht with ht | ht
  · exact Set.mem_iInter₂.mp hp.2 t ht
  · exact (Set.mem_iInter₂.mp hp.1 t ht).1

/-- The support of a reconstructed height cap is bounded by each defining height. -/
theorem supportValue_le_polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : ConvexBody Point) (hK : polygonHeightCap h = (K : Set Point))
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    supportValue K (t : Real.Angle) ≤ polygonHeightValue h t := by
  apply supportValue_le_of_subset_normalHalfPlane
  rw [← hK]
  exact polygonHeightCap_subset_normalHalfPlane h ht

/-- Unit width forces equality with the height of a distinguished strip. -/
theorem supportValue_eq_polygonHeightValue_of_width_one {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (K : ConvexBody Point)
    (hK : polygonHeightCap h = (K : Set Point)) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hw : supportValue K (t : Real.Angle) +
      supportValue K ((t + Real.pi : ℝ) : Real.Angle) = 1) :
    supportValue K (t : Real.Angle) = polygonHeightValue h t := by
  apply le_antisymm (supportValue_le_polygonHeightValue h K hK (Or.inr ht))
  have hopp : supportValue K ((t + Real.pi : ℝ) : Real.Angle) ≤
      1 - polygonHeightValue h t := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro p hp
    have hp' : p ∈ polygonHeightCap h := hK.symm ▸ hp
    have hl := (Set.mem_iInter₂.mp hp'.1 t ht).2
    change polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) at hl
    change inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ _
    rw [normalVector_add_pi, inner_neg_right]
    linarith
  linarith

/-- Niches grow with their heights when the fan remains fixed. -/
theorem polygonHeightNiche_mono_of_eq_endpoints {Θ : AngleSet}
    {h g : PolygonHeightSpace Θ} (hle : ∀ t, h t ≤ g t)
    (heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue h t = polygonHeightValue g t) :
    polygonHeightNiche h ⊆ polygonHeightNiche g := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t ≤ polygonHeightValue g t := by
    simpa only [polygonHeightValue, dite_eq_left ht] using hle ⟨t, ht⟩
  rintro p ⟨hpF, hpN⟩
  constructor
  · apply Set.mem_iInter₂.mpr
    intro t ht
    have hp := Set.mem_iInter₂.mp hpF t ht
    rwa [heq t ht] at hp
  · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_⟩
    · change inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue g t - 1
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue h t - 1 := hp.1
      exact hp₁.trans_le (sub_le_sub_right (hval t (Or.inl (Or.inl ht))) 1)
    · change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        polygonHeightValue g (t + Real.pi / 2) - 1
      have hp₂ : inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
          polygonHeightValue h (t + Real.pi / 2) - 1 := hp.2
      exact hp₂.trans_le (sub_le_sub_right
        (hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))) 1)

/-- Every polygon height niche is bounded. -/
theorem isBounded_polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Bornology.IsBounded (polygonHeightNiche h) := by
  let a := polygonHeightValue h (Real.pi / 2) - 1
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t - 1 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) - 1}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  apply hQ.subset
  rintro p ⟨hpF, hpN⟩
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
  apply Set.mem_iUnion₂.mpr
  refine ⟨t, ht, ?_, hp⟩
  have hpT := Set.mem_iInter₂.mp hpF (Real.pi / 2) (by simp)
  change a ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
  simpa [normalVector, frame, PiLp.inner_apply] using hpT

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Height / Raised Support
-/

public section

noncomputable section

namespace MovingSofa

/-- Increase one selected support height by the prescribed amount. -/
@[expose]
def raisedPolygonSupport {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ε : ℝ) : PolygonHeightSpace Θ := by
  classical
  exact fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle) +
    if s = t then ε else 0

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Basic
-/

public section

noncomputable section

namespace MovingSofa

/-- Normal direction, height and boundary conventions specifying a planar half-plane. -/
structure PlanarHalfPlaneData where
  /-- The angle of the half-plane’s normal vector. -/
  angle : Real.Angle
  /-- The scalar-product threshold defining the boundary line. -/
  height : ℝ
  /-- Select the side above the threshold when true, or below it when false. -/
  upper : Bool
  /-- Exclude the boundary line when true. -/
  strict : Bool

/-- The half-plane defined by the recorded normal, threshold and conventions. -/
@[expose]
def PlanarHalfPlaneData.carrier (H : PlanarHalfPlaneData) : Set Point :=
  normalHalfPlane H.angle H.height H.upper H.strict

/-- The line where the normal scalar product equals the recorded height. -/
@[expose]
def PlanarHalfPlaneData.boundaryLine (H : PlanarHalfPlaneData) : Set Point :=
  normalLine H.angle H.height

/-- Evaluate a Boolean function on the point’s memberships in a finite family of sets. -/
@[expose]
def booleanSet {n : ℕ} (E : BooleanFunction n) (H : Fin n → Set Point) : Set Point := by
  classical
  exact {p | E (fun i ↦ decide (p ∈ H i)) = true}

/-- The set is a finite Boolean combination of planar half-planes. -/
def IsNefPolygon (X : Set Point) : Prop :=
  ∃ (n : ℕ) (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData),
    X = booleanSet E (fun i ↦ (H i).carrier)

/-- A monotone Boolean representation uses the supplied walls with distinct boundary lines. -/
@[expose]
def IsSimpleNefPolygonWith {n : ℕ} (X : Set Point)
    (H : Fin n → PlanarHalfPlaneData) : Prop :=
  Function.Injective (fun i ↦ (H i).boundaryLine) ∧
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      X = booleanSet E (fun i ↦ (H i).carrier)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Cap Construction
-/

public section

noncomputable section

namespace MovingSofa

/-- The upper walls and two lower endpoint walls defining the polygonal cap. -/
@[expose]
def polygonCapWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ :
    PlanarHalfPlaneData)) '' angleDomain Θ ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

/-- The strict inner walls and two lower endpoint walls defining the polygonal niche. -/
@[expose]
def polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩ :
    PlanarHalfPlaneData)) ''
      ((Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

private theorem angleDomain_finite (Θ : AngleSet) : (angleDomain Θ).Finite := by
  unfold angleDomain
  exact (Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
      (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)

private theorem polygonInnerAngles_finite (Θ : AngleSet) :
    ((Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)).Finite :=
  Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))

private theorem polygonInnerAngles_subset_angleDomain (Θ : AngleSet) :
    (Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions) ⊆ angleDomain Θ := by
  intro t ht
  exact Or.inl ht

private theorem polygonInnerAngle_ne_endpoint {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ (Θ.directions : Set ℝ) ∪
      ((fun r : ℝ ↦ r + Real.pi / 2) '' Θ.directions))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : s ≠ t := by
  rcases hs with hs | ⟨r, hr, rfl⟩
  · have hsI := Θ.interior s hs
    rcases ht with ht | ht
    · intro hst
      exact hsI.2.ne (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      exact (ne_of_lt (hsI.2.trans_le Θ.angle_le)) (hst.trans ht')
  · have hrI := Θ.interior r hr
    rcases ht with ht | ht
    · intro hst
      have hgt : Θ.angle < r + Real.pi / 2 := by
        linarith [Θ.angle_le, hrI.1, Real.pi_pos]
      exact hgt.ne' (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      have hgt : Real.pi / 2 < r + Real.pi / 2 := by linarith [hrI.1]
      exact hgt.ne' (hst.trans ht')

private theorem polygonCapWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonCapWalls h).Finite := by
  unfold polygonCapWalls
  exact ((angleDomain_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private theorem polygonNicheWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonNicheWalls h).Finite := by
  unfold polygonNicheWalls
  exact ((polygonInnerAngles_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private def polygonUpperWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩

private def polygonLowerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩

private def polygonInnerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩

private theorem polygonCapWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonCapWalls h =
      polygonUpperWall h '' angleDomain Θ ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem polygonNicheWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonNicheWalls h =
      polygonInnerWall h ''
          ((Θ.directions : Set ℝ) ∪
            ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem boundaryLine_injOn_polygonCapWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonCapWalls h) := by
  intro A hA B hB hline
  rw [polygonCapWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht)).mp hline
    simp [hst.1]
  · have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ htD)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
    exfalso
    linarith
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ ht)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private theorem boundaryLine_injOn_polygonNicheWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonNicheWalls h) := by
  intro A hA B hB hline
  rw [polygonNicheWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint hs ht hst.1).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint ht hs hst.1.symm).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private def PositiveBooleanFormula.conjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .conjunction E (conjunctions default Es)

private def PositiveBooleanFormula.disjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .disjunction E (disjunctions default Es)

private theorem PositiveBooleanFormula.conjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.conjunctions Es).eval P = true ↔
      default.eval P = true ∧ ∀ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.conjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.conjunctions, PositiveBooleanFormula.eval, ih,
        and_left_comm]

private theorem PositiveBooleanFormula.disjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.disjunctions Es).eval P = true ↔
      default.eval P = true ∨ ∃ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.disjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.disjunctions, PositiveBooleanFormula.eval, ih,
        or_left_comm]

private theorem mem_polygonHeightCap_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightCap h ↔
      ∀ W ∈ polygonCapWalls h, p ∈ W.carrier := by
  simp only [polygonHeightCap, polygonHeightParallelogram, polygonCapWalls,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hendpoint, hinner⟩ W
    rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · change p ∈ normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false
      rcases ht with ht | ht
      · exact hinner t ht
      · exact (hendpoint t ht).1
    · change p ∈ normalHalfPlane (t : Real.Angle)
          (polygonHeightValue h t - 1) true false
      exact (hendpoint t ht).2
  · intro hall
    refine ⟨?_, ?_⟩
    · intro t ht
      constructor
      · exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · exact hall (polygonLowerWall h t) (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem mem_polygonHeightNiche_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightNiche h ↔
      (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        p ∈ (polygonLowerWall h t).carrier) ∧
      ∃ t ∈ Θ.directions,
        p ∈ (polygonInnerWall h t).carrier ∧
        p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier := by
  unfold polygonHeightNiche polygonHeightFan
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hfan, hniche⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hfan t ht
    · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hniche
      exact ⟨t, ht, hp⟩
  · rintro ⟨hfan, t, ht, hp⟩
    refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    exact hp

private theorem exists_polygonHeightCap_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightCap h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonCapWalls h
  have hSfinite : S.Finite := polygonCapWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonCapWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonCapWalls h (e i).2 (e j).2 hij
  have hupperω : polygonUpperWall h Θ.angle ∈ S := by
    exact Or.inl ⟨Θ.angle, by simp [angleDomain], rfl⟩
  let i₀ : Fin n := e.symm ⟨polygonUpperWall h Θ.angle, hupperω⟩
  let varList : List (PositiveBooleanFormula n) :=
    List.ofFn fun i : Fin n ↦ PositiveBooleanFormula.variable i
  let formula : PositiveBooleanFormula n :=
    (PositiveBooleanFormula.variable i₀).conjunctions varList
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightCap_iff_walls]
  change (∀ W ∈ polygonCapWalls h, p ∈ W.carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔ ∀ i, P i = true := by
    rw [show formula = (PositiveBooleanFormula.variable i₀).conjunctions varList by rfl,
      PositiveBooleanFormula.conjunctions_eval_eq_true]
    simp [varList, PositiveBooleanFormula.eval]
    aesop
  rw [hformula]
  constructor
  · intro hall i
    apply decide_eq_true
    exact hall (H i) (e i).2
  · intro hall W hW
    obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
    have hi' : H i = W := congrArg Subtype.val hi
    subst W
    exact of_decide_eq_true (hall i)

private theorem exists_polygonHeightNiche_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightNiche h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonNicheWalls h
  have hSfinite : S.Finite := polygonNicheWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonNicheWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonNicheWalls h (e i).2 (e j).2 hij
  have hlowerω : polygonLowerWall h Θ.angle ∈ S := by
    exact Or.inr ⟨Θ.angle, by simp, rfl⟩
  have hlowerT : polygonLowerWall h (Real.pi / 2) ∈ S := by
    exact Or.inr ⟨Real.pi / 2, by simp, rfl⟩
  have hinner (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h t ∈ S := by
    exact Or.inl ⟨t, Or.inl ht, rfl⟩
  have hinnerShift (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h (t + Real.pi / 2) ∈ S := by
    exact Or.inl ⟨t + Real.pi / 2, Or.inr ⟨t, ht, rfl⟩, rfl⟩
  let iω : Fin n := e.symm ⟨polygonLowerWall h Θ.angle, hlowerω⟩
  let iT : Fin n := e.symm ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩
  let innerIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h t, hinner t t.property⟩
  let shiftedIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩
  let pairFormula : Θ.directions → PositiveBooleanFormula n :=
    fun t ↦ .conjunction (.variable (innerIndex t)) (.variable (shiftedIndex t))
  let t₀ : Θ.directions := ⟨Θ.nonempty.choose, Θ.nonempty.choose_spec⟩
  let pairList : List (PositiveBooleanFormula n) :=
    Θ.directions.attach.toList.map pairFormula
  let endpointFormula : PositiveBooleanFormula n :=
    .conjunction (.variable iω) (.variable iT)
  let interiorFormula : PositiveBooleanFormula n :=
    (pairFormula t₀).disjunctions pairList
  let formula : PositiveBooleanFormula n :=
    .conjunction endpointFormula interiorFormula
  have hHiω : H iω = polygonLowerWall h Θ.angle := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h Θ.angle, hlowerω⟩)
  have hHiT : H iT = polygonLowerWall h (Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩)
  have hHinner (t : Θ.directions) :
      H (innerIndex t) = polygonInnerWall h t := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h t, hinner t t.property⟩)
  have hHshift (t : Θ.directions) :
      H (shiftedIndex t) = polygonInnerWall h (t + Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩)
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightNiche_iff_walls]
  change ((∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      p ∈ (polygonLowerWall h t).carrier) ∧
    ∃ t ∈ Θ.directions,
      p ∈ (polygonInnerWall h t).carrier ∧
      p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hpair (t : Θ.directions) (P : Fin n → Bool) :
      (pairFormula t).eval P = true ↔
        P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    simp [pairFormula, PositiveBooleanFormula.eval]
  have hinterior (P : Fin n → Bool) :
      interiorFormula.eval P = true ↔
        ∃ t : Θ.directions,
          P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show interiorFormula = (pairFormula t₀).disjunctions pairList by rfl,
      PositiveBooleanFormula.disjunctions_eval_eq_true]
    simp only [hpair]
    constructor
    · rintro (ht₀ | ⟨E, hE, hEval⟩)
      · exact ⟨t₀, ht₀⟩
      · rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl] at hE
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hE
        exact ⟨t, (hpair t P).mp hEval⟩
    · rintro ⟨t, hEval⟩
      right
      refine ⟨pairFormula t, ?_, (hpair t P).mpr hEval⟩
      rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl]
      exact List.mem_map.mpr ⟨t, by simp, rfl⟩
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔
        (P iω = true ∧ P iT = true) ∧
          ∃ t : Θ.directions,
            P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show formula = .conjunction endpointFormula interiorFormula by rfl]
    simp only [PositiveBooleanFormula.eval, Bool.and_eq_true, hinterior]
    simp [endpointFormula, PositiveBooleanFormula.eval]
  rw [hformula]
  constructor
  · rintro ⟨hendpoint, t, ht, htinner, htshift⟩
    let ts : Θ.directions := ⟨t, ht⟩
    refine ⟨⟨?_, ?_⟩, ts, ?_, ?_⟩
    · apply decide_eq_true
      rw [hHiω]
      exact hendpoint Θ.angle (by simp)
    · apply decide_eq_true
      rw [hHiT]
      exact hendpoint (Real.pi / 2) (by simp)
    · apply decide_eq_true
      rw [hHinner ts]
      exact htinner
    · apply decide_eq_true
      rw [hHshift ts]
      exact htshift
  · rintro ⟨⟨hω, hT⟩, t, htinner, htshift⟩
    refine ⟨?_, t, t.property, ?_, ?_⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        rw [← hHiω]
        exact of_decide_eq_true hω
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        rw [← hHiT]
        exact of_decide_eq_true hT
    · rw [← hHinner t]
      exact of_decide_eq_true htinner
    · rw [← hHshift t]
      exact of_decide_eq_true htshift

theorem polygonCap_niche_simpleNef (Θ : AngleSet) (h : PolygonHeightSpace Θ) :
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧ IsSimpleNefPolygonWith (polygonHeightCap h) H) ∧
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧ IsSimpleNefPolygonWith (polygonHeightNiche h) H) := by
  exact ⟨exists_polygonHeightCap_simpleNef Θ h, exists_polygonHeightNiche_simpleNef Θ h⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Cells
-/

public section

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma monotoneBoolean_update_false {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E (Function.update P i false) = true → E P = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp at hj
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_update_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true → E (Function.update P i true) = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_eval_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true ↔ E (Function.update P i false) = true ∨
      (P i = true ∧ E (Function.update P i true) = true) := by
  constructor
  · intro h
    cases hp : P i
    · left
      rwa [← hp, Function.update_eq_self]
    · exact Or.inr ⟨rfl, monotoneBoolean_update_true hE P i h⟩
  · rintro (h | ⟨hp, h⟩)
    · exact monotoneBoolean_update_false hE P i h
    · rwa [(Function.update_eq_self_iff).mpr hp.symm] at h

lemma booleanSet_update_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S : Set Point) :
    booleanSet E (Function.update H i S) =
      booleanSet E (Function.update H i ∅) ∪
        (S ∩ booleanSet E (Function.update H i Set.univ)) := by
  classical
  ext p
  have hfun (T : Set Point) :
      (fun j ↦ decide (p ∈ Function.update H i T j)) =
        Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ T)) := by
    funext j
    by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, hfun]
  simp only [Set.mem_empty_iff_false, decide_false, Set.mem_univ, decide_true]
  have h := monotoneBoolean_eval_iff hE
    (Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ S))) i
  simpa only [Function.update_idem, Function.update_self, decide_eq_true_eq] using h

lemma booleanSet_update_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S T : Set Point) :
    booleanSet E (Function.update H i S) \ booleanSet E (Function.update H i T) =
      (S \ T) ∩ (booleanSet E (Function.update H i Set.univ) \
        booleanSet E (Function.update H i ∅)) := by
  rw [booleanSet_update_eq hE H i S, booleanSet_update_eq hE H i T]
  ext p
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
  tauto

lemma booleanSet_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) {H G : Fin n → Set Point}
    (hHG : ∀ i, H i ⊆ G i) : booleanSet E H ⊆ booleanSet E G := by
  classical
  intro p hp
  apply hE _ _ ?_ hp
  intro i hi
  simp only [decide_eq_true_eq] at hi ⊢
  exact hHG i hi

/-- The points realizing exactly the specified Boolean membership pattern. -/
def booleanCell {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool) : Set Point :=
  ⋂ j, if P j then H j else (H j)ᶜ

/-- The vector of membership decisions for a point in a finite set family. -/
@[expose]
def setMembershipPattern {n : ℕ} (H : Fin n → Set Point) (p : Point) : Fin n → Bool := by
  classical
  exact fun j ↦ decide (p ∈ H j)

lemma mem_booleanCell_iff {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool)
    (p : Point) :
    p ∈ booleanCell H P ↔ setMembershipPattern H p = P := by
  classical
  simp only [booleanCell, Set.mem_iInter]
  constructor
  · intro hp
    funext j
    have hj := hp j
    cases hP : P j <;> simp only [hP, Bool.false_eq_true, ↓reduceIte, Set.mem_compl_iff,
      setMembershipPattern,
      decide_eq_false_iff_not, decide_eq_true_eq] at hj ⊢ <;> exact hj
  · intro hp j
    have hj := congrFun hp j
    cases hP : P j <;> simp only [setMembershipPattern, hP, decide_eq_false_iff_not,
      Bool.false_eq_true, ↓reduceIte,
      Set.mem_compl_iff, decide_eq_true_eq] at hj ⊢ <;> exact hj

lemma booleanSet_eq_iUnion_booleanCell {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → Set Point) :
    booleanSet E H = ⋃ P : Fin n → Bool, if E P = true then booleanCell H P else ∅ := by
  classical
  ext p
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_ite_empty_right]
  constructor
  · intro hp
    change E (setMembershipPattern H p) = true at hp
    refine ⟨setMembershipPattern H p, ?_, (mem_booleanCell_iff H _ p).mpr rfl⟩
    exact hp
  · rintro ⟨P, hEP, hp⟩
    have hpat := (mem_booleanCell_iff H P p).mp hp
    calc
      E (fun j ↦ decide (p ∈ H j)) = E (setMembershipPattern H p) := by
        congr 1
      _ = E P := congrArg E hpat
      _ = true := hEP

/-- Intersect the closed sides of each wall selected by the Boolean pattern. -/
@[expose]
def closedBooleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) : Set Point :=
  ⋂ j, normalHalfPlane (H j).angle (H j).height
    (if P j then (H j).upper else !(H j).upper) false

lemma mem_booleanCell_iff_mem_closedBooleanCell_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (p : Point)
    (hp : ∀ j, inner ℝ p (normalVector (H j).angle) ≠ (H j).height) :
    p ∈ booleanCell (fun j ↦ (H j).carrier) P ↔ p ∈ closedBooleanCell H P := by
  simp only [booleanCell, closedBooleanCell, Set.mem_iInter]
  constructor <;> intro h j
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith

/-- Switching the selected input from false to true switches the output to true. -/
@[expose]
def IsActiveBooleanPattern {n : ℕ} (E : BooleanFunction n) (i : Fin n)
    (P : Fin n → Bool) : Prop :=
  E (Function.update P i false) = false ∧
    E (Function.update P i true) = true

/-- All input patterns for which the selected Boolean variable is active. -/
@[expose]
def activeBooleanPatterns {n : ℕ} (E : BooleanFunction n) (i : Fin n) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (IsActiveBooleanPattern E i)

/-- The set gained by making the selected wall universally true rather than false. -/
@[expose]
def activeBooleanRegion {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) : Set Point :=
  booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
    booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)

lemma mem_activeBooleanRegion_iff {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point) :
    p ∈ activeBooleanRegion E H i ↔
      IsActiveBooleanPattern E i (setMembershipPattern (fun j ↦ (H j).carrier) p) := by
  classical
  unfold activeBooleanRegion IsActiveBooleanPattern
  simp only [Set.mem_sdiff, booleanSet, Set.mem_ofPred_eq]
  have huniv : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i Set.univ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  have hempty : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i ∅ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i false := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  rw [huniv, hempty]
  cases hfalse : E (Function.update (setMembershipPattern
      (fun j ↦ (H j).carrier) p) i false) <;> simp

lemma measurableSet_planarHalfPlane_carrier (H : PlanarHalfPlaneData) :
    MeasurableSet H.carrier := by
  cases hu : H.upper <;> cases hs : H.strict <;>
    simp only [PlanarHalfPlaneData.carrier, normalHalfPlane, hu, hs,
      Bool.false_eq_true, ↓reduceIte] <;> measurability

lemma eventually_mem_carrier_iff_of_not_mem_boundaryLine (H : PlanarHalfPlaneData)
    (p : Point) (hp : p ∉ H.boundaryLine) :
    ∀ᶠ q in 𝓝 p, (q ∈ H.carrier ↔ p ∈ H.carrier) := by
  have hpne : inner ℝ p (normalVector H.angle) ≠ H.height := hp
  have hcont : Continuous (fun q : Point ↦ inner ℝ q (normalVector H.angle)) := by
    fun_prop
  rcases lt_or_gt_of_ne hpne with hplt | hpgt
  · have hev : ∀ᶠ q in 𝓝 p, inner ℝ q (normalVector H.angle) < H.height :=
      hcont.continuousAt.eventually_lt continuousAt_const hplt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith
  · have hev : ∀ᶠ q in 𝓝 p, H.height < inner ℝ q (normalVector H.angle) :=
      continuousAt_const.eventually_lt hcont.continuousAt hpgt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith

lemma eventually_setMembershipPattern_eq_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point)
    (hp : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    ∀ᶠ q in 𝓝 p, ∀ j, j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j := by
  suffices ∀ᶠ q in 𝓝 p, ∀ j ∈ (Set.univ : Set (Fin n)), j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j by
    exact this.mono fun q hq j ↦ hq j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hji : j = i
  · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
  · filter_upwards [eventually_mem_carrier_iff_of_not_mem_boundaryLine (H j) p
      (hp j hji)] with q hq
    intro _
    simp only [setMembershipPattern]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hq

lemma measurableSet_booleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) :
    MeasurableSet (booleanCell (fun j ↦ (H j).carrier) P) := by
  apply MeasurableSet.iInter
  intro j
  cases hP : P j
  · simpa [booleanCell, hP] using (measurableSet_planarHalfPlane_carrier (H j)).compl
  · simpa [booleanCell, hP] using measurableSet_planarHalfPlane_carrier (H j)

lemma measurableSet_booleanSet {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) :
    MeasurableSet (booleanSet E (fun j ↦ (H j).carrier)) := by
  rw [booleanSet_eq_iUnion_booleanCell]
  apply MeasurableSet.iUnion
  intro P
  by_cases hP : E P = true
  · simpa [hP] using measurableSet_booleanCell H P
  · simp [hP]

lemma monotoneBoolean_update_false_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    E (Function.update P i false) = true →
      E (Function.update P i true) = true := by
  intro htrue
  apply hE _ _ _ htrue
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma not_isActiveBooleanPattern_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    ¬IsActiveBooleanPattern E i P ↔
      E (Function.update P i false) = E (Function.update P i true) := by
  unfold IsActiveBooleanPattern
  constructor
  · intro hnot
    cases hf : E (Function.update P i false) <;>
      cases ht : E (Function.update P i true)
    · rfl
    · exact (hnot ⟨hf, ht⟩).elim
    · have hcontra := monotoneBoolean_update_false_true hE i P hf
      rw [ht] at hcontra
      exact (Bool.false_ne_true hcontra).elim
    · rfl
  · intro heq hactive
    rw [hactive.1, hactive.2] at heq
    exact Bool.false_ne_true heq

end MovingSofa.Nef

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Nef / Height
-/

public section

noncomputable section

namespace MovingSofa

/-- Change one wall’s height by `δ` in a Boolean half-plane representation. -/
@[expose]
def perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) : Set Point :=
  booleanSet E (fun j ↦
    (if j = i then { H j with height := (H j).height + δ } else H j).carrier)

end MovingSofa

namespace MovingSofa.Nef

open Filter Topology

lemma perturbNefHeight_eq_update {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ = booleanSet E
      (Function.update (fun j ↦ (H j).carrier) i
        ({ H i with height := (H i).height + δ }).carrier) := by
  unfold perturbNefHeight
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, Function.update_of_ne]

lemma perturbNefHeight_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      (({ H i with height := (H i).height + δ }).carrier \
        ({ H i with height := (H i).height + ε }).carrier) ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_eq_update, perturbNefHeight_eq_update]
  exact booleanSet_update_sdiff hE _ _ _ _

/-- The half-open strip-height interval matching the wall’s strictness convention. -/
def heightInterval (strict : Bool) (h δ ε : ℝ) : Set ℝ :=
  if strict then Set.Ico (h + ε) (h + δ) else Set.Ioc (h + ε) (h + δ)

lemma measurableSet_heightInterval (strict : Bool) (h δ ε : ℝ) :
    MeasurableSet (heightInterval strict h δ ε) := by
  cases strict <;> simp [heightInterval]

lemma integral_heightInterval_eq_intervalIntegral (strict : Bool)
    (h δ ε : ℝ) (f : ℝ → ℝ) (hεδ : ε ≤ δ) :
    (∫ x in heightInterval strict h δ ε, f x) =
      ∫ x in h + ε..h + δ, f x := by
  have hle : h + ε ≤ h + δ := by linarith
  cases strict
  · simp only [heightInterval, Bool.false_eq_true, ↓reduceIte]
    exact (intervalIntegral.integral_of_le hle).symm
  · simp only [heightInterval, ↓reduceIte]
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le hle).symm

lemma mem_heightInterval_bounds {strict : Bool} {h δ ε x : ℝ}
    (hx : x ∈ heightInterval strict h δ ε) :
    h + ε ≤ x ∧ x ≤ h + δ := by
  cases strict <;> simp [heightInterval] at hx <;>
    constructor <;> linarith [hx.1, hx.2]

lemma carrier_sdiff_carrier_eq_heightInterval (H : PlanarHalfPlaneData)
    (hSide : H.upper = false) (δ ε : ℝ) :
    ({ H with height := H.height + δ }).carrier \
        ({ H with height := H.height + ε }).carrier =
      {p | inner ℝ p (normalVector H.angle) ∈
        heightInterval H.strict H.height δ ε} := by
  ext p
  cases hs : H.strict <;>
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hSide,
      heightInterval] <;> tauto

lemma perturbNefHeight_sdiff_eq_heightInterval {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      {p | inner ℝ p (normalVector (H i).angle) ∈
        heightInterval (H i).strict (H i).height δ ε} ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_sdiff hE H i δ ε,
    carrier_sdiff_carrier_eq_heightInterval (H i) hSide]

lemma perturbNefHeight_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) :
    Monotone (perturbNefHeight E H i) := by
  intro δ ε hδε
  apply booleanSet_mono hE
  intro j p hp
  by_cases hji : j = i
  · subst j
    simp only at hp ⊢
    change p ∈ normalHalfPlane (H i).angle ((H i).height + δ) (H i).upper
      (H i).strict at hp
    change p ∈ normalHalfPlane (H i).angle ((H i).height + ε) (H i).upper
      (H i).strict
    cases hstrict : (H i).strict <;>
      simp only [normalHalfPlane, hSide, hstrict, Bool.false_eq_true, ite_false,
        ite_true, Set.mem_ofPred_eq] at hp ⊢
    · exact hp.trans (add_le_add_right hδε _)
    · exact hp.trans_le (add_le_add_right hδε _)
  · simpa only [ite_eq_right hji] using hp

lemma measurableSet_perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    MeasurableSet (perturbNefHeight E H i δ) := by
  unfold perturbNefHeight
  apply measurableSet_booleanSet

lemma area_perturb_sub_eq_volume_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      (MeasureTheory.volume
        (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal := by
  have hmono := perturbNefHeight_mono hE H i hSide hεδ
  have hfiniteδ : MeasureTheory.volume (perturbNefHeight E H i δ) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound δ hδ))
      MeasureTheory.measure_closedBall_lt_top
  have hfiniteε : MeasureTheory.volume (perturbNefHeight E H i ε) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound ε hε))
      MeasureTheory.measure_closedBall_lt_top
  rw [ClassicalResults.area, ClassicalResults.area,
    ← ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hmono) hfiniteδ,
    ← MeasureTheory.measure_sdiff hmono
      (measurableSet_perturbNefHeight E H i ε).nullMeasurableSet hfiniteε]

lemma perturbNefHeight_zero {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) :
    perturbNefHeight E H i 0 = booleanSet E (fun j ↦ (H j).carrier) := by
  ext p
  simp [perturbNefHeight, PlanarHalfPlaneData.carrier]

end MovingSofa.Nef

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Perturbation Bounds
-/

public section

noncomputable section

namespace MovingSofa

/-- The polygonal cap with independently specified upper and lower wall heights. -/
@[expose]
def independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false

/-- The polygonal niche determined by independently specified lower wall heights. -/
@[expose]
def independentWallNiche {Θ : AngleSet} (lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue lower (t + Real.pi / 2)) false true

theorem polygonPerturbation_uniform_bounds (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ upper lower : PolygonHeightSpace Θ,
        (∀ t, |upper t - h t| ≤ ε₀) →
        (∀ t, |lower t - (h t - 1)| ≤ ε₀) →
        independentWallCap upper lower ⊆ Metric.closedBall 0 R ∧
        independentWallNiche lower ⊆ Metric.closedBall 0 R := by
  let a := polygonHeightValue h (Real.pi / 2) - 2
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t + 2 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) + 2}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  obtain ⟨R, hR, hbound⟩ := hQ.exists_pos_norm_le
  refine ⟨R, 1, hR, zero_lt_one, ?_⟩
  intro upper lower hu hl
  have huv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue upper t ≤ polygonHeightValue h t + 1 := by
    have hh := (abs_le.mp (hu ⟨t, ht⟩)).2
    simp only [polygonHeightValue, dite_eq_left ht]
    linarith
  have hlv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t - 2 ≤ polygonHeightValue lower t ∧
      polygonHeightValue lower t ≤ polygonHeightValue h t := by
    have hh := abs_le.mp (hl ⟨t, ht⟩)
    simp only [polygonHeightValue, dite_eq_left ht]
    constructor <;> linarith [hh.1, hh.2]
  have hy {p : Point}
      (hp : p ∈ ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
      a ≤ p 1 := by
    have hp' := Set.mem_iInter₂.mp hp (Real.pi / 2) (by simp)
    have hb := (hlv (Real.pi / 2) (Or.inr (by simp))).1
    have hp'' : polygonHeightValue lower (Real.pi / 2) ≤ p 1 := by
      simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hp'
    exact hb.trans hp''
  have hball {p : Point} (hp : p ∈ ⋃ t ∈ Θ.directions, Q t) :
      p ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound p hp
  constructor
  · intro p hp
    apply hball
    obtain ⟨t, ht⟩ := Θ.nonempty
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · apply hy
      exact Set.mem_iInter₂.mpr fun s hs ↦ (Set.mem_iInter₂.mp hp.1 s hs).2
    · have hb := Set.mem_iInter₂.mp hp.2 t (Or.inl ht)
      change inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue upper t at hb
      have hu' := huv t (Or.inl (Or.inl ht))
      linarith
    · have hb := Set.mem_iInter₂.mp hp.2 (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
      change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
        polygonHeightValue upper (t + Real.pi / 2) at hb
      have hu' := huv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))
      linarith
  · rintro p ⟨hpF, hpN⟩
    apply hball
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, hy hpF, ?_, ?_⟩
    · have hb := (hlv t (Or.inl (Or.inl ht))).2
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue lower t := hp.1
      exact hp₁.trans_le (by linarith)
    · have hb := (hlv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))).2
      exact hp.2.trans_le (by linarith)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Basic
-/

public section

namespace MovingSofa

/-- A finite vertex sequence whose horizontal coordinates strictly increase. -/
structure XMonotonePolylineData where
  /-- The number of consecutive line segments in the polyline. -/
  edges : ℕ
  /-- The ordered sequence of polyline vertices. -/
  vertices : Fin (edges + 1) → Point
  increasing : StrictMono (fun i ↦ vertices i 0)

/-- The union of the segments between consecutive vertices. -/
@[expose]
def XMonotonePolylineData.carrier (p : XMonotonePolylineData) : Set Point :=
  ⋃ i : Fin p.edges, segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)

/-- The set is the carrier of a polyline with strictly increasing horizontal coordinates. -/
def IsXMonotonePolyline (S : Set Point) : Prop :=
  ∃ p : XMonotonePolylineData, S = p.carrier

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Displacement
-/

public section

noncomputable section

namespace MovingSofa

/-- The horizontal displacement of a rightward edge is its length times the sine of its normal. -/
lemma dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    dist a b * Real.sin t = b 0 - a 0 := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hsin := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hr : r < 0 := by nlinarith
  have hn : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [EuclideanSpace.norm_sq_eq]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hdist : dist a b = -r := by
    rw [dist_comm, dist_eq_norm, ← hvec, norm_smul, hn, mul_one,
      Real.norm_eq_abs, abs_of_neg hr]
  rw [hdist]
  linarith

/-- The sine-weighted edge lengths telescope to the horizontal endpoint displacement. -/
lemma XMonotonePolylineData.sum_dist_mul_sin
    (p : XMonotonePolylineData) (t : Fin p.edges → ℝ)
    (ht : ∀ i, t i ∈ Set.Ioo 0 Real.pi)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ i : Fin p.edges,
      dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) =
        p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  have hedge (i : Fin p.edges) := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero
    (ht i) (p.increasing i.castSucc_lt_succ) (horth i)
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  have hlast := Fin.sum_univ_castSucc (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  linarith

/-- A nonvertical segment has at most one normal angle strictly between zero and pi. -/
lemma eq_of_inner_sub_normalVector_eq_zero {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hab : a 0 < b 0)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hz : Real.sin (s - t) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_pos.mpr hab).ne'
  have := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hz
  linarith

/-- Grouping edge lengths by normal preserves the horizontal displacement identity. -/
lemma XMonotonePolylineData.sum_normal_lengths_mul_sin
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0) :
    ∑ t ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t =
      p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  classical
  choose t ht horth using hlabels
  calc
    _ = ∑ i : Fin p.edges, ∑ u ∈ D,
        (if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin u := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin p.edges,
        dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (t i)]
      · rw [ite_eq_left (horth i)]
      · intro u hu hut
        have hne : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
            (normalVector (u : Real.Angle)) ≠ 0 := by
          intro hzero
          exact hut (eq_of_inner_sub_normalVector_eq_zero (hD u hu) (hD _ (ht i))
            (p.increasing i.castSucc_lt_succ) hzero (horth i))
        simp [hne]
      · exact fun hnot ↦ (hnot (ht i)).elim
    _ = _ := p.sum_dist_mul_sin t (fun i ↦ hD _ (ht i)) horth

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Graph
-/

public section

noncomputable section

namespace MovingSofa

/-- The point on the graph of a real-valued function above a given abscissa. -/
@[expose]
def pointOnGraph (f : ℝ → ℝ) (x : ℝ) : Point := !₂[x, f x]

/-- Evaluation of the affine function with slope-intercept pair `c`. -/
@[expose]
def affineValue (c : ℝ × ℝ) (x : ℝ) : ℝ := c.1 * x + c.2

/-- An affine real-valued function is continuous. -/
theorem continuous_affineValue (c : ℝ × ℝ) : Continuous (affineValue c) := by
  unfold affineValue
  fun_prop

private def affineCrossings (L : Finset (ℝ × ℝ)) : Set ℝ :=
  ⋃ c ∈ L, ⋃ d ∈ L.erase c, {x | affineValue c x = affineValue d x}

private theorem finite_affineValue_eq_of_ne {c d : ℝ × ℝ} (hcd : c ≠ d) :
    {x | affineValue c x = affineValue d x}.Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, affineValue] at hx hy
  by_cases hm : c.1 = d.1
  · rw [hm] at hx
    have hb : c.2 = d.2 := by linarith
    exact (hcd (Prod.ext hm hb)).elim
  · have hs : c.1 - d.1 ≠ 0 := sub_ne_zero.mpr hm
    have hprod : (c.1 - d.1) * (x - y) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hs)

private theorem finite_affineCrossings (L : Finset (ℝ × ℝ)) :
    (affineCrossings L).Finite := by
  apply L.finite_toSet.biUnion
  intro c hc
  apply (L.erase c).finite_toSet.biUnion
  intro d hd
  exact finite_affineValue_eq_of_ne (Finset.ne_of_mem_erase hd).symm

@[simp] theorem pointOnGraph_apply_zero (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 0 = x := by
  rfl

@[simp] theorem pointOnGraph_apply_one (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 1 = f x := by
  rfl

/-- The closed vertical epigraph of a real-valued function. -/
@[expose]
def verticalEpigraph (f : ℝ → ℝ) : Set Point :=
  {p | f (p 0) ≤ p 1}

/-- A continuous function has a closed vertical epigraph. -/
theorem isClosed_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    IsClosed (verticalEpigraph f) := by
  exact isClosed_le
    (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)

private theorem pointOnGraph_not_mem_interior_verticalEpigraph
    (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x ∉ interior (verticalEpigraph f) := by
  intro hx
  let q : ℕ → Point := fun n ↦ !₂[x, f x - (1 : ℝ) / (n + 1)]
  have hq : Filter.Tendsto q Filter.atTop (nhds (pointOnGraph f x)) := by
    apply (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Filter.Tendsto (fun _ : ℕ ↦ x) Filter.atTop (nhds x)
      exact tendsto_const_nhds
    · change Filter.Tendsto (fun n : ℕ ↦ f x - (1 : ℝ) / (n + 1))
        Filter.atTop (nhds (f x))
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hev : ∀ᶠ n in Filter.atTop, q n ∈ interior (verticalEpigraph f) :=
    hq (isOpen_interior.mem_nhds hx)
  obtain ⟨n, hn⟩ := hev.exists
  have hn' := interior_subset hn
  change f x ≤ f x - (1 : ℝ) / (n + 1) at hn'
  have : 0 < (1 : ℝ) / (n + 1) := by positivity
  linarith

/-- The frontier of a continuous vertical epigraph is its graph. -/
theorem frontier_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    frontier (verticalEpigraph f) = Set.range (pointOnGraph f) := by
  have hclosed := isClosed_verticalEpigraph hf
  ext p
  constructor
  · intro hp
    have hpE : p ∈ verticalEpigraph f := by
      exact hclosed.closure_eq ▸ frontier_subset_closure hp
    have hpNotInt : p ∉ interior (verticalEpigraph f) :=
      (mem_frontier_iff_notMem_interior hpE).mp hp
    have heq : f (p 0) = p 1 := by
      apply le_antisymm hpE
      apply le_of_not_gt
      intro hlt
      apply hpNotInt
      have hopen : IsOpen {q : Point | f (q 0) < q 1} :=
        isOpen_lt
          (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
          (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)
      exact interior_maximal (fun q hq ↦ by
        change f (q 0) ≤ q 1
        exact hq.le) hopen hlt
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp [pointOnGraph]
    · simpa [pointOnGraph] using heq
  · rintro ⟨x, rfl⟩
    apply (mem_frontier_iff_notMem_interior (s := verticalEpigraph f)
      (x := pointOnGraph f x) (by
        change f x ≤ f x
        exact le_rfl)).mpr
    exact pointOnGraph_not_mem_interior_verticalEpigraph f x

private def graphPolyline (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) : XMonotonePolylineData where
  edges := n
  vertices i := pointOnGraph f (x i)
  increasing := by
    simpa only [pointOnGraph_apply_zero] using hx

@[simp] private theorem graphPolyline_vertices (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    (graphPolyline n x hx f).vertices i = pointOnGraph f (x i) := by
  rfl

private theorem segment_pointOnGraph_affine {f : ℝ → ℝ} {m c a b : ℝ}
    (hab : a ≤ b) (hf : ∀ z ∈ Set.Icc a b, f z = m * z + c) :
    segment ℝ (pointOnGraph f a) (pointOnGraph f b) =
      pointOnGraph f '' Set.Icc a b := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    let z := u * a + v * b
    have hz : z ∈ Set.Icc a b := by
      constructor
      · calc
          a = (u + v) * a := by rw [huv]; ring
          _ = u * a + v * a := by ring
          _ ≤ u * a + v * b := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hab hv)
      · calc
          u * a + v * b ≤ u * b + v * b :=
            add_le_add (mul_le_mul_of_nonneg_left hab hu) (le_refl _)
          _ = (u + v) * b := by ring
          _ = b := by rw [huv]; ring
    refine ⟨z, hz, ?_⟩
    have hfa := hf a ⟨le_rfl, hab⟩
    have hfb := hf b ⟨hab, le_rfl⟩
    have hfz := hf z hz
    ext i
    fin_cases i
    · simp [pointOnGraph, z]
    · simp only [pointOnGraph, hfz, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hfa, hfb, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, z]
      calc
        m * (u * a + v * b) + c =
            u * (m * a) + v * (m * b) + (u + v) * c := by rw [huv]; ring
        _ = u * (m * a + c) + v * (m * b + c) := by ring
  · rintro ⟨z, hz, rfl⟩
    by_cases hab' : a = b
    · subst b
      have : z = a := by exact le_antisymm hz.2 hz.1
      subst z
      simp
    · have hlt : a < b := lt_of_le_of_ne hab hab'
      let u := (b - z) / (b - a)
      let v := (z - a) / (b - a)
      have hden : 0 < b - a := sub_pos.mpr hlt
      have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hz.2) hden.le
      have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hz.1) hden.le
      have huv : u + v = 1 := by
        dsimp [u, v]
        field_simp
        ring
      refine ⟨u, v, hu, hv, huv, ?_⟩
      have hfa := hf a ⟨le_rfl, hab⟩
      have hfb := hf b ⟨hab, le_rfl⟩
      have hfz := hf z hz
      ext i
      fin_cases i
      · simp [pointOnGraph]
        dsimp [u, v]
        field_simp
        ring
      · simp [pointOnGraph, hfz, hfa, hfb]
        dsimp [u, v]
        field_simp
        ring

/-- A graph segment of slope `m` is orthogonal to each normal annihilating `(1,m)`. -/
theorem inner_pointOnGraph_sub_normalVector_eq_zero {f : ℝ → ℝ}
    {m c a b t : ℝ}
    (hf : Set.EqOn f (fun x ↦ m * x + c) (Set.Icc a b))
    (hab : a ≤ b) (horth : Real.cos t + m * Real.sin t = 0) :
    inner ℝ (pointOnGraph f b - pointOnGraph f a)
      (normalVector (t : Real.Angle)) = 0 := by
  have hfa := hf ⟨le_rfl, hab⟩
  have hfb := hf ⟨hab, le_rfl⟩
  simp [pointOnGraph, normalVector, frame, PiLp.inner_apply, hfa, hfb]
  nlinarith

private theorem graphPolyline_carrier_eq_image_Icc {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) {f : ℝ → ℝ}
    (hpiece : ∀ i : Fin n, ∃ m c : ℝ, ∀ z ∈ Set.Icc (x i.castSucc) (x i.succ),
      f z = m * z + c)
    (hcover : Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ)) :
    (graphPolyline n x hx f).carrier =
      pointOnGraph f '' Set.Icc (x 0) (x (Fin.last n)) := by
  rw [hcover, Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  obtain ⟨m, c, hi⟩ := hpiece i
  exact segment_pointOnGraph_affine (hx i.castSucc_lt_succ).le hi

private theorem iUnion_Icc_fin {n : ℕ} (hn : 0 < n) {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) :
    Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        ext z
        constructor
        · intro hz
          exact Set.mem_iUnion.mpr ⟨0, by simpa using hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          fin_cases i
          simpa using hi
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let y : Fin (n + 1) → ℝ := fun i ↦ x i.castSucc
        have hy : StrictMono y := hx.comp Fin.strictMono_castSucc
        have hprefix := ih hnpos hy
        have hprefix' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            ⋃ i : Fin n, Set.Icc (x i.castSucc.castSucc) (x i.succ.castSucc) := by
          simpa [y] using hprefix
        have hprefix'' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            Set.iUnion ((fun i : Fin (n + 1) ↦
              Set.Icc (x i.castSucc) (x i.succ)) ∘ Fin.castSucc) := by
          rw [hprefix']
          apply Set.iUnion_congr
          intro i
          congr 2
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
        rw [← hprefix'']
        exact (Set.Icc_union_Icc_eq_Icc
          (hx.monotone (Fin.zero_le _))
          (hx (Fin.last n).castSucc_lt_succ).le).symm

private theorem exists_affineValue_eqOn_of_finite_selector {I : Set ℝ}
    (hI : IsPreconnected I) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f I)
    (hsel : ∀ x ∈ I, ∃ c ∈ L, f x = affineValue c x)
    (hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ I, affineValue c x ≠ affineValue d x)
    (hIne : I.Nonempty) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) I := by
  classical
  let _ : PreconnectedSpace I := Subtype.preconnectedSpace hI
  obtain ⟨x₀, hx₀⟩ := hIne
  obtain ⟨c₀, hc₀L, hc₀⟩ := hsel x₀ hx₀
  let A : Set I := {x | f x = affineValue c₀ x}
  have hAclosed : IsClosed A := by
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue c₀).comp continuous_subtype_val
  have hAc : Aᶜ = ⋃ d ∈ L.erase c₀,
      {x : I | f x = affineValue d x} := by
    ext x
    constructor
    · intro hx
      have hxne : f x ≠ affineValue c₀ x := by simpa [A] using hx
      obtain ⟨d, hdL, hd⟩ := hsel x x.2
      have hdc : d ≠ c₀ := by
        intro h
        subst d
        exact hxne hd
      exact Set.mem_iUnion₂.mpr ⟨d, Finset.mem_erase.mpr ⟨hdc, hdL⟩, hd⟩
    · intro hx
      obtain ⟨d, hdL, hd⟩ := Set.mem_iUnion₂.mp hx
      have hdc := (Finset.mem_erase.mp hdL).1
      intro hxc
      exact hsep d (Finset.mem_of_mem_erase hdL) c₀ hc₀L hdc x x.2 (hd.symm.trans hxc)
  have hAcclosed : IsClosed Aᶜ := by
    rw [hAc]
    apply isClosed_biUnion_finset
    intro d hd
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue d).comp continuous_subtype_val
  have hAclopen : IsClopen A := ⟨hAclosed, isClosed_compl_iff.mp hAcclosed⟩
  have hAnonempty : A.Nonempty := ⟨⟨x₀, hx₀⟩, hc₀⟩
  have hAuniv : A = Set.univ := hAclopen.eq_univ hAnonempty
  refine ⟨c₀, hc₀L, ?_⟩
  intro x hx
  have : (⟨x, hx⟩ : I) ∈ A := hAuniv.symm ▸ Set.mem_univ _
  exact this

private theorem exists_affineValue_eqOn_Icc_of_avoids_crossings {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x)
    (hcross : Set.Ioo a b ∩ affineCrossings L = ∅) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) (Set.Icc a b) := by
  classical
  have hf' : ContinuousOn f (Set.Ioo a b) :=
    hf.mono (Set.Ioo_subset_Icc_self)
  have hsel' : ∀ x ∈ Set.Ioo a b, ∃ c ∈ L, f x = affineValue c x :=
    fun x hx ↦ hsel x (Set.Ioo_subset_Icc_self hx)
  have hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ Set.Ioo a b, affineValue c x ≠ affineValue d x := by
    intro c hc d hd hcd x hx hEq
    have hxCross : x ∈ affineCrossings L := by
      exact Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_iUnion₂.mpr
        ⟨d, Finset.mem_erase.mpr ⟨hcd.symm, hd⟩, hEq⟩⟩
    have : x ∈ Set.Ioo a b ∩ affineCrossings L := ⟨hx, hxCross⟩
    simp [hcross] at this
  obtain ⟨c, hcL, hc⟩ := exists_affineValue_eqOn_of_finite_selector
    isPreconnected_Ioo L hf' hsel' hsep (Set.nonempty_Ioo.mpr hab)
  refine ⟨c, hcL, ?_⟩
  exact hc.of_subset_closure hf (continuous_affineValue c).continuousOn
    Set.Ioo_subset_Icc_self (by simp [closure_Ioo hab.ne])

/-- A continuous finite selector of affine functions on a compact interval is a polyline. -/
theorem exists_graphPolyline_of_finite_affine_selector {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph f a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph f b ∧
      p.carrier = pointOnGraph f '' Set.Icc a b ∧
      (∀ i : Fin (p.edges + 1),
        p.vertices i = pointOnGraph f (p.vertices i 0)) ∧
      ∀ i : Fin p.edges, ∃ c ∈ L,
        Set.EqOn f (affineValue c)
          (Set.Icc (p.vertices i.castSucc 0) (p.vertices i.succ 0)) := by
  classical
  let C := (finite_affineCrossings L).toFinset.filter (· ∈ Set.Icc a b)
  let B := insert a (insert b C)
  have haB : a ∈ B := by simp [B]
  have hbB : b ∈ B := by simp [B]
  have hBsub : ∀ z ∈ B, z ∈ Set.Icc a b := by
    intro z hz
    simp only [B, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact (Finset.mem_filter.mp hz).2
  have hcard2 : 2 ≤ B.card := by
    have hsub : ({a, b} : Finset ℝ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haB
      · exact hbB
    have hcard := Finset.card_le_card hsub
    simpa [hab.ne] using hcard
  let n := B.card - 1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hcard : B.card = n + 1 := by dsimp [n]; omega
  let x : Fin (n + 1) → ℝ := B.orderEmbOfFin hcard
  have hx : StrictMono x := (B.orderEmbOfFin hcard).strictMono
  have hxmem (i : Fin (n + 1)) : x i ∈ B := by
    exact B.orderEmbOfFin_mem hcard i
  have hxrange : Set.range x = B := by
    exact B.range_orderEmbOfFin hcard
  have hxzero : x 0 = a := by
    apply le_antisymm
    · have haRange : a ∈ Set.range x := by simpa [hxrange] using haB
      obtain ⟨i, hi⟩ := haRange
      rw [← hi]
      exact hx.monotone (Fin.zero_le i)
    · exact (hBsub _ (hxmem 0)).1
  have hxlast : x (Fin.last n) = b := by
    apply le_antisymm
    · exact (hBsub _ (hxmem (Fin.last n))).2
    · have hbRange : b ∈ Set.range x := by simpa [hxrange] using hbB
      obtain ⟨i, hi⟩ := hbRange
      rw [← hi]
      exact hx.monotone (Fin.le_last i)
  have hnocross (i : Fin n) :
      Set.Ioo (x i.castSucc) (x i.succ) ∩ affineCrossings L = ∅ := by
    ext z
    constructor
    · intro hz
      have hzab : z ∈ Set.Icc a b := by
        rw [← hxzero, ← hxlast]
        exact ⟨(hx.monotone (Fin.zero_le i.castSucc)).trans hz.1.1.le,
          hz.1.2.le.trans (hx.monotone (Fin.le_last i.succ))⟩
      have hzB : z ∈ B := by
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_filter.mpr
        exact ⟨(finite_affineCrossings L).mem_toFinset.mpr hz.2, hzab⟩
      have hzRange : z ∈ Set.range x := by simpa [hxrange] using hzB
      obtain ⟨j, hj⟩ := hzRange
      rw [← hj] at hz
      have hij : i.castSucc < j := hx.lt_iff_lt.mp hz.1.1
      have hji : j < i.succ := hx.lt_iff_lt.mp hz.1.2
      change i.val < j.val at hij
      change j.val < i.val + 1 at hji
      omega
    · intro hz
      exact hz.elim
  have hpiece : ∀ i : Fin n, ∃ c ∈ L,
      Set.EqOn f (affineValue c) (Set.Icc (x i.castSucc) (x i.succ)) := by
    intro i
    exact exists_affineValue_eqOn_Icc_of_avoids_crossings
      (hx i.castSucc_lt_succ) L
      (hf.mono (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _))))
      (fun z hz ↦ hsel z (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _)) hz))
      (hnocross i)
  let p := graphPolyline n x hx f
  refine ⟨p, hnpos, ?_, ?_, ?_, ?_, ?_⟩
  · change pointOnGraph f (x 0) = pointOnGraph f a
    rw [hxzero]
  · change pointOnGraph f (x (Fin.last n)) = pointOnGraph f b
    rw [hxlast]
  · rw [graphPolyline_carrier_eq_image_Icc hx]
    · simp [hxzero, hxlast]
    · intro i
      obtain ⟨c, -, hc⟩ := hpiece i
      exact ⟨c.1, c.2, hc⟩
    · exact iUnion_Icc_fin hnpos hx
  · intro i
    rfl
  · intro i
    change ∃ c ∈ L, Set.EqOn f (affineValue c)
      (Set.Icc (x i.castSucc) (x i.succ))
    exact hpiece i

/-- Injective graph parametrizations preserve disjointness of parameter sets. -/
theorem pointOnGraph_image_disjoint
    (f : ℝ → ℝ) {s t : Set ℝ} (hst : Disjoint s t) :
    Disjoint (pointOnGraph f '' s) (pointOnGraph f '' t) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have heq : x = y := by
    have := congrArg (fun p : Point ↦ p 0) hxy
    simpa [pointOnGraph] using this.symm
  exact Set.disjoint_left.mp hst hx (heq ▸ hy)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Measure
-/

public section

noncomputable section

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment_mbe8a367 {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private lemma eq_right_of_mem_segment_of_fst_eq {a b q : Point}
    (hab : a 0 < b 0) (hq : q ∈ segment ℝ a b) (heq : q 0 = b 0) : q = b := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hcoord : a 0 + r * (b 0 - a 0) = b 0 := heq
  have hrone : r = 1 := by nlinarith
  simp [hrone]

/-- Distinct increasing polyline segments meet only at a possible common endpoint. -/
lemma XMonotonePolylineData.segment_inter_subset_singleton
    (p : XMonotonePolylineData) {i j : Fin p.edges} (hij : i < j) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩
        segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ⊆
      {p.vertices i.succ} := by
  intro q hq
  have hi := fst_mem_Icc_of_mem_segment_mbe8a367 (p.increasing i.castSucc_lt_succ).le hq.1
  have hj := fst_mem_Icc_of_mem_segment_mbe8a367 (p.increasing j.castSucc_lt_succ).le hq.2
  have hindex : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact hij
  have horder := p.increasing.monotone hindex
  apply Set.mem_singleton_iff.mpr
  exact eq_right_of_mem_segment_of_fst_eq (p.increasing i.castSucc_lt_succ) hq.1
    (le_antisymm hi.2 (horder.trans hj.1))

open MeasureTheory

/-- The segments of an increasing polyline are almost disjoint for length measure. -/
lemma XMonotonePolylineData.pairwise_aedisjoint_segments
    (p : XMonotonePolylineData) :
    Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ))) := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  have hlt (i j : Fin p.edges) (hij : i < j) :
      AEDisjoint (Measure.hausdorffMeasure 1)
        (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
        (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ)) := by
    exact measure_mono_null (p.segment_inter_subset_singleton hij) (measure_singleton _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

/-- A supporting-line slice has the sum of the lengths of its parallel segments. -/
lemma XMonotonePolylineData.hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c}) =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          ENNReal.ofReal (dist (p.vertices i.castSucc) (p.vertices i.succ)) else 0 := by
  classical
  have hd : Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩ {q | inner ℝ q n = c})
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ∩ {q | inner ℝ q n = c})) := by
    intro i j hij
    exact (p.pairwise_aedisjoint_segments hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [XMonotonePolylineData.carrier, Set.iUnion_inter, measure_iUnion₀ hd, tsum_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0
    · rw [ite_eq_left hi, Set.inter_eq_left.mpr (hparallel i hi), hausdorffMeasure_segment,
        edist_dist]
    · rw [ite_eq_right hi]
      exact EuclideanGeometry.hausdorffMeasure_segment_inter_hyperplane_eq_zero hi
  · intro i
    have hc : IsCompact (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    exact (hc.isClosed.measurableSet.inter
      (isClosed_eq (by fun_prop) continuous_const).measurableSet).nullMeasurableSet

/-- The real length of a supporting-line slice is the sum of its parallel segment lengths. -/
lemma XMonotonePolylineData.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    (Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c})).toReal =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
  classical
  rw [p.hausdorffMeasure_carrier_inter_hyperplane n c hparallel,
    ENNReal.toReal_sum (by intro i _; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [dist_nonneg]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Polygon / Polyline / Projection
-/

public section

noncomputable section

namespace MovingSofa

/-- A leftward edge displacement is its length times its oriented tangent. -/
theorem sub_eq_dist_smul_tangentVector {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    a - b = dist a b • tangentVector (t : Real.Angle) := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hdist := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero ht hab horth
  have hr : r = -dist a b := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    nlinarith
  rw [hr, neg_smul] at hvec
  simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hvec).symm

/-- Every point of a polyline satisfies the bound by positive projected edge increments. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_pos
    (p : XMonotonePolylineData) (u : Point) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q u ≤ inner ℝ (p.vertices (Fin.last p.edges)) u +
      ∑ i : Fin p.edges, max (inner ℝ (p.vertices i.castSucc - p.vertices i.succ) u) 0 := by
  have hvertex (i : Fin (p.edges + 1)) :=
    Fin.apply_le_last_add_sum_max_sub (fun i ↦ inner ℝ (p.vertices i) u) i
  simp only [← inner_sub_left] at hvertex
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hqi
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left (hvertex i.castSucc) ha
  have h₂ := mul_le_mul_of_nonneg_left (hvertex i.succ) hb
  have h := add_le_add h₁ h₂
  rwa [← add_mul, hab, one_mul] at h

/-- Grouping edge lengths by their unique normal preserves every weighted sum. -/
theorem XMonotonePolylineData.sum_normal_lengths_mul
    (p : XMonotonePolylineData) (D : Finset ℝ) (g : ℝ → ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (t : Fin p.edges → ℝ) (ht : ∀ i, t i ∈ D)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ u ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * g u =
      ∑ i : Fin p.edges, dist (p.vertices i.castSucc) (p.vertices i.succ) * g (t i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (t i)]
  · rw [ite_eq_left (horth i)]
  · intro u hu hut
    have hne : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) ≠ 0 := by
      intro hzero
      exact hut (eq_of_inner_sub_normalVector_eq_zero (hD u hu) (hD _ (ht i))
        (p.increasing i.castSucc_lt_succ) hzero (horth i))
    simp [hne]
  · exact fun hnot ↦ (hnot (ht i)).elim

/-- Positive normal projections bound every point of a polyline by its right endpoint. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_normal_lengths
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0)
    (s : ℝ) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ (p.vertices (Fin.last p.edges)) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) *
        max (Real.sin (s - u)) 0 := by
  classical
  choose t ht horth using hlabels
  rw [p.sum_normal_lengths_mul D (fun u ↦ max (Real.sin (s - u)) 0) hD t ht horth]
  have h := p.inner_le_endpoint_add_sum_pos (normalVector (s : Real.Angle)) hq
  convert h using 2
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_eq_dist_smul_tangentVector (hD _ (ht i))
    (p.increasing i.castSucc_lt_succ) (horth i), real_inner_smul_left,
    inner_tangentVector_normalVector_real, mul_max_of_nonneg _ _ dist_nonneg, mul_zero]

end MovingSofa

end

end

end

end

end

end

end

end

end
