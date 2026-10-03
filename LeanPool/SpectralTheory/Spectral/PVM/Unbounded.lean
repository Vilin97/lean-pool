/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.PVM.Integral
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.Measurability
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space


/-!
# Unbounded spectral integration

This file extends the bounded spectral integral to unbounded measurable
functions by a monotone-limit construction, giving the partial operator
`E_pvm.unboundedIntegral f hf` for a PVM `E_pvm` and measurable `f`.
-/

public section

open MeasureTheory
open Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The nonnegative scalar set function induced by a PVM and a vector. -/
@[expose] def PVM.scalarContent (E_pvm : PVM E) (x : E) (S : Set ℝ) : ℝ :=
  (@inner ℂ E _ (E_pvm.proj S x) x).re

/-- Scalar PVM content is nonnegative for measurable sets. -/
theorem PVM.scalarContent_nonneg (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    0 ≤ E_pvm.scalarContent x S := by
  change 0 ≤ (@inner ℂ E _ (E_pvm.proj S x) x).re
  have h := E_pvm.monotone MeasurableSet.empty hS (Set.empty_subset S) x
  rw [E_pvm.empty, zero_apply, inner_zero_left, Complex.zero_re] at h
  exact h

/-- Scalar PVM content vanishes on the empty set. -/
theorem PVM.scalarContent_empty (E_pvm : PVM E) (x : E) :
    E_pvm.scalarContent x ∅ = 0 := by
  change (@inner ℂ E _ (E_pvm.proj ∅ x) x).re = 0
  rw [E_pvm.empty, zero_apply, inner_zero_left, Complex.zero_re]

/-- Scalar PVM content is additive on disjoint measurable sets. -/
theorem PVM.scalarContent_union (E_pvm : PVM E) (x : E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.scalarContent x (S ∪ T) =
      E_pvm.scalarContent x S + E_pvm.scalarContent x T := by
  change (@inner ℂ E _ (E_pvm.proj (S ∪ T) x) x).re =
    (@inner ℂ E _ (E_pvm.proj S x) x).re +
      (@inner ℂ E _ (E_pvm.proj T x) x).re
  rw [E_pvm.proj_union hS hT hdisj, add_apply, inner_add_left, Complex.add_re]

/-- Strong countable additivity of a PVM implies scalar countable-additivity convergence. -/
theorem PVM.scalarContent_countably_additive_tendsto (E_pvm : PVM E) (x : E)
    (S : ℕ → Set ℝ) (hmeas : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise (Disjoint on S)) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, E_pvm.scalarContent x (S i))
      Filter.atTop (nhds (E_pvm.scalarContent x (⋃ i, S i))) := by
  have hSOT := E_pvm.countably_additive S hmeas hpair x
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hSOT (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hre := (Complex.continuous_re.tendsto _).comp hinner
  convert hre using 1
  · funext n
    change (∑ i ∈ Finset.range n,
      (@inner ℂ E _ (E_pvm.proj (S i) x) x).re) =
        (@inner ℂ E _ (∑ i ∈ Finset.range n, E_pvm.proj (S i) x) x).re
    rw [sum_inner, Complex.re_sum]
  · rfl

/-- The finite positive measure obtained by evaluating the PVM at a vector. -/
noncomputable def PVM.scalarMeasure (E_pvm : PVM E) (x : E) :
    MeasureTheory.Measure ℝ :=
  Measure.ofMeasurable
    (fun S _ => ENNReal.ofReal (E_pvm.scalarContent x S))
    (by rw [E_pvm.scalarContent_empty, ENNReal.ofReal_zero])
    (by
      intro S hmeas hpair
      have hnonneg : ∀ i, 0 ≤ E_pvm.scalarContent x (S i) :=
        fun i => E_pvm.scalarContent_nonneg x (S i) (hmeas i)
      have hHasSum : HasSum (fun i => E_pvm.scalarContent x (S i))
          (E_pvm.scalarContent x (⋃ i, S i)) :=
        (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
          (E_pvm.scalarContent_countably_additive_tendsto x S hmeas hpair)
      rw [← hHasSum.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg hnonneg hHasSum.summable])

/-- On measurable sets, the scalar measure agrees with the PVM quadratic form. -/
theorem PVM.scalarMeasure_apply (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarMeasure x S = ENNReal.ofReal (E_pvm.scalarContent x S) := by
  exact Measure.ofMeasurable_apply S hS

/-- Scalar PVM content is the squared norm of the projected vector. -/
theorem PVM.scalarContent_eq_norm_sq (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent x S = ‖E_pvm.proj S x‖ ^ 2 := by
  have hproj := E_pvm.isOrthogonalProjection S hS
  change (@inner ℂ E _ (E_pvm.proj S x) x).re = ‖E_pvm.proj S x‖ ^ 2
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  rw [hproj.1.adjoint_eq]
  exact congr_arg (fun T : E →L[ℂ] E => (@inner ℂ E _ (T x) x).re) hproj.2.symm

/-- The total mass of the scalar measure is the squared norm of its vector. -/
theorem PVM.scalarMeasure_univ (E_pvm : PVM E) (x : E) :
    E_pvm.scalarMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [E_pvm.scalarMeasure_apply x Set.univ MeasurableSet.univ,
    E_pvm.scalarContent_eq_norm_sq x Set.univ MeasurableSet.univ,
    E_pvm.univ, one_apply_eq_self]

/-- Every set has finite scalar measure. -/
theorem PVM.scalarMeasure_lt_top (E_pvm : PVM E) (x : E) (S : Set ℝ) :
    E_pvm.scalarMeasure x S < ⊤ := by
  calc
    E_pvm.scalarMeasure x S ≤ E_pvm.scalarMeasure x Set.univ :=
      measure_mono (Set.subset_univ S)
    _ = ENNReal.ofReal (‖x‖ ^ 2) := E_pvm.scalarMeasure_univ x
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Scalar PVM measures are finite measures. -/
noncomputable instance PVM.scalarMeasure_isFiniteMeasure (E_pvm : PVM E) (x : E) :
    IsFiniteMeasure (E_pvm.scalarMeasure x) where
  measure_univ_lt_top := E_pvm.scalarMeasure_lt_top x Set.univ

/-- Diagonal matrix coefficients of simple spectral integrals are scalar integrals. -/
theorem PVM.inner_simpleIntegral_self (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) (x : E) :
    @inner ℂ E _ x (E_pvm.simpleIntegral f x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by
  rw [PVM.simpleIntegral, sum_apply, inner_sum]
  have hfint : Integrable f (E_pvm.scalarMeasure x) := by
    apply Integrable.of_bound f.measurable.aestronglyMeasurable
      (∑ z ∈ f.range, ‖z‖)
    apply ae_of_all
    intro t
    exact Finset.single_le_sum
      (fun z _hz => norm_nonneg z) (f.mem_range_self t)
  rw [SimpleFunc.integral_eq_sum f hfint]
  apply Finset.sum_congr rfl
  intro z hz
  rw [smul_apply, inner_smul_right]
  have hreal : (E_pvm.scalarMeasure x).real (f ⁻¹' {z}) =
      E_pvm.scalarContent x (f ⁻¹' {z}) := by
    rw [measureReal_def,
      E_pvm.scalarMeasure_apply x (f ⁻¹' {z}) (f.measurableSet_fiber z),
      ENNReal.toReal_ofReal
        (E_pvm.scalarContent_nonneg x (f ⁻¹' {z}) (f.measurableSet_fiber z))]
  rw [hreal]
  change z * (@inner ℂ E _ x (E_pvm.proj (f ⁻¹' {z}) x)) =
      (E_pvm.scalarContent x (f ⁻¹' {z})) • z
  rw [show @inner ℂ E _ x (E_pvm.proj (f ⁻¹' {z}) x) =
      E_pvm.scalarContent x (f ⁻¹' {z}) by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,
      (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
        (f.measurableSet_fiber z)).1]
    change @inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x =
      (((@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re : ℝ) : ℂ)
    have hpos : ContinuousLinearMap.IsPositive
        (E_pvm.proj (f ⁻¹' {z})) :=
      (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
          (f.measurableSet_fiber z)).2).mpr
          (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
            (f.measurableSet_fiber z)).1
    exact ((LinearMap.isPositive_iff_complex _).mp hpos.toLinearMap x).1.symm]
  change z * (E_pvm.scalarContent x (f ⁻¹' {z}) : ℂ) =
    (E_pvm.scalarContent x (f ⁻¹' {z}) : ℂ) * z
  exact mul_comm _ _

/-- Diagonal matrix coefficients of bounded measurable spectral integrals are scalar
integrals. -/
theorem PVM.inner_integral_self (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : E) :
    @inner ℂ E _ x (E_pvm.integral f hf hbdd x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by
  let C : ℝ := Classical.choose hbdd
  have hC : ∀ t, ‖f t‖ ≤ C := Classical.choose_spec hbdd
  obtain ⟨s, hs, hsC⟩ := exists_bounded_simpleFunc_tendstoUniformly f hf C hC
  have hop := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly f hf hbdd s hs
  have happly : Filter.Tendsto
      (fun n => E_pvm.simpleIntegral (s n) x) Filter.atTop
      (nhds (E_pvm.integral f hf hbdd x)) := by
    exact (Continuous.continuousAt
      (Continuous.clm_apply continuous_id continuous_const)).tendsto.comp hop
  have hinner : Filter.Tendsto
      (fun n => @inner ℂ E _ x (E_pvm.simpleIntegral (s n) x))
      Filter.atTop (nhds (@inner ℂ E _ x (E_pvm.integral f hf hbdd x))) := by
    exact Filter.Tendsto.inner (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => x) Filter.atTop (nhds x)) happly
  have hintegral : Filter.Tendsto
      (fun n => ∫ t, s n t ∂(E_pvm.scalarMeasure x)) Filter.atTop
      (nhds (∫ t, f t ∂(E_pvm.scalarMeasure x))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (s n).measurable.aestronglyMeasurable
    · exact integrable_const C
    · intro n
      exact ae_of_all _ (hsC n)
    · exact ae_of_all _ fun t => hs.tendsto_at t
  apply tendsto_nhds_unique hinner
  simpa only [E_pvm.inner_simpleIntegral_self] using hintegral

/-- The simple spectral integral satisfies the pointwise `L²` norm identity. -/
theorem PVM.ofReal_norm_sq_simpleIntegral (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) (x : E) :
    ENNReal.ofReal (‖E_pvm.simpleIntegral f x‖ ^ 2) =
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) := by
  rw [E_pvm.norm_sq_simpleIntegral f x]
  change ENNReal.ofReal
      (∑ z ∈ f.range, ‖z‖ ^ 2 * E_pvm.scalarContent x (f ⁻¹' {z})) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun z hz =>
    mul_nonneg (sq_nonneg ‖z‖)
      (E_pvm.scalarContent_nonneg x (f ⁻¹' {z}) (f.measurableSet_fiber z)))]
  let g : ℂ → ENNReal := fun z => (↑‖z‖₊ : ENNReal) ^ 2
  have hfun : (fun t => (↑‖f t‖₊ : ENNReal) ^ 2) = fun t => f.map g t := by
    funext t
    rw [SimpleFunc.map_apply]
  rw [hfun, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ENNReal.ofReal_mul (sq_nonneg ‖z‖),
    E_pvm.scalarMeasure_apply x (f ⁻¹' {z}) (f.measurableSet_fiber z),
    ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]
  rfl

/-- The bounded spectral integral satisfies the pointwise `L²` norm identity. -/
theorem PVM.ofReal_norm_sq_integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) (x : E) :
    ENNReal.ofReal (‖E_pvm.integral f hf hbdd x‖ ^ 2) =
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) := by
  obtain ⟨C, hC⟩ := hbdd
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  obtain ⟨s, hs, hsC⟩ :=
    exists_bounded_simpleFunc_tendstoUniformly f hf C hC
  have hop := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    f hf ⟨C, hC⟩ s hs
  have hval : Filter.Tendsto (fun n => E_pvm.simpleIntegral (s n) x)
      Filter.atTop (nhds (E_pvm.integral f hf ⟨C, hC⟩ x)) := by
    exact (Continuous.continuousAt
      (Continuous.clm_apply continuous_id continuous_const)).tendsto.comp hop
  have hleft : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖E_pvm.simpleIntegral (s n) x‖ ^ 2))
      Filter.atTop
      (nhds (ENNReal.ofReal (‖E_pvm.integral f hf ⟨C, hC⟩ x‖ ^ 2))) := by
    exact ENNReal.tendsto_ofReal (hval.norm.pow 2)
  have hright : Filter.Tendsto
      (fun n => ∫⁻ t, ‖s n t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x))
      Filter.atTop (nhds (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x))) := by
    apply tendsto_lintegral_of_dominated_convergence
      (fun _ => ENNReal.ofReal (C ^ 2))
    · intro n
      exact ((s n).measurable.nnnorm.pow_const 2).coe_nnreal_ennreal
    · intro n
      apply ae_of_all
      intro t
      change ‖s n t‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2)
      calc
        ‖s n t‖ₑ ^ 2 = ENNReal.ofReal (‖s n t‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg (s n t)) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal (C ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg (s n t)) hC_nonneg).2 (hsC n t))
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (E_pvm.scalarMeasure_lt_top x Set.univ).ne
    · apply ae_of_all
      intro t
      have hst : Filter.Tendsto (fun n => s n t) Filter.atTop (nhds (f t)) :=
        hs.tendsto_at t
      have hreal := ENNReal.tendsto_ofReal (hst.norm.pow 2)
      convert hreal using 1
      · ext n
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm]
      · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm]
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext n
  exact E_pvm.ofReal_norm_sq_simpleIntegral (s n) x

/-- Scalar PVM content is quadratic under complex scalar multiplication. -/
theorem PVM.scalarContent_smul (E_pvm : PVM E) (c : ℂ) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent (c • x) S = ‖c‖ ^ 2 * E_pvm.scalarContent x S := by
  rw [E_pvm.scalarContent_eq_norm_sq (c • x) S hS,
    E_pvm.scalarContent_eq_norm_sq x S hS, map_smul, norm_smul]
  ring

/-- Scalar content of a sum is controlled by the two summands. -/
theorem PVM.scalarContent_add_le (E_pvm : PVM E) (x y : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarContent (x + y) S ≤
      2 * (E_pvm.scalarContent x S + E_pvm.scalarContent y S) := by
  rw [E_pvm.scalarContent_eq_norm_sq (x + y) S hS,
    E_pvm.scalarContent_eq_norm_sq x S hS,
    E_pvm.scalarContent_eq_norm_sq y S hS, map_add]
  exact ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (norm_add_le _ _)).trans add_sq_le

/-- Projecting the vector restricts its scalar content to the projection set. -/
theorem PVM.scalarContent_proj (E_pvm : PVM E) (x : E) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    E_pvm.scalarContent (E_pvm.proj S x) T = E_pvm.scalarContent x (T ∩ S) := by
  rw [E_pvm.scalarContent_eq_norm_sq (E_pvm.proj S x) T hT,
    E_pvm.scalarContent_eq_norm_sq x (T ∩ S) (hT.inter hS),
    E_pvm.inter T S hT hS]
  rfl

/-- Projecting a vector restricts its scalar measure to the projection set. -/
theorem PVM.scalarMeasure_proj (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarMeasure (E_pvm.proj S x) = (E_pvm.scalarMeasure x).restrict S := by
  apply Measure.ext
  intro T hT
  rw [E_pvm.scalarMeasure_apply (E_pvm.proj S x) T hT,
    E_pvm.scalarContent_proj x S T hS hT, Measure.restrict_apply hT,
    E_pvm.scalarMeasure_apply x (T ∩ S) (hT.inter hS)]

/-- The scalar measure associated to the zero vector is the zero measure. -/
@[simp]
theorem PVM.scalarMeasure_zero (E_pvm : PVM E) :
    E_pvm.scalarMeasure (0 : E) = 0 := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply 0 S hS,
    E_pvm.scalarContent_eq_norm_sq 0 S hS, map_zero, norm_zero,
    zero_pow (by omega), ENNReal.ofReal_zero]
  rfl

/-- The scalar measure is quadratic under complex scalar multiplication. -/
theorem PVM.scalarMeasure_smul (E_pvm : PVM E) (c : ℂ) (x : E) :
    E_pvm.scalarMeasure (c • x) =
      ENNReal.ofReal (‖c‖ ^ 2) • E_pvm.scalarMeasure x := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply (c • x) S hS,
    E_pvm.scalarContent_smul c x S hS,
    ENNReal.ofReal_mul (sq_nonneg ‖c‖), Measure.smul_apply, smul_eq_mul,
    E_pvm.scalarMeasure_apply x S hS]

/-- The scalar measure of a sum is dominated by twice the sum of the scalar measures. -/
theorem PVM.scalarMeasure_add_le (E_pvm : PVM E) (x y : E) :
    E_pvm.scalarMeasure (x + y) ≤
      (2 : ENNReal) • (E_pvm.scalarMeasure x + E_pvm.scalarMeasure y) := by
  apply Measure.le_iff.2
  intro S hS
  rw [E_pvm.scalarMeasure_apply (x + y) S hS, Measure.smul_apply,
    smul_eq_mul, Measure.add_apply, E_pvm.scalarMeasure_apply x S hS,
    E_pvm.scalarMeasure_apply y S hS]
  calc
    ENNReal.ofReal (E_pvm.scalarContent (x + y) S) ≤
        ENNReal.ofReal
          (2 * (E_pvm.scalarContent x S + E_pvm.scalarContent y S)) :=
      ENNReal.ofReal_le_ofReal (E_pvm.scalarContent_add_le x y S hS)
    _ = (2 : ENNReal) *
        (ENNReal.ofReal (E_pvm.scalarContent x S) +
          ENNReal.ofReal (E_pvm.scalarContent y S)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add
          (E_pvm.scalarContent_nonneg x S hS)
          (E_pvm.scalarContent_nonneg y S hS)]
      norm_num

/-- The vectors square-integrable against their scalar PVM measures form a submodule. -/
noncomputable def PVM.squareIntegrableDomain (E_pvm : PVM E)
    (f : ℝ → ℂ) : Submodule ℂ E where
  carrier := {x | ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤}
  zero_mem' := by
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (0 : E))) < ⊤
    rw [E_pvm.scalarMeasure_zero, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro x y hx hy
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x + y))) < ⊤
    have hle := lintegral_mono' (E_pvm.scalarMeasure_add_le x y)
      (le_refl (fun t : ℝ => (↑(‖f t‖₊ ^ 2) : ENNReal)))
    refine hle.trans_lt ?_
    rw [lintegral_smul_measure, lintegral_add_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) ((ENNReal.add_lt_top).2 ⟨hx, hy⟩)
  smul_mem' := by
    intro c x hx
    change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (c • x))) < ⊤
    rw [E_pvm.scalarMeasure_smul c x, lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx

/-- A spectral projection onto a set where `f` is bounded belongs to the square-integrable
domain. -/
private theorem PVM.proj_mem_squareIntegrableDomain (E_pvm : PVM E)
    (f : ℝ → ℂ) (x : E) (S : Set ℝ) (hS : MeasurableSet S) (C : ℝ)
    (hC : 0 ≤ C) (hbdd : ∀ t ∈ S, ‖f t‖ ≤ C) :
    E_pvm.proj S x ∈ E_pvm.squareIntegrableDomain f := by
  change (∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure (E_pvm.proj S x))) < ⊤
  rw [E_pvm.scalarMeasure_proj x S hS]
  calc
    (∫⁻ t in S, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x)) ≤
        ∫⁻ _t in S, ENNReal.ofReal (C ^ 2) ∂(E_pvm.scalarMeasure x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with t ht
      change ‖f t‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2)
      calc
        ‖f t‖ₑ ^ 2 = ENNReal.ofReal (‖f t‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg (f t)) 2, ofReal_norm]
        _ ≤ ENNReal.ofReal (C ^ 2) := ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg (f t)) hC).2 (hbdd t ht))
    _ = ENNReal.ofReal (C ^ 2) * E_pvm.scalarMeasure x S :=
      setLIntegral_const S (ENNReal.ofReal (C ^ 2))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (E_pvm.scalarMeasure_lt_top x S)

/-- The bounded truncation of a measurable function at level `n`. -/
noncomputable def PVM.spectralTruncation (f : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if ‖f t‖ ≤ n then f t else 0

/-- Bounded spectral truncations preserve measurability. -/
private theorem PVM.spectralTruncation_measurable (f : ℝ → ℂ) (hf : Measurable f)
    (n : ℕ) : Measurable (PVM.spectralTruncation f n) := by
  unfold PVM.spectralTruncation
  exact Measurable.ite (measurableSet_le hf.norm measurable_const) hf measurable_const

/-- The `n`th spectral truncation has uniform norm bound `n`. -/
private theorem PVM.norm_spectralTruncation_le (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    ‖PVM.spectralTruncation f n t‖ ≤ n := by
  by_cases h : ‖f t‖ ≤ n
  · rw [PVM.spectralTruncation, ite_eq_left h]
    exact h
  · rw [PVM.spectralTruncation, ite_eq_right h, norm_zero]
    exact Nat.cast_nonneg n

/-- Spectral truncations converge pointwise to the original function. -/
private theorem PVM.spectralTruncation_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Filter.Tendsto (fun n => PVM.spectralTruncation f n t)
      Filter.atTop (nhds (f t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, ite_eq_left]
  exact hN.trans (Nat.cast_le.2 hn)

/-- The bounded spectral integral of the `n`th truncation. -/
noncomputable def PVM.truncatedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) : E →L[ℂ] E :=
  E_pvm.integral (PVM.spectralTruncation f n)
    (by exact PVM.spectralTruncation_measurable f hf n)
    (by exact ⟨n, PVM.norm_spectralTruncation_le f n⟩)

/-- The difference of two spectral truncations has the sum of their truncation levels as a
uniform bound. -/
private theorem PVM.norm_spectralTruncation_sub_le (f : ℝ → ℂ)
    (n m : ℕ) (t : ℝ) :
    ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖ ≤ m + n := by
  calc
    ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖ ≤
        ‖PVM.spectralTruncation f m t‖ + ‖PVM.spectralTruncation f n t‖ :=
      norm_sub_le _ _
    _ ≤ m + n := add_le_add
      (PVM.norm_spectralTruncation_le f m t)
      (PVM.norm_spectralTruncation_le f n t)

/-- The squared error of spectral truncation is measurable as an `ENNReal`-valued function. -/
private theorem PVM.spectralTruncation_error_measurable (f : ℝ → ℂ)
    (hf : Measurable f) (n : ℕ) :
    Measurable (fun t => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal)) := by
  exact ((hf.sub (PVM.spectralTruncation_measurable f hf n)).nnnorm.pow_const 2).coe_nnreal_ennreal

/-- Squared truncation error is bounded by the original squared norm. -/
private theorem PVM.spectralTruncation_error_le (f : ℝ → ℂ) (n : ℕ) (t : ℝ) :
    (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal) ≤
      ↑(‖f t‖₊ ^ 2) := by
  by_cases h : ‖f t‖ ≤ n
  · rw [PVM.spectralTruncation, ite_eq_left h, sub_self, nnnorm_zero,
      zero_pow (by omega)]
    exact bot_le
  · rw [PVM.spectralTruncation, ite_eq_right h, sub_zero]

/-- Squared truncation error converges pointwise to zero. -/
private theorem PVM.spectralTruncation_error_tendsto_zero (f : ℝ → ℂ) (t : ℝ) :
    Filter.Tendsto
      (fun n => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f t‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, ite_eq_left, sub_self, nnnorm_zero,
    zero_pow (by omega), ENNReal.coe_zero]
  exact hN.trans (Nat.cast_le.2 hn)

/-- For a vector in the square-integrable domain, the squared truncation error tends to zero
in scalar measure. -/
private theorem PVM.lintegral_truncation_error_tendsto_zero (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f) :
    Filter.Tendsto
      (fun n => ∫⁻ t,
        (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop (nhds 0) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := E_pvm.scalarMeasure (x : E))
    (F := fun n t => (↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal))
    (f := fun _ => 0)
    (fun t => (↑(‖f t‖₊ ^ 2) : ENNReal))
    (fun n => PVM.spectralTruncation_error_measurable f hf n)
    (fun n => ae_of_all _ fun t => PVM.spectralTruncation_error_le f n t)
    x.property.ne
    (ae_of_all _ fun t => PVM.spectralTruncation_error_tendsto_zero f t)
  simpa only [lintegral_zero] using h

/-- Later truncations differ from an earlier truncation by no more than the earlier truncation's
error. -/
private theorem PVM.spectralTruncation_sub_le_error (f : ℝ → ℂ) {n m : ℕ}
    (hnm : n ≤ m) (t : ℝ) :
    (↑(‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2) : ENNReal) ≤
      ↑(‖f t - PVM.spectralTruncation f n t‖₊ ^ 2) := by
  unfold PVM.spectralTruncation
  by_cases hn : ‖f t‖ ≤ n
  · have hm : ‖f t‖ ≤ m := hn.trans (Nat.cast_le.2 hnm)
    rw [ite_eq_left hn, ite_eq_left hm]
  · by_cases hm : ‖f t‖ ≤ m
    · rw [ite_eq_right hn, ite_eq_left hm]
    · rw [ite_eq_right hn, ite_eq_right hm, sub_self, nnnorm_zero, zero_pow (by omega)]
      exact bot_le

/-- Differences of bounded truncation integrals satisfy the pointwise `L²` identity. -/
private theorem PVM.ofReal_norm_sq_truncatedIntegral_sub (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E) (n m : ℕ) :
    ENNReal.ofReal
        (‖E_pvm.truncatedIntegral f hf m x -
          E_pvm.truncatedIntegral f hf n x‖ ^ 2) =
      ∫⁻ t,
        ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
          ∂(E_pvm.scalarMeasure x) := by
  let gm := PVM.spectralTruncation f m
  let gn := PVM.spectralTruncation f n
  have hgm : Measurable gm := PVM.spectralTruncation_measurable f hf m
  have hgn : Measurable gn := PVM.spectralTruncation_measurable f hf n
  let hbddm : ∃ C, ∀ t, ‖gm t‖ ≤ C :=
    ⟨m, PVM.norm_spectralTruncation_le f m⟩
  let hbddn : ∃ C, ∀ t, ‖gn t‖ ≤ C :=
    (by exact ⟨n, PVM.norm_spectralTruncation_le f n⟩)
  let hbddsub : ∃ C, ∀ t, ‖(gm - gn) t‖ ≤ C :=
    ⟨m + n, PVM.norm_spectralTruncation_sub_le f n m⟩
  have hid := E_pvm.ofReal_norm_sq_integral
    (gm - gn) (hgm.sub hgn) hbddsub x
  rw [E_pvm.integral_sub gm gn hgm hgn hbddm hbddn hbddsub] at hid
  simpa only [PVM.truncatedIntegral, gm, gn, Pi.sub_apply, sub_apply] using hid

/-- The pairwise `L²` identity for bounded truncations implies that their values form a Cauchy
sequence on every square-integrable vector. -/
private theorem PVM.cauchySeq_truncatedIntegral_of_l2 (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f)
    (hL2 : ∀ {n m : ℕ}, n ≤ m →
      ENNReal.ofReal
          (‖E_pvm.truncatedIntegral f hf m (x : E) -
            E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2) =
        ∫⁻ t,
          ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E))) :
    CauchySeq (fun n => E_pvm.truncatedIntegral f hf n (x : E)) := by
  apply Metric.cauchySeq_iff.2
  intro ε hε
  have herr := E_pvm.lintegral_truncation_error_tendsto_zero f hf x
  have hthreshold :
      0 < ENNReal.ofReal (ε ^ 2) :=
    ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1
    (herr.eventually (gt_mem_nhds hthreshold)))
  refine ⟨N, ?_⟩
  have hordered : ∀ {n m : ℕ}, N ≤ n → n ≤ m →
      dist (E_pvm.truncatedIntegral f hf m (x : E))
        (E_pvm.truncatedIntegral f hf n (x : E)) < ε := by
    intro n m hNn hnm
    rw [dist_eq_norm]
    have hlintegral :
        (∫⁻ t,
          ‖PVM.spectralTruncation f m t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E))) ≤
          ∫⁻ t, ‖f t - PVM.spectralTruncation f n t‖₊ ^ 2
            ∂(E_pvm.scalarMeasure (x : E)) :=
      lintegral_mono (fun t => PVM.spectralTruncation_sub_le_error f hnm t)
    have hofReal :
        ENNReal.ofReal
            (‖E_pvm.truncatedIntegral f hf m (x : E) -
              E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2) <
          ENNReal.ofReal (ε ^ 2) :=
      (hL2 hnm).trans_lt (hlintegral.trans_lt (hN n hNn))
    have hsquare :
        ‖E_pvm.truncatedIntegral f hf m (x : E) -
          E_pvm.truncatedIntegral f hf n (x : E)‖ ^ 2 < ε ^ 2 :=
      (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).1 hofReal
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 hsquare
  intro m hm n hn
  rcases le_total n m with hnm | hmn
  · exact hordered hn hnm
  · rw [dist_comm]
    exact hordered hm hmn

/-- Bounded truncation integrals converge on each square-integrable vector. -/
private theorem PVM.cauchySeq_truncatedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E_pvm.squareIntegrableDomain f) :
    CauchySeq (fun n => E_pvm.truncatedIntegral f hf n (x : E)) := by
  apply E_pvm.cauchySeq_truncatedIntegral_of_l2 f hf x
  intro n m _hnm
  exact E_pvm.ofReal_norm_sq_truncatedIntegral_sub f hf (x : E) n m

/-- Spectral integration on the domain of vectors with finite second moment. -/
noncomputable def PVM.unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) : E →ₗ.[ℂ] E :=
  { domain := E_pvm.squareIntegrableDomain f
    toFun :=
      { toFun := fun x => Filter.limUnder Filter.atTop
          (fun n => E_pvm.truncatedIntegral f hf n (x : E))
        map_add' := by
          intro x y
          have hxy := (E_pvm.cauchySeq_truncatedIntegral f hf (x + y)).tendsto_limUnder
          have hx := (E_pvm.cauchySeq_truncatedIntegral f hf x).tendsto_limUnder
          have hy := (E_pvm.cauchySeq_truncatedIntegral f hf y).tendsto_limUnder
          apply tendsto_nhds_unique hxy
          have hfun :
              (fun n => E_pvm.truncatedIntegral f hf n ((x + y : _) : E)) =
                fun n => E_pvm.truncatedIntegral f hf n (x : E) +
                  E_pvm.truncatedIntegral f hf n (y : E) := by
            funext n
            change E_pvm.truncatedIntegral f hf n ((x : E) + (y : E)) = _
            exact map_add _ _ _
          rw [hfun]
          exact hx.add hy
        map_smul' := by
          intro c x
          have hcx := (E_pvm.cauchySeq_truncatedIntegral f hf (c • x)).tendsto_limUnder
          have hx := (E_pvm.cauchySeq_truncatedIntegral f hf x).tendsto_limUnder
          apply tendsto_nhds_unique hcx
          have hfun :
              (fun n => E_pvm.truncatedIntegral f hf n ((c • x : _) : E)) =
                fun n => c • E_pvm.truncatedIntegral f hf n (x : E) := by
            funext n
            change E_pvm.truncatedIntegral f hf n (c • (x : E)) = _
            exact map_smul _ _ _
          rw [hfun]
          exact hx.const_smul c } }

theorem PVM.mem_domain_unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (x : E) :
    x ∈ (E_pvm.unboundedIntegral f hf).domain ↔
      ∫⁻ t, ‖f t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤ :=
  Iff.rfl

/-- The diagonal matrix coefficient of the coordinate spectral integral is
the first moment of the associated scalar spectral measure. -/
theorem PVM.inner_coordinate_unboundedIntegral_self (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    @inner ℂ E _ (x : E)
        (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x) =
      ∫ t, (t : ℂ) ∂(E_pvm.scalarMeasure (x : E)) := by
  let coord : ℝ → ℂ := (↑)
  let hcoord : Measurable coord := Complex.continuous_ofReal.measurable
  have hxL2 : ∫⁻ t, ‖coord t‖₊ ^ 2
      ∂(E_pvm.scalarMeasure (x : E)) < ⊤ := by
    have hx := x.property
    change (∫⁻ t, ‖((t : ℂ))‖₊ ^ 2
      ∂(E_pvm.scalarMeasure (x : E))) < ⊤ at hx
    simpa only [coord] using hx
  have hsq : Integrable (fun t : ℝ ↦ ‖coord t‖ ^ 2)
      (E_pvm.scalarMeasure (x : E)) := by
    constructor
    · fun_prop
    · rw [hasFiniteIntegral_iff_enorm]
      simpa only [Real.enorm_of_nonneg (sq_nonneg _),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
        using hxL2
  have hmemLp : MemLp coord 2 (E_pvm.scalarMeasure (x : E)) :=
    (memLp_two_iff_integrable_sq_norm hcoord.aestronglyMeasurable).2 hsq
  have hcoordInt : Integrable coord (E_pvm.scalarMeasure (x : E)) :=
    hmemLp.integrable (by norm_num)
  have htrunc :=
    (E_pvm.cauchySeq_truncatedIntegral coord hcoord x).tendsto_limUnder
  change Filter.Tendsto
    (fun n ↦ E_pvm.truncatedIntegral coord hcoord n (x : E))
    Filter.atTop
    (nhds (E_pvm.unboundedIntegral coord hcoord x)) at htrunc
  have hinner : Filter.Tendsto
      (fun n ↦ @inner ℂ E _ (x : E)
        (E_pvm.truncatedIntegral coord hcoord n (x : E)))
      Filter.atTop
      (nhds (@inner ℂ E _ (x : E)
        (E_pvm.unboundedIntegral coord hcoord x))) :=
    Filter.Tendsto.inner tendsto_const_nhds htrunc
  have hintegral : Filter.Tendsto
      (fun n ↦ ∫ t, PVM.spectralTruncation coord n t
        ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop
      (nhds (∫ t, coord t ∂(E_pvm.scalarMeasure (x : E)))) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖coord t‖)
    · intro n
      exact (PVM.spectralTruncation_measurable coord hcoord n).aestronglyMeasurable
    · exact hcoordInt.norm
    · intro n
      apply ae_of_all
      intro t
      unfold PVM.spectralTruncation
      split_ifs
      · exact le_rfl
      · simp
    · exact ae_of_all _ fun t ↦ PVM.spectralTruncation_tendsto coord t
  apply tendsto_nhds_unique hinner
  simpa only [PVM.truncatedIntegral, E_pvm.inner_integral_self, coord, hcoord]
    using hintegral

/-- The pointwise `L²` identity comparing a bounded spectral integral with an unbounded
spectral integral on the latter's domain. -/
theorem PVM.ofReal_norm_sq_integral_sub_unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) - E_pvm.unboundedIntegral g hg x‖ ^ 2) =
      ∫⁻ r, ‖f r - g r‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
  let C : ℝ := Classical.choose hbdd
  have hC : ∀ r, ‖f r‖ ≤ C := Classical.choose_spec hbdd
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let gn : ℕ → ℝ → ℂ := fun n => PVM.spectralTruncation g n
  have hgn_meas (n : ℕ) : Measurable (gn n) :=
    PVM.spectralTruncation_measurable g hg n
  have hgn_bdd (n : ℕ) : ∀ r, ‖gn n r‖ ≤ n :=
    PVM.norm_spectralTruncation_le g n
  have hgn_norm (n : ℕ) (r : ℝ) : ‖gn n r‖ ≤ ‖g r‖ := by
    unfold gn PVM.spectralTruncation
    by_cases hr : ‖g r‖ ≤ n
    · rw [ite_eq_left hr]
    · rw [ite_eq_right hr, norm_zero]
      exact norm_nonneg _
  have hdiff_bdd (n : ℕ) : ∀ r, ‖(f - gn n) r‖ ≤ C + n := by
    intro r
    change ‖f r - gn n r‖ ≤ C + n
    exact (norm_sub_le _ _).trans (add_le_add (hC r) (hgn_bdd n r))
  have hidentity (n : ℕ) :
      ENNReal.ofReal
          (‖E_pvm.integral f hf hbdd (x : E) -
            E_pvm.truncatedIntegral g hg n (x : E)‖ ^ 2) =
        ∫⁻ r, ‖f r - gn n r‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
    have hL2 := E_pvm.ofReal_norm_sq_integral
      (f - gn n) (hf.sub (hgn_meas n)) ⟨C + n, hdiff_bdd n⟩ (x : E)
    rw [E_pvm.integral_sub f (gn n) hf (hgn_meas n) hbdd
      ⟨n, hgn_bdd n⟩ ⟨C + n, hdiff_bdd n⟩] at hL2
    simpa only [PVM.truncatedIntegral, gn, Pi.sub_apply, sub_apply] using hL2
  have htrunc := (E_pvm.cauchySeq_truncatedIntegral g hg x).tendsto_limUnder
  change Filter.Tendsto
    (fun n => E_pvm.truncatedIntegral g hg n (x : E)) Filter.atTop
    (nhds (E_pvm.unboundedIntegral g hg x)) at htrunc
  have hleft : Filter.Tendsto
      (fun n => ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) -
          E_pvm.truncatedIntegral g hg n (x : E)‖ ^ 2))
      Filter.atTop
      (nhds (ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) - E_pvm.unboundedIntegral g hg x‖ ^ 2))) := by
    exact ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub htrunc).norm.pow 2)
  have hgSq_meas : Measurable
      (fun r => (↑(‖g r‖₊ ^ 2) : ENNReal)) :=
    ((hg.nnnorm.pow_const 2).coe_nnreal_ennreal)
  let bound : ℝ → ENNReal := fun r =>
    2 * (ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal))
  have hbound_meas : Measurable bound := by
    unfold bound
    exact measurable_const.mul (measurable_const.add hgSq_meas)
  have hpoint_bound (n : ℕ) (r : ℝ) :
      (↑(‖f r - gn n r‖₊ ^ 2) : ENNReal) ≤ bound r := by
    have hnorm : ‖f r - gn n r‖ ≤ C + ‖g r‖ :=
      (norm_sub_le _ _).trans (add_le_add (hC r) (hgn_norm n r))
    have hsquare : ‖f r - gn n r‖ ^ 2 ≤ 2 * (C ^ 2 + ‖g r‖ ^ 2) := by
      calc
        ‖f r - gn n r‖ ^ 2 ≤ (C + ‖g r‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (add_nonneg hC_nonneg (norm_nonneg _))).2 hnorm
        _ ≤ 2 * (C ^ 2 + ‖g r‖ ^ 2) := add_sq_le
    change ‖f r - gn n r‖ₑ ^ 2 ≤ bound r
    calc
      ‖f r - gn n r‖ₑ ^ 2 = ENNReal.ofReal (‖f r - gn n r‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ ≤ ENNReal.ofReal (2 * (C ^ 2 + ‖g r‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hsquare
      _ = bound r := by
        unfold bound
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add (sq_nonneg C) (sq_nonneg ‖g r‖),
          ENNReal.ofReal_pow (norm_nonneg (g r)) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
        norm_num
  have hbound_finite : (∫⁻ r, bound r ∂(E_pvm.scalarMeasure (x : E))) ≠ ⊤ := by
    have hconst :
        (∫⁻ _r : ℝ, ENNReal.ofReal (C ^ 2) ∂(E_pvm.scalarMeasure (x : E))) < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (E_pvm.scalarMeasure_lt_top (x : E) Set.univ)
    have hsum :
        (∫⁻ r, ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal)
          ∂(E_pvm.scalarMeasure (x : E))) < ⊤ := by
      rw [lintegral_add_left measurable_const]
      exact (ENNReal.add_lt_top).2 ⟨hconst, x.property⟩
    unfold bound
    have hmul :
        (∫⁻ r, (2 : ENNReal) *
          (ENNReal.ofReal (C ^ 2) + (↑(‖g r‖₊ ^ 2) : ENNReal))
            ∂(E_pvm.scalarMeasure (x : E))) =
          2 * ∫⁻ r, ENNReal.ofReal (C ^ 2) +
            (↑(‖g r‖₊ ^ 2) : ENNReal) ∂(E_pvm.scalarMeasure (x : E)) :=
      lintegral_const_mul 2 (measurable_const.add hgSq_meas)
    rw [hmul]
    exact (ENNReal.mul_lt_top (by norm_num) hsum).ne
  have hright : Filter.Tendsto
      (fun n => ∫⁻ r, (↑(‖f r - gn n r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))
      Filter.atTop
      (nhds (∫⁻ r, (↑(‖f r - g r‖₊ ^ 2) : ENNReal)
        ∂(E_pvm.scalarMeasure (x : E)))) := by
    apply tendsto_lintegral_of_dominated_convergence bound
    · intro n
      exact ((hf.sub (hgn_meas n)).nnnorm.pow_const 2).coe_nnreal_ennreal
    · intro n
      exact ae_of_all _ (hpoint_bound n)
    · exact hbound_finite
    · apply ae_of_all
      intro r
      have hsub : Filter.Tendsto (fun n => f r - gn n r) Filter.atTop
          (nhds (f r - g r)) :=
        tendsto_const_nhds.sub (PVM.spectralTruncation_tendsto g r)
      have hreal := ENNReal.tendsto_ofReal (hsub.norm.pow 2)
      convert hreal using 1
      · ext n
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
      · rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm,
          enorm_eq_nnnorm, ENNReal.coe_pow]
  apply tendsto_nhds_unique hleft
  convert hright using 1
  · ext n
    exact hidentity n
  · congr 1

private noncomputable def complexIndicator (S : Set ℝ) (r : ℝ) : ℂ :=
  S.indicator (fun _ => (1 : ℂ)) r

private theorem complexIndicator_measurable {S : Set ℝ}
    (hS : MeasurableSet S) : Measurable (complexIndicator S) := by
  exact measurable_const.indicator hS

private theorem complexIndicator_bounded (S : Set ℝ) :
    ∃ C, ∀ r, ‖complexIndicator S r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  by_cases hr : r ∈ S
  · rw [complexIndicator, Set.indicator_of_mem hr, norm_one]
  · rw [complexIndicator, Set.indicator_of_notMem hr, norm_zero]
    exact zero_le_one

private theorem complexIndicator_mul_bounded
    (S : Set ℝ) (f : ℝ → ℂ) {C : ℝ} (hf : ∀ r, ‖f r‖ ≤ C) :
    ∃ D, ∀ r, ‖complexIndicator S r * f r‖ ≤ D := by
  refine ⟨C, fun r => ?_⟩
  by_cases hr : r ∈ S
  · rw [complexIndicator, Set.indicator_of_mem hr, one_mul]
    exact hf r
  · rw [complexIndicator, Set.indicator_of_notMem hr, zero_mul, norm_zero]
    exact (norm_nonneg (f 0)).trans (hf 0)

private theorem PVM.integral_complexIndicator (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E_pvm.integral (complexIndicator S) (complexIndicator_measurable hS)
      (complexIndicator_bounded S) = E_pvm.proj S := by
  let s : SimpleFunc ℝ ℂ :=
    SimpleFunc.piecewise S hS (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)
  have hsfun : ∀ r, s r = complexIndicator S r := by
    intro r
    dsimp only [s]
    by_cases hr : r ∈ S
    · rw [SimpleFunc.piecewise_apply, ite_eq_left hr,
        SimpleFunc.const_apply, complexIndicator, Set.indicator_of_mem hr]
    · rw [SimpleFunc.piecewise_apply, ite_eq_right hr,
        SimpleFunc.const_apply, complexIndicator, Set.indicator_of_notMem hr]
  have hU : TendstoUniformly (fun _n : ℕ => fun r => s r)
      (complexIndicator S) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    apply Filter.Eventually.of_forall
    intro n r
    rw [hsfun r, dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (complexIndicator S) (complexIndicator_measurable hS)
      (complexIndicator_bounded S) (fun _n => s) hU
  have hsint : E_pvm.simpleIntegral s = E_pvm.proj S := by
    simpa only [one_smul] using E_pvm.simpleIntegral_piecewise_const S hS 1
  have hlim' : Filter.Tendsto (fun _n : ℕ => E_pvm.proj S)
      Filter.atTop
      (nhds (E_pvm.integral (complexIndicator S)
        (complexIndicator_measurable hS) (complexIndicator_bounded S))) := by
    convert hlim using 1
    funext n
    exact hsint.symm
  exact tendsto_nhds_unique hlim' tendsto_const_nhds

private theorem PVM.proj_mul_integral (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C) :
    E_pvm.proj S * E_pvm.integral f hf hbdd =
      E_pvm.integral (fun r => complexIndicator S r * f r)
        ((complexIndicator_measurable hS).mul hf)
        (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd)) := by
  rw [← E_pvm.integral_complexIndicator S hS]
  symm
  exact E_pvm.integral_mul (complexIndicator S) f
    (complexIndicator_measurable hS) hf (complexIndicator_bounded S) hbdd
    (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd))

/-- The scalar measure of a bounded spectral-integral vector is the original scalar measure
weighted by the squared norm of the integrand. -/
theorem PVM.scalarMeasure_integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (x : E) :
    E_pvm.scalarMeasure (E_pvm.integral f hf hbdd x) =
      (E_pvm.scalarMeasure x).withDensity
        (fun r => ((↑(‖f r‖₊ ^ 2) : ENNReal))) := by
  apply Measure.ext
  intro S hS
  rw [E_pvm.scalarMeasure_apply _ S hS,
    E_pvm.scalarContent_eq_norm_sq _ S hS]
  rw [show E_pvm.proj S (E_pvm.integral f hf hbdd x) =
      E_pvm.integral (fun r => complexIndicator S r * f r)
        ((complexIndicator_measurable hS).mul hf)
        (complexIndicator_mul_bounded S f (Classical.choose_spec hbdd)) x by
    have happ := congrArg (fun T : E →L[ℂ] E => T x)
      (E_pvm.proj_mul_integral S hS f hf hbdd)
    simpa only [mul_apply_eq_comp] using happ]
  rw [E_pvm.ofReal_norm_sq_integral]
  rw [withDensity_apply _ hS]
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ S
  · rw [Set.indicator_of_mem hr, complexIndicator,
      Set.indicator_of_mem hr, one_mul, ENNReal.coe_pow]
  · rw [Set.indicator_of_notMem hr, complexIndicator,
      Set.indicator_of_notMem hr, zero_mul, nnnorm_zero]
    norm_num

/-- A bounded spectral integral lies in the domain of an unbounded spectral integral when
the pointwise product of their integrands is bounded. -/
theorem PVM.integral_mem_domain_unboundedIntegral
    (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (hprodBdd : ∃ C, ∀ r : ℝ, ‖g r * f r‖ ≤ C) (x : E) :
    E_pvm.integral f hf hbdd x ∈
      (E_pvm.unboundedIntegral g hg).domain := by
  rw [E_pvm.mem_domain_unboundedIntegral]
  rw [E_pvm.scalarMeasure_integral f hf hbdd x]
  let density : ℝ → ENNReal := fun r => (↑(‖f r‖₊ ^ 2) : ENNReal)
  have hdensity : Measurable density :=
    ((hf.nnnorm.pow_const 2).coe_nnreal_ennreal)
  have hgSq : Measurable (fun r : ℝ =>
      (↑(‖g r‖₊ ^ 2) : ENNReal)) :=
    ((hg.nnnorm.pow_const 2).coe_nnreal_ennreal)
  change (∫⁻ t : ℝ, (↑(‖g t‖₊ ^ 2) : ENNReal)
    ∂(E_pvm.scalarMeasure x).withDensity density) < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hgSq]
  have hfun : (fun r : ℝ => density r * (↑(‖g r‖₊ ^ 2) : ENNReal)) =
      (fun r : ℝ => (↑(‖g r * f r‖₊ ^ 2) : ENNReal)) := by
    funext r
    unfold density
    rw [← ENNReal.coe_mul, nnnorm_mul, mul_pow, mul_comm]
  change (∫⁻ r : ℝ, density r * (↑(‖g r‖₊ ^ 2) : ENNReal)
    ∂E_pvm.scalarMeasure x) < ⊤
  rw [hfun]
  have hL2 := E_pvm.ofReal_norm_sq_integral
    (fun r => g r * f r) (hg.mul hf) hprodBdd x
  have hL2' : ENNReal.ofReal
      (‖E_pvm.integral (fun r => g r * f r) (hg.mul hf) hprodBdd x‖ ^ 2) =
      ∫⁻ r : ℝ, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
        ∂E_pvm.scalarMeasure x := by
    simpa only [ENNReal.coe_pow] using hL2
  rw [← hL2']
  exact ENNReal.ofReal_lt_top

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem tendsto_of_ofReal_norm_sq_sub_tendsto_zero
    {u : ℕ → E} {y : E}
    (h : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖u n - y‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds y) := by
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hsq : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero] using hreal
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hnorm

private theorem PVM.tendsto_integral_boundedTruncation
    (E_pvm : PVM E) (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    Filter.Tendsto
      (fun n => E_pvm.integral (PVM.spectralTruncation g n)
        (PVM.spectralTruncation_measurable g hg n)
        ⟨n, PVM.norm_spectralTruncation_le g n⟩ (x : E))
      Filter.atTop (nhds (E_pvm.unboundedIntegral g hg x)) := by
  exact (E_pvm.cauchySeq_truncatedIntegral g hg x).tendsto_limUnder

private theorem boundedTruncation_mul_bounded
    (g f : ℝ → ℂ) (n : ℕ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C) :
    ∃ C, ∀ r, ‖(PVM.spectralTruncation g n * f) r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨n * C, fun r => ?_⟩
  change ‖PVM.spectralTruncation g n r * f r‖ ≤ (n : ℝ) * C
  rw [norm_mul]
  exact mul_le_mul (PVM.norm_spectralTruncation_le g n r) (hC r)
    (norm_nonneg (f r)) (Nat.cast_nonneg n)

private theorem sub_bounded
    (f g : ℝ → ℂ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    ∃ C, ∀ r, ‖f r - g r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun r => ?_⟩
  exact (norm_sub_le (f r) (g r)).trans (add_le_add (hC r) (hD r))

private theorem boundedTruncation_mul_sub_error_measurable
    (g f : ℝ → ℂ) (hg : Measurable g) (hf : Measurable f) (n : ℕ) :
    Measurable (fun r =>
      (↑(‖PVM.spectralTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal)) := by
  have hnorm := ((((PVM.spectralTruncation_measurable g hg n).mul hf).sub
    (hg.mul hf)).nnnorm.pow_const 2)
  exact hnorm.coe_nnreal_ennreal

private theorem boundedTruncation_mul_sub_error_le
    (g f : ℝ → ℂ) (n : ℕ) (r : ℝ) :
    (↑(‖PVM.spectralTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal) ≤
      (↑(‖g r * f r‖₊ ^ 2) : ENNReal) := by
  by_cases hr : ‖g r‖ ≤ n
  · rw [PVM.spectralTruncation, ite_eq_left hr, sub_self, nnnorm_zero,
      zero_pow (by omega)]
    exact bot_le
  · rw [PVM.spectralTruncation, ite_eq_right hr, zero_mul, zero_sub, nnnorm_neg]

private theorem boundedTruncation_mul_sub_error_tendsto_zero
    (g f : ℝ → ℂ) (r : ℝ) :
    Filter.Tendsto
      (fun n =>
        (↑(‖PVM.spectralTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g r‖
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  rw [PVM.spectralTruncation, ite_eq_left, sub_self, nnnorm_zero,
    zero_pow (by omega), ENNReal.coe_zero]
  exact hN.trans (Nat.cast_le.2 hn)

private theorem PVM.tendsto_integral_boundedTruncation_mul
    (E_pvm : PVM E) (g f : ℝ → ℂ) (hg : Measurable g) (hf : Measurable f)
    (hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hprodBdd : ∃ C, ∀ r, ‖(g * f) r‖ ≤ C) (x : E) :
    Filter.Tendsto
      (fun n => E_pvm.integral (PVM.spectralTruncation g n * f)
        ((PVM.spectralTruncation_measurable g hg n).mul hf)
        (boundedTruncation_mul_bounded g f n hfBdd) x)
      Filter.atTop
      (nhds (E_pvm.integral (g * f) (hg.mul hf) hprodBdd x)) := by
  apply tendsto_of_ofReal_norm_sq_sub_tendsto_zero
  have htargetL2 := E_pvm.ofReal_norm_sq_integral
    (g * f) (hg.mul hf) hprodBdd x
  have hdomFinite :
      (∫⁻ r, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
        ∂E_pvm.scalarMeasure x) ≠ ⊤ := by
    have htargetL2' : ENNReal.ofReal
        (‖E_pvm.integral (g * f) (hg.mul hf) hprodBdd x‖ ^ 2) =
        ∫⁻ r, (↑(‖g r * f r‖₊ ^ 2) : ENNReal)
          ∂E_pvm.scalarMeasure x := by
      simpa only [Pi.mul_apply, ENNReal.coe_pow] using htargetL2
    rw [← htargetL2']
    exact ENNReal.ofReal_ne_top
  have herr : Filter.Tendsto
      (fun n => ∫⁻ r,
        (↑(‖PVM.spectralTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal)
          ∂E_pvm.scalarMeasure x)
      Filter.atTop (nhds 0) := by
    have h := tendsto_lintegral_of_dominated_convergence
      (μ := E_pvm.scalarMeasure x)
      (F := fun n r =>
        (↑(‖PVM.spectralTruncation g n r * f r - g r * f r‖₊ ^ 2) : ENNReal))
      (f := fun _ => 0)
      (fun r => (↑(‖g r * f r‖₊ ^ 2) : ENNReal))
      (fun n => boundedTruncation_mul_sub_error_measurable g f hg hf n)
      (fun n => ae_of_all _ fun r => boundedTruncation_mul_sub_error_le g f n r)
      hdomFinite
      (ae_of_all _ fun r => boundedTruncation_mul_sub_error_tendsto_zero g f r)
    simpa only [lintegral_zero] using h
  apply herr.congr'
  apply Filter.Eventually.of_forall
  intro n
  let fn : ℝ → ℂ := PVM.spectralTruncation g n * f
  let p : ℝ → ℂ := g * f
  have hfn : Measurable fn := (PVM.spectralTruncation_measurable g hg n).mul hf
  have hp : Measurable p := hg.mul hf
  have hfnBdd : ∃ C, ∀ r, ‖fn r‖ ≤ C :=
    boundedTruncation_mul_bounded g f n hfBdd
  have hsubBdd : ∃ C, ∀ r, ‖fn r - p r‖ ≤ C :=
    sub_bounded fn p hfnBdd hprodBdd
  have hL2 := E_pvm.ofReal_norm_sq_integral (fn - p)
    (hfn.sub hp) hsubBdd x
  rw [E_pvm.integral_sub fn p hfn hp hfnBdd hprodBdd hsubBdd] at hL2
  simpa only [fn, p, Pi.mul_apply, Pi.sub_apply, sub_apply,
    ENNReal.coe_pow] using hL2.symm

/-- Unbounded spectral integration acts on bounded spectral-integral vectors by pointwise
multiplication, provided the product integrand is bounded. -/
theorem PVM.unboundedIntegral_integral
    (E_pvm : PVM E) (f : ℝ → ℂ) (hf : Measurable f)
    (hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (hprodBdd : ∃ C, ∀ r, ‖(g * f) r‖ ≤ C) (x : E) :
    E_pvm.unboundedIntegral g hg
        ⟨E_pvm.integral f hf hfBdd x,
          E_pvm.integral_mem_domain_unboundedIntegral
            f hf hfBdd g hg hprodBdd x⟩ =
      E_pvm.integral (g * f) (hg.mul hf) hprodBdd x := by
  let z : (E_pvm.unboundedIntegral g hg).domain :=
    ⟨E_pvm.integral f hf hfBdd x,
      E_pvm.integral_mem_domain_unboundedIntegral
        f hf hfBdd g hg hprodBdd x⟩
  have hleft := E_pvm.tendsto_integral_boundedTruncation g hg z
  have hright := E_pvm.tendsto_integral_boundedTruncation_mul
    g f hg hf hfBdd hprodBdd x
  have hseq (n : ℕ) :
      E_pvm.integral (PVM.spectralTruncation g n)
          (PVM.spectralTruncation_measurable g hg n)
          ⟨n, PVM.norm_spectralTruncation_le g n⟩ (z : E) =
        E_pvm.integral (PVM.spectralTruncation g n * f)
          ((PVM.spectralTruncation_measurable g hg n).mul hf)
          (boundedTruncation_mul_bounded g f n hfBdd) x := by
    have hop := E_pvm.integral_mul (PVM.spectralTruncation g n) f
      (PVM.spectralTruncation_measurable g hg n) hf
      ⟨n, PVM.norm_spectralTruncation_le g n⟩ hfBdd
      (boundedTruncation_mul_bounded g f n hfBdd)
    have happ := congrArg (fun T : E →L[ℂ] E => T x) hop
    simpa only [mul_apply_eq_comp, z] using happ.symm
  have hleft' : Filter.Tendsto
      (fun n => E_pvm.integral (PVM.spectralTruncation g n * f)
        ((PVM.spectralTruncation_measurable g hg n).mul hf)
        (boundedTruncation_mul_bounded g f n hfBdd) x)
      Filter.atTop (nhds (E_pvm.unboundedIntegral g hg z)) := by
    apply hleft.congr'
    exact Filter.Eventually.of_forall hseq
  change E_pvm.unboundedIntegral g hg z = _
  exact tendsto_nhds_unique hleft' hright

open Filter

private theorem PVM.integral_const_for_symmetry (E_pvm : PVM E) (z : ℂ) :
    E_pvm.integral (fun _ : ℝ => z) measurable_const
      ⟨‖z‖, fun _ => le_refl _⟩ = z • 1 := by
  exact E_pvm.integral_const z

private theorem coordinateImaginaryDistances (r : ℝ) :
    ‖Complex.I - (r : ℂ)‖₊ ^ 2 = ‖-Complex.I - (r : ℂ)‖₊ ^ 2 := by
  apply NNReal.eq
  change ‖Complex.I - (r : ℂ)‖ ^ 2 = ‖-Complex.I - (r : ℂ)‖ ^ 2
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  norm_num

private theorem PVM.coordinate_inner_self_real (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    (starRingEnd ℂ) (@inner ℂ E _
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable x) (x : E)) =
      @inner ℂ E _
        (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x) (x : E) := by
  let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  let fi : ℝ → ℂ := fun _ => Complex.I
  let fni : ℝ → ℂ := fun _ => -Complex.I
  have hfi : Measurable fi := measurable_const
  have hfni : Measurable fni := measurable_const
  let hbi : ∃ C, ∀ r, ‖fi r‖ ≤ C :=
    ⟨‖Complex.I‖, fun _ => le_refl _⟩
  let hbni : ∃ C, ∀ r, ‖fni r‖ ≤ C :=
    ⟨‖-Complex.I‖, fun _ => le_refl _⟩
  have hi := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    fi hfi hbi ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hni := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    fni hfni hbni ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hright :
      (∫⁻ r, ‖fi r - (r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E))) =
        ∫⁻ r, ‖fni r - (r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
    apply lintegral_congr
    intro r
    exact_mod_cast coordinateImaginaryDistances r
  have hsq :
      ‖Complex.I • (x : E) - A x‖ ^ 2 =
        ‖(-Complex.I) • (x : E) - A x‖ ^ 2 := by
    have hofReal : ENNReal.ofReal
          (‖E_pvm.integral fi hfi hbi (x : E) - A x‖ ^ 2) =
        ENNReal.ofReal
          (‖E_pvm.integral fni hfni hbni (x : E) - A x‖ ^ 2) :=
      hi.trans (hright.trans hni.symm)
    have hsquares := (ENNReal.ofReal_eq_ofReal_iff
      (sq_nonneg ‖E_pvm.integral fi hfi hbi (x : E) - A x‖)
      (sq_nonneg ‖E_pvm.integral fni hfni hbni (x : E) - A x‖)).mp hofReal
    rw [show E_pvm.integral fi hfi hbi = Complex.I • 1 by
      exact E_pvm.integral_const_for_symmetry Complex.I,
      show E_pvm.integral fni hfni hbni = (-Complex.I) • 1 by
        exact E_pvm.integral_const_for_symmetry (-Complex.I)] at hsquares
    simpa only [smul_apply, one_apply_eq_self] using hsquares
  have hIm : (@inner ℂ E _ (x : E) (A x)).im = 0 := by
    have hstarI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
    have hstarNegI : (starRingEnd ℂ) (-Complex.I) = Complex.I := by
      rw [map_neg, Complex.conj_I, neg_neg]
    have hreI : RCLike.re (Complex.I * @inner ℂ E _ (x : E) (A x)) =
        -(@inner ℂ E _ (x : E) (A x)).im := by
      change (Complex.I * @inner ℂ E _ (x : E) (A x)).re = _
      rw [Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    have hreNegI : RCLike.re (-(Complex.I * @inner ℂ E _ (x : E) (A x))) =
        (@inner ℂ E _ (x : E) (A x)).im := by
      rw [map_neg, hreI]
      ring
    rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), norm_smul, norm_smul,
      Complex.norm_I, norm_neg, Complex.norm_I, one_mul,
      inner_smul_left, inner_smul_left, hstarI, hstarNegI,
      neg_mul, hreI, hreNegI] at hsq
    linarith
  change (starRingEnd ℂ) (@inner ℂ E _ (A x) (x : E)) =
    @inner ℂ E _ (A x) (x : E)
  apply Complex.conj_eq_iff_im.mpr
  rw [← inner_conj_symm (A x) (x : E), Complex.conj_im, hIm, neg_zero]

omit [CompleteSpace E] in
private theorem linearPMap_isFormalAdjoint_self_of_inner_real
    (A : E →ₗ.[ℂ] E)
    (hreal : ∀ z : A.domain,
      (starRingEnd ℂ) (@inner ℂ E _ (A z) (z : E)) =
        @inner ℂ E _ (A z) (z : E)) :
    A.IsFormalAdjoint A := by
  intro x y
  have hpolarization (a b : A.domain) :
      @inner ℂ E _ (A b) (a : E) =
        (@inner ℂ E _ (A (a + b)) ((a + b : A.domain) : E) -
            @inner ℂ E _ (A (a - b)) ((a - b : A.domain) : E) +
              Complex.I * @inner ℂ E _ (A (a + Complex.I • b))
                ((a + Complex.I • b : A.domain) : E) -
            Complex.I * @inner ℂ E _ (A (a - Complex.I • b))
              ((a - Complex.I • b : A.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left, inner_add_right,
      LinearPMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_I,
      ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right, mul_add,
      ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  have hpolarization' (a b : A.domain) :
      @inner ℂ E _ (A a) (b : E) =
        (@inner ℂ E _ (A (a + b)) ((a + b : A.domain) : E) -
            @inner ℂ E _ (A (a - b)) ((a - b : A.domain) : E) -
              Complex.I * @inner ℂ E _ (A (a + Complex.I • b))
                ((a + Complex.I • b : A.domain) : E) +
            Complex.I * @inner ℂ E _ (A (a - Complex.I • b))
              ((a - Complex.I • b : A.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left, inner_add_right,
      LinearPMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_I,
      ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right, mul_add,
      ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  rw [← inner_conj_symm (x : E) (A y), hpolarization x y]
  simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
  simp only [← starRingEnd_apply]
  rw [hreal (x + y), hreal (x - y), hreal (x + Complex.I • y),
    hreal (x - Complex.I • y)]
  simp only [Complex.conj_I, map_ofNat]
  rw [hpolarization' x y]
  norm_num
  ring

/-- Integration of the real coordinate against any PVM is a symmetric partial operator. -/
theorem PVM.coordinate_unboundedIntegral_isFormalAdjoint (E_pvm : PVM E) :
    let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable
    A.IsFormalAdjoint A := by
  dsimp only
  apply linearPMap_isFormalAdjoint_self_of_inner_real
  exact E_pvm.coordinate_inner_self_real

private theorem PVM.scalarMeasure_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (x : E) :
    E₁.scalarMeasure x = E₂.scalarMeasure x := by
  apply Measure.ext
  intro S hS
  rw [E₁.scalarMeasure_apply x S hS, E₂.scalarMeasure_apply x S hS]
  unfold PVM.scalarContent
  rw [hproj S hS]

private theorem PVM.simpleIntegral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (s : SimpleFunc ℝ ℂ) :
    E₁.simpleIntegral s = E₂.simpleIntegral s := by
  classical
  unfold PVM.simpleIntegral
  apply Finset.sum_congr rfl
  intro z hz
  rw [hproj (s ⁻¹' {z}) (s.measurableSet_fiber z)]

private theorem PVM.integral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    E₁.integral f hf hbdd = E₂.integral f hf hbdd := by
  unfold PVM.integral
  congr 1
  funext n
  exact PVM.simpleIntegral_eq_of_proj_eq_on_measurable E₁ E₂ hproj _

/-- Unbounded spectral integration depends only on a PVM's values on measurable sets. -/
theorem PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (f : ℝ → ℂ) (hf : Measurable f) :
    E₁.unboundedIntegral f hf = E₂.unboundedIntegral f hf := by
  apply LinearPMap.ext
  · ext x
    rw [E₁.mem_domain_unboundedIntegral f hf x,
      E₂.mem_domain_unboundedIntegral f hf x,
      PVM.scalarMeasure_eq_of_proj_eq_on_measurable E₁ E₂ hproj x]
  · intro x hx hy
    unfold PVM.unboundedIntegral
    apply congrArg (fun g : ℕ → E => limUnder atTop g)
    funext n
    exact congrArg (fun T : E →L[ℂ] E => T x)
      (PVM.integral_eq_of_proj_eq_on_measurable E₁ E₂ hproj _ _ _)
