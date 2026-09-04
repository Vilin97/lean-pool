/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KContinuity
import LeanPool.Feige.TransferProbability

/-!
# Nullity of the moving halfspace boundary

The continuity proof for `dirichletK` reduces to the fact that the
coordinate `E₀` has an atomless law and is independent of all other
coordinates.  This file supplies the atomlessness calculation for the
nonnegative exponential law and then applies the product decomposition of a
finite `Option`-indexed product.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Feige

/-- The pushed-forward nonnegative exponential law has no atoms. -/
theorem nnexpMeasure_singleton (x : NNReal) :
    nnexpMeasure {x} = 0 := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [nnexpMeasure, Measure.map_apply measurable_real_toNNReal
    (measurableSet_singleton x)]
  by_cases hx : x = 0
  · subst x
    have hpre :
        Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic (0 : ℝ) := by
      ext r
      simp [Real.toNNReal_eq_zero]
    rw [hpre, ← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _)]
    rw [ExponentialTransfer.expMeasure_one_Ioi (x := 0) le_rfl]
    simp
  · have hpre :
        Real.toNNReal ⁻¹' ({x} : Set NNReal) = {(x : ℝ)} := by
      ext r
      simp only [mem_preimage, mem_singleton_iff]
      exact Real.toNNReal_eq_iff_eq_coe hx
    rw [hpre, ExponentialTransfer.expMeasure_one_singleton]

instance nnexpMeasure.nullSingletonClass : NullSingletonClass nnexpMeasure :=
  ⟨nnexpMeasure_singleton⟩

/-- Every affine boundary in the definition of `K` is null: after splitting
off `E₀`, every fiber is either empty or a singleton. -/
theorem expProductMeasure_kBoundary (ι : Type*) [Fintype ι]
    (y : ι → ℝ) :
    expProductMeasure ι (kBoundary y) = 0 := by
  let e :
      (Option ι → NNReal) ≃ᵐ ((ι → NNReal) × NNReal) :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option ι ↦ NNReal)
  let μrest : Measure (ι → NNReal) := Measure.pi fun _ : ι ↦ nnexpMeasure
  have hmap :
      (μrest.prod nnexpMeasure).map e.symm = expProductMeasure ι := by
    simpa [e, μrest, expProductMeasure] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option ι ↦ nnexpMeasure))
  rw [← hmap, Measure.map_apply e.symm.measurable
    (measurableSet_kBoundary y)]
  have hs :
      MeasurableSet (e.symm ⁻¹' kBoundary y) :=
    (measurableSet_kBoundary y).preimage e.symm.measurable
  rw [Measure.prod_apply hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with rest
  have hfiber :
      Prod.mk rest ⁻¹' (e.symm ⁻¹' kBoundary y) =
        {z : NNReal |
          (∑ i, (y i - 1) * (rest i : ℝ)) = (z : ℝ)} := by
    ext z
    simp only [mem_preimage, kBoundary, mem_ofPred_eq, kLinear]
    rfl
  rw [hfiber]
  by_cases hnonneg : 0 ≤ ∑ i, (y i - 1) * (rest i : ℝ)
  · let z : NNReal :=
      ⟨∑ i, (y i - 1) * (rest i : ℝ), hnonneg⟩
    have hset :
        {w : NNReal |
          (∑ i, (y i - 1) * (rest i : ℝ)) = (w : ℝ)} = {z} := by
      ext w
      simp only [mem_ofPred_eq, mem_singleton_iff]
      exact ⟨fun h ↦ NNReal.eq h.symm, fun h ↦ by subst w; rfl⟩
    rw [hset, nnexpMeasure_singleton]
    rfl
  · have hset :
        {w : NNReal |
          (∑ i, (y i - 1) * (rest i : ℝ)) = (w : ℝ)} = ∅ := by
      ext w
      simp only [not_le] at hnonneg
      simp only [mem_empty_iff_false, iff_false]
      exact ne_of_lt (hnonneg.trans_le w.coe_nonneg)
    rw [hset, measure_empty]
    rfl

/-- The Dirichlet statistic is sequentially continuous everywhere. -/
theorem tendsto_dirichletK' {ι : Type*} [Fintype ι]
    {yseq : ℕ → ι → ℝ} {y : ι → ℝ}
    (hy : Filter.Tendsto yseq Filter.atTop (nhds y)) :
    Filter.Tendsto (fun n ↦ dirichletK (yseq n)) Filter.atTop
      (nhds (dirichletK y)) :=
  tendsto_dirichletK hy (expProductMeasure_kBoundary ι y)

/-- Continuity of the Dirichlet statistic, used to complete Theorem 2.1. -/
theorem continuous_dirichletK {ι : Type*} [Fintype ι] :
    Continuous (dirichletK : (ι → ℝ) → ℝ) := by
  rw [continuous_iff_seqContinuous]
  intro yseq y hy
  exact tendsto_dirichletK' hy

end Feige
