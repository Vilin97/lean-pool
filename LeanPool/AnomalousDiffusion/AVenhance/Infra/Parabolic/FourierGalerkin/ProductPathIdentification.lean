/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakLimitPassage
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Identifying product and weak-path scalar limits

The pointwise weakly continuous Galerkin limit and the product-space limit have the same pairings
against separated time/spatial tests. The proof uses dominated convergence and the uniform scalar
energy bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The synchronized product scalar limit pairs with a separated test as the time integral of the
weakly continuous path pairing. -/
theorem FrozenDriftProblem.productScalar_pairing_eq_path_integral
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUprodWeak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    {η : ℝ → ℝ} (hηMem : MemLp η ⊤ GalerkinTimeMeasure)
    (ψ : ScalarTorusL2) :
    inner ℝ Uprod (scalarProductTestLp η ψ hηMem) =
      ∫ t, if ht : t ∈ Icc (0 : ℝ) 1 then
        η t * inner ℝ (u ⟨t, ht⟩) ψ else 0 ∂GalerkinTimeMeasure := by
  let fseq : ℕ → ℝ → ℝ := fun n t => η t *
    inner ℝ (P.scalarTimeFunction (σ n) t) ψ
  let flimit : ℝ → ℝ := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then
    η t * inner ℝ (u ⟨t, ht⟩) ψ else 0
  let C : ℝ := lpNorm η ⊤ GalerkinTimeMeasure
  have hCnonneg : 0 ≤ C := MeasureTheory.lpNorm_nonneg
  have hboundInt : Integrable (fun _ : ℝ => C * (P.scalarBound * ‖ψ‖))
      GalerkinTimeMeasure := integrable_const _
  have hfseqMeas (n : ℕ) : AEStronglyMeasurable (fseq n) GalerkinTimeMeasure := by
    have hpair : Continuous (fun t => inner ℝ (P.scalarTimeFunction (σ n) t) ψ) := by
      have hpair' : Continuous (fun t => inner ℝ ψ (P.scalarTimeFunction (σ n) t)) :=
        (innerSL ℝ ψ).continuous.comp (scalarTimeFunction_continuous P (σ n))
      exact hpair'.congr fun t => by simp [real_inner_comm]
    exact hηMem.aestronglyMeasurable.mul hpair.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂GalerkinTimeMeasure,
      ‖fseq n t‖ ≤ C * (P.scalarBound * ‖ψ‖) := by
    filter_upwards [MeasureTheory.ae_le_lpNorm_exponent_top hηMem,
      ae_restrict_mem measurableSet_Ioc] with t hηt ht
    have hηt' : |η t| ≤ C := by
      simpa [C, Real.norm_eq_abs] using hηt
    have hpathNorm := scalarTimeFunction_norm_bound P (σ n) ht
    rw [Real.norm_eq_abs]
    calc
      |η t * inner ℝ (P.scalarTimeFunction (σ n) t) ψ| =
          |η t| * |inner ℝ (P.scalarTimeFunction (σ n) t) ψ| := abs_mul _ _
      _ ≤ C * (‖P.scalarTimeFunction (σ n) t‖ * ‖ψ‖) :=
        mul_le_mul hηt' (abs_real_inner_le_norm _ _) (abs_nonneg _) hCnonneg
      _ ≤ C * (P.scalarBound * ‖ψ‖) := by
        gcongr
  have hpoint : ∀ᵐ t ∂GalerkinTimeMeasure,
      Tendsto (fun n => fseq n t) atTop (𝓝 (flimit t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hpath := hPathWeak ⟨t, htIcc⟩ ψ
    have hknown : Tendsto (fun n => η t * inner ℝ (P.scalarPath (σ n) ⟨t, htIcc⟩) ψ)
        atTop (𝓝 (η t * inner ℝ (u ⟨t, htIcc⟩) ψ)) :=
      tendsto_const_nhds.mul hpath
    have hseqEq : ∀ n, fseq n t =
        η t * inner ℝ (P.scalarPath (σ n) ⟨t, htIcc⟩) ψ := by
      intro n
      simp [fseq, scalarTimeFunction_eq_scalarPath P (σ n) ht]
    have hcongr := hknown.congr fun n => (hseqEq n).symm
    simpa only [flimit, dite_eq_left htIcc] using hcongr
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => C * (P.scalarBound * ‖ψ‖)) hfseqMeas hboundInt hbound hpoint
  have hpairTendsto : Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n))
        (scalarProductTestLp η ψ hηMem)) atTop (𝓝 (∫ t, flimit t ∂GalerkinTimeMeasure)) := by
    have heq : (fun n => ∫ t, fseq n t ∂GalerkinTimeMeasure) =ᶠ[atTop]
        fun n => inner ℝ (P.scalarProductLp (σ n))
          (scalarProductTestLp η ψ hηMem) := by
      filter_upwards with n
      exact (P.scalarProductLp_pairing_time (σ n) η hηMem ψ).symm
    exact Filter.Tendsto.congr' heq hDCT
  have hprodTendsto := hUprodWeak (scalarProductTestLp η ψ hηMem)
  have hcenter := tendsto_nhds_unique hprodTendsto hpairTendsto
  simpa [flimit, C] using hcenter

end AVenhance.Infra.Parabolic.FourierGalerkin

end
