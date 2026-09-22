/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Finite-exponent closure of weak gradients

This file records the finite-`p` graph-closure step for the concrete
coordinate weak-gradient representation.  It is deliberately independent of
any zero-trace approximation: that additional closure property is supplied by
the next layer.
-/

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

private theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent) {h : Vec d → ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h p.conjugate.exponent (volume.restrict U))
    (hf : ∀ n, MemLp (f n) p.exponent (volume.restrict U))
    (hg : MemLp g p.exponent (volume.restrict U))
    (htend : Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in U, f n x * h x ∂volume)
      atTop (nhds (∫ x in U, g x * h x ∂volume)) := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
  let : ENNReal.HolderConjugate p.conjugate.exponent p.exponent := inferInstance
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp (hh.mul' (hf n)))
  have hgh_int : Integrable (fun x => g x * h x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hh.mul' hg))
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ)
        = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) p.exponent μ *
      eLpNorm h p.conjugate.exponent μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h p.conjugate.exponent μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.eLpNorm_ne_top)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p.exponent) (q := p.conjugate.exponent) (r := 1)
      (fun a b : ℝ => a * b) 1 (continuous_fst.mul continuous_snd)
      ((hf n).sub hg).aestronglyMeasurable hh.aestronglyMeasurable hbound
    simpa [B] using! h
  calc
    ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
      have hmeas : AEStronglyMeasurable (fun x => (f n x - g x) * h x) μ :=
        ((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_enorm hmeas]
      simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
      apply ENNReal.toReal_mono _ hHolder
      exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_ne_top hh.eLpNorm_ne_top

/-- The finite-`p` weak derivative graph is closed under coordinatewise
`L^p` convergence. -/
theorem HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent) {i : Fin d}
    {u gi : Vec d → ℝ} {u_n g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hgi : MemLp gi p.exponent (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) p.exponent (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_g : Tendsto
      (fun n => eLpNorm (fun x => g_n n x - gi x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) p.conjugate.exponent
      (volume.restrict U) := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφ_compact.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hφmem : MemLp φ p.conjugate.exponent (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
  have hlhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp
    p hDφ hu_n hu htend_u
  have hrhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm_finiteLp
    p hφmem hg_n hgi htend_g
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
        = -(∫ x in U, g_n n x * φ x ∂volume) :=
    fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Tendsto
      (fun n => -(∫ x in U, g_n n x * φ x ∂volume))
      atTop (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n
    rw [heq_n n]
  exact tendsto_nhds_unique hlhs' hrhs.neg

/-- The finite-`p` weak-gradient graph is closed under coordinatewise `L^p`
convergence. -/
theorem HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp
    {d : ℕ} {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {u_n : ℕ → Vec d → ℝ} {Du_n : ℕ → Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hDu_n : ∀ n, GradMemLpOn U p.exponent (Du_n n))
    (hweak : ∀ n, HasWeakGradientOn U (u_n n) (Du_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => Du_n n x i - Du x i) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakGradientOn U u Du := by
  intro i
  exact HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp p hu (hDu i)
    hu_n (fun n => hDu_n n i) (fun n => hweak n i) htend_u (htend_Du i)

end
end Homogenization
