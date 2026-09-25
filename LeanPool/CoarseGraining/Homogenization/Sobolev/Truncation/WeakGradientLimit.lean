/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Definitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.WeakDerivatives
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Weak Gradient Limit -/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Weak partial derivatives are closed under `L²` limits

If `uₙ → u` and `gₙ → gᵢ` in `L²(U)` and each `uₙ` has weak `i`-partial
derivative `gₙ`, then `u` has weak `i`-partial derivative `gᵢ`.  The pairing
identity `∫ uₙ ∂ᵢφ = −∫ gₙ φ` holds for each `n`; both sides are continuous in
the `L²` factor, so the identity passes to the limit.

Two spellings of the same principle are provided:

* one built on the Lebesgue `L²` realizations `MemScalarL2` / `toScalarL2` and
  `volumeMeasureOn U`, with an `L²` dominated-convergence helper
  (`hasWeakPartialDerivOn_of_tendsto_L2`);
* one built directly on `MemLp _ 2 (volume.restrict U)` via a
  Cauchy–Schwarz/Hölder pairing-continuity lemma, closing over both the partial
  derivative (`HasWeakPartialDerivOn.of_tendsto_eLpNorm_two`) and the full
  gradient (`HasWeakGradientOn.of_tendsto_eLpNorm_two`).
-/

/-- **L² dominated convergence.**  If `fₙ → g` a.e., all dominated in norm by a
fixed `L²` function `h`, with `g ∈ L²`, then `fₙ → g` in `L²`.  (General
finite/σ-finite measure; the dominator provides the integrability.) -/
theorem tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
    {d : ℕ} {μ : Measure (Vec d)}
    {f : ℕ → Vec d → ℝ} {g h : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ h x)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0) := by
  have h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  set F : ℕ → Vec d → ℝ≥0∞ := fun n x => ‖f n x - g x‖ₑ ^ (2 : ℝ) with hF
  set B : Vec d → ℝ≥0∞ := fun x => (‖h x‖ₑ + ‖g x‖ₑ) ^ (2 : ℝ) with hB
  have hFmeas : ∀ n, AEMeasurable (F n) μ := by
    intro n
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (((hf n).sub hg.1).enorm)
  have hBound : ∀ n, F n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    have hfe : ‖f n x‖ₑ ≤ ‖h x‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
    have hsub : ‖f n x - g x‖ₑ ≤ ‖h x‖ₑ + ‖g x‖ₑ :=
      enorm_sub_le.trans (by gcongr)
    exact ENNReal.rpow_le_rpow hsub (by norm_num)
  have hlhh : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    simpa [h2r] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2z h2t hh.eLpNorm_lt_top).ne
  have hlgg : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    simpa [h2r] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2z h2t hg.eLpNorm_lt_top).ne
  have hBfin : ∫⁻ x, B x ∂μ ≠ ⊤ := by
    have hpt : ∀ x, B x ≤ 4 * (‖h x‖ₑ ^ (2 : ℝ) + ‖g x‖ₑ ^ (2 : ℝ)) := by
      intro x
      have hsum : ‖h x‖ₑ + ‖g x‖ₑ ≤ 2 * (‖h x‖ₑ ⊔ ‖g x‖ₑ) := by
        rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
      calc B x = (‖h x‖ₑ + ‖g x‖ₑ) ^ (2 : ℝ) := rfl
        _ ≤ (2 * (‖h x‖ₑ ⊔ ‖g x‖ₑ)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hsum (by norm_num)
        _ = (2 : ℝ≥0∞) ^ (2 : ℝ) * (‖h x‖ₑ ⊔ ‖g x‖ₑ) ^ (2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        _ ≤ 4 * (‖h x‖ₑ ^ (2 : ℝ) + ‖g x‖ₑ ^ (2 : ℝ)) := by
            gcongr
            · rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℝ) by
                  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
            · rw [(ENNReal.strictMono_rpow_of_pos (by norm_num)).monotone.map_max]
              exact max_le (le_add_right le_rfl) (le_add_left le_rfl)
    have hHmeas : AEMeasurable (fun x => ‖h x‖ₑ ^ (2:ℝ)) μ :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hh.1.enorm
    have hle : ∫⁻ x, B x ∂μ ≤ 4 * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ + ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ) := by
      calc ∫⁻ x, B x ∂μ ≤ ∫⁻ x, 4 * (‖h x‖ₑ ^ (2:ℝ) + ‖g x‖ₑ ^ (2:ℝ)) ∂μ :=
            lintegral_mono hpt
        _ = 4 * (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂μ + ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hHmeas]
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hlhh, hlgg⟩)
  have hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0) := by
    filter_upwards [hfg] with x hx
    have hen : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
        have := hx.sub (tendsto_const_nhds (x := g x))
        rwa [sub_self] at this
      simpa using! (continuous_enorm.tendsto 0).comp h0
    have := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0 |>.comp hen
    simpa [hF] using! this
  have hlim0 : Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μ)) :=
    tendsto_lintegral_of_dominated_convergence' B hFmeas hBound hBfin hFlim
  rw [lintegral_zero] at hlim0
  have hrw : ∀ n, eLpNorm (fun x => f n x - g x) 2 μ = (∫⁻ x, F n x ∂μ) ^ (1 / (2:ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t, h2r]
  simp_rw [hrw]
  have hc : Tendsto (fun y : ℝ≥0∞ => y ^ (1 / (2:ℝ))) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / (2:ℝ))).tendsto 0
    simpa using this
  simpa using! hc.comp hlim0

/-- **Weak partial derivative closed under L² limits.**  If `uₙ → u` and
`gₙ → gᵢ` in `L²(U)`, all in `L²(U)`, and each `uₙ` has weak `i`-partial
derivative `gₙ`, then `u` has weak `i`-partial derivative `gᵢ`. -/
theorem hasWeakPartialDerivOn_of_tendsto_L2
    {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} {un gn : ℕ → Vec d → ℝ}
    (hu : MemScalarL2 U u) (hgi : MemScalarL2 U gi)
    (hun : ∀ n, MemScalarL2 U (un n)) (hgn : ∀ n, MemScalarL2 U (gn n))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (un n) (gn n))
    (hun_to :
      Filter.Tendsto
        (fun n => eLpNorm (fun x => un n x - u x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0))
    (hgn_to :
      Filter.Tendsto
        (fun n => eLpNorm (fun x => gn n x - gi x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ_smooth hφ_compact hφ_sub
  -- The coordinate derivative of the test and the test itself are in `L²(U)`.
  set dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i) with hdφ_def
  have hdφ_cont : Continuous dφ := by
    simpa [hdφ_def] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [hdφ_def] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdφ_mem : MemScalarL2 U dφ :=
    hdφ_cont.memLp_of_hasCompactSupport hdφ_compact
  have hφ_mem : MemScalarL2 U φ :=
    hφ_smooth.continuous.memLp_of_hasCompactSupport hφ_compact
  -- L² convergence of the classes.
  have hun_cl :
      Filter.Tendsto (fun n => toScalarL2 (hun n)) Filter.atTop (nhds (toScalarL2 hu)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hun hu hun_to
  have hgn_cl :
      Filter.Tendsto (fun n => toScalarL2 (hgn n)) Filter.atTop (nhds (toScalarL2 hgi)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hgn hgi hgn_to
  -- The two sides of the pairing converge.
  have hleft :
      Filter.Tendsto
        (fun n => ∫ x in U, dφ x * un n x ∂volume) Filter.atTop
        (nhds (∫ x in U, dφ x * u x ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hdφ_mem hun hu hun_cl
  have hright :
      Filter.Tendsto
        (fun n => ∫ x in U, φ x * gn n x ∂volume) Filter.atTop
        (nhds (∫ x in U, φ x * gi x ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hφ_mem hgn hgi hgn_cl
  -- Per-`n` pairing identity, rearranged into `dφ * un` / `φ * gn` order.
  have hpair : ∀ n,
      ∫ x in U, dφ x * un n x ∂volume = -∫ x in U, φ x * gn n x ∂volume := by
    intro n
    have h := hweak n φ hφ_smooth hφ_compact hφ_sub
    calc
      ∫ x in U, dφ x * un n x ∂volume
          = ∫ x in U, un n x * dφ x ∂volume := by
            simp_rw [mul_comm]
      _ = -∫ x in U, gn n x * φ x ∂volume := h
      _ = -∫ x in U, φ x * gn n x ∂volume := by simp_rw [mul_comm]
  -- Pass to the limit.
  have hleft' :
      Filter.Tendsto
        (fun n => -∫ x in U, φ x * gn n x ∂volume) Filter.atTop
        (nhds (∫ x in U, dφ x * u x ∂volume)) := by
    refine hleft.congr ?_
    intro n; exact hpair n
  have hlimeq :
      ∫ x in U, dφ x * u x ∂volume = -∫ x in U, φ x * gi x ∂volume :=
    tendsto_nhds_unique hleft' hright.neg
  calc
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume
        = ∫ x in U, dφ x * u x ∂volume := by simp_rw [hdφ_def, mul_comm]
    _ = -∫ x in U, φ x * gi x ∂volume := hlimeq
    _ = -∫ x in U, gi x * φ x ∂volume := by simp_rw [mul_comm]

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Pairing against a fixed `L²` test is continuous along `L²`-convergent
sequences: if `f n → g` in `L²(U)` and `h ∈ L²(U)`, then
`∫_U (f n)·h → ∫_U g·h`. -/
theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm_two
    {h : Vec d → ℝ} {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict U))
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (htend : Filter.Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, f n x * h x ∂volume)
      Filter.atTop (nhds (∫ x in U, g x * h x ∂volume)) := by
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have hht : ENNReal.HolderTriple 2 2 1 :=
    ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  -- integrability of the products
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    exact memLp_one_iff_integrable.mp (hh.mul' (hf n))
  have hgh_int : Integrable (fun x => g x * h x) μ :=
    memLp_one_iff_integrable.mp (hh.mul' hg)
  -- rewrite the goal as a difference tending to zero
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ)
        = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- the ℝ≥0∞ bound that tends to zero
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) 2 μ * eLpNorm h 2 μ with hB
  have hBtend : Filter.Tendsto (fun n => (B n).toReal) Filter.atTop (nhds 0) := by
    have hprod : Filter.Tendsto B Filter.atTop (nhds (0 * eLpNorm h 2 μ)) := by
      refine ENNReal.Tendsto.mul htend (Or.inr hh.2.ne) tendsto_const_nhds
        (Or.inr (by simp))
    rw [zero_mul] at hprod
    have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! this
  -- squeeze the norm of the difference
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hae : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Filter.Eventually.of_forall (fun x => by rw [nnnorm_mul]; simp)
  have hHolder :
      eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (μ := μ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      ((hf n).sub hg).1 hh.1 (fun a b => a * b) 1 hae
    simpa [hB] using! this
  calc ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
        apply ENNReal.toReal_mono _ hHolder
        exact ENNReal.mul_ne_top ((hf n).sub hg).2.ne hh.2.ne

/-- **Weak partial derivatives are closed under `L²` limits.**
If `u n → u` and `g n → g` in `L²(U)` and each `u n` has weak `i`-th partial
derivative `g n` on `U`, then `u` has weak `i`-th partial derivative `g`. -/
theorem HasWeakPartialDerivOn.of_tendsto_eLpNorm_two
    {i : Fin d}
    {u : Vec d → ℝ} {gi : Vec d → ℝ}
    {u_n : ℕ → Vec d → ℝ} {g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) 2 (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) 2 (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Filter.Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) 2 (volume.restrict U))
      Filter.atTop (nhds 0))
    (htend_g : Filter.Tendsto
      (fun n => eLpNorm (fun x => g_n n x - gi x) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  -- the two smooth test factors, both L² on U (continuous, compact support)
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) 2 (volume.restrict U) := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφ_compact.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]; simp
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hφmem : MemLp φ 2 (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
  -- pass to the limit on both sides of the pairing identity for each n
  have hlhs : Filter.Tendsto
      (fun n => ∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
      Filter.atTop (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) :=
    tendsto_setIntegral_mul_of_tendsto_eLpNorm_two hDφ hu_n hu htend_u
  have hrhs : Filter.Tendsto
      (fun n => ∫ x in U, g_n n x * φ x ∂volume)
      Filter.atTop (nhds (∫ x in U, gi x * φ x ∂volume)) :=
    tendsto_setIntegral_mul_of_tendsto_eLpNorm_two hφmem hg_n hgi htend_g
  -- each n: LHS = -RHS
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
        = -(∫ x in U, g_n n x * φ x ∂volume) :=
    fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Filter.Tendsto
      (fun n => -(∫ x in U, g_n n x * φ x ∂volume))
      Filter.atTop (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n; rw [heq_n n]
  have hlim := tendsto_nhds_unique hlhs' hrhs.neg
  simpa using hlim

/-- **Weak gradients are closed under `L²` limits** (all coordinates at once). -/
theorem HasWeakGradientOn.of_tendsto_eLpNorm_two
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {u_n : ℕ → Vec d → ℝ} {Du_n : ℕ → Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U)) (hDu : GradMemL2On U Du)
    (hu_n : ∀ n, MemLp (u_n n) 2 (volume.restrict U))
    (hDu_n : ∀ n, GradMemL2On U (Du_n n))
    (hweak : ∀ n, HasWeakGradientOn U (u_n n) (Du_n n))
    (htend_u : Filter.Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) 2 (volume.restrict U))
      Filter.atTop (nhds 0))
    (htend_Du : ∀ i, Filter.Tendsto
      (fun n => eLpNorm (fun x => Du_n n x i - Du x i) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    HasWeakGradientOn U u Du := by
  intro i
  exact HasWeakPartialDerivOn.of_tendsto_eLpNorm_two hu (hDu i)
    hu_n (fun n => hDu_n n i) (fun n => hweak n i) htend_u (htend_Du i)

end

end Homogenization
