/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Uniform.HeatGradient

/-!
# `analytic_approximation` with the `H¹` contraction conjunct

The proof of `Section5.analytic_approximation` (its helper lemmas are private there and are
restated here) with the extra conjunct `‖∇g‖² ≤ ‖∇f‖²`, from `realHeatApprox_gradNormSq_le`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization
open scoped BigOperators
open AVenhance.Infra.Torus AVenhance.Infra.Heat

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance heatApproxH1MeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance heatApproxH1MeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance heatApproxH1IsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.FullTheorem.Uniform

open AVenhance AVenhance.Infra.Section5

theorem HeatApproxH1.cube_finite : volume unitCube < ⊤ := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance heatApproxH1IsFiniteMeasure4 : IsFiniteMeasure (volume.restrict unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using HeatApproxH1.cube_finite⟩

theorem HeatApproxH1.l2_nonneg (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  integral_nonneg fun x => sq_nonneg (f x)

theorem HeatApproxH1.transfer_sub {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hg : MemL2On unitCube g) :
    frozenCellToTorusL2 (hf.sub hg) = frozenCellToTorusL2 hf - frozenCellToTorusL2 hg := by
  apply Lp.ext
  have h1 := (memLp_frozenCellTransfer hf).coeFn_toLp
  have h2 := (memLp_frozenCellTransfer hg).coeFn_toLp
  have h3 := (memLp_frozenCellTransfer (hf.sub hg)).coeFn_toLp
  filter_upwards [h1, h2, h3, Lp.coeFn_sub (frozenCellToTorusL2 hf)
    (frozenCellToTorusL2 hg)] with x hx1 hx2 hx3 hx4
  change (frozenCellToTorusL2 (hf.sub hg) : UnitAddTorus (Fin 2) → ℂ) x = _ at hx3
  change (frozenCellToTorusL2 hf : UnitAddTorus (Fin 2) → ℂ) x = _ at hx1
  change (frozenCellToTorusL2 hg : UnitAddTorus (Fin 2) → ℂ) x = _ at hx2
  rw [hx3, hx4]
  simp only [Pi.sub_apply]
  rw [hx1, hx2]
  simp only [periodicToTorus, Complex.ofReal_sub]

theorem HeatApproxH1.value_norm {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) :
    ‖frozenCellToTorusL2 hf‖ = Real.sqrt (l2NormSq f) := by
  rw [← normSq_frozenCellToTorusL2_eq hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem HeatApproxH1.gradient_pos {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    0 < gradNormSq Df := by
  have hP := meanZero_frozenPeriodicH1_fourierPoincare hf hm
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (by positivity : 0 ≤ 4 * Real.pi ^ 2)) (le_of_not_gt h)
  exact (not_le_of_gt hA) (hP.trans hh)

theorem HeatApproxH1.datumLength_pos {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    0 < datumLength f Df :=
  div_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr (HeatApproxH1.gradient_pos hf hm hA))

theorem HeatApproxH1.scale_energy {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f) :
    datumLength f Df ^ 2 * gradNormSq Df = l2NormSq f := by
  unfold datumLength
  rw [div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt (HeatApproxH1.gradient_pos hf hm hA).le,
    div_mul_cancel₀ _ (HeatApproxH1.gradient_pos hf hm hA).ne']

theorem HeatApproxH1.normalization_loss {N M r : ℝ} (hM : 0 ≤ M)
    (hNM : N ≤ 2 * M) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) * (1 / r) ^ n * N ≤ M * ((n.factorial : ℝ) / (r / 2) ^ n) := by
  have he : (n.factorial : ℝ) / (r / 2) ^ n =
      (n.factorial : ℝ) * (1 / r) ^ n * (2 : ℝ) ^ n := by
    rw [div_pow, div_div_eq_mul_div, one_div, inv_pow]
    ring
  have hpow : (2 : ℝ) ≤ 2 ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hfac : 0 ≤ (n.factorial : ℝ) * (1 / r) ^ n := by positivity
  rw [he]
  calc
    (n.factorial : ℝ) * (1 / r) ^ n * N ≤
        (n.factorial : ℝ) * (1 / r) ^ n * (2 * M) := mul_le_mul_of_nonneg_left hNM hfac
    _ ≤ (n.factorial : ℝ) * (1 / r) ^ n * (2 ^ n * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) hfac
    _ = _ := by ring

/-- `analytic_approximation` together with the `H¹` contraction `‖∇g‖ ≤ ‖∇f‖`. -/
theorem analytic_approximation_gradient {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (hf : IsPeriodicH1With f Df) (hm : MeanZeroOn unitCube f) (hA : 0 < l2NormSq f)
    {α : ℝ} (hα : 0 < α) (hαsmall : α ≤ 1 / 4) :
    ∃ g : Vec 2 → ℝ, MemL2On unitCube g ∧ IsZ2Periodic g ∧ MeanZeroOn unitCube g ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ IsThetaAnalytic (α * datumLength f Df / 2) g ∧
      l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f ∧
      l2NormSq f / 4 ≤ l2NormSq g ∧ gradNormSq (spaceGrad g) ≤ gradNormSq Df := by
  have hL := HeatApproxH1.datumLength_pos hf hm hA
  let s := α ^ 2 * datumLength f Df ^ 2
  have hs : 0 < s := mul_pos (sq_pos_of_pos hα) (sq_pos_of_pos hL)
  let g := realHeatApprox hf hs
  have hg := realHeatApprox_memL2 hf hs
  have herr : l2NormSq (f - g) ≤ α ^ 2 * l2NormSq f := by
    have h := realHeatApprox_error_sq hf hs
    change l2NormSq (f - g) ≤ s * gradNormSq Df at h
    have he : s * gradNormSq Df = α ^ 2 * l2NormSq f := by
      dsimp [s]
      rw [mul_assoc, HeatApproxH1.scale_energy hf hm hA]
    exact h.trans_eq he
  have herrNorm : Real.sqrt (l2NormSq (f - g)) ≤ α * Real.sqrt (l2NormSq f) := by
    calc
      Real.sqrt (l2NormSq (f - g)) ≤ Real.sqrt (α ^ 2 * l2NormSq f) :=
        Real.sqrt_le_sqrt herr
      _ = α * Real.sqrt (l2NormSq f) := by
        rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs, abs_of_pos hα]
  have htri := norm_le_norm_sub_add (frozenCellToTorusL2 hf.2.2.1) (frozenCellToTorusL2 hg)
  rw [← HeatApproxH1.transfer_sub hf.2.2.1 hg, HeatApproxH1.value_norm, HeatApproxH1.value_norm,
      HeatApproxH1.value_norm] at htri
  change Real.sqrt (l2NormSq f) ≤ Real.sqrt (l2NormSq (f - g)) +
    Real.sqrt (l2NormSq g) at htri
  have hsmall := mul_le_mul_of_nonneg_right hαsmall (Real.sqrt_nonneg (l2NormSq f))
  have hnorm : Real.sqrt (l2NormSq f) ≤ 2 * Real.sqrt (l2NormSq g) := by
    linarith only [htri, herrNorm, hsmall, Real.sqrt_nonneg (l2NormSq f)]
  have hnormSq : l2NormSq f / 4 ≤ l2NormSq g := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (l2NormSq f))
      (by positivity : 0 ≤ 2 * Real.sqrt (l2NormSq g))).2 hnorm
    rw [mul_pow, Real.sq_sqrt (HeatApproxH1.l2_nonneg f), Real.sq_sqrt (HeatApproxH1.l2_nonneg g)]
        at hsq
    linarith only [hsq]
  have hsroot : Real.sqrt s = α * datumLength f Df := by
    dsimp [s]
    rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_pos hα, abs_of_pos hL]
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    change ContDiff ℝ (⊤ : ℕ∞) (Complex.reCLM ∘
      heatTorusSmoothLift hs (frozenPeriodicH1ValueL2 hf))
    exact Complex.reCLM.contDiff.comp
      (heatTorusSmoothLift_contDiff hs (frozenPeriodicH1ValueL2 hf))
  refine ⟨g, hg, realHeatApprox_periodic hf hs, realHeatApprox_meanZero hf hm hs,
    hgc, ?_, herr, hnormSq, realHeatApprox_gradNormSq_le hf hs⟩
  intro n hn i
  have hd := realHeatApprox_derivative_bound hf hs n i
  have hnormBound := HeatApproxH1.normalization_loss (Real.sqrt_nonneg (l2NormSq g)) hnorm
    (Real.sqrt_pos.mpr hs) hn
  rw [hsroot] at hd hnormBound
  exact hd.trans hnormBound

end AVenhance.Infra.FullTheorem.Uniform
