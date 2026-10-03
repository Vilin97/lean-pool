/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import LeanPool.Zeta5Irrational.Kernel
public import LeanPool.Zeta5Irrational.Gaussian

/-! Zero-mass logarithmic energy inequality for finite measures on `ℂ`
(the proof notes (12), GLOBAL-INTEGRAL-v1 §4): for finite measures `μ_k` and real weights `w_k` with
`Σ w_k μ_k(ℂ) = 0`, integrable `log|z − w|` and null diagonals,
`Σ_{k,l} w_k w_l ∫∫ log|z − w| dμ_k dμ_l ≤ 0`.

Gaussian positivity for the truncated kernel `L_{a,b}(r) = ½∫_a^b (e^{-s} − e^{-s r²})/s ds`,
then dominated
convergence `L_{1/(n+1), n+1} → log`. The scalar kernel facts and the Gaussian convolution on
`ℂ` are
adapted from the Li₂(1/2) formalization (Li2Unified/Modular/Positive/Packed/P183–P185,
themselves a port of
mo271/Zeta5 Apery/Gaussian, Kernel, ZeroMass, EnergyLimit, Apache-2.0); the measure-level
Gaussian positivity is
new here (the Li₂ version needs bounded continuous curve densities; our comparison density is
unbounded). -/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-! ### Shared truncated-kernel and Gaussian facts -/

export Zeta5Irrational (Ltr integral_exp_neg_mul' intervalIntegral_swap_of_continuous
  intervalIntegral_swap_of_continuous' Ltr_eq_v Ltr_integrand_bounds intervalIntegrable_of_pos
  log_eq_half_integral abs_Ltr_le continuous_inv_max Ltr_eq_max continuous_Ltr log_sub_Ltr
  diff_integrand_bounds abs_log_sub_Ltr_le tendsto_Ltr integral_gaussian_sub
  integrable_gaussian_sub gaussian_conv_one normSq_eq gaussian_conv integrable_gaussC)

/-! ### Gaussian positivity for finite measures (new) -/

section gauss
variable {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The Gaussian smoothing of a measure. -/
def gM (μ : Measure ℂ) (t : ℝ) (u : ℂ) : ℝ := ∫ z, Real.exp (-(2 * t) * ‖z - u‖ ^ 2) ∂μ

/-- The integrand of the Gaussian convolution. -/
def gF (t : ℝ) (q : (ℂ × ℂ) × ℂ) : ℝ :=
  Real.exp (-(2 * t) * ‖q.1.1 - q.2‖ ^ 2) * Real.exp (-(2 * t) * ‖q.1.2 - q.2‖ ^ 2)

theorem continuous_gF (t : ℝ) : Continuous (gF t) := by unfold gF; fun_prop

theorem integral_gF {t : ℝ} (ht : 0 < t) (p : ℂ × ℂ) :
    ∫ u, gF t (p, u) = π / (4 * t) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) :=
  gaussian_conv ht p.1 p.2

theorem integrable_gF_slice {t : ℝ} (ht : 0 < t) (p : ℂ × ℂ) :
    Integrable (fun u => gF t (p, u)) := by
  refine (integrable_gaussC (show 0 < 2 * t by positivity) p.2).mono'
    ((continuous_gF t).comp (Continuous.prodMk_right p)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [gF, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have h1 : Real.exp (-(2 * t) * ‖p.1 - u‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - u‖])
  have : 0 < Real.exp (-(2 * t) * ‖p.2 - u‖ ^ 2) := Real.exp_pos _
  nlinarith

theorem integrable_gF {t : ℝ} (ht : 0 < t) : Integrable (gF t) ((μ.prod ν).prod volume) := by
  rw [integrable_prod_iff (continuous_gF t).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun p => integrable_gF_slice ht p, ?_⟩
  have e : (fun p : ℂ × ℂ => ∫ u, ‖gF t (p, u)‖) =
      fun p => π / (4 * t) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) := by
    funext p
    rw [← integral_gF ht p]
    congr 1; funext u
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold gF; positivity)]
  rw [e]
  refine (integrable_const (π / (4 * t))).mono' (by fun_prop) (Filter.Eventually.of_forall fun p
    => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - p.2‖])
  have hc : 0 < π / (4 * t) := by positivity
  nlinarith

theorem gM_mul_eq {t : ℝ} (u : ℂ) :
    ∫ p, gF t (p, u) ∂(μ.prod ν) = gM μ t u * gM ν t u := by
  unfold gF gM
  exact integral_prod_mul (fun z => Real.exp (-(2 * t) * ‖z - u‖ ^ 2))
    (fun w => Real.exp (-(2 * t) * ‖w - u‖ ^ 2))

theorem integrable_gM_mul {t : ℝ} (ht : 0 < t) : Integrable (fun u => gM μ t u * gM ν t u) := by
  have := (integrable_gF (μ := μ) (ν := ν) ht).integral_prod_right
  exact this.congr (Filter.Eventually.of_forall fun u => gM_mul_eq u)

/-- `∫∫ e^{-t|z−w|²} dμ dν = (4t/π) ∫ g_μ g_ν`. -/
theorem gauss_pair_eq {t : ℝ} (ht : 0 < t) :
    ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν) = (4 * t / π) * ∫ u, gM μ t u * gM ν t u := by
  have hpi : 0 < π := Real.pi_pos
  have h1 : ∀ p : ℂ × ℂ, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) = (4 * t / π) * ∫ u, gF t (p, u) := by
    intro p; rw [integral_gF ht p]; field_simp
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hsw := integral_integral_swap (μ := μ.prod ν) (ν := volume) (f := fun p u => gF t (p, u))
    (integrable_gF ht)
  rw [hsw]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => gM_mul_eq u)

/-- Gaussian positivity of a signed finite combination. -/
theorem gauss_energy_nonneg {ι : Type*} [Fintype ι] (m : ι → Measure ℂ) [∀ k, IsFiniteMeasure (m k)]
    (w : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂((m k).prod (m l)) := by
  have hpi : 0 < π := Real.pi_pos
  have hI : ∀ k l, Integrable (fun u => w k * gM (m k) t u * (w l * gM (m l) t u)) := by
    intro k l
    exact ((integrable_gM_mul (μ := m k) (ν := m l) ht).const_mul (w k * w l)).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have e : (∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂((m k).prod (m l))) =
      (4 * t / π) * ∫ u, (∑ k, w k * gM (m k) t u) ^ 2 := by
    simp_rw [gauss_pair_eq ht, sq, Finset.sum_mul_sum]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hI k l)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun l _ => hI k l), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (fun u => w k * gM (m k) t u * (w l * gM (m l) t u)) =
        fun u => (w k * w l) * (gM (m k) t u * gM (m l) t u) := by funext u; ring
    rw [this, MeasureTheory.integral_const_mul]
    ring
  rw [e]
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

end gauss

/-! ### The truncated kernel against finite measures -/

section trunc
variable {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The integrand of `Ltr` as a function of `(p, s)`. -/
def ltrF (p : ℂ × ℂ) (s : ℝ) : ℝ := (Real.exp (-s) - Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) / s

theorem measurable_ltrF : Measurable (Function.uncurry ltrF) := by
  unfold ltrF; fun_prop

theorem integrable_ltrF {α β : ℝ} (hα : 0 < α) :
    Integrable (Function.uncurry ltrF) ((μ.prod ν).prod (volume.restrict (Ioc α β))) := by
  refine (integrable_const (2 / α)).mono' measurable_ltrF.aestronglyMeasurable ?_
  have hmem : ∀ᵐ q ∂((μ.prod ν).prod (volume.restrict (Ioc α β))), q.2 ∈ Ioc α β :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with q hq
  have hs : 0 < q.2 := hα.trans hq.1
  simp only [Function.uncurry, ltrF, Real.norm_eq_abs, abs_div, abs_of_pos hs]
  have h1 : |Real.exp (-q.2) - Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2)| ≤ 2 := by
    have e1 : Real.exp (-q.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have e2 : Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖q.1.1 - q.1.2‖])
    have := Real.exp_pos (-q.2)
    have := Real.exp_pos (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2)
    rw [abs_le]; constructor <;> linarith
  rw [div_le_div_iff₀ hs hα]
  nlinarith [hq.1]

/-- `∫ Ltr(|z − w|) dμ dν = ½ ∫_α^β ∫ ltrF`. -/
theorem integral_Ltr_eq {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ p, Ltr α β ‖p.1 - p.2‖ ∂(μ.prod ν) =
      (1 / 2) * ∫ s in Ioc α β, ∫ p, ltrF p s ∂(μ.prod ν) := by
  have e : ∀ p : ℂ × ℂ, Ltr α β ‖p.1 - p.2‖ = (1 / 2) * ∫ s in Ioc α β, ltrF p s := by
    intro p; unfold Ltr ltrF; rw [intervalIntegral.integral_of_le hαβ]
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_ltrF hα)

theorem integral_ltrF {s : ℝ} (hs : 0 ≤ s) :
    ∫ p, ltrF p s ∂(μ.prod ν) =
      (Real.exp (-s) * (μ.real univ * ν.real univ) -
        ∫ p, Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν)) / s := by
  unfold ltrF
  have hint : Integrable (fun p : ℂ × ℂ => Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) (μ.prod ν) := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - p.2‖])
  rw [MeasureTheory.integral_div, integral_sub (integrable_const _) hint,
    MeasureTheory.integral_const,
    smul_eq_mul]
  congr 2
  rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
  simp only [Measure.real]
  ring

end trunc

/-- Zero-mass logarithmic energy inequality for a finite signed combination of finite measures
on `ℂ`. -/
theorem zero_mass_energy_nonpos {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ)
    [∀ k, IsFiniteMeasure (μ k)] (w : ι → ℝ)
    (hmass : ∑ k, w k * (μ k).real Set.univ = 0)
    (hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((μ k).prod (μ l)))
    (hdiag : ∀ k l, ∀ᵐ p ∂((μ k).prod (μ l)), p.1 ≠ p.2) :
    ∑ k, ∑ l, w k * w l * ∫ p, Real.log ‖p.1 - p.2‖ ∂((μ k).prod (μ l)) ≤ 0 := by
  have htrunc : ∀ n : ℕ, ∑ k, ∑ l, w k * w l *
      ∫ p, Ltr (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1) ‖p.1 - p.2‖ ∂((μ k).prod (μ l)) ≤ 0 := by
    intro n
    have hα : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    have hαβ : 1 / ((n:ℝ) + 1) ≤ (n:ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    simp_rw [integral_Ltr_eq hα hαβ]
    set S := Ioc (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1)
    have hΦ : ∀ k l, Integrable (fun x => ∫ p, ltrF p x ∂((μ k).prod (μ l))) (volume.restrict S) :=
      fun k l => (integrable_ltrF (μ := μ k) (ν := μ l) hα).integral_prod_right
    have hΦ' : ∀ k l, Integrable (fun x => w k * w l * ∫ p, ltrF p x ∂((μ k).prod (μ l)))
        (volume.restrict S) := fun k l => (hΦ k l).const_mul _
    have e : (∑ k, ∑ l, w k * w l * ((1 / 2) * ∫ x in S, ∫ p, ltrF p x ∂((μ k).prod (μ l)))) =
        (1 / 2) * ∫ x in S, ∑ k, ∑ l, w k * w l * ∫ p, ltrF p x ∂((μ k).prod (μ l)) := by
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hΦ' k l)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (fun l _ => hΦ' k l), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [MeasureTheory.integral_const_mul]
      ring
    rw [e]
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply setIntegral_nonpos measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := hα.trans hx.1
    simp_rw [integral_ltrF hx0.le]
    have hQ := gauss_energy_nonneg μ w hx0
    have halg : (∑ k, ∑ l, w k * w l * ((Real.exp (-x) * ((μ k).real univ * (μ l).real univ) -
        ∫ p, Real.exp (-x * ‖p.1 - p.2‖ ^ 2) ∂((μ k).prod (μ l))) / x)) =
        (Real.exp (-x) * (∑ k, w k * (μ k).real univ) ^ 2 -
          ∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-x * ‖p.1 - p.2‖ ^ 2) ∂((μ k).prod (μ l))) / x := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [halg, hmass]
    apply div_nonpos_of_nonpos_of_nonneg _ hx0.le
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub,
      Left.neg_nonpos_iff]
    exact hQ
  have hlim : Tendsto (fun n : ℕ => ∑ k, ∑ l, w k * w l *
      ∫ p, Ltr (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1) ‖p.1 - p.2‖ ∂((μ k).prod (μ l))) atTop
      (𝓝 (∑ k, ∑ l, w k * w l * ∫ p, Real.log ‖p.1 - p.2‖ ∂((μ k).prod (μ l)))) := by
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
    refine Tendsto.const_mul _ ?_
    have hα : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
    have hαβ : ∀ n : ℕ, 1 / ((n:ℝ) + 1) ≤ (n:ℝ) + 1 := fun n => by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    refine tendsto_integral_of_dominated_convergence (fun p => |Real.log ‖p.1 - p.2‖|)
      (fun n => ((continuous_Ltr (hα n) (hαβ n)).comp
        (continuous_fst.sub continuous_snd).norm).aestronglyMeasurable) (hint k l).abs ?_ ?_
    · intro n
      filter_upwards [hdiag k l] with p hp
      rw [Real.norm_eq_abs]
      exact abs_Ltr_le (hα n) (hαβ n) (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
    · filter_upwards [hdiag k l] with p hp
      exact tendsto_Ltr (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  exact le_of_tendsto' hlim htrunc

end
end Zeta32.Analytic.EnergyI

end
