/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import LeanPool.CarlsonFunctions.Pochhammer.Gamma
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Regularized incomplete Mellin transforms

The regularized incomplete Mellin transform of a `C^N` integrand on a compact interval `[0, a]`
continues holomorphically from `{0 < re α}` to `{-(N : ℝ) < re α}`.  This is the one-variable
engine for finite-order continuation of regularized Dirichlet integrals.
-/

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Topology

@[expose] public noncomputable section IncompleteMellin

namespace Complex

/-- The slope remainder `(K t - K 0) / t`, equal to the one-sided derivative at the origin. -/
def mellinSlope (a : ℝ) (K : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t = 0 then derivWithin K (Icc (0 : ℝ) a) 0 else slope K 0 t

/-- The first-order Taylor identity on `[0, a]`. -/
theorem eq_add_mellinSlope {a : ℝ} {K : ℝ → ℂ} {t : ℝ} (_ht : t ∈ Icc (0 : ℝ) a) :
    K t = K 0 + t * mellinSlope a K t := by
  by_cases h : t = 0
  · subst t
    simp [mellinSlope]
  · have hdiff : (t : ℝ) • slope K 0 t = K t - K 0 := by
      rw [slope_def_module, sub_zero, ← smul_assoc]
      simp [h]
    simp only [mellinSlope, h, ↓reduceIte]
    rw [real_smul] at hdiff
    have h' : K t - K 0 = (t : ℂ) * slope K 0 t := hdiff.symm
    rw [← h']
    abel

/-- A `C¹` integrand on `[0, a]` has a continuous slope remainder. -/
theorem continuousOn_mellinSlope {a : ℝ} (ha : 0 < a) {K : ℝ → ℂ}
    (hK : ContDiffOn ℝ 1 K (Icc 0 a)) :
    ContinuousOn (mellinSlope a K) (Icc 0 a) := by
  have h0 : (0 : ℝ) ∈ Icc 0 a := left_mem_Icc.2 ha.le
  have hdiff : DifferentiableWithinAt ℝ K (Icc 0 a) 0 :=
    hK.differentiableOn (by norm_num) 0 h0
  have hhas : HasDerivWithinAt K (derivWithin K (Icc 0 a) 0) (Icc 0 a) 0 :=
    hdiff.hasDerivWithinAt
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hlim : Tendsto (slope K 0) (nhdsWithin 0 (Icc 0 a \ {0}))
        (nhds (derivWithin K (Icc 0 a) 0)) :=
      hasDerivWithinAt_iff_tendsto_slope.mp hhas
    have hlim' : Tendsto (mellinSlope a K) (nhdsWithin 0 (Icc 0 a \ {0}))
        (nhds (mellinSlope a K 0)) := by
      simp only [mellinSlope, ↓reduceIte]
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := hx.2
      simp [mellinSlope, hx0]
    have hC : ContinuousWithinAt (mellinSlope a K) (Icc 0 a \ {0}) 0 := hlim'
    have hinsert : insert (0 : ℝ) (Icc 0 a \ {0}) = Icc 0 a := by
      rw [insert_sdiff_singleton]
      exact insert_eq_of_mem h0
    rw [← hinsert]
    exact continuousWithinAt_insert_self.2 hC
  · have hne : t ≠ 0 := ht0
    have hK' : ContinuousOn K (Icc 0 a) := hK.continuousOn
    have hEq : EqOn (mellinSlope a K) (slope K 0) (Icc 0 a \ {0}) := by
      intro x hx
      have hx0 : x ≠ 0 := hx.2
      simp [mellinSlope, hx0]
    have hcont : ContinuousOn (slope K 0) (Icc 0 a \ {0}) := by
      have hden : ContinuousOn (fun y : ℝ => (y : ℂ)⁻¹) (Icc 0 a \ {0}) :=
        Complex.continuous_ofReal.continuousOn.inv₀ fun y hy => ofReal_ne_zero.mpr hy.2
      have hnum : ContinuousOn (fun y : ℝ => K y - K 0) (Icc 0 a \ {0}) :=
        (hK'.mono (sdiff_subset (t := ({0} : Set ℝ)))).sub continuousOn_const
      intro x hx
      have := (hden.mul hnum).continuousWithinAt hx
      refine this.congr ?_ ?_
      · intro y hy
        simp [slope_def_module, sub_zero, ← ofReal_inv]
      · simp [slope_def_module, sub_zero, ← ofReal_inv]
    have hC : ContinuousWithinAt (mellinSlope a K) (Icc 0 a \ {0}) t :=
      ((hcont.congr hEq).continuousWithinAt ⟨ht, hne⟩)
    have hnhds : 𝓝[Icc (0 : ℝ) a \ {0}] t = 𝓝[Icc 0 a] t := by
      have : ({0} : Set ℝ)ᶜ ∈ 𝓝[Icc 0 a] t :=
        mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
      rw [sdiff_eq, inter_comm]
      exact nhdsWithin_inter_of_mem this
    change Tendsto (mellinSlope a K) (𝓝[Icc 0 a] t) _
    rw [← hnhds]
    exact hC

/-- Integrability of `t ↦ (t : ℂ)^{α - 1}` on `[0, a]` when `0 < re α`. -/
theorem integrableOn_cpow_Icc {α : ℂ} {a : ℝ} (hα : 0 < α.re) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1)) (Icc 0 a) := by
  rcases eq_or_lt_of_le ha with rfl | _
  · simp
  have h : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (α - 1)) volume 0 a :=
    intervalIntegral.intervalIntegrable_cpow' (by simpa [sub_re] using hα)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le ha).1 h

/-- Integrability of a continuous integrand against the Mellin kernel on `[0, a]`. -/
theorem integrableOn_cpow_mul_Icc {α : ℂ} {a : ℝ} (hα : 0 < α.re) (ha : 0 ≤ a)
    {K : ℝ → ℂ} (hK : ContinuousOn K (Icc 0 a)) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * K t) (Icc 0 a) :=
  (integrableOn_cpow_Icc hα ha).mul_continuousOn hK isCompact_Icc

/-- The regularized incomplete Mellin transform on `[0, a]`. -/
def regIncompleteMellin (α : ℂ) (a : ℝ) (K : ℝ → ℂ) : ℂ :=
  (Gamma α)⁻¹ * ∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * K t

/-- The integral of `t^{β-1}` on `[0, a]` for `0 < re β`. -/
theorem integral_Icc_cpow {β : ℂ} {a : ℝ} (hβ : 0 < β.re) (ha : 0 < a) :
    (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (β - 1)) = (a : ℂ) ^ β / β := by
  have hI := _root_.integral_cpow (a := (0 : ℝ)) (b := a) (r := β - 1)
    (Or.inl (by simpa [sub_re] using hβ))
  have hne : β ≠ 0 := ne_zero_of_re_pos hβ
  rw [intervalIntegral.integral_of_le ha.le] at hI
  rw [integral_Icc_eq_integral_Ioc, hI]
  simp [sub_add_cancel, zero_cpow hne]

/-- Evaluating the Mellin transform of a constant. -/
theorem regIncompleteMellin_const {α : ℂ} {a : ℝ} (hα : 0 < α.re) (ha : 0 < a) (c : ℂ) :
    regIncompleteMellin α a (fun _ => c) =
      c * (a : ℂ) ^ α * (Gamma (α + 1))⁻¹ := by
  have hmul :
      (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * c) =
        (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1)) * c :=
    MeasureTheory.integral_mul_const (μ := volume.restrict (Icc (0 : ℝ) a))
      (f := fun t : ℝ => (t : ℂ) ^ (α - 1)) c
  unfold regIncompleteMellin
  rw [hmul, integral_Icc_cpow hα ha, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one α]
  have hne : α ≠ 0 := ne_zero_of_re_pos hα
  field_simp [hne]

/-- Mellin transform of the monomial `t ↦ t ^ k`. -/
theorem regIncompleteMellin_pow {α : ℂ} {a : ℝ} (hα : 0 < α.re) (ha : 0 < a) (k : ℕ) :
    regIncompleteMellin α a (fun t => (t : ℂ) ^ k) =
      (a : ℂ) ^ (α + k) * (ascPochhammer ℂ k).eval α * (Gamma (α + k + 1))⁻¹ := by
  have hαk : 0 < (α + k).re := by
    simp only [add_re, natCast_re]
    exact add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg k)
  have hfun : (fun t : ℝ => (t : ℂ) ^ (α - 1) * (t : ℂ) ^ k) =ᵐ[volume.restrict (Icc 0 a)]
      fun t : ℝ => (t : ℂ) ^ (α + k - 1) := by
    have ht0 : ∀ᵐ t ∂volume.restrict (Icc 0 a), t ≠ 0 :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton (0 : ℝ)])
    filter_upwards [ht0] with t ht0
    have hne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
    rw [← cpow_natCast, ← cpow_add _ _ hne]
    congr 1
    ring
  unfold regIncompleteMellin
  rw [integral_congr_ae hfun, integral_Icc_cpow hαk ha]
  have hne : α + k ≠ 0 := ne_zero_of_re_pos hαk
  have hΓid : Gamma (α + k + 1) = (α + k) * Gamma (α + k) := Gamma_add_one _ hne
  have hrec := one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat α k
  have hinv : (Gamma (α + k))⁻¹ * (α + k)⁻¹ = (Gamma (α + k + 1))⁻¹ := by
    rw [hΓid, mul_inv, mul_comm]
  rw [hrec, div_eq_mul_inv]
  grind

/-- The Peano remainder of order `N ≥ 1`. -/
def mellinPeanoRemainder (N : ℕ) (a : ℝ) (K : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t = 0 then
    (N.factorial : ℂ)⁻¹ * iteratedDerivWithin N K (Icc (0 : ℝ) a) 0
  else
    (t ^ N : ℝ)⁻¹ • (K t - taylorWithinEval K (N - 1) (Icc (0 : ℝ) a) 0 t)

theorem eq_taylor_add_mellinPeanoRemainder {N : ℕ} (hN : 0 < N) {a : ℝ}
    {K : ℝ → ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) a) :
    K t = taylorWithinEval K (N - 1) (Icc 0 a) 0 t +
      (t ^ N : ℝ) • mellinPeanoRemainder N a K t := by
  by_cases ht0 : t = 0
  · subst t
    rw [taylorWithinEval_self, mellinPeanoRemainder, ite_eq_left rfl]
    simp [zero_pow hN.ne']
  · simp only [mellinPeanoRemainder, ht0, ↓reduceIte]
    have hne : t ^ N ≠ 0 := pow_ne_zero N ht0
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hne, one_smul]
    abel

theorem taylorWithinEval_succ_pred {N : ℕ} (hN : 0 < N) (K : ℝ → ℂ) (a x : ℝ) :
    taylorWithinEval K N (Icc (0 : ℝ) a) 0 x =
      taylorWithinEval K (N - 1) (Icc 0 a) 0 x +
        ((N.factorial : ℝ)⁻¹ * x ^ N) • iteratedDerivWithin N K (Icc 0 a) 0 := by
  simp_rw [taylor_within_apply, sub_zero]
  rw [Finset.sum_range_succ, Nat.sub_add_cancel hN]

/-- The Peano remainder of a `C^N` integrand is continuous on `[0, a]`. -/
theorem continuousOn_mellinPeanoRemainder {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a)
    {K : ℝ → ℂ} (hK : ContDiffOn ℝ N K (Icc 0 a)) :
    ContinuousOn (mellinPeanoRemainder N a K) (Icc 0 a) := by
  have h0 : (0 : ℝ) ∈ Icc 0 a := left_mem_Icc.2 ha.le
  have hTcont : Continuous (fun x : ℝ => taylorWithinEval K (N - 1) (Icc 0 a) 0 x) := by
    simp_rw [taylor_within_apply, sub_zero]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hlim := taylor_tendsto (convex_Icc (0 : ℝ) a) h0 hK
    have hψ0 : mellinPeanoRemainder N a K 0 =
        (N.factorial : ℝ)⁻¹ • iteratedDerivWithin N K (Icc 0 a) 0 := by
      simp [mellinPeanoRemainder, real_smul]
    have heq : ∀ x ∈ Icc (0 : ℝ) a \ {0},
        mellinPeanoRemainder N a K x =
          (x ^ N)⁻¹ • (K x - taylorWithinEval K N (Icc 0 a) 0 x) +
            (N.factorial : ℝ)⁻¹ • iteratedDerivWithin N K (Icc 0 a) 0 := by
      intro x hx
      have hx0 : x ≠ 0 := hx.2
      have hxN : x ^ N ≠ 0 := pow_ne_zero N hx0
      rw [mellinPeanoRemainder, ite_eq_right hx0, taylorWithinEval_succ_pred hN K a]
      simp only [smul_sub, smul_add]
      have hcancel :
          (x ^ N)⁻¹ • (((N.factorial : ℝ)⁻¹ * x ^ N) •
            iteratedDerivWithin N K (Icc 0 a) 0) =
          (N.factorial : ℝ)⁻¹ • iteratedDerivWithin N K (Icc 0 a) 0 := by
        simp only [smul_smul]
        congr 1
        field_simp [hxN]
      rw [hcancel]
      abel
    have hfirst : Tendsto
        (fun x => (x ^ N)⁻¹ • (K x - taylorWithinEval K N (Icc 0 a) 0 x))
        (nhdsWithin 0 (Icc 0 a \ {0})) (nhds 0) := by
      simpa [sub_zero] using
        hlim.mono_left (nhdsWithin_mono (0 : ℝ) (sdiff_subset (t := ({0} : Set ℝ))))
    have hlim' : Tendsto (mellinPeanoRemainder N a K)
        (nhdsWithin 0 (Icc 0 a \ {0}))
        (nhds (mellinPeanoRemainder N a K 0)) := by
      rw [hψ0]
      have hsum := hfirst.add (tendsto_const_nhds
        (x := (N.factorial : ℝ)⁻¹ • iteratedDerivWithin N K (Icc 0 a) 0))
      have hevent :
          (fun x =>
              (x ^ N)⁻¹ • (K x - taylorWithinEval K N (Icc 0 a) 0 x) +
                (N.factorial : ℝ)⁻¹ • iteratedDerivWithin N K (Icc 0 a) 0) =ᶠ[nhdsWithin 0 (Icc 0 a \ {0})]
            mellinPeanoRemainder N a K := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (heq x hx).symm
      simpa using hsum.congr' hevent
    have hC : ContinuousWithinAt (mellinPeanoRemainder N a K) (Icc 0 a \ {0}) 0 := hlim'
    have hinsert : insert (0 : ℝ) (Icc 0 a \ {0}) = Icc 0 a := by
      rw [insert_sdiff_singleton]
      exact insert_eq_of_mem h0
    rw [← hinsert]
    exact continuousWithinAt_insert_self.2 hC
  · have hne : t ≠ 0 := ht0
    have hEq : EqOn (mellinPeanoRemainder N a K)
        (fun x => (x ^ N : ℝ)⁻¹ • (K x - taylorWithinEval K (N - 1) (Icc 0 a) 0 x))
        (Icc 0 a \ {0}) := by
      intro x hx
      have hx0 : x ≠ 0 := hx.2
      simp [mellinPeanoRemainder, hx0]
    have hcont : ContinuousOn
        (fun x => (x ^ N : ℝ)⁻¹ • (K x - taylorWithinEval K (N - 1) (Icc 0 a) 0 x))
        (Icc 0 a \ {0}) := by
      have hK' : ContinuousOn K (Icc 0 a \ {0}) :=
        hK.continuousOn.mono (sdiff_subset (s := Icc (0 : ℝ) a) (t := ({0} : Set ℝ)))
      have hpow : ContinuousOn (fun x : ℝ => (x ^ N : ℝ)⁻¹) (Icc 0 a \ {0}) :=
        (continuousOn_id.pow N).inv₀ fun x hx => pow_ne_zero N hx.2
      have hT : ContinuousOn (fun x => taylorWithinEval K (N - 1) (Icc 0 a) 0 x)
          (Icc 0 a \ {0}) :=
        hTcont.continuousOn.mono
          (sdiff_subset (s := Icc (0 : ℝ) a) (t := ({0} : Set ℝ)))
      exact hpow.smul (hK'.sub hT)
    have hC : ContinuousWithinAt (mellinPeanoRemainder N a K) (Icc 0 a \ {0}) t :=
      ((hcont.congr hEq).continuousWithinAt ⟨ht, hne⟩)
    have hnhds : 𝓝[Icc (0 : ℝ) a \ {0}] t = 𝓝[Icc 0 a] t := by
      have : ({0} : Set ℝ)ᶜ ∈ 𝓝[Icc 0 a] t :=
        mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
      rw [sdiff_eq, inter_comm]
      exact nhdsWithin_inter_of_mem this
    change Tendsto (mellinPeanoRemainder N a K) (𝓝[Icc 0 a] t) _
    rw [← hnhds]
    exact hC

/-- Extending a compactly supported integrand by zero, the incomplete Mellin integral agrees
with Mathlib's Mellin transform. -/
theorem integral_Icc_eq_mellin_indicator {α : ℂ} {a : ℝ} {K : ℝ → ℂ} :
    (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * K t) =
      mellin (Set.indicator (Ioc (0 : ℝ) a) K) α := by
  unfold mellin
  simp_rw [smul_eq_mul]
  have hmul :
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) * Set.indicator (Ioc (0 : ℝ) a) K t) =
        ∫ t in Ioi (0 : ℝ),
          Set.indicator (Ioc (0 : ℝ) a) (fun t => (t : ℂ) ^ (α - 1) * K t) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact (Set.indicator_mul_right (Ioc (0 : ℝ) a)
      (fun t => (t : ℂ) ^ (α - 1)) K).symm
  rw [hmul, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, integral_Icc_eq_integral_Ioc]

/-- Zero extension of a continuous integrand on `[0, a]` is locally integrable on `(0, ∞)`. -/
theorem locallyIntegrableOn_indicator_Ioc {a : ℝ} {K : ℝ → ℂ}
    (hK : ContinuousOn K (Icc 0 a)) :
    LocallyIntegrableOn (Set.indicator (Ioc (0 : ℝ) a) K) (Ioi 0) := by
  have hint : IntegrableOn (Set.indicator (Ioc (0 : ℝ) a) K) (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Ioc,
      inter_eq_left.mpr Ioc_subset_Ioi_self]
    exact (hK.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  exact hint.locallyIntegrableOn

/-- Compact support on `[0, a]` gives arbitrary polynomial decay at infinity. -/
theorem isBigO_atTop_indicator_Ioc {a : ℝ} (K : ℝ → ℂ) (b : ℝ) :
    (Set.indicator (Ioc (0 : ℝ) a) K) =O[atTop] fun t : ℝ => t ^ (-b) := by
  refine Asymptotics.isBigO_iff.2 ⟨0, ?_⟩
  filter_upwards [eventually_gt_atTop a] with t (ht : a < t)
  have hnot : t ∉ Ioc (0 : ℝ) a := fun h => (not_le_of_gt ht) h.2
  simp [Set.indicator_of_notMem hnot]

/-- A continuous integrand on `[0, a]` is `O(1)` at the origin. -/
theorem isBigO_nhdsGT_zero_indicator_Ioc {a : ℝ} {K : ℝ → ℂ}
    (hK : ContinuousOn K (Icc 0 a)) :
    (Set.indicator (Ioc (0 : ℝ) a) K) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
  refine Asymptotics.isBigO_iff.2 ⟨max C 0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  by_cases hta : t ≤ a
  · have htIoc : t ∈ Ioc (0 : ℝ) a := ⟨ht0, hta⟩
    rw [Set.indicator_of_mem htIoc]
    exact (hC t ⟨ht0.le, hta⟩).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem (fun h : t ∈ Ioc (0 : ℝ) a => hta h.2), norm_zero]
    exact le_max_right _ _

/-- The regularized incomplete Mellin transform of a continuous integrand is holomorphic
on `{0 < re α}`. -/
theorem analyticOn_regIncompleteMellin {a : ℝ} (_ha : 0 < a) {K : ℝ → ℂ}
    (hK : ContinuousOn K (Icc 0 a)) :
    AnalyticOn ℂ (fun α => regIncompleteMellin α a K) {α : ℂ | 0 < α.re} := by
  have hopen : IsOpen {α : ℂ | 0 < α.re} := isOpen_lt continuous_const Complex.continuous_re
  let Kext := Set.indicator (Ioc (0 : ℝ) a) K
  have hloc := locallyIntegrableOn_indicator_Ioc hK
  have hf_bot := isBigO_nhdsGT_zero_indicator_Ioc hK
  have hEq : EqOn (fun α => regIncompleteMellin α a K)
      (fun α => (Gamma α)⁻¹ * mellin Kext α) {α | 0 < α.re} := by
    intro α _
    dsimp [regIncompleteMellin]
    rw [integral_Icc_eq_mellin_indicator (α := α) (a := a) (K := K)]
  refine DifferentiableOn.analyticOn ?_ hopen
  intro α hα
  have hf_top := isBigO_atTop_indicator_Ioc (a := a) K (α.re + 1)
  have hM : DifferentiableAt ℂ (mellin Kext) α :=
    mellin_differentiableAt_of_isBigO_rpow hloc hf_top (lt_add_one _) hf_bot hα
  have hprod : DifferentiableAt ℂ (fun β => (Gamma β)⁻¹ * mellin Kext β) α :=
    (differentiable_one_div_Gamma α).mul hM
  have hev : (fun β => regIncompleteMellin β a K) =ᶠ[𝓝 α]
      fun β => (Gamma β)⁻¹ * mellin Kext β := by
    filter_upwards [hopen.mem_nhds hα] with β hβ
    exact hEq hβ
  exact (hprod.congr_of_eventuallyEq hev).differentiableWithinAt

/-- Linearity of the regularized incomplete Mellin transform in the integrand. -/
theorem regIncompleteMellin_add {α : ℂ} {a : ℝ} (hα : 0 < α.re) (ha : 0 ≤ a)
    {K L : ℝ → ℂ} (hK : ContinuousOn K (Icc 0 a)) (hL : ContinuousOn L (Icc 0 a)) :
    regIncompleteMellin α a (fun t => K t + L t) =
      regIncompleteMellin α a K + regIncompleteMellin α a L := by
  unfold regIncompleteMellin
  have hKL : ContinuousOn (fun t => K t + L t) (Icc 0 a) := hK.add hL
  have hintK := integrableOn_cpow_mul_Icc hα ha hK
  have hintL := integrableOn_cpow_mul_Icc hα ha hL
  have hadd :
      (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * (K t + L t)) =
        (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * K t) +
          ∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * L t := by
    simp_rw [mul_add]
    exact integral_add hintK hintL
  rw [hadd, mul_add]

theorem regIncompleteMellin_const_mul {α : ℂ} {a : ℝ} {K : ℝ → ℂ} (c : ℂ) :
    regIncompleteMellin α a (fun t => c * K t) = c * regIncompleteMellin α a K := by
  unfold regIncompleteMellin
  have hfun : (fun t : ℝ => (t : ℂ) ^ (α - 1) * (c * K t)) =
      fun t : ℝ => c * ((t : ℂ) ^ (α - 1) * K t) := by
    funext t; ring
  rw [hfun, MeasureTheory.integral_const_mul, mul_left_comm]

/-- Mellin of `t ↦ t^k K t` is the Pochhammer shift of the Mellin of `K`. -/
theorem regIncompleteMellin_mul_pow {α : ℂ} {a : ℝ} (hα : 0 < α.re) (_ha : 0 < a)
    {K : ℝ → ℂ} (_hK : ContinuousOn K (Icc 0 a)) (k : ℕ) :
    regIncompleteMellin α a (fun t => (t : ℂ) ^ k * K t) =
      (ascPochhammer ℂ k).eval α * regIncompleteMellin (α + k) a K := by
  have hαk : 0 < (α + k).re := by
    simp only [add_re, natCast_re]
    exact add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg k)
  have hfun :
      (fun t : ℝ => (t : ℂ) ^ (α - 1) * ((t : ℂ) ^ k * K t)) =ᵐ[volume.restrict (Icc 0 a)]
        fun t => (t : ℂ) ^ (α + k - 1) * K t := by
    have ht0 : ∀ᵐ t ∂volume.restrict (Icc 0 a), t ≠ 0 :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton (0 : ℝ)])
    filter_upwards [ht0] with t ht0
    have hne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
    rw [← mul_assoc, ← cpow_natCast, ← cpow_add _ _ hne]
    congr 1
    ring
  unfold regIncompleteMellin
  rw [integral_congr_ae hfun, one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat α k]
  ring_nf

/-- The Taylor polynomial of order `n` as a sum of monomials. -/
theorem taylorWithinEval_eq_sum_cpow {n : ℕ} (K : ℝ → ℂ) (a t : ℝ) :
    taylorWithinEval K n (Icc (0 : ℝ) a) 0 t =
      ∑ k ∈ Finset.range (n + 1),
        ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) * (t : ℂ) ^ k := by
  rw [taylor_within_apply]
  simp only [sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_smul, ofReal_mul, ofReal_inv, ofReal_natCast, ofReal_pow]
  ring

/-- Native identity: the incomplete Mellin of a `C^N` integrand is the explicit Mellin of its
Taylor polynomial plus a Pochhammer-shifted Mellin of the Peano remainder. -/
theorem regIncompleteMellin_eq_taylor_peano {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a)
    {K : ℝ → ℂ} (hK : ContDiffOn ℝ N K (Icc 0 a)) {α : ℂ} (hα : 0 < α.re) :
    regIncompleteMellin α a K =
      (∑ k ∈ Finset.range N,
        ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
          ((a : ℂ) ^ (α + k) * (ascPochhammer ℂ k).eval α * (Gamma (α + k + 1))⁻¹)) +
      (ascPochhammer ℂ N).eval α *
        regIncompleteMellin (α + N) a (mellinPeanoRemainder N a K) := by
  have hψ : ContinuousOn (mellinPeanoRemainder N a K) (Icc 0 a) :=
    continuousOn_mellinPeanoRemainder hN ha hK
  have hT : ContinuousOn (fun t => taylorWithinEval K (N - 1) (Icc 0 a) 0 t) (Icc 0 a) := by
    simp_rw [taylor_within_apply, sub_zero]
    exact (continuous_finsetSum _ fun k _ => by fun_prop).continuousOn
  have hpowψ : ContinuousOn
      (fun t : ℝ => (t : ℂ) ^ N * mellinPeanoRemainder N a K t) (Icc (0 : ℝ) a) :=
    ((Complex.continuous_ofReal.pow N).continuousOn).mul hψ
  have hsplit : EqOn (fun t : ℝ => K t)
      (fun t : ℝ => taylorWithinEval K (N - 1) (Icc (0 : ℝ) a) 0 t +
        (t : ℂ) ^ N * mellinPeanoRemainder N a K t) (Icc (0 : ℝ) a) := by
    intro t ht
    have halg := eq_taylor_add_mellinPeanoRemainder (K := K) hN ht
    have hsmul : (t ^ N : ℝ) • mellinPeanoRemainder N a K t =
        (t : ℂ) ^ N * mellinPeanoRemainder N a K t := by
      rw [real_smul, ofReal_pow]
    dsimp
    rw [halg, hsmul]
  have hadd := regIncompleteMellin_add hα ha.le hT hpowψ
  have hcongr : regIncompleteMellin α a K =
      regIncompleteMellin α a (fun t =>
        taylorWithinEval K (N - 1) (Icc 0 a) 0 t +
          (t : ℂ) ^ N * mellinPeanoRemainder N a K t) := by
    unfold regIncompleteMellin
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc fun t ht => by
      simp [mul_add, hsplit ht]
  rw [hcongr, hadd]
  have hTaylor :
      regIncompleteMellin α a (fun t => taylorWithinEval K (N - 1) (Icc 0 a) 0 t) =
        ∑ k ∈ Finset.range N,
          ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
            regIncompleteMellin α a (fun t => (t : ℂ) ^ k) := by
    have hsum : EqOn (fun t => taylorWithinEval K (N - 1) (Icc 0 a) 0 t)
        (fun t => ∑ k ∈ Finset.range N,
          ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) * (t : ℂ) ^ k)
        (Icc 0 a) := by
      intro t _
      simpa [Nat.sub_add_cancel hN] using taylorWithinEval_eq_sum_cpow (n := N - 1) K a t
    unfold regIncompleteMellin
    have hinter :
        (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) *
            taylorWithinEval K (N - 1) (Icc 0 a) 0 t) =
          ∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) *
            ∑ k ∈ Finset.range N,
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                (t : ℂ) ^ k :=
      setIntegral_congr_fun measurableSet_Icc fun t ht => by simp [hsum ht]
    rw [hinter]
    have hswap :
        (∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) *
            ∑ k ∈ Finset.range N,
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                (t : ℂ) ^ k) =
          ∑ k ∈ Finset.range N,
            ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
              ∫ t in Icc (0 : ℝ) a, (t : ℂ) ^ (α - 1) * (t : ℂ) ^ k := by
      have hpoint (t : ℝ) :
          (t : ℂ) ^ (α - 1) *
              ∑ k ∈ Finset.range N,
                ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                  (t : ℂ) ^ k =
            ∑ k ∈ Finset.range N,
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                ((t : ℂ) ^ (α - 1) * (t : ℂ) ^ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      simp_rw [hpoint]
      have hterm (k : ℕ) :
          Integrable (fun t : ℝ =>
            ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
              ((t : ℂ) ^ (α - 1) * (t : ℂ) ^ k))
            (volume.restrict (Icc 0 a)) := by
        have hfun :
            (fun t : ℝ =>
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                ((t : ℂ) ^ (α - 1) * (t : ℂ) ^ k)) =
              fun t : ℝ => (t : ℂ) ^ (α - 1) *
                (((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
                  (t : ℂ) ^ k) := by
          funext t; ring
        rw [hfun]
        exact integrableOn_cpow_mul_Icc hα ha.le (by fun_prop)
      rw [integral_finsetSum (Finset.range N) fun k _ => hterm k]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MeasureTheory.integral_const_mul]
    rw [hswap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hTaylor]
  have hpow (k : ℕ) :
      regIncompleteMellin α a (fun t => (t : ℂ) ^ k) =
        (a : ℂ) ^ (α + k) * (ascPochhammer ℂ k).eval α * (Gamma (α + k + 1))⁻¹ :=
    regIncompleteMellin_pow hα ha k
  simp_rw [hpow]
  have hrem :
      regIncompleteMellin α a (fun t => (t : ℂ) ^ N * mellinPeanoRemainder N a K t) =
        (ascPochhammer ℂ N).eval α *
          regIncompleteMellin (α + N) a (mellinPeanoRemainder N a K) :=
    regIncompleteMellin_mul_pow hα ha hψ N
  rw [hrem]

/-- Finite differentiability of the integrand yields an analytic continuation of the
regularized incomplete Mellin transform from `{0 < re α}` to `{-(N : ℝ) < re α}`. -/
theorem exists_regIncompleteMellin_continuation {N : ℕ} {a : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1)
    {K : ℝ → ℂ} (hK : ContDiffOn ℝ N K (Icc 0 a)) :
    ∃ Φ : ℂ → ℂ,
      AnalyticOn ℂ Φ {α : ℂ | -(N : ℝ) < α.re} ∧
        Set.EqOn Φ (fun α => regIncompleteMellin α a K) {α : ℂ | 0 < α.re} := by
  cases N with
  | zero =>
      refine ⟨fun α => regIncompleteMellin α a K, ?_, fun _ _ => rfl⟩
      convert analyticOn_regIncompleteMellin ha hK.continuousOn
      simp
  | succ n =>
      have hN : 0 < n + 1 := Nat.succ_pos _
      have hψ : ContinuousOn (mellinPeanoRemainder (n + 1) a K) (Icc 0 a) :=
        continuousOn_mellinPeanoRemainder hN ha (by simpa using hK)
      let Φ : ℂ → ℂ := fun α =>
        (∑ k ∈ Finset.range (n + 1),
          ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc 0 a) 0) *
            ((a : ℂ) ^ (α + k) * (ascPochhammer ℂ k).eval α * (Gamma (α + k + 1))⁻¹)) +
          (ascPochhammer ℂ (n + 1)).eval α *
            regIncompleteMellin (α + (n + 1 : ℕ)) a (mellinPeanoRemainder (n + 1) a K)
      refine ⟨Φ, ?_, ?_⟩
      · have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
        have hTdiff : Differentiable ℂ
            (fun α : ℂ => ∑ k ∈ Finset.range (n + 1),
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc (0 : ℝ) a) 0) *
                ((a : ℂ) ^ (α + k) * Polynomial.eval α (ascPochhammer ℂ k) *
                  (Gamma (α + k + 1))⁻¹)) := by
          refine Differentiable.fun_sum fun k _ => ?_
          intro α
          have hcpow : DifferentiableAt ℂ (fun β : ℂ => (a : ℂ) ^ (β + k)) α :=
            ((differentiable_id.add (differentiable_const _)).const_cpow (Or.inl ha0)) α
          have hP : DifferentiableAt ℂ (fun β : ℂ => Polynomial.eval β (ascPochhammer ℂ k)) α :=
            (ascPochhammer ℂ k).differentiable α
          have hG : DifferentiableAt ℂ (fun β : ℂ => (Gamma (β + k + 1))⁻¹) α :=
            (Complex.differentiable_one_div_Gamma.comp (by fun_prop : Differentiable ℂ
              (fun β : ℂ => β + k + 1))) α
          exact ((hcpow.mul hP).mul hG).const_mul _
        have hT : AnalyticOn ℂ
            (fun α : ℂ => ∑ k ∈ Finset.range (n + 1),
              ((k.factorial : ℂ)⁻¹ * iteratedDerivWithin k K (Icc (0 : ℝ) a) 0) *
                ((a : ℂ) ^ (α + k) * Polynomial.eval α (ascPochhammer ℂ k) *
                  (Gamma (α + k + 1))⁻¹))
            Set.univ :=
          (analyticOn_univ_iff_differentiable).mpr hTdiff
        have hP : AnalyticOn ℂ (fun α : ℂ => (ascPochhammer ℂ (n + 1)).eval α) Set.univ :=
          AnalyticOn.eval_polynomial (ascPochhammer ℂ (n + 1))
        have hM := analyticOn_regIncompleteMellin ha hψ
        have hshift : AnalyticOn ℂ (fun α : ℂ => α + (n + 1 : ℕ))
            {α | -((n + 1 : ℕ) : ℝ) < α.re} :=
          (analyticOn_id.add analyticOn_const).mono (subset_univ _)
        have hMs : AnalyticOn ℂ
            (fun α =>
              regIncompleteMellin (α + (n + 1 : ℕ)) a (mellinPeanoRemainder (n + 1) a K))
            {α | -((n + 1 : ℕ) : ℝ) < α.re} :=
          hM.comp hshift fun α hα => by
            change 0 < (α + (n + 1 : ℕ)).re
            have : -((n + 1 : ℕ) : ℝ) < α.re := hα
            simp only [add_re, natCast_re]
            linarith
        exact (hT.mono (subset_univ _)).add ((hP.mono (subset_univ _)).mul hMs)
      · intro α hα
        dsimp [Φ]
        exact (regIncompleteMellin_eq_taylor_peano (N := n + 1) hN ha hK hα).symm

end Complex

end IncompleteMellin
