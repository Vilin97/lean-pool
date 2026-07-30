/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.LocalFactor
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealEulerProduct
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealFactor
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex

namespace NumberField.Odlyzko

theorem hasDerivAt_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (localFactor q)
      (-(inverseNormPower q s * Complex.log q /
        (1 - inverseNormPower q s) ^ 2)) s := by
  have hx := hasDerivAt_inverseNormPower (q := q) (Nat.ne_zero_of_lt hq) s
  have hden : 1 - inverseNormPower q s ≠ 0 :=
    one_sub_inverseNormPower_ne_zero hq hs
  change HasDerivAt (fun z : ℂ ↦ (1 - inverseNormPower q z)⁻¹) _ s
  apply (hx.const_sub 1).fun_inv hden |>.congr_deriv
  ring

theorem logDeriv_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (localFactor q) s =
      -(Complex.log q * inverseNormPower q s /
        (1 - inverseNormPower q s)) := by
  rw [logDeriv_apply, (hasDerivAt_localFactor hq hs).deriv]
  simp only [localFactor]
  grind

theorem hasSum_logDeriv_localFactor {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun e : ℕ ↦ Complex.log q * inverseNormPower q s ^ (e + 1))
      (-logDeriv (localFactor q) s) := by
  have hgeom := hasSum_inverseNormPower_pow hq hs
  have hmul := hgeom.mul_left
    (Complex.log q * inverseNormPower q s)
  have hvalue :
      Complex.log q * inverseNormPower q s * localFactor q s =
        Complex.log q * inverseNormPower q s /
          (1 - inverseNormPower q s) := by
    simp [localFactor, div_eq_mul_inv]
  rw [logDeriv_localFactor hq hs, neg_neg, ← hvalue]
  grind

end NumberField.Odlyzko

end

section

open Complex IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_primeIdealFactor (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (primeIdealFactor K P) s =
      -(Complex.log (primeIdealNorm K P) *
        inverseNormPower (primeIdealNorm K P) s /
          (1 - inverseNormPower (primeIdealNorm K P) s)) := by
  exact logDeriv_localFactor (one_lt_primeIdealNorm K P) hs

theorem hasSum_neg_logDeriv_primeIdealFactor
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun e : ℕ ↦ Complex.log (primeIdealNorm K P) *
        inverseNormPower (primeIdealNorm K P) s ^ (e + 1))
      (-logDeriv (primeIdealFactor K P) s) :=
  hasSum_logDeriv_localFactor (one_lt_primeIdealNorm K P) hs

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A dedekind zeta half plane used in the Odlyzko-bound argument. -/
def dedekindZetaHalfPlane : Set ℂ := {s | 1 < s.re}

lemma isOpen_dedekindZetaHalfPlane : IsOpen dedekindZetaHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem multipliableLocallyUniformlyOn_primeIdealFactor :
    MultipliableLocallyUniformlyOn
      (primeIdealFactor K) dedekindZetaHalfPlane := by
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 1 < s.re at hs
  let δ : ℝ := (s.re - 1) / 2
  let σ : ℝ := (s.re + 1) / 2
  have hδ : 0 < δ := by grind
  have hσ : 1 < σ := by grind
  refine ⟨Metric.closedBall s δ, ?_, ?_⟩
  · exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Metric.closedBall s δ, Metric.closedBall_mem_nhds s hδ,
        Set.inter_subset_left⟩
  · have hu :
        Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
          2 * (primeIdealNorm K P : ℝ) ^ (-σ)) :=
      (summable_primeIdealNorm_rpow K hσ).mul_left 2
    have hbound :
        ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          ∀ z ∈ Metric.closedBall s δ,
            ‖primeIdealFactor K P z - 1‖ ≤
              2 * (primeIdealNorm K P : ℝ) ^ (-σ) := by
      filter_upwards [] with P z hz
      apply norm_primeIdealFactor_sub_one_le K P hσ
      have hdist : dist z s ≤ δ := Metric.mem_closedBall.mp hz
      have hre : |(z - s).re| ≤ dist z s := by
        simpa [dist_eq, norm_sub_rev] using Complex.abs_re_le_norm (z - s)
      dsimp [δ] at hdist
      dsimp [σ]
      rw [Complex.sub_re] at hre
      grind
    simpa only [add_sub_cancel] using
      Summable.multipliableUniformlyOn_one_add
        (ProperSpace.isCompact_closedBall s δ) hu hbound
        (fun P z hz ↦ by
          have hdist : dist z s ≤ δ := Metric.mem_closedBall.mp hz
          have hre : |(z - s).re| ≤ dist z s := by
            simpa [dist_eq, norm_sub_rev] using Complex.abs_re_le_norm (z - s)
          dsimp [δ] at hdist
          rw [Complex.sub_re] at hre
          have hzσ : σ ≤ z.re := by grind
          change ContinuousWithinAt
            (localFactor (primeIdealNorm K P) - fun _ ↦ 1)
              (Metric.closedBall s δ) z
          exact ((hasDerivAt_localFactor (one_lt_primeIdealNorm K P)
            (hσ.trans_le hzσ |> zero_lt_one.trans)).continuousAt.sub
              continuousAt_const).continuousWithinAt)

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_logDeriv_primeIdealFactor {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun P : HeightOneSpectrum (𝓞 K) ↦
        logDeriv (primeIdealFactor K P) s) := by
  let ε : ℝ := (s.re - 1) / 2
  let σ : ℝ := (s.re + 1) / 2
  have hε : 0 < ε := by grind
  have hσ : 1 < σ := by grind
  rw [← summable_norm_iff]
  apply ((summable_primeIdealNorm_rpow K hσ).mul_left (2 / ε)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro P
  let q := primeIdealNorm K P
  let x := inverseNormPower q s
  have hq : 1 < q := one_lt_primeIdealNorm K P
  have hx : ‖x‖ < 1 / 2 :=
    norm_inverseNormPower_primeIdeal_lt_half K P hs
  have hdenLower : 1 / 2 ≤ ‖1 - x‖ := by
    calc
      1 / 2 ≤ 1 - ‖x‖ := by linarith
      _ ≤ ‖1 - x‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) x
  rw [logDeriv_primeIdealFactor K P (zero_lt_one.trans hs),
    norm_neg, norm_div, norm_mul]
  have hlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    calc
      ‖Complex.log (q : ℂ)‖ =
          ‖((Real.log (q : ℝ) : ℝ) : ℂ)‖ := by simp
      _ = Real.log q := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast
            (Nat.le_of_lt hq)))]
  rw [hlog, show ‖x‖ = (q : ℝ) ^ (-s.re) by
    exact norm_inverseNormPower q (Nat.zero_lt_of_lt hq) s]
  calc
    Real.log q * (q : ℝ) ^ (-s.re) / ‖1 - x‖ ≤
        Real.log q * (q : ℝ) ^ (-s.re) / (1 / 2) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · simp_all
    _ = 2 * (Real.log q * (q : ℝ) ^ (-s.re)) := by ring
    _ ≤ 2 * (((q : ℝ) ^ ε / ε) * (q : ℝ) ^ (-s.re)) := by
      gcongr
      exact Real.log_le_rpow_div (by positivity) hε
    _ = (2 / ε) * (q : ℝ) ^ (-σ) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add (by positivity)]
      grind

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_dedekindZeta_eq_tsum_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    logDeriv (dedekindZeta K) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        logDeriv (primeIdealFactor K P) s := by
  have hs_mem : s ∈ dedekindZetaHalfPlane := hs
  have hprod :=
    logDeriv_tprod_eq_tsum
      (isOpen_dedekindZetaHalfPlane)
      hs_mem
      (f := primeIdealFactor K)
      (fun P ↦ primeIdealFactor_ne_zero K P (zero_lt_one.trans hs))
      (fun P z hz ↦
        (hasDerivAt_localFactor (one_lt_primeIdealNorm K P)
          (zero_lt_one.trans hz)).differentiableAt.differentiableWithinAt)
      (summable_logDeriv_primeIdealFactor K hs)
      (multipliableLocallyUniformlyOn_primeIdealFactor K)
      (tprod_primeIdealFactor_ne_zero K hs)
  rw [← hprod]
  have heq :
      (fun z : ℂ ↦
        ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P z) =ᶠ[𝓝 s]
          dedekindZeta K := by
    filter_upwards [(isOpen_dedekindZetaHalfPlane.mem_nhds hs_mem)]
      with z hz
    exact dedekindZeta_primeIdeal_eulerProduct_tprod K hz
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
    dedekindZeta_primeIdeal_eulerProduct_tprod K hs]

theorem neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (dedekindZeta K) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -logDeriv (primeIdealFactor K P) s := by
  rw [logDeriv_dedekindZeta_eq_tsum_primeIdeal K hs,
    tsum_neg]

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime power log term used in the Odlyzko-bound argument. -/
noncomputable def primePowerLogTerm
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) : ℂ :=
  Complex.log (primeIdealNorm K P) *
    inverseNormPower (primeIdealNorm K P) s ^ (e + 1)

theorem primePowerLogTerm_eq_log_mul_cexp_neg
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    primePowerLogTerm K P e s =
      (Real.log (primeIdealNorm K P) : ℂ) *
        Complex.exp
          (-(((e + 1 : ℕ) : ℝ) *
            Real.log (primeIdealNorm K P)) * s) := by
  have hq : (0 : ℝ) ≤ primeIdealNorm K P := by positivity
  have hqC : (primeIdealNorm K P : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_primeIdealNorm K P)).ne'
  rw [primePowerLogTerm, inverseNormPower,
    Complex.cpow_def_of_ne_zero hqC, ← Complex.exp_nat_mul]
  rw [Complex.ofReal_log hq]
  push_cast
  ring_nf

lemma norm_primePowerLogTerm
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    ‖primePowerLogTerm K P e s‖ =
      Real.log (primeIdealNorm K P) *
        ((primeIdealNorm K P : ℝ) ^ (-s.re)) ^ (e + 1) := by
  let q := primeIdealNorm K P
  have hq : 1 < q := one_lt_primeIdealNorm K P
  have hlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    calc
      ‖Complex.log (q : ℂ)‖ =
          ‖((Real.log (q : ℝ) : ℝ) : ℂ)‖ := by simp
      _ = Real.log q := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast
            (Nat.le_of_lt hq)))]
  rw [primePowerLogTerm, norm_mul, norm_pow, hlog,
    norm_inverseNormPower q (Nat.zero_lt_of_lt hq)]

theorem summable_norm_primePowerLogTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      ‖primePowerLogTerm K pe.1 pe.2 s‖) := by
  rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
  constructor
  · intro P
    rw [show (fun e ↦ ‖primePowerLogTerm K P e s‖) =
        fun e ↦ Real.log (primeIdealNorm K P) *
          ((primeIdealNorm K P : ℝ) ^ (-s.re)) ^ (e + 1) by
      funext e
      exact norm_primePowerLogTerm K P e s]
    exact ((summable_geometric_of_lt_one
      (Real.rpow_nonneg (by positivity) _)
      (by
        rw [← norm_inverseNormPower
          (primeIdealNorm K P)
          (Nat.zero_lt_of_lt <| one_lt_primeIdealNorm K P) s]
        exact (norm_inverseNormPower_primeIdeal_lt_half K P hs).trans
          (by norm_num))).comp_injective
            (fun _ _ h ↦ Nat.add_right_cancel h)).mul_left _
  · have hmajor :=
      (summable_primeIdeal_log_mul_rpow K hs).mul_left 2
    apply hmajor.of_nonneg_of_le
      (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
    intro P
    let q := primeIdealNorm K P
    let r : ℝ := (q : ℝ) ^ (-s.re)
    have hq : 1 < q := one_lt_primeIdealNorm K P
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    have hrhalf : r < 1 / 2 := by
      dsimp [r]
      rw [← norm_inverseNormPower q (Nat.zero_lt_of_lt hq) s]
      exact norm_inverseNormPower_primeIdeal_lt_half K P hs
    rw [show (fun e ↦ ‖primePowerLogTerm K P e s‖) =
        fun e ↦ Real.log q * r ^ (e + 1) by
      funext e
      exact norm_primePowerLogTerm K P e s]
    rw [tsum_mul_left]
    have hgeom :
        ∑' e : ℕ, r ^ (e + 1) = r / (1 - r) := by
      rw [show (fun e : ℕ ↦ r ^ (e + 1)) =
          fun e ↦ r * r ^ e by
        grind]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (hrhalf.trans (by norm_num))]
      simp [div_eq_mul_inv]
    rw [hgeom]
    calc
      Real.log q * (r / (1 - r)) ≤ Real.log q * (2 * r) := by
        gcongr
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      _ = 2 * (Real.log q * (q : ℝ) ^ (-s.re)) := by grind

theorem neg_logDeriv_dedekindZeta_eq_tsum_primePower {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (dedekindZeta K) s =
      ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        primePowerLogTerm K pe.1 pe.2 s := by
  have habs := summable_norm_primePowerLogTerm K hs
  have hsum :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        primePowerLogTerm K pe.1 pe.2 s) :=
    summable_norm_iff.mp habs
  rw [neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal K hs]
  rw [hsum.tsum_prod]
  congr 1
  funext P
  exact (hasSum_neg_logDeriv_primeIdealFactor K P
    (zero_lt_one.trans hs)).tsum_eq.symm

end NumberField.Odlyzko

end
