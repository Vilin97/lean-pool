/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ParameterAbsorption
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField

/-! # Stream-function and diffusivity bounds parameter instance -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Flow

theorem TraceInstanceFrozen.e44_rpow_sqrt {e q : ℝ} (he : 0 < e) :
    Real.sqrt (e ^ q) = e ^ (q / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]
  congr 1
  ring

theorem TraceInstanceFrozen.e44_inverse_sqrt_kappa_of_power_lower
    {e c q ν : ℝ} (he : 0 < e) (hc : 0 < c)
    (hν : c * e ^ q ≤ ν) :
    (Real.sqrt ν)⁻¹ ≤ (Real.sqrt c)⁻¹ * e ^ (-q / 2) := by
  have hroot : Real.sqrt c * e ^ (q / 2) ≤ Real.sqrt ν := by
    calc
      Real.sqrt c * e ^ (q / 2) = Real.sqrt (c * e ^ q) := by
        rw [Real.sqrt_mul hc.le, TraceInstanceFrozen.e44_rpow_sqrt he]
      _ ≤ Real.sqrt ν := Real.sqrt_le_sqrt hν
  have hrootν : 0 < Real.sqrt ν := Real.sqrt_pos.2 (lt_of_lt_of_le (by positivity) hν)
  have hrootc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have heq : 0 < e ^ (q / 2) := Real.rpow_pos_of_pos he _
  have hinvPow : (e ^ (q / 2))⁻¹ = e ^ (-q / 2) := by
    rw [← Real.rpow_neg he.le]
    congr 1
    ring
  calc
    (Real.sqrt ν)⁻¹ ≤ (Real.sqrt c * e ^ (q / 2))⁻¹ :=
      (inv_le_inv₀ hrootν (mul_pos hrootc heq)).2 hroot
    _ = (Real.sqrt c)⁻¹ * e ^ (-q / 2) := by
      rw [mul_inv, hinvPow]

/-- The later-scale hypothesis gives the two radius comparisons used by the
parameter absorption and the cutoff recombination. -/
theorem TraceInstanceFrozen.e44_later_scale_comparisons
    {e p δ R : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hδ : 0 < δ)
    (hlater : e ^ (p - δ) ≤ R) :
    e ^ p ≤ R ∧ e ^ (-δ) ≤ R / e ^ p := by
  have hpower : e ^ p ≤ e ^ (p - δ) :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hr : 0 < e ^ p := Real.rpow_pos_of_pos he _
  have hratio : e ^ (-δ) = e ^ (p - δ) / e ^ p := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  refine ⟨hpower.trans hlater, ?_⟩
  rw [hratio]
  exact div_le_div_of_nonneg_right hlater hr.le

/-- Derivative cutoff order used to control the E44 trace tail. -/
def e44TraceTailOrder (β : ℝ) : ℕ :=
  ⌈((β + gamma β) / 2) / delta β⌉₊

/-- Amplitude required for the E44 trace frequency cutoff. -/
def e44TraceCutoffAmplitude (β c : ℝ) : ℝ :=
  (4096 * (e44TraceTailOrder β : ℝ) * max 1 (Real.sqrt c)⁻¹) /
    e44TailExponent

/-- Fixed positive-word trace constant generated from the diffusivity bounds lower constant.
Once `c` is chosen from `l_recurse β C₀`, this constant is independent of
the Ingredients instance. -/
def e44FrozenTraceConstant (β c : ℝ) : ℝ :=
  e44TraceCombinationConstant (e44TraceCutoffAmplitude β c)
    (Real.sqrt 3) e44TailConstant

theorem TraceInstanceFrozen.e44_trace_rpow_le_nat_power
    {ε p δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (hn : p ≤ δ * (n : ℝ)) :
    Real.rpow ε (-p) ≤ (Real.rpow ε (-δ)) ^ n := by
  have hpow : (Real.rpow ε (-δ)) ^ n = Real.rpow ε (-δ * (n : ℝ)) := by
    exact (Real.rpow_mul_natCast hε.le (-δ) n).symm
  calc
    Real.rpow ε (-p) ≤ Real.rpow ε (-δ * (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by nlinarith)
    _ = (Real.rpow ε (-δ)) ^ n := hpow.symm

/- The tail amplitude is chosen from the polynomial loss exponent and the
Diffusivity bounds constant. This makes the absorption uniform over every positive `c`. -/
theorem e44_trace_numeric_absorption
    {β c ε : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2 ^ 24 ≤ c * e44TraceCutoffAmplitude β c ^ 2) ∧
    (32 ≤ e44TraceCutoffAmplitude β c) ∧
    (Real.sqrt c)⁻¹ * Real.rpow ε (-((β + gamma β) / 2)) *
      Real.exp (-e44TailExponent * e44TraceCutoffAmplitude β c *
        Real.rpow ε (-delta β)) ≤ 1 := by
  let n := e44TraceTailOrder β
  let nr : ℝ := n
  let M := max 1 (Real.sqrt c)⁻¹
  let X := Real.rpow ε (-delta β)
  let A := e44TraceCutoffAmplitude β c
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hβpos : 0 < β := by linarith
  have hp : 0 < (β + gamma β) / 2 := by
    exact (div_pos (add_pos hβpos hγ) (by norm_num))
  have hpdiv : 0 < ((β + gamma β) / 2) / delta β := div_pos hp hδ
  have hceil : ((β + gamma β) / 2) / delta β ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_ceil (((β + gamma β) / 2) / delta β))
  have hnr : 1 ≤ nr := by
    dsimp [nr, n, e44TraceTailOrder]
    have hpos : 0 < ⌈((β + gamma β) / 2) / delta β⌉₊ :=
      Nat.ceil_pos.mpr hpdiv
    exact_mod_cast (Nat.succ_le_iff.mpr hpos)
  have horder : (β + gamma β) / 2 ≤ delta β * nr := by
    calc
      (β + gamma β) / 2 ≤ (n : ℝ) * delta β :=
        (div_le_iff₀ hδ).mp hceil
      _ = delta β * nr := by simp [nr, mul_comm]
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hMnonneg : 0 ≤ M := le_trans (by norm_num) hM1
  have hMroot : (Real.sqrt c)⁻¹ ≤ M := by dsimp [M]; exact le_max_right _ _
  have hX1 : 1 ≤ X := by
    dsimp [X]
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1
    linarith
  have hXnonneg : 0 ≤ X := le_trans (by norm_num) hX1
  have hpower : Real.rpow ε (-((β + gamma β) / 2)) ≤ X ^ n := by
    simpa [X] using TraceInstanceFrozen.e44_trace_rpow_le_nat_power hε hε1 n horder
  have htailPos : 0 < e44TailExponent := e44_tail_exponent_pos
  have htailLe : e44TailExponent ≤ 1 := by
    have hroot : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        Real.sqrt_nonneg (2 : ℝ)]
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hmul : 1 ≤ Real.pi * Real.sqrt 2 := by
      simpa using mul_le_mul hpi hroot (by norm_num) (by positivity)
    have hden : 1 ≤ 2048 * Real.pi * Real.sqrt 2 := by
      calc
        1 ≤ Real.pi * Real.sqrt 2 := hmul
        _ ≤ 2048 * (Real.pi * Real.sqrt 2) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2048)
              (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _))
        _ = 2048 * Real.pi * Real.sqrt 2 := by ring
    dsimp [e44TailExponent]
    exact (div_le_iff₀ (by positivity)).2 (by simpa using hden)
  have hAlo : 4096 * nr * M ≤ A := by
    have hbase : 0 ≤ 4096 * (e44TraceTailOrder β : ℝ) *
        max 1 (Real.sqrt c)⁻¹ := by positivity
    have hprod : 4096 * (e44TraceTailOrder β : ℝ) *
        max 1 (Real.sqrt c)⁻¹ * e44TailExponent ≤
        4096 * (e44TraceTailOrder β : ℝ) * max 1 (Real.sqrt c)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_left htailLe hbase
    have hdiv : 4096 * (e44TraceTailOrder β : ℝ) *
        max 1 (Real.sqrt c)⁻¹ ≤
        (4096 * (e44TraceTailOrder β : ℝ) *
          max 1 (Real.sqrt c)⁻¹) / e44TailExponent :=
      (le_div_iff₀ htailPos).2 hprod
    simpa [A, e44TraceCutoffAmplitude, nr, n] using hdiv
  have hAlarge : 32 ≤ A := by
    have : 4096 ≤ 4096 * nr * M := by nlinarith [hnr, hM1]
    exact (by norm_num : (32 : ℝ) ≤ 4096).trans (this.trans hAlo)
  have hCM : 1 ≤ c * M ^ 2 := by
    by_cases hc1 : c ≤ 1
    · have hroot : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
      have hInv : c * (Real.sqrt c)⁻¹ ^ 2 = 1 := by
        rw [inv_pow, Real.sq_sqrt hc.le]
        field_simp [ne_of_gt hroot]
      have hsquare : (Real.sqrt c)⁻¹ ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (by positivity) hMroot 2
      have hmul := mul_le_mul_of_nonneg_left hsquare hc.le
      nlinarith
    · have hc1 : 1 ≤ c := le_of_not_ge hc1
      nlinarith [sq_nonneg (M - 1)]
  have hA5scale : 2 ^ 24 ≤ c * A ^ 2 := by
    have hnsq : 1 ≤ nr ^ 2 := by nlinarith
    have hprod : 1 ≤ nr ^ 2 * (c * M ^ 2) := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ nr ^ 2 * (c * M ^ 2) :=
          mul_le_mul hnsq hCM (by norm_num) (by nlinarith)
    have hbase : 4096 ^ 2 ≤ c * (4096 * nr * M) ^ 2 := by
      calc
        4096 ^ 2 = 4096 ^ 2 * 1 := by ring
        _ ≤ 4096 ^ 2 * (nr ^ 2 * (c * M ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = c * (4096 * nr * M) ^ 2 := by ring
    have hAsq : (4096 * nr * M) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by positivity) hAlo 2
    have hmul := mul_le_mul_of_nonneg_left hAsq hc.le
    nlinarith [hbase]
  have hArg : e44TailExponent * A * X = 4096 * nr * M * X := by
    dsimp [A, e44TraceCutoffAmplitude, n, e44TraceTailOrder, nr, M]
    field_simp [ne_of_gt htailPos]
  have hArgNeg : -e44TailExponent * A * X = -(4096 * nr * M * X) := by
    calc
      -e44TailExponent * A * X = -(e44TailExponent * A * X) := by ring
      _ = -(4096 * nr * M * X) := congrArg Neg.neg hArg
  have hMexp : M * X ^ n ≤ Real.exp (4096 * nr * M * X) := by
    have hMexp0 : M ≤ Real.exp M := by
      have h := Real.add_one_le_exp M
      linarith
    have hXexp0 : X ≤ Real.exp X := by
      have h := Real.add_one_le_exp X
      linarith
    have hXpow : X ^ n ≤ Real.exp (nr * X) := by
      calc
        X ^ n ≤ (Real.exp X) ^ n :=
          by exact pow_le_pow_left₀ hXnonneg hXexp0 n
        _ = Real.exp (nr * X) := by rw [← Real.exp_nat_mul]
    have hMpow : M * X ^ n ≤ Real.exp (M + nr * X) := by
      calc
        M * X ^ n ≤ Real.exp M * Real.exp (nr * X) :=
          mul_le_mul hMexp0 hXpow (pow_nonneg hXnonneg n) (Real.exp_nonneg _)
        _ = Real.exp (M + nr * X) := by rw [← Real.exp_add]
    have hMterm : M ≤ nr * M * X := by
      calc
        M ≤ M * X := by simpa using mul_le_mul_of_nonneg_left hX1 hMnonneg
        _ ≤ nr * (M * X) :=
          by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hnr
              (mul_nonneg hMnonneg hXnonneg)
        _ = nr * M * X := by ring
    have hNXterm : nr * X ≤ nr * M * X := by
      calc
        nr * X ≤ nr * (M * X) :=
          have hMX : X ≤ M * X := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hM1 hXnonneg
          mul_le_mul_of_nonneg_left hMX (by linarith)
        _ = nr * M * X := by ring
    have hExponent : M + nr * X ≤ 4096 * nr * M * X := by
      calc
        M + nr * X ≤ nr * M * X + nr * M * X := add_le_add hMterm hNXterm
        _ = 2 * (nr * M * X) := by ring
        _ ≤ 4096 * nr * M * X := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4096)
            (mul_nonneg (mul_nonneg (le_trans (by norm_num) hnr) hMnonneg) hXnonneg)
    exact hMpow.trans (Real.exp_le_exp.mpr hExponent)
  have hExpProduct : M * X ^ n *
      Real.exp (-(4096 * nr * M * X)) ≤ 1 := by
    calc
      M * X ^ n * Real.exp (-(4096 * nr * M * X)) ≤
          Real.exp (4096 * nr * M * X) *
            Real.exp (-(4096 * nr * M * X)) :=
        mul_le_mul_of_nonneg_right hMexp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpre : (Real.sqrt c)⁻¹ * Real.rpow ε (-((β + gamma β) / 2)) ≤
      M * X ^ n := by
    exact mul_le_mul hMroot hpower (Real.rpow_nonneg hε.le _) (by positivity)
  refine ⟨hA5scale, hAlarge, ?_⟩
  calc
    (Real.sqrt c)⁻¹ * Real.rpow ε (-((β + gamma β) / 2)) *
        Real.exp (-e44TailExponent * A * X) ≤
      M * X ^ n * Real.exp (-(4096 * nr * M * X)) := by
        rw [hArgNeg]
        exact mul_le_mul_of_nonneg_right hpre (Real.exp_nonneg _)
    _ ≤ 1 := hExpProduct

/-- The floor cutoff realizes the two-sided Fourier radius estimates needed
for the low-frequency trace and the analytic tail. -/
theorem TraceInstanceFrozen.e44_natural_cutoff_data
    {r R A : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hr1 : r ≤ 1)
    (hA : 32 ≤ A) :
    ∃ M : ℕ, 0 < M ∧
      2 * Real.pi * Real.sqrt 2 * (M : ℝ) ≤ A / r ∧
      A / (2 * r) ≤ 2 * Real.pi * Real.sqrt 2 * (M : ℝ) ∧
      A / r ≤ 2 * Real.pi * Real.sqrt 2 * (M + 1 : ℝ) ∧
      1 ≤ (R / 2) * (M + 1 : ℝ) := by
  let lam : ℝ := 2 * Real.pi * Real.sqrt 2
  let x : ℝ := A / (lam * r)
  let M : ℕ := Nat.floor x
  have hLamPos : 0 < lam := by dsimp [lam]; positivity
  have hroot : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  have hpi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have hLamLe : lam ≤ 16 := by
    dsimp [lam]
    calc
      2 * Real.pi * Real.sqrt 2 ≤ 2 * 4 * Real.sqrt 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpi (by norm_num)) (Real.sqrt_nonneg _)
      _ ≤ 2 * 4 * 2 := by nlinarith [hroot]
      _ = 16 := by norm_num
  have hden : lam * r ≤ 16 := by
    calc
      lam * r ≤ 16 * r := mul_le_mul_of_nonneg_right hLamLe hr.le
      _ ≤ 16 := by
        calc
          16 * r ≤ 16 * 1 := mul_le_mul_of_nonneg_left hr1 (by norm_num)
          _ = 16 := by ring
  have hx2 : 2 ≤ x := by
    apply (le_div_iff₀ (mul_pos hLamPos hr)).2
    nlinarith [hden, hA]
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx2
  have hfloor : (M : ℝ) ≤ x := by dsimp [M]; exact Nat.floor_le hx0
  have hxlt : x < (M : ℝ) + 1 := by dsimp [M]; exact Nat.lt_floor_add_one x
  have hMpos : 0 < M := by
    by_contra hnot
    have hM0 : M = 0 := by omega
    have hxsmall : x < 1 := by simpa [hM0] using hxlt
    linarith
  have hxminus : x - 1 ≤ (M : ℝ) := by linarith
  have hxhalf : x / 2 ≤ (M : ℝ) := by
    have hhalf : x / 2 ≤ x - 1 := by linarith
    linarith
  have hlamx : lam * x = A / r := by
    dsimp [x]
    field_simp [ne_of_gt hr, ne_of_gt hLamPos]
  have hKup : lam * (M : ℝ) ≤ A / r := by
    calc
      lam * (M : ℝ) ≤ lam * x := mul_le_mul_of_nonneg_left hfloor hLamPos.le
      _ = A / r := hlamx
  have hKlower : A / (2 * r) ≤ lam * (M : ℝ) := by
    have hlamhalf : lam * (x / 2) = A / (2 * r) := by
      dsimp [x]
      field_simp [ne_of_gt hr, ne_of_gt hLamPos]
    calc
      A / (2 * r) = lam * (x / 2) := hlamhalf.symm
      _ ≤ lam * (M : ℝ) := mul_le_mul_of_nonneg_left hxhalf hLamPos.le
  have hKupper : A / r ≤ lam * ((M : ℝ) + 1) := by
    calc
      A / r = lam * x := hlamx.symm
      _ ≤ lam * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hxlt.le hLamPos.le
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hratio : 1 ≤ R / r := (le_div_iff₀ hr).2 (by simpa using hrR)
  have hscaled : A / (2 * lam) ≤ (R / 2) * x := by
    have heq : (R / 2) * x = (A / (2 * lam)) * (R / r) := by
      dsimp [x]
      field_simp [ne_of_gt hr, ne_of_gt hLamPos]
    rw [heq]
    calc
      A / (2 * lam) = (A / (2 * lam)) * 1 := by ring
      _ ≤ (A / (2 * lam)) * (R / r) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  have hscaledFloor : (R / 2) * x ≤ (R / 2) * ((M : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hxlt.le (by positivity)
  have hAdiv : A / 32 ≤ A / (2 * lam) := by
    exact div_le_div_of_nonneg_left
      (le_trans (by norm_num) hA) (by positivity)
      (by nlinarith [hLamLe])
  have hTailScale : 1 ≤ (R / 2) * ((M : ℝ) + 1) := by
    calc
      1 ≤ A / 32 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2 (by simpa using hA)
      _ ≤ A / (2 * lam) := hAdiv
      _ ≤ (R / 2) * x := hscaled
      _ ≤ (R / 2) * ((M : ℝ) + 1) := hscaledFloor
  exact ⟨M, hMpos, by simpa [lam] using hKup, by simpa [lam] using hKlower,
    by simpa [lam] using hKupper, by simpa using hTailScale⟩

/-- The stream-function estimates second-jet bound gives the actual drift gradient bound used
by the low-mode trace estimate. -/
theorem e44_streamVelocity_spatialDerivative_bound_of_A3
    {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ t x, ‖jointSpatialFDeriv
      (streamVel (fun s y => Φ (m - 1) s y)) t x‖ ≤
      2 ^ 22 * a β I.Λ (m - 1) := by
  let φ := fun s y => Φ (m - 1) s y
  let b := streamVel φ
  have hφ : IsAdmissibleStream φ :=
    Infra.Section4.theta_prev_stream_admissible I Φ hΦ hm
  have hb := streamVel_smoothPeriodic φ hφ
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos he _
  have hP : 0 ≤ 2 ^ 21 * a β I.Λ (m - 1) := by positivity
  intro t x
  rw [jointSpatialFDeriv_eq_slice hb t x]
  let L := fderiv ℝ (fun y => b t y) x
  have hslice : DifferentiableAt ℝ (fun y => b t y) x := by
    have hmap : ContDiff ℝ ∞ (fun y : Vec 2 => (t, y)) :=
      contDiff_const.prodMk contDiff_id
    have hsliceSmooth : ContDiff ℝ ∞ (fun y => b t y) := by
      simpa [b, Function.uncurry, Function.comp_def] using hb.smooth.comp hmap
    exact (hsliceSmooth.differentiable (by norm_num)) x
  have hpartial (d i : Fin 2) :
      |(L (basisVec d)) i| ≤ 2 ^ 21 * a β I.Λ (m - 1) := by
    have hcoord : spaceGrad (fun y => b t y i) x d = (L (basisVec d)) i := by
      rw [spaceGrad, fderiv_apply hslice i]
      simp [ContinuousLinearMap.comp_apply, L]
    have hvel := Infra.Section4.iterate_velocity_analytic_profile_of_A3
      I hΦ hm hA3 t [d] (by simp) x i
    have hscale : |spaceGrad (fun y => b t y i) x d| ≤
        2 ^ 21 * a β I.Λ (m - 1) := by
      calc
        |spaceGrad (fun y => b t y i) x d| =
            |Infra.Section4.iterateSpatialWord [d]
              (fun y => streamVel (Φ (m - 1)) t y i) x| := by
                simp [b, φ, Infra.Section4.iterateSpatialWord, AVenhance.spaceGrad]
        _ ≤ 8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) *
            (1 : ℝ) * (256 * (epsilon β I.Λ (m - 1))⁻¹) := by
              simpa [List.length_cons, Nat.factorial_one, pow_one] using hvel
        _ = 2 ^ 21 * a β I.Λ (m - 1) := by
              field_simp [ne_of_gt he]
              norm_num
    rw [← hcoord]
    exact hscale
  have hcol (d : Fin 2) :
      ‖L (basisVec d)‖ ≤ 2 ^ 21 * a β I.Λ (m - 1) := by
    apply (pi_norm_le_iff_of_nonneg hP).2
    intro i
    rw [Real.norm_eq_abs]
    exact hpartial d i
  have hL : ‖L‖ ≤ 2 * (2 ^ 21 * a β I.Λ (m - 1)) := by
    apply L.opNorm_le_bound (by positivity)
    intro v
    have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
      ext i
      fin_cases i <;> simp [basisVec]
    have hmap : L v = v 0 • L (basisVec 0) + v 1 • L (basisVec 1) := by
      rw [hv]
      simp
    calc
      ‖L v‖ = ‖v 0 • L (basisVec 0) + v 1 • L (basisVec 1)‖ :=
        congrArg norm hmap
      _ ≤ |v 0| * ‖L (basisVec 0)‖ + |v 1| * ‖L (basisVec 1)‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_add_le (v 0 • L (basisVec 0)) (v 1 • L (basisVec 1))
      _ ≤ ‖v‖ * (2 ^ 21 * a β I.Λ (m - 1)) +
          ‖v‖ * (2 ^ 21 * a β I.Λ (m - 1)) := by
        apply add_le_add
        · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0)
            (hcol 0) (by positivity) (by positivity)
        · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1)
            (hcol 1) (by positivity) (by positivity)
      _ = (2 * (2 ^ 21 * a β I.Λ (m - 1))) * ‖v‖ := by ring
  change ‖L‖ ≤ 2 ^ 22 * a β I.Λ (m - 1)
  calc
    ‖L‖ ≤ 2 * (2 ^ 21 * a β I.Λ (m - 1)) := hL
    _ = 2 ^ 22 * a β I.Λ (m - 1) := by ring

/-- Concrete stream-function and diffusivity bounds trace instance. `hNumeric` is the explicit
    large-Λ
absorption threshold; the constants and cutoff radius stay visible in the
statement so the later-scale and profile-radius checks cannot be hidden. -/
theorem e44_initialTrace_of_A3_A5_data
    {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    {κ : ℝ}
    (c C : ℝ) (hc : 0 < c) (_hcC : c < C)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < N →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (N - j) ∧
      I.kappaAt κ j (N - j) ≤
        C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)))
    {g : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {R : ℝ}
    (hsol : IsClassicalSol
      (streamVel (fun t y => Φ (m - 1) t y))
      (Ingredients.kappaSeq I κ N (m - 1)) (fun _ _ => 0) g u)
    (hθ : IsThetaAnalytic R g) (hmean : ∫ x in AVenhance.unitCube, g x = 0)
    (hκ1 : Ingredients.kappaSeq I κ N (m - 1) ≤ 1)
    (hLater : epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2 - delta β) ≤ R)
    (A : ℝ) (hA1 : 1 ≤ A) (hA5scale : 2 ^ 24 ≤ c * A ^ 2)
    (Mcut : ℕ) (hMcut : 0 < Mcut)
    (hKup : 2 * Real.pi * Real.sqrt 2 * (Mcut : ℝ) ≤
      A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
    (hKlower : A / (2 * epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2)) ≤ 2 * Real.pi * Real.sqrt 2 * (Mcut : ℝ))
    (hKupperTail : A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤
      2 * Real.pi * Real.sqrt 2 * (Mcut + 1 : ℝ))
    (hTailScale : 1 ≤ (R / 2) * (Mcut + 1 : ℝ))
    (hNumeric :
      (Real.sqrt c)⁻¹ *
        Real.rpow (epsilon β I.Λ (m - 1)) (-(β + gamma β) / 2) *
        Real.exp (-e44TailExponent * A *
          Real.rpow (epsilon β I.Λ (m - 1)) (-delta β)) ≤ 1) :
    (1 ≤ e44TraceCombinationConstant A (Real.sqrt 3) e44TailConstant) ∧
      ∀ w : List (Fin 2), 1 ≤ w.length →
        Real.sqrt (∫ x in AVenhance.unitCube,
          (Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
        (Real.sqrt (Ingredients.kappaSeq I κ N (m - 1)) *
          Real.sqrt (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) *
          ((w.length.factorial : ℝ) /
            ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) /
              e44TraceCombinationConstant A (Real.sqrt 3) e44TailConstant ^ 2) ^
                w.length) := by
  let e := epsilon β I.Λ (m - 1)
  let p := 1 + gamma β / 2
  let q := β + gamma β
  let ν := Ingredients.kappaSeq I κ N (m - 1)
  let r := e ^ p
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : e ≤ 1 := Infra.Construction.epsilon_le_one
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hpδ : 0 < p - delta β := by
    have hp := Infra.Ingredients.delta_le_one_sixteenth I.one_lt_beta I.beta_lt
    have hg := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
    dsimp [p]
    linarith
  have hR : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos he _) hLater
  have hscales := TraceInstanceFrozen.e44_later_scale_comparisons he he1 hδ (by simpa [e, p] using
      hLater)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by simpa [r, e, p] using hscales.1
  have hratio : Real.rpow e (-delta β) ≤ R / r := by
    simpa [r, e, p] using hscales.2
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hqpos : 0 < q := by
    dsimp [q]
    have hg := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
    have hβ : 1 < β := I.one_lt_beta
    linarith
  have hνlowA5 : c * (a β I.Λ (m - 1) * e ^ (2 + gamma β)) ≤ ν := by
    have hidx : m - 1 < N := by omega
    have hraw := hA5 (m - 1) (by omega) hidx
    simpa [ν, e, Ingredients.kappaSeq] using hraw.1
  have hνlow : c * e ^ q ≤ ν := by
    have hid := Infra.Section4.theta_kappa_power_identity
      (β := β) (Λ := I.Λ) (m := m - 1) he
    simpa [q, e, hid] using hνlowA5
  have hνpos : 0 < ν := lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos he _)) hνlow
  have hνinv := TraceInstanceFrozen.e44_inverse_sqrt_kappa_of_power_lower he hc hνlow
  have hnumeric := hNumeric
  have hAbsorb : (Real.sqrt ν)⁻¹ *
      Real.exp (-e44TailExponent * R * (A / r)) ≤ 1 := by
    have hνinv' : (Real.sqrt ν)⁻¹ ≤
        (Real.sqrt c)⁻¹ * epsilon β I.Λ (m - 1) ^
          (-((β + gamma β) / 2)) := by
      have hexp : -q / 2 = -((β + gamma β) / 2) := by dsimp [q]; ring
      simpa [e, hexp] using hνinv
    have hratio' : epsilon β I.Λ (m - 1) ^ (-delta β) ≤
        R / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := by
      simpa [e, p] using hratio
    have hnumeric' : (Real.sqrt c)⁻¹ *
        Real.rpow (epsilon β I.Λ (m - 1)) (-(β + gamma β) / 2) *
        Real.exp (-e44TailExponent * A *
          Real.rpow (epsilon β I.Λ (m - 1)) (-delta β)) ≤ 1 := by
      convert hnumeric using 1
    have hnumeric'' := hnumeric'
    rw [show (-(β + gamma β)) / 2 = -((β + gamma β) / 2) by ring] at hnumeric''
    have habs := e44_parameter_exponential_absorption
      (ε := epsilon β I.Λ (m - 1)) (p := (β + gamma β) / 2)
      (δ := delta β) (c := e44TailExponent) (A := A) (Cν := (Real.sqrt c)⁻¹)
      (ν := ν) (r := r) (R := R)
      he e44_tail_exponent_pos hApos
      (inv_nonneg.mpr (Real.sqrt_nonneg c)) hr hνinv' hratio'
      hnumeric''
    simpa [r, e, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using habs
  let B := 2 ^ 22 * a β I.Λ (m - 1)
  have ha : 0 < a β I.Λ (m - 1) :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hB : 0 ≤ B := by positivity
  have hDb : ∀ t x, ‖jointSpatialFDeriv
      (streamVel (fun s y => Φ (m - 1) s y)) t x‖ ≤ B := by
    simpa [B] using e44_streamVelocity_spatialDerivative_bound_of_A3 I hΦ hm hA3
  let K := 2 * Real.pi * Real.sqrt 2 * (Mcut : ℝ)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKlowSquare : (A / (2 * r)) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by simpa [K, r, e, p] using hKlower) 2
  have hpowR : r ^ 2 = e ^ (2 + gamma β) := by
    dsimp [r, p]
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1
    ring
  have hpowRatio : e ^ q / r ^ 2 = e ^ (β - 2) := by
    rw [hpowR, ← Real.rpow_sub he]
    congr 1
    dsimp [q]
    ring
  have hcoefficient : 2 ^ 22 ≤ c * A ^ 2 / 4 := by
    nlinarith [hA5scale]
  have hνK : 2 ^ 22 * e ^ (β - 2) ≤ ν * K ^ 2 := by
    have hbase : c * e ^ q * (A / (2 * r)) ^ 2 ≤ ν * K ^ 2 :=
      mul_le_mul hνlow hKlowSquare (by positivity) (by positivity)
    have hfactor : 2 ^ 22 * e ^ (β - 2) ≤
        c * e ^ q * (A / (2 * r)) ^ 2 := by
      rw [show c * e ^ q * (A / (2 * r)) ^ 2 =
        (c * A ^ 2 / 4) * (e ^ q / r ^ 2) by
          field_simp [ne_of_gt hr]
          ring, hpowRatio]
      exact mul_le_mul_of_nonneg_right hcoefficient
        (Real.rpow_nonneg he.le _)
    exact hfactor.trans hbase
  have hpowGeOne : 1 ≤ e ^ (β - 2) := by
    have hβpow : β - 2 ≤ 0 := by linarith [I.beta_lt]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 hβpow
  have hBbound : B ≤ ν * K ^ 2 := by
    dsimp [B]
    rw [a]
    exact hνK
  have hmax : max 1 B ≤ ν * K ^ 2 := by
    apply max_le
    · calc
        (1 : ℝ) ≤ 2 ^ 22 * e ^ (β - 2) := by nlinarith [hpowGeOne]
        _ ≤ ν * K ^ 2 := hνK
    · exact hBbound
  have hφ : IsAdmissibleStream (fun s y => Φ (m - 1) s y) :=
    Infra.Section4.theta_prev_stream_admissible I Φ hΦ hm
  have hb := streamVel_smoothPeriodic (fun s y => Φ (m - 1) s y) hφ
  obtain ⟨X, hX, _⟩ := Infra.Flow.existsUnique_smoothPeriodic_flow hb
  have hTailScale' : 1 ≤ (R / 2) * (Mcut + 1 : ℝ) := hTailScale
  have htrace := e44_initialTrace_of_classical_cutoff
    (κ := ν) (A := A) (r := r) (R := R) (B := B) (Mcut)
    (g := g) (u := u) (X := X)
    (fun s y => Φ (m - 1) s y) hφ hX hsol hθ hmean hνpos hκ1
    hr hR hA1 hrR hB hDb hMcut hKup hKupperTail hmax hTailScale' hAbsorb
  constructor
  · dsimp [e44TraceCombinationConstant]
    exact le_max_left _ _
  · intro w hw
    simpa [r, ν, e] using htrace w hw

/-- Identify the classical slice-energy integral with the space-time
gradient norm used by the initial-trace premise. -/
theorem e44_classical_energy_eq_spaceTimeGradNormSq
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u) :
    (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) =
      spaceTimeGradNormSq (fun t => spaceGrad (u t)) := by
  have hVcont : ContinuousOn (fun p : ℝ × Vec 2 =>
      spaceGrad (u p.1) p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (Infra.Section5.LeftToShow.spaceGrad_continuousOn hsol.1).mono (by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact ⟨ht.1, by trivial⟩)
  have hslice : classicalCellGradientEnergy u = fun t =>
      ∫ x in unitCube, vecNormSq (spaceGrad (u t) x) := by
    funext t
    dsimp [classicalCellGradientEnergy]
    exact Infra.Torus.integral_unitCell_eq_unitCube _
  rw [hslice]
  exact (Infra.Section5.LeftToShow.spaceTimeGradNormSq_eq_intervalIntegral
    hVcont).symm

/-- The same trace construction with the diffusivity bounds constants supplied
explicitly. This is the family-level form: callers may choose `c,C` before
the `Ingredients` instance and provide the corresponding stream-function and diffusivity bounds. -/
theorem e44_initialTrace_of_explicit_A3_A5
    {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    {κ : ℝ} (c C : ℝ) (hc : 0 < c) (hcC : c < C)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < N →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
        I.kappaAt κ j (N - j) ∧
      I.kappaAt κ j (N - j) ≤
        C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)))
    {g : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {R : ℝ}
    (hsol : IsClassicalSol
      (streamVel (fun t y => Φ (m - 1) t y))
      (Ingredients.kappaSeq I κ N (m - 1)) (fun _ _ => 0) g u)
    (hθ : IsThetaAnalytic R g) (hmean : ∫ x in AVenhance.unitCube, g x = 0)
    (hκ1 : Ingredients.kappaSeq I κ N (m - 1) ≤ 1)
    (hLater : epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2 - delta β) ≤ R) :
    (1 ≤ e44FrozenTraceConstant β c) ∧
      ∀ w : List (Fin 2), 1 ≤ w.length →
        Real.sqrt (∫ x in AVenhance.unitCube,
          (Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
        (Real.sqrt (Ingredients.kappaSeq I κ N (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (u t)))) *
          ((w.length.factorial : ℝ) /
            ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) /
              e44FrozenTraceConstant β c ^ 2) ^ w.length) := by
  let e := epsilon β I.Λ (m - 1)
  let p := 1 + gamma β / 2
  let r := e ^ p
  let A := e44TraceCutoffAmplitude β c
  have he : 0 < e := Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : e ≤ 1 := Infra.Construction.epsilon_le_one
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hp : 0 < p := by
    dsimp [p]
    have hg := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
    linarith
  have hLater' : e ^ (p - delta β) ≤ R := by
    simpa [e, p] using hLater
  have hscales := TraceInstanceFrozen.e44_later_scale_comparisons he he1 hδ hLater'
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by simpa [r, e, p] using hscales.1
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hr1 : r ≤ 1 := by
    dsimp [r, e, p]
    exact Real.rpow_le_one he.le he1 hp.le
  have hnumeric := e44_trace_numeric_absorption
    I.one_lt_beta I.beta_lt hc he he1
  rcases hnumeric with ⟨hA5scale, hAlarge, hAbsorb⟩
  have hA1 : 1 ≤ A :=
    le_trans (by norm_num : (1 : ℝ) ≤ 32) (by simpa [A] using hAlarge)
  have hA5scale' : 2 ^ 24 ≤ c * A ^ 2 := by simpa [A] using hA5scale
  obtain ⟨Mcut, hMcut, hKup, hKlower, hKupperTail, hTailScale⟩ :=
    TraceInstanceFrozen.e44_natural_cutoff_data hr hrR hr1 (by simpa [A] using hAlarge)
  have hNumeric :
      (Real.sqrt c)⁻¹ * Real.rpow (epsilon β I.Λ (m - 1))
        (-(β + gamma β) / 2) *
      Real.exp (-e44TailExponent * A *
        Real.rpow (epsilon β I.Λ (m - 1)) (-delta β)) ≤ 1 := by
    have hAbsorb' := hAbsorb
    rw [show -((β + gamma β) / 2) =
      (-gamma β + -β) / 2 by ring] at hAbsorb'
    simpa [A, e] using hAbsorb'
  have hEnergy := e44_classical_energy_eq_spaceTimeGradNormSq hsol
  have htrace := e44_initialTrace_of_A3_A5_data I hΦ hm hmN c C hc hcC hA3 hA5
    hsol hθ hmean hκ1 hLater A hA1 hA5scale' Mcut hMcut
    (by simpa [r, e, p] using hKup)
    (by simpa [r, e, p] using hKlower)
    (by simpa [e, p, r] using hKupperTail)
    hTailScale hNumeric
  constructor
  · simp [e44FrozenTraceConstant, e44TraceCombinationConstant]
  · intro w hw
    rw [← hEnergy]
    simpa [r, e, p, e44FrozenTraceConstant, e44TraceCombinationConstant] using
      htrace.2 w hw

end AVenhance.Infra.Section5.RelativeError

end
