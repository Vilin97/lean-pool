/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Probability.Moments.Basic
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigma

/-! # Preliminaries -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The Hölder-conjugate exponent `σ / (σ - 1)` used in the large-`λ`
exponential regime when `1 < σ`. -/
noncomputable def gammaExpConjExponent (σ : ℝ) : ℝ :=
  σ / (σ - 1)

lemma gammaExpConjExponent_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < gammaExpConjExponent σ := by
  have hσ_pos : 0 < σ := by linarith
  have hσ_sub_pos : 0 < σ - 1 := by linarith
  dsimp [gammaExpConjExponent]
  exact div_pos hσ_pos hσ_sub_pos

lemma gammaExpConjExponent_holderConjugate {σ : ℝ} (hσ : 1 < σ) :
    σ.HolderConjugate (gammaExpConjExponent σ) := by
  simpa [gammaExpConjExponent] using
    (Real.holderConjugate_iff_eq_conjExponent hσ).2 rfl

lemma inv_gammaExpConjExponent {σ : ℝ} (hσ : 1 < σ) :
    (gammaExpConjExponent σ)⁻¹ = (σ - 1) / σ := by
  have hσ_ne : σ ≠ 0 := by linarith
  have hσ_sub_ne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
  dsimp [gammaExpConjExponent]
  field_simp [hσ_ne, hσ_sub_ne]

/-- Young's inequality in the Chapter 4 large-`λ` shape. -/
lemma gammaExp_young {σ l t : ℝ} (hσ : 1 < σ) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    l * t ≤ t ^ σ / σ + ((σ - 1) / σ) * l ^ gammaExpConjExponent σ := by
  have hyoung :=
    Real.young_inequality_of_nonneg ht hl
      (gammaExpConjExponent_holderConjugate hσ)
  have hq :
      l ^ gammaExpConjExponent σ / gammaExpConjExponent σ =
        ((σ - 1) / σ) * l ^ gammaExpConjExponent σ := by
    rw [div_eq_mul_inv, inv_gammaExpConjExponent hσ]
    ring
  calc
    l * t = t * l := by ring
    _ ≤ t ^ σ / σ + l ^ gammaExpConjExponent σ / gammaExpConjExponent σ := hyoung
    _ = t ^ σ / σ + ((σ - 1) / σ) * l ^ gammaExpConjExponent σ := by
          rw [hq]

/-- Scaled Young inequality matching the tail parameterization `x = B t`. -/
lemma gammaExp_young_scale {σ B l t : ℝ}
    (hσ : 1 < σ) (hB : 0 ≤ B) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    l * (B * t) ≤ t ^ σ / σ + ((σ - 1) / σ) * (B * l) ^ gammaExpConjExponent σ := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    gammaExp_young (σ := σ) (l := B * l) (t := t) hσ (mul_nonneg hB hl) ht

/-- Exponent comparison extracted from `gammaExp_young`. This is the basic
kernel estimate behind the large-`λ` regime. -/
lemma gammaExp_largeLambda_exponent_le {σ l t : ℝ}
    (hσ : 1 < σ) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    l * t - t ^ σ ≤
      ((σ - 1) / σ) * l ^ gammaExpConjExponent σ -
        ((σ - 1) / σ) * t ^ σ := by
  have hyoung := gammaExp_young (σ := σ) (l := l) (t := t) hσ hl ht
  have hσ_ne : σ ≠ 0 := by linarith
  calc
    l * t - t ^ σ ≤ (t ^ σ / σ + ((σ - 1) / σ) * l ^ gammaExpConjExponent σ) - t ^ σ := by
      exact sub_le_sub_right hyoung _
    _ = ((σ - 1) / σ) * l ^ gammaExpConjExponent σ -
          ((σ - 1) / σ) * t ^ σ := by
          field_simp [hσ_ne]
          ring

/-- Exponential form of the Chapter 4 large-`λ` kernel comparison. -/
lemma exp_gammaExp_largeLambda_exponent_le {σ l t : ℝ}
    (hσ : 1 < σ) (hl : 0 ≤ l) (ht : 0 ≤ t) :
    Real.exp (l * t - t ^ σ) ≤
      Real.exp (((σ - 1) / σ) * l ^ gammaExpConjExponent σ) *
        Real.exp (-((σ - 1) / σ) * t ^ σ) := by
  have hle := Real.exp_le_exp.2
    (gammaExp_largeLambda_exponent_le (σ := σ) (l := l) (t := t) hσ hl ht)
  calc
    Real.exp (l * t - t ^ σ)
      ≤ Real.exp (((σ - 1) / σ) * l ^ gammaExpConjExponent σ -
          ((σ - 1) / σ) * t ^ σ) := hle
    _ = Real.exp (((σ - 1) / σ) * l ^ gammaExpConjExponent σ) *
          Real.exp (-((σ - 1) / σ) * t ^ σ) := by
            rw [sub_eq_add_neg, Real.exp_add]
            congr 2
            ring

lemma gammaExpSlope_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < (σ - 1) / σ := by
  have hσ_pos : 0 < σ := by linarith
  have hσ_sub_pos : 0 < σ - 1 := by linarith
  exact div_pos hσ_sub_pos hσ_pos

/-- The large-`λ` shell kernel is summable after comparison with an
exponentially decaying sequence. -/
lemma summable_nat_sq_mul_exp_gammaExpKernel {σ α : ℝ}
    (hσ : 1 < σ) (hα : 0 ≤ α) :
    Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * Real.exp (α * n - (n : ℝ) ^ σ)) := by
  let c : ℝ := (σ - 1) / σ
  have hc_pos : 0 < c := gammaExpSlope_pos hσ
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * Real.exp (-c * n)) := by
    simpa [c] using Real.summable_pow_mul_exp_neg_nat_mul 2 hc_pos
  refine Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (by positivity) (by positivity))
      (fun n => ?_)
      (hbase.mul_left (Real.exp (c * α ^ gammaExpConjExponent σ)))
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hkernel :=
    exp_gammaExp_largeLambda_exponent_le (σ := σ) (l := α) (t := n) hσ hα hn_nonneg
  have hnpow_ge : (n : ℝ) ≤ (n : ℝ) ^ σ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using (Real.rpow_nonneg (show 0 ≤ (0 : ℝ) by positivity) σ)
    · have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact Real.self_le_rpow_of_one_le hn_one hσ.le
  have hExpMono :
      Real.exp (-c * (n : ℝ) ^ σ) ≤ Real.exp (-c * n) := by
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonpos_left hnpow_ge (by linarith [hc_pos])
  have hkernel' :
      Real.exp (α * n - (n : ℝ) ^ σ) ≤
        Real.exp (c * α ^ gammaExpConjExponent σ) * Real.exp (-c * n) := by
    calc
      Real.exp (α * n - (n : ℝ) ^ σ)
        ≤ Real.exp (c * α ^ gammaExpConjExponent σ) * Real.exp (-c * (n : ℝ) ^ σ) := hkernel
      _ ≤ Real.exp (c * α ^ gammaExpConjExponent σ) * Real.exp (-c * n) := by
            exact mul_le_mul_of_nonneg_left hExpMono (by positivity)
  have hmul :=
    mul_le_mul_of_nonneg_left hkernel' (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℕ))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The scaling constant produced by the `δ`-version of Young's inequality in
the exponential regime `σ > 1`. -/
noncomputable def gammaExpYoungScaleConst (σ δ : ℝ) : ℝ :=
  ((σ - 1) / σ) * ((((σ * δ) ^ σ⁻¹)⁻¹) ^ gammaExpConjExponent σ)

lemma gammaExpYoungScaleConst_pos {σ δ : ℝ} (hσ : 1 < σ) (hδ : 0 < δ) :
    0 < gammaExpYoungScaleConst σ δ := by
  dsimp [gammaExpYoungScaleConst]
  have hleft : 0 < (σ - 1) / σ := gammaExpSlope_pos hσ
  have hσδ_pos : 0 < σ * δ := by positivity
  have hbase_pos : 0 < (((σ * δ) ^ σ⁻¹)⁻¹) := by
    exact inv_pos.mpr (Real.rpow_pos_of_pos hσδ_pos _)
  exact mul_pos hleft (Real.rpow_pos_of_pos hbase_pos _)

/-- `δ`-scaled Young inequality in the Chapter 4 exponential regime. -/
lemma gammaExp_young_scale_delta {σ B l t δ : ℝ}
    (hσ : 1 < σ) (hB : 0 ≤ B) (hl : 0 ≤ l) (ht : 0 ≤ t) (hδ : 0 < δ) :
    l * (B * t) ≤
      δ * t ^ σ + gammaExpYoungScaleConst σ δ * (B * l) ^ gammaExpConjExponent σ := by
  let c : ℝ := (((σ * δ) ^ σ⁻¹)⁻¹)
  have hσ_pos : 0 < σ := by linarith
  have hσ_ne : σ ≠ 0 := by linarith
  have hσδ_pos : 0 < σ * δ := by positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.rpow_pos_of_pos hσδ_pos _)
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hc_inv : c⁻¹ = (σ * δ) ^ σ⁻¹ := by
    dsimp [c]
    simp
  have hyoung :=
    gammaExp_young (σ := σ) (l := c * (B * l)) (t := c⁻¹ * t)
      hσ (mul_nonneg hc_nonneg (mul_nonneg hB hl))
      (mul_nonneg (inv_nonneg.mpr hc_nonneg) ht)
  have hfirst : (c⁻¹ * t) ^ σ / σ = δ * t ^ σ := by
    calc
      (c⁻¹ * t) ^ σ / σ = (((σ * δ) ^ σ⁻¹) * t) ^ σ / σ := by
        rw [hc_inv]
      _ = ((((σ * δ) ^ σ⁻¹) ^ σ) * t ^ σ) / σ := by
        rw [Real.mul_rpow (by positivity) ht]
      _ = ((σ * δ) * t ^ σ) / σ := by
        rw [Real.rpow_inv_rpow (show 0 ≤ σ * δ by positivity) hσ_ne]
      _ = δ * t ^ σ := by
        field_simp [hσ_ne]
  have hsecond :
      ((σ - 1) / σ) * (c * (B * l)) ^ gammaExpConjExponent σ =
        gammaExpYoungScaleConst σ δ * (B * l) ^ gammaExpConjExponent σ := by
    have hBl_nonneg : 0 ≤ B * l := mul_nonneg hB hl
    calc
      ((σ - 1) / σ) * (c * (B * l)) ^ gammaExpConjExponent σ
        = ((σ - 1) / σ) *
            (c ^ gammaExpConjExponent σ * (B * l) ^ gammaExpConjExponent σ) := by
              rw [Real.mul_rpow hc_nonneg hBl_nonneg]
      _ = gammaExpYoungScaleConst σ δ * (B * l) ^ gammaExpConjExponent σ := by
        dsimp [gammaExpYoungScaleConst, c]
        ring
  have hleft : (c * (B * l)) * (c⁻¹ * t) = l * (B * t) := by
    calc
      (c * (B * l)) * (c⁻¹ * t) = (c * c⁻¹) * ((B * l) * t) := by ring
      _ = (B * l) * t := by rw [mul_inv_cancel₀ hc_pos.ne', one_mul]
      _ = l * (B * t) := by ring
  calc
    l * (B * t) = (c * (B * l)) * (c⁻¹ * t) := hleft.symm
    _ ≤ (c⁻¹ * t) ^ σ / σ + ((σ - 1) / σ) * (c * (B * l)) ^ gammaExpConjExponent σ := hyoung
    _ = δ * t ^ σ + gammaExpYoungScaleConst σ δ * (B * l) ^ gammaExpConjExponent σ := by
      rw [hfirst, hsecond]

/-- Fixed coefficient appearing in the one-variable large-`λ` mgf estimate for
the Chapter 4 exponential regime `σ > 1`. -/
noncomputable def gammaExpLargeLambdaConst (σ : ℝ) : ℝ :=
  gammaExpYoungScaleConst σ ((4 * Real.exp 1 * gammaMomentConst 1)⁻¹)

/-- The Taylor tail used in the small-`λ` mgf expansion. -/
def gammaExpTaylorTail (l : ℝ) (X : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (l * X ω) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)

/-- The full exponential-series term attached to `l * X`. -/
def gammaExpSeriesTerm (l : ℝ) (X : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (l * X ω) ^ n / (Nat.factorial n : ℝ)

omit [MeasurableSpace Ω] in
lemma gammaExpTaylorTail_eq_gammaExpSeriesTerm_add_two
    (l : ℝ) (X : Ω → ℝ) (n : ℕ) :
    gammaExpTaylorTail l X n = gammaExpSeriesTerm l X (n + 2) := by
  rfl

lemma nat_div_exp_pow_le_factorial (n : ℕ) :
    (((n : ℝ) / Real.exp 1) ^ n) ≤ (Nat.factorial n : ℝ) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hstirling := Stirling.le_factorial_stirling n
  have hsqrt_one : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    have hinner : 1 ≤ 2 * Real.pi * n := by
      have hpi : 1 ≤ Real.pi := by
        linarith [Real.pi_gt_three]
      have htwo_pi : 1 ≤ 2 * Real.pi := by
        nlinarith
      have hn_real : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn)
      nlinarith
    exact (Real.one_le_sqrt).2 hinner
  have hnonneg : 0 ≤ (((n : ℝ) / Real.exp 1) ^ n) := by positivity
  calc
    (((n : ℝ) / Real.exp 1) ^ n)
      ≤ Real.sqrt (2 * Real.pi * n) * (((n : ℝ) / Real.exp 1) ^ n) := by
          nlinarith
    _ ≤ (Nat.factorial n : ℝ) := hstirling

lemma nat_pow_div_factorial_le_exp_nat (n : ℕ) :
    ((n : ℝ) ^ n) / (Nat.factorial n : ℝ) ≤ Real.exp n := by
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by positivity
  have hmain := nat_div_exp_pow_le_factorial n
  have hexp_nat : (Real.exp 1) ^ n = Real.exp n := by
    calc
      (Real.exp 1) ^ n = Real.exp ((n : ℝ) * 1) := by
        rw [(Real.exp_nat_mul 1 n).symm]
      _ = Real.exp n := by simp
  have hmain' :
      ((n : ℝ) / Real.exp 1) ^ n * (Real.exp 1) ^ n ≤
        (Nat.factorial n : ℝ) * (Real.exp 1) ^ n := by
    exact mul_le_mul_of_nonneg_right hmain (by positivity)
  have hleft :
      (((n : ℝ) / Real.exp 1) ^ n) * (Real.exp 1) ^ n = (n : ℝ) ^ n := by
    rw [div_pow]
    field_simp [Real.exp_pos 1]
  refine (div_le_iff₀ hfac_pos).2 ?_
  calc
    (n : ℝ) ^ n = (((n : ℝ) / Real.exp 1) ^ n) * (Real.exp 1) ^ n := hleft.symm
    _ ≤ (Nat.factorial n : ℝ) * (Real.exp 1) ^ n := hmain'
    _ = (Nat.factorial n : ℝ) * Real.exp n := by
          rw [hexp_nat]
    _ = Real.exp n * (Nat.factorial n : ℝ) := by ring

lemma gammaMomentGrowth_natCast_bound
    {σ M : ℝ} {X : Ω → ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (fun ω => |X ω| ^ (n : ℕ)) μ ∧
      ∫ ω, |X ω| ^ (n : ℕ) ∂μ ≤ (M * (n : ℝ) ^ σ⁻¹) ^ (n : ℕ) := by
  have h := hXmom (by exact_mod_cast hn : 1 ≤ (n : ℝ))
  simpa [Real.rpow_natCast] using h

lemma gammaMomentGrowth_natCast_term_le
    {σ M l : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hσ : 1 ≤ σ) (hM_nonneg : 0 ≤ M) (hl_nonneg : 0 ≤ l) :
    ((M * l * (n : ℝ) ^ σ⁻¹) ^ n) / (Nat.factorial n : ℝ) ≤
      (Real.exp 1 * M * l) ^ n := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hexp_le_one : σ⁻¹ ≤ (1 : ℝ) := by
    rw [inv_eq_one_div]
    simpa using one_div_le_one_div_of_le zero_lt_one hσ
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow_le :
      (n : ℝ) ^ σ⁻¹ ≤ (n : ℝ) := by
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn_real hexp_le_one
  have hmul_le :
      M * l * (n : ℝ) ^ σ⁻¹ ≤ M * l * (n : ℝ) := by
    gcongr
  have hmul_pow :
      (M * l * (n : ℝ)) ^ n = (M * l) ^ n * (n : ℝ) ^ n := by
    rw [show M * l * (n : ℝ) = (M * l) * (n : ℝ) by ring]
    rw [mul_pow]
  have hexp_nat : Real.exp n = (Real.exp 1) ^ n := by
    calc
      Real.exp n = Real.exp ((n : ℝ) * 1) := by simp
      _ = (Real.exp 1) ^ n := by rw [Real.exp_nat_mul 1 n]
  calc
    ((M * l * (n : ℝ) ^ σ⁻¹) ^ n) / (Nat.factorial n : ℝ)
      ≤ ((M * l * (n : ℝ)) ^ n) / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hmul_le n)
            (by positivity)
    _ = ((M * l) ^ n * (n : ℝ) ^ n) / (Nat.factorial n : ℝ) := by
          rw [hmul_pow]
    _ = (M * l) ^ n * (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    _ ≤ (M * l) ^ n * Real.exp n := by
          gcongr
          exact nat_pow_div_factorial_le_exp_nat n
    _ = (Real.exp 1 * M * l) ^ n := by
          rw [hexp_nat]
          calc
            (M * l) ^ n * (Real.exp 1) ^ n = ((M * l) * Real.exp 1) ^ n := by
              rw [← mul_pow]
            _ = (Real.exp 1 * M * l) ^ n := by
              congr 1
              ring

/-- The normed Taylor tail is controlled by the geometric scale
`(e M λ)^(n+2)` once `Γ_σ` moment growth is available with `σ ≥ 1`. -/
theorem integral_norm_gammaExpTaylorTail_le_geometric
    {X : Ω → ℝ} {σ M l : ℝ} (n : ℕ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    ∫ ω, ‖gammaExpTaylorTail l X n ω‖ ∂μ ≤
      (Real.exp 1 * M * l) ^ (n + 2) := by
  rcases gammaMomentGrowth_natCast_bound
      (μ := μ) (X := X) (σ := σ) (M := M) (n := n + 2) (by omega) hXmom with
    ⟨h_int, h_bound⟩
  have hnorm_fun :
      (fun ω => ‖gammaExpTaylorTail l X n ω‖) =
        fun ω => ((l ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ)) * |X ω| ^ (n + 2) := by
    funext ω
    have hfact_pos : 0 < (Nat.factorial (n + 2) : ℝ) := by positivity
    calc
      ‖gammaExpTaylorTail l X n ω‖
        = |(l * X ω) ^ (n + 2)| / (Nat.factorial (n + 2) : ℝ) := by
            simp [gammaExpTaylorTail, Real.norm_eq_abs]
      _ = (l ^ (n + 2) * |X ω| ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ) := by
            rw [abs_pow, abs_mul, abs_of_nonneg hl, mul_pow]
      _ = ((l ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ)) * |X ω| ^ (n + 2) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
  calc
    ∫ ω, ‖gammaExpTaylorTail l X n ω‖ ∂μ
      = ((l ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ)) *
          ∫ ω, |X ω| ^ (n + 2) ∂μ := by
            rw [hnorm_fun, integral_const_mul]
    _ ≤ ((l ^ (n + 2)) / (Nat.factorial (n + 2) : ℝ)) *
          (M * ((n + 2 : ℕ) : ℝ) ^ σ⁻¹) ^ (n + 2) := by
            gcongr
    _ = (((M * l * ((n + 2 : ℕ) : ℝ) ^ σ⁻¹) ^ (n + 2)) /
          (Nat.factorial (n + 2) : ℝ)) := by
            field_simp [div_eq_mul_inv]
            ring
    _ ≤ (Real.exp 1 * M * l) ^ (n + 2) := by
            exact gammaMomentGrowth_natCast_term_le
              (n := n + 2) (by omega) hσ hM hl

/-- Under the Chapter 4 small-`λ` hypothesis `e M λ ≤ 1/2`, the Taylor tails
form a summable family in `L¹`. This is the summability input needed to
interchange the mgf integral with the exponential power series. -/
theorem summable_integral_norm_gammaExpTaylorTail
    {X : Ω → ℝ} {σ M l : ℝ}
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Summable (fun n : ℕ => ∫ ω, ‖gammaExpTaylorTail l X n ω‖ ∂μ) := by
  let r : ℝ := Real.exp 1 * M * l
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_le_half : r ≤ 1 / 2 := by
    by_cases hM0 : M = 0
    · have hl_zero : l = 0 := by
        have hl_nonpos : l ≤ 0 := by simpa [hM0] using hl_small
        linarith
      simp [r, hM0, hl_zero]
    · let C : ℝ := 2 * Real.exp 1 * M
      have htmp := mul_le_mul_of_nonneg_left hl_small (show 0 ≤ C by
        dsimp [C]
        positivity)
      have hC_ne : C ≠ 0 := by
        dsimp [C]
        positivity
      have hbound : C * l ≤ 1 := by
        calc
          C * l ≤ C * C⁻¹ := by simpa [C] using htmp
          _ = 1 := by field_simp [hC_ne]
      dsimp [r, C] at hbound ⊢
      nlinarith
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  have hgeom : Summable (fun n : ℕ => r ^ (n + 2)) := by
    have hs : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr_nonneg hr_lt_one
    simpa [pow_add, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hs.mul_left (r ^ (2 : ℕ))
  refine Summable.of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_)
    hgeom
  exact integral_norm_gammaExpTaylorTail_le_geometric
    (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hσ hM hl hXmom

lemma integrable_gammaExpSeriesTerm_of_one_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hXm : AEMeasurable X μ)
    (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (gammaExpSeriesTerm l X n) μ := by
  rcases gammaMomentGrowth_natCast_bound
      (μ := μ) (X := X) (σ := σ) (M := M) (n := n) hn hXmom with
    ⟨hpow_int, _⟩
  have hterm_meas : AEStronglyMeasurable (gammaExpSeriesTerm l X n) μ := by
    simpa [gammaExpSeriesTerm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using!
      (((hXm.aestronglyMeasurable.const_mul l).pow n).const_mul
        ((Nat.factorial n : ℝ)⁻¹))
  have hnorm_eq :
      (fun ω => ‖gammaExpSeriesTerm l X n ω‖) =
        fun ω => ((l ^ n) / (Nat.factorial n : ℝ)) * |X ω| ^ n := by
    funext ω
    calc
      ‖gammaExpSeriesTerm l X n ω‖
        = |(l * X ω) ^ n| / (Nat.factorial n : ℝ) := by
            simp [gammaExpSeriesTerm, Real.norm_eq_abs]
      _ = (l ^ n * |X ω| ^ n) / (Nat.factorial n : ℝ) := by
            rw [abs_pow, abs_mul, abs_of_nonneg hl, mul_pow]
      _ = ((l ^ n) / (Nat.factorial n : ℝ)) * |X ω| ^ n := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
  have hnorm_int :
      Integrable (fun ω => ‖gammaExpSeriesTerm l X n ω‖) μ := by
    rw [hnorm_eq]
    exact hpow_int.const_mul ((l ^ n) / (Nat.factorial n : ℝ))
  exact (integrable_norm_iff hterm_meas).1 hnorm_int

lemma integrable_gammaExpSeriesTerm
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ} (n : ℕ)
    (hXm : AEMeasurable X μ)
    (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (gammaExpSeriesTerm l X n) μ := by
  rcases n with _ | n
  · have hzero : gammaExpSeriesTerm l X 0 = fun _ : Ω => (1 : ℝ) := by
      funext ω
      simp [gammaExpSeriesTerm]
    rw [hzero]
    exact integrable_const (μ := μ) (c := (1 : ℝ))
  · exact integrable_gammaExpSeriesTerm_of_one_le
      (n := n.succ) (by exact Nat.succ_le_succ (Nat.zero_le _))
      hXm hl hXmom

theorem summable_integral_norm_gammaExpSeriesTerm
    {X : Ω → ℝ} {σ M l : ℝ}
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Summable (fun n : ℕ => ∫ ω, ‖gammaExpSeriesTerm l X n ω‖ ∂μ) := by
  have htail :
      Summable
        (fun n : ℕ => ∫ ω, ‖gammaExpSeriesTerm l X (n + 2) ω‖ ∂μ) := by
    simpa [gammaExpTaylorTail_eq_gammaExpSeriesTerm_add_two] using
      summable_integral_norm_gammaExpTaylorTail
        (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
        hσ hM hl hl_small hXmom
  exact (summable_nat_add_iff 2).1 htail

lemma ae_summable_norm_gammaExpSeriesTerm
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    ∀ᵐ ω ∂μ, Summable (fun n : ℕ => ‖gammaExpSeriesTerm l X n ω‖) := by
  let F : ℕ → Ω → ℝ := gammaExpSeriesTerm l X
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    exact integrable_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hXm hl hXmom
  have hF_sum :
      Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) := by
    simpa [F] using summable_integral_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hσ hM hl hl_small hXmom
  have hF_meas : ∀ n : ℕ, AEMeasurable (fun ω => ‖F n ω‖ₑ) μ := by
    intro n
    exact (hF_int n).1.enorm
  have hlin :
      (∑' n : ℕ, ∫⁻ ω : Ω, ‖F n ω‖ₑ ∂μ) ≠ (⊤ : ENNReal) := by
    have haux (n : ℕ) : ∫⁻ ω : Ω, ‖F n ω‖ₑ ∂μ = ‖∫ ω, ‖F n ω‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [MeasureTheory.lintegral_coe_eq_integral _ (hF_int n).norm]
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      rw [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun ω => by simp [abs_nonneg (F n ω)])]
      rfl
    rw [funext haux]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
  have hlin' : ∫⁻ ω : Ω, ∑' n : ℕ, ‖F n ω‖ₑ ∂μ ≠ (⊤ : ENNReal) := by
    rw [lintegral_tsum hF_meas]
    exact hlin
  refine (ae_lt_top' (AEMeasurable.tsum hF_meas) hlin').mono ?_
  intro ω hω
  have hωsum : Summable (fun n : ℕ => ((‖F n ω‖₊ : NNReal) : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa [enorm_eq_nnnorm] using hω.ne
  simpa [F] using hωsum

lemma integrable_tsum_norm_gammaExpSeriesTerm
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (fun ω => ∑' n : ℕ, ‖gammaExpSeriesTerm l X n ω‖) μ := by
  let F : ℕ → Ω → ℝ := gammaExpSeriesTerm l X
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    exact integrable_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hXm hl hXmom
  have hF_sum :
      Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) := by
    simpa [F] using summable_integral_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hσ hM hl hl_small hXmom
  have hsum_ae :
      ∀ᵐ ω ∂μ, Summable (fun n : ℕ => ‖F n ω‖) := by
    simpa [F] using ae_summable_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM hl hl_small hXmom
  let G : Ω → NNReal := fun ω => ∑' n : ℕ, ‖F n ω‖₊
  have hG_real :
      (fun ω => ∑' n : ℕ, ‖gammaExpSeriesTerm l X n ω‖) = fun ω => (G ω : ℝ) := by
        funext ω
        calc
          ∑' n : ℕ, ‖gammaExpSeriesTerm l X n ω‖
            = ∑' n : ℕ, ((‖F n ω‖₊ : NNReal) : ℝ) := by
                simp [F]
          _ = (G ω : ℝ) := by
                simp [G, NNReal.coe_tsum]
  refine ⟨?_, ?_⟩
  · rw [hG_real]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.coe_nnreal_real
    apply AEMeasurable.tsum
    intro n
    exact (hF_int n).1.nnnorm.aemeasurable
  · rw [hG_real]
    rw [MeasureTheory.hasFiniteIntegral_iff_ofNNReal]
    have hF_meas : ∀ n : ℕ, AEMeasurable (fun ω => ‖F n ω‖ₑ) μ := by
      intro n
      exact (hF_int n).1.enorm
    have hlin :
        ∫⁻ ω : Ω, ∑' n : ℕ, ‖F n ω‖ₑ ∂μ < ⊤ := by
      have htop :
          (∑' n : ℕ, ∫⁻ ω : Ω, ‖F n ω‖ₑ ∂μ) ≠ (⊤ : ENNReal) := by
        have haux (n : ℕ) : ∫⁻ ω : Ω, ‖F n ω‖ₑ ∂μ = ‖∫ ω, ‖F n ω‖ ∂μ‖ₑ := by
          dsimp [enorm]
          rw [MeasureTheory.lintegral_coe_eq_integral _ (hF_int n).norm]
          rw [ENNReal.coe_nnreal_eq]
          congr 1
          rw [coe_nnnorm, Real.norm_eq_abs,
            abs_of_nonneg (integral_nonneg fun ω => by simp [abs_nonneg (F n ω)])]
          rfl
        rw [funext haux]
        exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
      have htop' : ∫⁻ ω : Ω, ∑' n : ℕ, ‖F n ω‖ₑ ∂μ ≠ (⊤ : ENNReal) := by
        rw [lintegral_tsum hF_meas]
        exact htop
      exact lt_top_iff_ne_top.2 htop'
    have hG_enn_ae :
        (fun ω => (G ω : ENNReal)) =ᵐ[μ] fun ω => ∑' n : ℕ, ‖F n ω‖ₑ := by
      filter_upwards [hsum_ae] with ω hω
      have hωnn : Summable (fun n : ℕ => ‖F n ω‖₊) := by
        apply NNReal.summable_coe.1
        simpa [F, Real.norm_eq_abs] using hω
      calc
        (G ω : ENNReal) = (↑(∑' n : ℕ, ‖F n ω‖₊) : ENNReal) := by rfl
        _ = ∑' n : ℕ, ((‖F n ω‖₊ : NNReal) : ENNReal) := by
              simpa using (ENNReal.coe_tsum hωnn)
        _ = ∑' n : ℕ, ‖F n ω‖ₑ := by
              simp [enorm_eq_nnnorm]
    rw [lintegral_congr_ae hG_enn_ae]
    exact hlin

theorem integrable_exp_mul_of_gammaMomentGrowth_small
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  let F : ℕ → Ω → ℝ := gammaExpSeriesTerm l X
  have hbound_int :
      Integrable (fun ω => ∑' n : ℕ, ‖F n ω‖) μ := by
    simpa [F] using integrable_tsum_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM hl hl_small hXmom
  have hsum_ae :
      ∀ᵐ ω ∂μ, Summable (fun n : ℕ => ‖F n ω‖) := by
    simpa [F] using ae_summable_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM hl hl_small hXmom
  have hmeas_exp : AEStronglyMeasurable (fun ω => Real.exp (l * X ω)) μ := by
    exact (hXm.const_mul l).exp.aestronglyMeasurable
  refine Integrable.mono' hbound_int hmeas_exp ?_
  filter_upwards [hsum_ae] with ω hω
  have hsum_exp :
      HasSum (fun n : ℕ => F n ω) (Real.exp (l * X ω)) := by
    simpa [F, gammaExpSeriesTerm, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (l * X ω))
  calc
    ‖Real.exp (l * X ω)‖ = ‖∑' n : ℕ, F n ω‖ := by
          rw [hsum_exp.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖F n ω‖ := norm_tsum_le_tsum_norm hω

theorem mgf_pos_of_gammaMomentGrowth_small
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    0 < mgf X μ l := by
  exact mgf_pos
    (integrable_exp_mul_of_gammaMomentGrowth_small
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM hl hl_small hXmom)


end

end IndependentSums

end Homogenization
