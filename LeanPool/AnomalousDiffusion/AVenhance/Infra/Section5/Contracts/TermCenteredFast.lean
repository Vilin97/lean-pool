/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.SpaceErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterialRates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.SpaceAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise

/-! # Fast factors of the nondivergence parts of `twistie4`, `twistie5`

`sdFast4 = ∂_aΧ_{m,k,j}` and `sdFast5 = ζ̂ζ ψ_{m,k} σ_{aj} + κ_m ∂_aΧ_{m,k,j}`: continuous,
`1/ε_m`-periodic (fast periodic at frequency `ergodicFrequency β Λ m = ε_m⁻¹`), mean zero, and
bounded by `a_m ε_m² / κ_m` resp. `2 a_m ε_m²`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Section5.LeftToShow

variable {β : ℝ} (I : Ingredients β) {m : ℕ}

/-! ### `sdFast4` -/

theorem sdFast4_isFastPeriodic {m : ℕ} (hm : 1 ≤ m) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Infra.Ergodic.IsFastPeriodic (ergodicFrequency β I.Λ m) (sdFast4 I κm m k t p q) :=
  gradMatrix_chiMK_isFastPeriodic I hm κm k t p q

theorem sdFast4_continuous (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Continuous (sdFast4 I κm m k t p q) := by
  have h : ContDiff ℝ ∞ (fun z => I.chiMK κm m k t z q) :=
    (contDiff_apply ℝ ℝ q).comp (contDiff_chiMK I κm m k t)
  exact (contDiff_spaceGrad_coord h p).continuous

theorem sdFast4_cellAverage {m : ℕ} (hm : 1 ≤ m) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Infra.Ergodic.cellAverage (sdFast4 I κm m k t p q) = 0 := by
  rw [← spaceAvg_eq_cellAverage]
  exact spaceAvg_gradMatrix_chiMK I hm κm k t p q

theorem sdFast4_abs_le {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (k : ℤ) (t : ℝ)
    (p q : Fin 2) (y : Vec 2) :
    |sdFast4 I κm m k t p q y| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κm :=
  gradMatrix_chiMK_entry_abs_le I hm hκm k t y p q

/-! ### `ψ_{m,k}` -/

theorem psi_fast_shift (k : ℤ) (y : Vec 2) (n : Fin 2 → ℤ) :
    psi β I.Λ m k (y + fun i => (n i : ℝ) / (ergodicFrequency β I.Λ m : ℝ)) =
      psi β I.Λ m k y := by
  have hN : (ergodicFrequency β I.Λ m : ℝ) = (epsilon β I.Λ m)⁻¹ :=
    Infra.Section5.ergodicFrequency_cast β _ m
  have hε : epsilon β I.Λ m ≠ 0 := (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le).ne'
  have key : ∀ c : Fin 2, ((epsilon β I.Λ m)⁻¹ • (y + fun i => (n i : ℝ) /
      (ergodicFrequency β I.Λ m : ℝ))) c = ((epsilon β I.Λ m)⁻¹ • y) c + (n c : ℤ) := by
    intro c
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hN]
    field_simp
  simp only [psi, psi0]
  split_ifs
  · rw [key 0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show 2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * y 0 + (n 0 : ℤ)) =
      2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * y 0) + (n 0 : ℤ) * (2 * Real.pi) by ring,
      Real.sin_add_int_mul_two_pi]
  · rw [key 1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show 2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * y 1 + (n 1 : ℤ)) =
      2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * y 1) + (n 1 : ℤ) * (2 * Real.pi) by ring,
      Real.sin_add_int_mul_two_pi]
  · rfl

theorem psi_spaceAvg {m : ℕ} (hm : 1 ≤ m) (k : ℤ) :
    spaceAvg (psi β I.Λ m k) = 0 := by
  have hsin (r : Fin 2) : spaceAvg (fun x : Vec 2 =>
      Real.sin (2 * Real.pi * ((epsilon β I.Λ m)⁻¹ • x) r)) = 0 := by
    have h := Infra.Section3.spaceAvg_sin_epsilon I hm r
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using h
  unfold psi psi0
  split_ifs with h1 h3
  · simp only [Pi.smul_apply] at hsin ⊢
    unfold spaceAvg at hsin ⊢
    rw [integral_const_mul, hsin 0, mul_zero]
  · simp only [Pi.smul_apply] at hsin ⊢
    unfold spaceAvg at hsin ⊢
    rw [integral_const_mul, hsin 1, mul_zero]
  · simp [spaceAvg]

/-! ### `sdFast5` -/

theorem sdFast5_continuous (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Continuous (sdFast5 I κm m k t p q) := by
  have hψ : Continuous (psi β I.Λ m k) := (Infra.Section4.amnr_psi_contDiff I m k).continuous
  unfold sdFast5
  exact ((continuous_const.mul hψ).mul continuous_const).add
    (continuous_const.mul (sdFast4_continuous I m κm k t p q))

theorem sdFast5_isFastPeriodic (hm : 1 ≤ m) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Infra.Ergodic.IsFastPeriodic (ergodicFrequency β I.Λ m) (sdFast5 I κm m k t p q) := by
  intro y n
  have h4 := sdFast4_isFastPeriodic I hm κm k t p q y n
  have hψ := psi_fast_shift I (m := m) k y n
  simp only [sdFast4] at h4
  unfold sdFast5
  rw [h4, hψ]

theorem sdFast5_cellAverage (hm : 1 ≤ m) (κm : ℝ) (k : ℤ) (t : ℝ) (p q : Fin 2) :
    Infra.Ergodic.cellAverage (sdFast5 I κm m k t p q) = 0 := by
  rw [← spaceAvg_eq_cellAverage]
  have hψ : Continuous (psi β I.Λ m k) := (Infra.Section4.amnr_psi_contDiff I m k).continuous
  have hg := sdFast4_continuous I m κm k t p q
  have i1 : IntegrableOn (fun y => (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
      psi β I.Λ m k y) * sigmaMat p q) unitCube :=
    integrableOn_unitCube_of_continuous ((continuous_const.mul hψ).mul continuous_const)
  have i2 : IntegrableOn (fun y => κm * gradMatrix (fun z => I.chiMK κm m k t z) y p q)
      unitCube := integrableOn_unitCube_of_continuous (continuous_const.mul hg)
  unfold spaceAvg sdFast5
  rw [integral_add i1 i2]
  have h1 : (∫ y in unitCube, (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
      psi β I.Λ m k y) * sigmaMat p q) = 0 := by
    have := psi_spaceAvg I hm k
    unfold spaceAvg at this
    rw [integral_mul_const, integral_const_mul, this]
    simp
  have h2 : (∫ y in unitCube, κm * gradMatrix (fun z => I.chiMK κm m k t z) y p q) = 0 := by
    have := spaceAvg_gradMatrix_chiMK I hm κm k t p q
    unfold spaceAvg at this
    rw [integral_const_mul, this, mul_zero]
  rw [h1, h2, add_zero]

theorem sdFast5_abs_le (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (k : ℤ) (t : ℝ)
    (p q : Fin 2) (y : Vec 2) :
    |sdFast5 I κm m k t p q y| ≤ 2 * (a β I.Λ m * epsilon β I.Λ m ^ 2) := by
  have hz := Infra.Section3.zetaProd_mem_Icc I hm k t
  have hψ := Infra.Section4.amnr_psi_abs_le I m k y
  have hg := sdFast4_abs_le I hm hκm k t p q y
  have hzp : I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t = I.zetaProd m k t := rfl
  have hA : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 :=
    mul_nonneg (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le (sq_nonneg _)
  unfold sdFast5
  rw [hzp]
  refine (abs_add_le _ _).trans ?_
  have e1 : |I.zetaProd m k t * psi β I.Λ m k y * sigmaMat p q| ≤
      a β I.Λ m * epsilon β I.Λ m ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hz.1]
    calc I.zetaProd m k t * |psi β I.Λ m k y| * |sigmaMat p q|
        ≤ 1 * (a β I.Λ m * epsilon β I.Λ m ^ 2) * 1 :=
          mul_le_mul (mul_le_mul hz.2 hψ (abs_nonneg _) zero_le_one)
            (sa_sigma_abs_le p q) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |κm * gradMatrix (fun z => I.chiMK κm m k t z) y p q| ≤
      a β I.Λ m * epsilon β I.Λ m ^ 2 := by
    rw [abs_mul, abs_of_pos hκm]
    have : |gradMatrix (fun z => I.chiMK κm m k t z) y p q| ≤
        a β I.Λ m * epsilon β I.Λ m ^ 2 / κm := hg
    calc κm * |gradMatrix (fun z => I.chiMK κm m k t z) y p q|
        ≤ κm * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) :=
          mul_le_mul_of_nonneg_left this hκm.le
      _ = _ := by field_simp
  linarith

end AVenhance.Infra.Section5.Contracts
end
