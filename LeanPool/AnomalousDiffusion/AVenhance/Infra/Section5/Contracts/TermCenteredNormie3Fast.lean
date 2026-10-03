/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.CellMean
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.CellMeanPull
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFluxEntries

/-! # Fast factor of `normie3`

`normie3 = Σ_k ξ_k frob (F_kᵀ (𝒥 - C⁰_k)) ∇G_k` with `C⁰_k = cellFluxCell ∘ Y_k`.  Expanding the
Frobenius product, the fast factor in the cell variable is the `(p, j)` entry of
`𝒥 - cellFluxCell`, which is continuous, `1/ε_m`-periodic, has exact zero cell mean on the support
of `ξ_{m,k}` and is bounded by `4 ψ (1 + ψ/κ)`, `ψ = a_m ε_m²`.  Off the support the fast factor is
set to `0` (the slow factor vanishes there). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Section5.LeftToShow

variable {β : ℝ} (I : Ingredients β) {m : ℕ}

/-- The fast factor `(𝒥 - C⁰_k)_{pj}` of `normie3` in the cell variable (zero off `supp ξ_{m,k}`).
-/
def n3Fast (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (p j : Fin 2) (z : Vec 2) : ℝ :=
  if I.xiMK m k t = 0 then 0 else (I.flux κ m t - LeftJacobian.cellFluxCell I m κ k t z) p j

theorem n3Fast_of_xi_eq_zero (κ : ℝ) (k : ℤ) (t : ℝ) (p j : Fin 2) (h : I.xiMK m k t = 0) :
    n3Fast I κ m k t p j = fun _ => 0 := by
  funext z
  simp [n3Fast, h]

theorem n3Fast_of_xi_ne_zero (κ : ℝ) (k : ℤ) (t : ℝ) (p j : Fin 2) (h : I.xiMK m k t ≠ 0)
    (z : Vec 2) :
    n3Fast I κ m k t p j z = (I.flux κ m t - LeftJacobian.cellFluxCell I m κ k t z) p j := by
  simp [n3Fast, h]

/-- Entry form of the cell flux. -/
theorem cellFluxCell_apply (κ : ℝ) (k : ℤ) (t : ℝ) (z : Vec 2) (p j : Fin 2) :
    LeftJacobian.cellFluxCell I m κ k t z p j =
      ∑ q : Fin 2, (κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p q +
          (I.zetaProd m k t * psi β I.Λ m k z) * sigmaMat p q) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) q j + gradMatrix (fun y => I.chiMK κ m k t y) z q j) := by
  simp [LeftJacobian.cellFluxCell, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply]

theorem cellFluxCell_expand (κ : ℝ) (k : ℤ) (t : ℝ) (z : Vec 2) :
    LeftJacobian.cellFluxCell I m κ k t z =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        κ • gradMatrix (fun y => I.chiMK κ m k t y) z +
        (I.zetaProd m k t * psi β I.Λ m k z) • sigmaMat +
        (I.zetaProd m k t * psi β I.Λ m k z) •
          (sigmaMat * gradMatrix (fun y => I.chiMK κ m k t y) z) := by
  unfold LeftJacobian.cellFluxCell
  simp only [add_mul, mul_add, smul_mul_assoc, Matrix.mul_one, Matrix.one_mul]
  abel

theorem n3Fast_continuous (κ : ℝ) {k : ℤ} (hk : Odd k) (t : ℝ) (p j : Fin 2) :
    Continuous (n3Fast I κ m k t p j) := by
  by_cases hξ : I.xiMK m k t = 0
  · rw [n3Fast_of_xi_eq_zero I κ k t p j hξ]
    exact continuous_const
  · have hg : Continuous (fun z : Vec 2 => gradMatrix (fun y => I.chiMK κ m k t y) z) :=
      (LeftToShow.continuous_gradMatrix_chiMK I κ m hk).comp
        (continuous_const.prodMk continuous_id)
    have hψ : Continuous (psi β I.Λ m k) := (Infra.Section4.amnr_psi_contDiff I m k).continuous
    have hc : Continuous (fun z => LeftJacobian.cellFluxCell I m κ k t z p j) := by
      simp only [cellFluxCell_apply]
      refine continuous_finsetSum _ fun q _ => ?_
      exact (continuous_const.add ((continuous_const.mul hψ).mul continuous_const)).mul
        (continuous_const.add (hg.matrix_elem q j))
    have : n3Fast I κ m k t p j = fun z => I.flux κ m t p j - LeftJacobian.cellFluxCell I m κ k t
        z p j := by
      funext z
      rw [n3Fast_of_xi_ne_zero I κ k t p j hξ]
      simp [Matrix.sub_apply]
    rw [this]
    exact continuous_const.sub hc

theorem n3Fast_isFastPeriodic (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) (p j : Fin 2) :
    Infra.Ergodic.IsFastPeriodic (ergodicFrequency β I.Λ m) (n3Fast I κ m k t p j) := by
  intro y n
  by_cases hξ : I.xiMK m k t = 0
  · rw [n3Fast_of_xi_eq_zero I κ k t p j hξ]
  · rw [n3Fast_of_xi_ne_zero I κ k t p j hξ, n3Fast_of_xi_ne_zero I κ k t p j hξ]
    have hψ := psi_fast_shift I (m := m) k y n
    have hg : ∀ q j' : Fin 2, gradMatrix (fun z => I.chiMK κ m k t z)
        (y + fun i => (n i : ℝ) / (ergodicFrequency β I.Λ m : ℝ)) q j' =
        gradMatrix (fun z => I.chiMK κ m k t z) y q j' :=
      fun q j' => gradMatrix_chiMK_isFastPeriodic I hm κ k t q j' y n
    simp only [Matrix.sub_apply, cellFluxCell_apply, hψ, hg]

theorem n3Fast_cellAverage (hm : 1 ≤ m) (κ : ℝ) {k : ℤ} (hk : Odd k) (t : ℝ) (p j : Fin 2) :
    Infra.Ergodic.cellAverage (n3Fast I κ m k t p j) = 0 := by
  by_cases hξ : I.xiMK m k t = 0
  · rw [n3Fast_of_xi_eq_zero I κ k t p j hξ]
    simp
  · rw [← spaceAvg_eq_cellAverage]
    have h := LeftJacobian.cellFluxCell_fastFactor_mean_zero I m hm κ hk t hξ
    have h' : spaceAvg (fun z => (I.flux κ m t - LeftJacobian.cellFluxCell I m κ k t z) p j) = 0 :=
      congrFun (congrFun h p) j
    have : n3Fast I κ m k t p j = fun z => (I.flux κ m t - LeftJacobian.cellFluxCell I m κ k t z)
        p j := by
      funext z
      exact n3Fast_of_xi_ne_zero I κ k t p j hξ z
    rw [this]
    exact h'

/-- Entries of `cellFluxCell - κ I` are bounded by `2ψ(1 + ψ/κ)`, `ψ = a_m ε_m²`. -/
theorem cellFluxCell_sub_kappa_le (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ) (t : ℝ)
    (z : Vec 2) (p j : Fin 2) :
    |LeftJacobian.cellFluxCell I m κ k t z p j - κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j| ≤
      2 * (a β I.Λ m * epsilon β I.Λ m ^ 2) *
        (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κ) := by
  set ψ : ℝ := a β I.Λ m * epsilon β I.Λ m ^ 2 with hψdef
  have hψ0 : 0 ≤ ψ := scf_P_nonneg I
  have hz := Infra.Section3.zetaProd_mem_Icc I hm k t
  have hpsi := Infra.Section4.amnr_psi_abs_le I m k z
  have hP : |I.zetaProd m k t * psi β I.Λ m k z| ≤ ψ := by
    rw [abs_mul, abs_of_nonneg hz.1]
    calc I.zetaProd m k t * |psi β I.Λ m k z| ≤ 1 * ψ :=
          mul_le_mul hz.2 hpsi (abs_nonneg _) zero_le_one
      _ = ψ := one_mul _
  have hg : ∀ u v : Fin 2, |gradMatrix (fun y => I.chiMK κ m k t y) z u v| ≤ ψ / κ :=
    fun u v => gradMatrix_chiMK_entry_abs_le I hm hκ k t z u v
  have hσg : |(sigmaMat * gradMatrix (fun y => I.chiMK κ m k t y) z) p j| ≤ 2 * 1 * (ψ / κ) :=
    abs_matMul_le (fun u v => sa_sigma_abs_le u v) hg p j
  rw [cellFluxCell_expand]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : |κ * gradMatrix (fun y => I.chiMK κ m k t y) z p j| ≤ ψ := by
    rw [abs_mul, abs_of_pos hκ]
    calc κ * |gradMatrix (fun y => I.chiMK κ m k t y) z p j| ≤ κ * (ψ / κ) :=
          mul_le_mul_of_nonneg_left (hg p j) hκ.le
      _ = ψ := by field_simp
  have e2 : |(I.zetaProd m k t * psi β I.Λ m k z) * sigmaMat p j| ≤ ψ := by
    rw [abs_mul]
    calc _ ≤ ψ * 1 := mul_le_mul hP (sa_sigma_abs_le p j) (abs_nonneg _) hψ0
      _ = ψ := mul_one _
  have e3 : |(I.zetaProd m k t * psi β I.Λ m k z) *
      (sigmaMat * gradMatrix (fun y => I.chiMK κ m k t y) z) p j| ≤ 2 * (ψ * (ψ / κ)) := by
    rw [abs_mul]
    calc _ ≤ ψ * (2 * 1 * (ψ / κ)) := mul_le_mul hP hσg (abs_nonneg _) hψ0
      _ = 2 * (ψ * (ψ / κ)) := by ring
  have key := abs_add_le_of_le (abs_add_le_of_le e1 e2) e3
  have hrw : κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j + κ * gradMatrix (fun y => I.chiMK κ m k t y)
      z p j +
      (I.zetaProd m k t * psi β I.Λ m k z) * sigmaMat p j +
      (I.zetaProd m k t * psi β I.Λ m k z) *
        (sigmaMat * gradMatrix (fun y => I.chiMK κ m k t y) z) p j -
      κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j =
      κ * gradMatrix (fun y => I.chiMK κ m k t y) z p j +
        (I.zetaProd m k t * psi β I.Λ m k z) * sigmaMat p j +
        (I.zetaProd m k t * psi β I.Λ m k z) *
          (sigmaMat * gradMatrix (fun y => I.chiMK κ m k t y) z) p j := by ring
  rw [hrw]
  refine key.trans (le_of_eq ?_)
  ring

/-- Entries of `𝒥 - κ I` are bounded by `ψ²/(2κ)`. -/
theorem flux_sub_kappa_le (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (t : ℝ) (p j : Fin 2) :
    |I.flux κ m t p j - κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j| ≤
      (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2 / (2 * κ) := by
  have hψ2 : (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2 / (2 * κ) =
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by ring
  rw [hψ2]
  by_cases hpj : p = j
  · subst hpj
    have h1 := Infra.Section3.flux_diag_ge_kappa I hm κ t p
    have h2 := Infra.Section3.flux_diag_le_kappa_add_amplitude I hm κ hκ t p
    rw [abs_le]
    simp only [Matrix.one_apply_eq, mul_one]
    constructor <;> linarith [h1, h2, show 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) by
      positivity]
  · rw [Infra.Section3.flux_offdiag_eq_zero I hm κ t hpj, Matrix.one_apply_ne hpj]
    simp only [mul_zero, sub_self, abs_zero]
    positivity

/-- **Sup bound of the fast factor**: `|n3Fast| ≤ 4ψ(1 + ψ/κ)`. -/
theorem n3Fast_abs_le (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ) (t : ℝ) (p j : Fin 2)
    (z : Vec 2) :
    |n3Fast I κ m k t p j z| ≤
      4 * (a β I.Λ m * epsilon β I.Λ m ^ 2) * (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / κ) := by
  set ψ : ℝ := a β I.Λ m * epsilon β I.Λ m ^ 2 with hψdef
  have hψ0 : 0 ≤ ψ := scf_P_nonneg I
  have hpos : 0 ≤ 4 * ψ * (1 + ψ / κ) := by positivity
  by_cases hξ : I.xiMK m k t = 0
  · rw [n3Fast_of_xi_eq_zero I κ k t p j hξ]
    simpa using hpos
  · rw [n3Fast_of_xi_ne_zero I κ k t p j hξ]
    have h1 := flux_sub_kappa_le I hm hκ t p j
    have h2 := cellFluxCell_sub_kappa_le I hm hκ k t z p j
    have hsplit : (I.flux κ m t - LeftJacobian.cellFluxCell I m κ k t z) p j =
        (I.flux κ m t p j - κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j) -
          (LeftJacobian.cellFluxCell I m κ k t z p j - κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) p j) := by
      simp only [Matrix.sub_apply]
      ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have h3 : ψ ^ 2 / (2 * κ) ≤ ψ * (ψ / κ) := by
      have : ψ ^ 2 / (2 * κ) = (ψ * (ψ / κ)) / 2 := by field_simp
      rw [this]
      have : 0 ≤ ψ * (ψ / κ) := by positivity
      linarith
    calc _ ≤ ψ * (ψ / κ) + 2 * ψ * (1 + ψ / κ) := add_le_add (h1.trans h3) h2
      _ ≤ 4 * ψ * (1 + ψ / κ) := by
        have : 0 ≤ ψ * (ψ / κ) := by positivity
        nlinarith [this]

end AVenhance.Infra.Section5.Contracts
end
