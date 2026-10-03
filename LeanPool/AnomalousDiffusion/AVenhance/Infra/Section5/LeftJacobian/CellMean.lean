/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BracketFF

/-!: the zero cell mean of the fast factor of `normie3⁺`.

For an odd `k` with `ξ_{m,k}(t) ≠ 0`, the unpulled cell flux
`z ↦ (κ I + p₀(z) σ)(I + ∇χ_k(z))`, `p₀ = ζ̂_{l_k} ζ_k ψ_k`, has cell average exactly the
flux `𝒥 = I.flux κ m t`. Hence `𝒥 - C⁰_k` has exact zero cell mean. Two cases:
if `ζ_k(t) ≠ 0` the unpulled integrand *is* the flux integrand pointwise; if
`ζ_k(t) = 0` then (by transition separation) every odd `ζ` vanishes, so `𝒥 = κ I`, and
`⟨κ (I + ∇χ_k)⟩ = κ I` because `∇χ_k` has mean zero. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.LeftToShow
  AVenhance.Infra.Section3

variable {β : ℝ} (I : Ingredients β)

/-- The unpulled cell flux in the cell variable: `(κ I + p₀ σ)(I + ∇χ_k)`, `p₀ = ζ̂ ζ_k ψ_k`. -/
def cellFluxCell (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (z : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (I.zetaProd m k t * psi β I.Λ m k z) • sigmaMat) *
    (1 + gradMatrix (fun y => I.chiMK κ m k t y) z)

theorem CellMean.spaceAvg_const_eq' (c : ℝ) : spaceAvg (fun _ : Vec 2 => c) = c := by
  unfold spaceAvg
  rw [setIntegral_const]
  have hvol : volume unitCube = 1 := by
    unfold unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  simp [Measure.real, hvol]

theorem CellMean.spaceAvg_add' {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    spaceAvg (fun x => f x + g x) = spaceAvg f + spaceAvg g :=
  integral_add (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

theorem CellMean.spaceAvg_sub' {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    spaceAvg (fun x => f x - g x) = spaceAvg f - spaceAvg g :=
  integral_sub (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

theorem CellMean.spaceAvg_const_mul' (c : ℝ) (f : Vec 2 → ℝ) :
    spaceAvg (fun x => c * f x) = c * spaceAvg f :=
  integral_const_mul c f

theorem CellMean.continuous_psi (m : ℕ) (k : ℤ) : Continuous (psi β I.Λ m k) := by
  have h : ContDiff ℝ 2 (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ 2
        (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  exact h.continuous

theorem CellMean.continuous_cellFluxCell (m : ℕ) (κ : ℝ) {k : ℤ} (hk : Odd k) (t : ℝ) :
    Continuous (cellFluxCell I m κ k t) := by
  have hg : Continuous (fun z : Vec 2 => gradMatrix (fun y => I.chiMK κ m k t y) z) :=
    (continuous_gradMatrix_chiMK I κ m hk).comp (continuous_const.prodMk continuous_id)
  have hp : Continuous (fun z : Vec 2 => I.zetaProd m k t * psi β I.Λ m k z) :=
    continuous_const.mul (CellMean.continuous_psi I m k)
  unfold cellFluxCell
  exact ((continuous_const.add (hp.smul continuous_const)).matrix_mul
    (continuous_const.add hg))

/-- The cell average of the unpulled cell flux is the flux. -/
theorem cellFluxCell_mean (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) {k : ℤ} (hk : Odd k) (t : ℝ)
    (hξ : I.xiMK m k t ≠ 0) :
    spaceAvgMat (cellFluxCell I m κ k t) = I.flux κ m t := by
  by_cases hz : I.zetaMK m k t = 0
  · have hzero : ∀ l : ℤ, Odd l → I.zetaMK m l t = 0 := by
      intro l hl
      by_contra hne
      by_cases hlk : k = l
      · subst hlk
        exact hne hz
      · exact hξ (xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne I hm hl hk hlk t hne)
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hzero]
    have hp : I.zetaProd m k t = 0 := by simp [Ingredients.zetaProd, hz]
    have hg : Continuous (fun z : Vec 2 => gradMatrix (fun y => I.chiMK κ m k t y) z) :=
      (continuous_gradMatrix_chiMK I κ m hk).comp (continuous_const.prodMk continuous_id)
    ext i j
    have hentry : (fun z => cellFluxCell I m κ k t z i j) =
        fun z => κ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
          κ * gradMatrix (fun y => I.chiMK κ m k t y) z i j := by
      funext z
      simp only [cellFluxCell, hp, zero_mul, zero_smul, add_zero]
      rw [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one]
      simp [Matrix.add_apply]
      ring
    have hcont : Continuous (fun z : Vec 2 =>
        κ * gradMatrix (fun y => I.chiMK κ m k t y) z i j) :=
      continuous_const.mul (hg.matrix_elem i j)
    have h0 := spaceAvg_gradMatrix_chiMK I hm κ k t i j
    change spaceAvg (fun z => cellFluxCell I m κ k t z i j) = _
    rw [hentry, CellMean.spaceAvg_add' continuous_const hcont, CellMean.spaceAvg_const_eq',
      CellMean.spaceAvg_const_mul', h0]
    simp [Matrix.smul_apply]
  · have hchi : I.chiM κ m t = fun x => I.chiMK κ m k t x := by
      funext x
      exact chiM_eq_chiMK_of_zetaMK_ne_zero I hm κ hk t x hz
    have hfun : I.fluxIntegrand κ m t = cellFluxCell I m κ k t := by
      funext z
      unfold Ingredients.fluxIntegrand cellFluxCell
      rw [psiM_eq_single_of_zetaMK_ne_zero I hm hk t z hz, hchi]
    unfold Ingredients.flux
    rw [hfun]

/-- The fast factor `𝒥 - C⁰_k` of `normie3⁺` has exact zero cell mean. -/
theorem cellFluxCell_fastFactor_mean_zero (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) {k : ℤ}
    (hk : Odd k) (t : ℝ) (hξ : I.xiMK m k t ≠ 0) :
    spaceAvgMat (fun z => I.flux κ m t - cellFluxCell I m κ k t z) = 0 := by
  have hmean := cellFluxCell_mean I m hm κ hk t hξ
  have hc := CellMean.continuous_cellFluxCell I m κ hk t
  ext i j
  have hmij : spaceAvg (fun z => cellFluxCell I m κ k t z i j) = I.flux κ m t i j :=
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hmean
  have hfun : (fun z => (I.flux κ m t - cellFluxCell I m κ k t z) i j) =
      fun z => I.flux κ m t i j - cellFluxCell I m κ k t z i j := by
    funext z
    simp [Matrix.sub_apply]
  change spaceAvg (fun z => (I.flux κ m t - cellFluxCell I m κ k t z) i j) = _
  rw [hfun, CellMean.spaceAvg_sub' continuous_const (hc.matrix_elem i j),
      CellMean.spaceAvg_const_eq', hmij]
  simp

end AVenhance.Infra.Section5.LeftJacobian

end
