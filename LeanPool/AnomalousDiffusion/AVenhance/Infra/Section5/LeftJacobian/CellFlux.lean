/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum

/-!: the exact cell-flux identity (33) and the `normie3` split.

For every odd (indeed every) `k`, with `Q = ∇Y_{l_k}`, `F = F_{l_k}`, `B = (∇χ_k) ∘ Y_{l_k}`,
`p = selCoeff`, the determinant-one/Piola identity `σ Q = Fᵀ σ` gives
`C_k = Fᵀ C⁰_k + κ (I - Fᵀ) + D_k + E_k` (the corrected formulation (33)). Consequently the
literal-name `normie3Sel` equals the centered `normie3Plus` minus the two defect
contractions. All statements are unconditional: smoothness of `χ_k` and of the inverse
flow is supplied by `FrozenFlowRegularity` and `Section3.chiMK_component_contDiff_two`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `σ Q = cof(Q) σ` for every `2 × 2` matrix: the algebraic core of `σ Q = Fᵀ σ`. -/
theorem sigmaMat_mul_eq_rowCofactor_mul (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    sigmaMat * Q = rowCofactor Q * sigmaMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowCofactor, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sigmaMat]

/-- Pure matrix algebra behind (33): from `σ Q = Fᵀ σ`. -/
theorem cellFlux_algebra (κ p : ℝ) (Ft Q B : Matrix (Fin 2) (Fin 2) ℝ)
    (hσ : sigmaMat * Q = Ft * sigmaMat) :
    (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + p • sigmaMat) * (1 + Q * B) =
      Ft * ((κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + p • sigmaMat) * (1 + B)) +
        κ • (1 - Ft) + κ • ((Q - 1) * B) + (1 - Ft) * (p • sigmaMat + κ • B) := by
  have h : sigmaMat * (Q * B) = Ft * (sigmaMat * B) := by
    rw [← Matrix.mul_assoc, hσ, Matrix.mul_assoc]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.mul_one,
    Matrix.one_mul, sub_mul, smul_sub]
  rw [h]
  abel

/-- The inverse flow's row-Jacobian satisfies `σ ∇Y = Fᵀ σ` (det one). -/
theorem sigmaMat_mul_gradMatrix_xFlowInv (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (x : Vec 2) :
    sigmaMat * gradMatrix (I.xFlowInv hΦ m l t) x =
      (I.flowGrad hΦ m l t x).transpose * sigmaMat := by
  rw [sigmaMat_mul_eq_rowCofactor_mul,
    xFlowInv_rowCofactor_eq_flowGrad_transpose I hΦ m l t x
      (streamVel_spatialDivergence_eq_zero I hΦ m)]

/-- Each corrector `χ_k(t, ·)` is differentiable (indeed `C²`). -/
theorem chiMK_differentiable (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (z : Vec 2) :
    DifferentiableAt ℝ (fun y => I.chiMK κ m k t y) z := by
  have hχ2 : ContDiff ℝ 2 (fun y => I.chiMK κ m k t y) := by
    let E : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
    have hE : ContDiff ℝ 2 E := by fun_prop
    apply contDiff_pi.2
    intro c
    have hc := (Infra.Section3.chiMK_component_contDiff_two I (m := m) κ k c).comp hE
    simpa [E, Function.comp_def] using hc
  exact hχ2.differentiable (by norm_num) z

/-- Exact identity (33): `C_k = F_kᵀ C⁰_k + κ (I - F_kᵀ) + D_k + E_k`. -/
theorem correctorFlux_eq_cellFlux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) :
    correctorFlux I hΦ m κm k t x =
      (flowGradK I hΦ m k t x).transpose * cellFlux I hΦ m κm k t x +
        κm • (1 - (flowGradK I hΦ m k t x).transpose) +
        correctorDefectMatrix I hΦ m k t κm x +
        correctorPushforwardMatrix I hΦ m k t κm x := by
  have hY : DifferentiableAt ℝ (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x :=
    (xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) x
  have hchain : gradChiTilde I hΦ m κm k t x =
      gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x *
        gradMatrix (fun z => I.chiMK κm m k t z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) :=
    gradMatrix_comp (chiMK_differentiable I m κm k t _) hY
  have hσ := sigmaMat_mul_gradMatrix_xFlowInv I hΦ m (lIdx β I.Λ m k) t x
  have key := cellFlux_algebra κm (selCoeff I hΦ m k t x)
    (flowGradK I hΦ m k t x).transpose
    (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x)
    (gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) hσ
  unfold correctorFlux
  rw [hchain]
  simp only [cellFlux, correctorDefectMatrix, correctorPushforwardMatrix,
    correctorBaseMatrix, Ingredients.zetaProd, selCoeff, mul_assoc] at key ⊢
  exact key

/-! ### The `normie3` split -/

theorem frob_sub_left (A B G : Matrix (Fin 2) (Fin 2) ℝ) :
    frob (A - B) G = frob A G - frob B G := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]

theorem frob_add_left (A B G : Matrix (Fin 2) (Fin 2) ℝ) :
    frob (A + B) G = frob A G + frob B G := by
  simp [frob, add_mul, Finset.sum_add_distrib]

/-- The matrix split: `κ I + Fᵀ(𝒥 - κ I) - C_k = Fᵀ(𝒥 - C⁰_k) - D_k - E_k`. -/
theorem normie3_matrix_split (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (x : Vec 2) :
    κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k t x).transpose *
          (I.flux κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
        correctorFlux I hΦ m κm k t x =
      (flowGradK I hΦ m k t x).transpose * (I.flux κm m t - cellFlux I hΦ m κm k t x) -
        correctorDefectMatrix I hΦ m k t κm x -
        correctorPushforwardMatrix I hΦ m k t κm x := by
  rw [correctorFlux_eq_cellFlux I hΦ m κm k t x]
  simp only [mul_sub, smul_sub, Matrix.mul_one, Matrix.mul_smul]
  abel

/-- The literal-name `normie3` equals the centered `normie3⁺` minus the two defect
contractions `Σ_k ξ_k (D_k + E_k) : ∇G_k`. -/
theorem normie3Sel_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    normie3Sel I hΦ m κm T t x =
      normie3Plus I hΦ m κm T t x -
        ∑' k : {k : ℤ // Odd k}, I.xiMK m k t *
          (frob (correctorDefectMatrix I hΦ m k t κm x)
              (gradG I hΦ m T (lIdx β I.Λ m k) t x) +
            frob (correctorPushforwardMatrix I hΦ m k t κm x)
              (gradG I hΦ m T (lIdx β I.Λ m k) t x)) := by
  have hfin := AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t
  have hsum : ∀ f : {k : ℤ // Odd k} → ℝ, (∀ q, I.xiMK m q.1 t = 0 → f q = 0) →
      Summable f := by
    intro f hf
    refine summable_of_hasFiniteSupport (show (Function.support f).Finite from hfin.subset ?_)
    intro q hq
    by_contra hxi
    exact hq (hf q (not_not.mp hxi))
  unfold normie3Sel normie3Plus
  rw [← Summable.tsum_sub]
  · apply tsum_congr
    intro q
    rw [normie3_matrix_split, frob_sub_left, frob_sub_left]
    ring
  · exact hsum _ (fun q hq => by simp [hq])
  · exact hsum _ (fun q hq => by simp [hq])

end AVenhance.Infra.Section5.LeftJacobian

end
