/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice

/-! # Smoothness and periodicity of the defect matrices at a fixed time

For fixed `(m, k, t)` the entries of the defect matrices `D_k`, `E_k` are `C^∞` and `ℤ²`-periodic
in the position; the `Y = X⁻¹_{m-1,l_k}(t,·)` gradient is periodic because `Y` is lattice
equivariant, and `∇Χ_{m,k}` is periodic because the shear field is. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem sd_xFlowInv_slice (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l t) :=
  (xFlowInv_joint_contDiff_infty I hΦ m l).comp (contDiff_prodMk_right t)

theorem sd_chiMK_component_contDiff (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => I.chiMK κm m k t z j) := by
  have h := (contDiff_const (c := -(I.corrTime κm m k t))).smul (contDiff_uShear' β I.Λ m k)
  have h' : ContDiff ℝ (⊤ : ℕ∞) (I.chiMK κm m k t) := by
    unfold Ingredients.chiMK
    exact h
  exact (contDiff_apply ℝ ℝ j).comp h'

theorem sd_chiMK_component_periodic (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (j : Fin 2) :
    IsZ2Periodic (fun z => I.chiMK κm m k t z j) := by
  intro n x
  have h := uShear_isZ2Periodic β I.Λ m k n x
  simp only [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
  rw [h]

/-- Entries of `∇Χ_{m,k}` are `C^∞`. -/
theorem sd_gradChi_contDiff (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => gradMatrix (fun z => I.chiMK κm m k t z) y a j) :=
  contDiff_spaceGrad_component (f := fun z => I.chiMK κm m k t z j)
    (sd_chiMK_component_contDiff I κm m k t j) a

/-- Entries of `∇Χ_{m,k}` are `ℤ²`-periodic. -/
theorem sd_gradChi_periodic (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (a j : Fin 2) :
    IsZ2Periodic (fun y => gradMatrix (fun z => I.chiMK κm m k t z) y a j) := by
  intro n x
  exact congrFun (spaceGrad_isZ2Periodic (sd_chiMK_component_periodic I κm m k t j) n x) a

theorem sd_gradY_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (i a : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i a) :=
  contDiff_spaceGrad_component (f := fun z => I.xFlowInv hΦ m l t z a)
    ((contDiff_apply ℝ ℝ a).comp (sd_xFlowInv_slice I hΦ m l t)) i

theorem sd_gradY_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (i a : Fin 2) :
    IsZ2Periodic (fun x => gradMatrix (fun z => I.xFlowInv hΦ m l t z) x i a) := by
  have hs := sd_xFlowInv_slice I hΦ m l t
  have hp := Infra.Section4.amnr_fderiv_periodic_of_equivariant
    (hs.differentiable (by simp))
    (fun k x => Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m l t k x)
  intro n x
  change fderiv ℝ (fun z => I.xFlowInv hΦ m l t z a) (x + latticeShift n) (basisVec i) =
    fderiv ℝ (fun z => I.xFlowInv hΦ m l t z a) x (basisVec i)
  rw [fderiv_apply (hs.differentiable (by simp) _) a, fderiv_apply (hs.differentiable (by simp) _)
      a,
    hp n x]

/-- Entries of `∇Χ_{m,k} ∘ Y` are `C^∞`. -/
theorem sd_gradChi_comp_contDiff (hΦ : IsStreamSeq I Φ) (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ)
    (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) a j) :=
  (sd_gradChi_contDiff I κm m k t a j).comp (sd_xFlowInv_slice I hΦ m _ t)

theorem sd_gradChi_comp_periodic (hΦ : IsStreamSeq I Φ) (κm : ℝ) (m : ℕ) (k : ℤ) (t : ℝ)
    (a j : Fin 2) :
    IsZ2Periodic (fun x => gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) a j) := by
  intro n x
  simp only
  rw [Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m _ t n x]
  exact sd_gradChi_periodic I κm m k t a j n _

/-! ### `D_k` -/

theorem sd_defect4_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sdDefect4 I hΦ m κm k t x i j) := by
  simp only [sdDefect4, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two,
    smul_eq_mul]
  exact contDiff_const.mul
    ((((sd_gradY_contDiff I hΦ m _ t i 0).sub contDiff_const).mul
        (sd_gradChi_comp_contDiff I hΦ κm m k t 0 j)).add
      (((sd_gradY_contDiff I hΦ m _ t i 1).sub contDiff_const).mul
        (sd_gradChi_comp_contDiff I hΦ κm m k t 1 j)))

theorem sd_defect4_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) :
    IsZ2Periodic (sdDefect4 I hΦ m κm k t) := by
  intro n x
  ext i j
  simp only [sdDefect4, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two,
    smul_eq_mul]
  have hA : ∀ a : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z)
      (x + latticeShift n) i a =
      gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i a := fun a =>
    sd_gradY_periodic I hΦ m _ t i a n x
  have hC : ∀ a : Fin 2, gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift n)) a j =
      gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) a j :=
    fun a => sd_gradChi_comp_periodic I hΦ κm m k t a j n x
  rw [hA 0, hA 1, hC 0, hC 1]

/-! ### `E_k` -/

theorem sd_psiCoeff_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) :=
  contDiff_const.mul ((Infra.Section4.amnr_psi_contDiff I m k).comp (sd_xFlowInv_slice I hΦ m _ t))

theorem sd_flowGradK_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => flowGradK I hΦ m k t x i j) :=
  (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).comp
    (contDiff_prodMk_right t)

theorem sd_defect5_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sdDefect5 I hΦ m κm k t x i j) := by
  simp only [sdDefect5, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, smul_eq_mul]
  have hp := sd_psiCoeff_contDiff I hΦ m k t
  exact ((contDiff_const.sub (sd_flowGradK_contDiff I hΦ m k t 0 i)).mul
      ((hp.mul contDiff_const).add (contDiff_const.mul (sd_gradChi_comp_contDiff I hΦ κm m k t 0
          j)))).add
    ((contDiff_const.sub (sd_flowGradK_contDiff I hΦ m k t 1 i)).mul
      ((hp.mul contDiff_const).add (contDiff_const.mul (sd_gradChi_comp_contDiff I hΦ κm m k t 1
          j))))

theorem sd_defect5_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) :
    IsZ2Periodic (sdDefect5 I hΦ m κm k t) := by
  intro n x
  ext i j
  simp only [sdDefect5, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, smul_eq_mul]
  have hψ : psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift n)) =
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) := by
    rw [Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m _ t n x, tf_psi_periodic I m k n]
  have hF : ∀ a : Fin 2, flowGradK I hΦ m k t (x + latticeShift n) a i =
      flowGradK I hΦ m k t x a i := fun a =>
    Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m (lIdx β I.Λ m k) t a i n x
  have hC : ∀ a : Fin 2, gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift n)) a j =
      gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) a j :=
    fun a => sd_gradChi_comp_periodic I hΦ κm m k t a j n x
  rw [hψ, hF 0, hF 1, hC 0, hC 1]

end AVenhance.Infra.Section5.Contracts
end
