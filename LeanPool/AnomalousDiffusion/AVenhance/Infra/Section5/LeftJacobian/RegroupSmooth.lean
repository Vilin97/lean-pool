/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs

/-!: spatial smoothness of the objects regrouped in `Regroup`.

At a fixed time every selected-mode object (`selCoeff`, `flowGradK`, `B_k`, `D_k`, `E_k`, `G_k`,
`∇T`) is `C^∞` in space, given `T t ∈ C^∞`. These are consequences of the smoothness
lemmas of `RelativeError.LeadingErrorAlgebraDefs`; only `ContDiff ℝ ∞ (T t)` is assumed. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Entries of the row-Jacobian of a smooth field are smooth. -/
theorem contDiff_gradMatrix_entry {f : Vec 2 → Vec 2} (hf : ContDiff ℝ ∞ f) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun x => gradMatrix f x i j) :=
  Integration.contDiff_spaceGrad_component (f := fun y => f y j)
    ((contDiff_apply ℝ ℝ j).comp hf) i

theorem contDiff_psi_infty (m : ℕ) (k : ℤ) : ContDiff ℝ ∞ (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ ∞
      (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

theorem contDiff_selCoeff (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ ∞ (fun y => selCoeff I hΦ m k t y) :=
  contDiff_const.mul ((contDiff_psi_infty I m k).comp
    (RelativeError.contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t))

theorem contDiff_flowGradK_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) : ContDiff ℝ ∞ (fun y => flowGradK I hΦ m k t y i j) :=
  (contDiff_gradMatrix_entry (RelativeError.contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t) i
      j).comp
    (RelativeError.contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t)

theorem contDiff_gradYEntry (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y i j) :=
  contDiff_gradMatrix_entry (RelativeError.contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t) i j

theorem contDiff_cellGradEntry (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => gradMatrix (fun z => I.chiMK κm m k t z)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) i j) :=
  (contDiff_gradMatrix_entry (RelativeError.contDiff_chiMK I κm m k t) i j).comp
    (RelativeError.contDiff_xFlowInv_slice I hΦ m (lIdx β I.Λ m k) t)

theorem contDiff_defect_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => correctorDefectMatrix I hΦ m k t κm y i j) := by
  have heq : (fun y => correctorDefectMatrix I hΦ m k t κm y i j) = fun y =>
      κm * ∑ p : Fin 2,
        (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y i p -
          (1 : Matrix (Fin 2) (Fin 2) ℝ) i p) *
        gradMatrix (fun z => I.chiMK κm m k t z)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) p j := by
    funext y
    simp [correctorDefectMatrix, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]
  rw [heq]
  refine contDiff_const.mul (ContDiff.sum fun p _ => ?_)
  exact ((contDiff_gradYEntry I hΦ m k t i p).sub contDiff_const).mul
    (contDiff_cellGradEntry I hΦ m κm k t p j)

theorem contDiff_pushforward_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => correctorPushforwardMatrix I hΦ m k t κm y i j) := by
  have heq : (fun y => correctorPushforwardMatrix I hΦ m k t κm y i j) = fun y =>
      ∑ p : Fin 2,
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) i p - flowGradK I hΦ m k t y p i) *
          (selCoeff I hΦ m k t y * sigmaMat p j +
            κm * gradMatrix (fun z => I.chiMK κm m k t z)
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) p j) := by
    funext y
    simp [correctorPushforwardMatrix, correctorBaseMatrix, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.transpose_apply, selCoeff, Ingredients.zetaProd, flowGradK]
  rw [heq]
  refine ContDiff.sum fun p _ => ?_
  exact (contDiff_const.sub (contDiff_flowGradK_entry I hΦ m k t p i)).mul
    ((((contDiff_selCoeff I hΦ m k t).mul contDiff_const)).add
      (contDiff_const.mul (contDiff_cellGradEntry I hΦ m κm k t p j)))

theorem contDiff_spaceGrad_T {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hT : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (fun y => spaceGrad (T t) y) :=
  contDiff_pi.2 fun p => Integration.contDiff_spaceGrad_component hT p

end AVenhance.Infra.Section5.LeftJacobian

end
