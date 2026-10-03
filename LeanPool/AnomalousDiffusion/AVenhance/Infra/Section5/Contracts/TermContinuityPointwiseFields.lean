/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuityPointwiseTools

/-! # Joint regularity of the building blocks of the pointwise §5.1 terms

Each lemma is on the open half space `tcU = (0,∞) × ℝ²`, componentwise.  `T` is any field that is
jointly `C^∞` on `[0,∞) × ℝ²` (an actual iterate). -/

@[expose] public section

noncomputable section

open Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)

/-- The pulled gradient `G_l` is jointly `C^∞` on the open half space. -/
theorem tc_G_contDiffOn (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => G I hΦ m T l p.1 p.2 i) tcU :=
  (Integration.transportedGrad_contDiffOn I hΦ m l hT i).mono
    (Set.prod_mono Set.Ioi_subset_Ici_self le_rfl)

/-- The spatial derivative matrix `∇G_l` is jointly `C^∞` on the open half space. -/
theorem tc_gradG_contDiffOn (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => gradG I hΦ m T l p.1 p.2 i j) tcU :=
  Integration.contDiffOn_spaceGrad_slice_Ioi (F := fun t y => G I hΦ m T l t y j)
    (tc_G_contDiffOn I hΦ m l hT j) i

/-- The twisted corrector components are jointly `C²`. -/
theorem tc_chiTilde_contDiffOn (κm : ℝ) (k : ℤ) (i : Fin 2) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.chiTilde hΦ m κm k p.1 p.2 i) tcU :=
  (Integration.chiTilde_component_contDiff_two I hΦ m κm k i).contDiffOn

/-- The flow gradient `flowGradK` is jointly `C^∞`. -/
theorem tc_flowGradK_contDiffOn (k : ℤ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => flowGradK I hΦ m k p.1 p.2 i j) tcU :=
  (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).contDiffOn

/-- `ζ_{m,k}` is `C^∞`. -/
theorem tc_zetaMK_contDiff (k : ℤ) : ContDiff ℝ ∞ (I.zetaMK m k) := by
  unfold Ingredients.zetaMK scaledCutoff
  exact I.zeta_smooth.comp (by fun_prop)

/-- The scalar coefficient `ζ̂_{m,l_k} ζ_{m,k} ψ_{m,k} ∘ X⁻¹` is jointly `C^∞`. -/
theorem tc_psiCoeff_contDiffOn (k : ℤ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      I.hatZetaML m (lIdx β I.Λ m k) p.1 * I.zetaMK m k p.1 *
        psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2)) tcU := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      I.hatZetaML m (lIdx β I.Λ m k) p.1 * I.zetaMK m k p.1) :=
    ((Section5.RelativeError.hatZetaML_contDiff I m (lIdx β I.Λ m k)).comp contDiff_fst).mul
      ((tc_zetaMK_contDiff I m k).comp contDiff_fst)
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2)) :=
    (Infra.Section4.amnr_psi_contDiff I m k).comp
      (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k))
  exact (h1.mul h2).contDiffOn

/-- The matrix `∇Χ^κ_{m,k}` evaluated at the inverse flow is jointly `C¹`. -/
theorem tc_gradChiMK_comp_contDiffOn (κm : ℝ) (k l : ℤ) (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      gradMatrix (fun z => I.chiMK κm m k p.1 z) (I.xFlowInv hΦ m l p.1 p.2) i j) tcU := by
  have h0 : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.chiMK κm m k p.1 p.2 j) tcU :=
    (Infra.Section3.chiMK_component_contDiff_two I κm k j).contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 =>
      spaceGrad (fun z => I.chiMK κm m k p.1 z j) p.2 i) tcU :=
    tc_spaceGrad_contDiffOn (F := fun t z => I.chiMK κm m k t z j) (m := 1) (n := 2)
      (by norm_num) h0 i
  exact tc_comp_xFlowInv I hΦ m l (n := 1) (by simp)
    (f := fun t w => spaceGrad (fun z => I.chiMK κm m k t z j) w i) h1

/-- The Jacobian of the inverse flow is jointly `C^∞`. -/
theorem tc_gradXInv_contDiffOn (l : ℤ) (i a : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      gradMatrix (fun z => I.xFlowInv hΦ m l p.1 z) p.2 i a) tcU :=
  Integration.contDiffOn_spaceGrad_slice_Ioi (F := fun t z => I.xFlowInv hΦ m l t z a)
    (((contDiff_apply ℝ ℝ a).comp
      (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m l)).contDiffOn) i

end AVenhance.Infra.Section5.Contracts
