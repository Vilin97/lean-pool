/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Continuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientWords

/-! Joint continuity of the actual sMat spatial jets from conditional flow jets.
The time cutoff sum is represented locally by a fixed finite sum. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesCoefficientContinuity.iterate_hatXi_active_distance {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ) (hne : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ 1 / 2 * tauPP β I.Λ m + tauP β I.Λ m := by
  have hle := I.hatXi_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatXi m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatXi_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-- Continuity of all actual sMat word jets. The conditional premise is joint
smoothness of the actual flow Jacobians; K and cutoff continuity are proved. -/
theorem iterate_sMat_word_joint_continuousOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (i j : Fin 2) :
    ContinuousOn (fun z : AmnrSpace => iterateSpatialWord w
      (fun y => I.sMat hΦ m κm z.1 y i j) z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  exact (sMat_coarseCoeffForm I hΦ m κm).word_joint_continuousOn hm hκm hflow w i j

/-- Matrix-valued joint continuity of the actual coefficient jet. -/
theorem iterate_sMat_matrixWord_joint_continuousOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (I.sMat hΦ m κm z.1) w z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact iterate_sMat_word_joint_continuousOn I hΦ hm hκm hflow w i j

end AVenhance.Infra.Section4
