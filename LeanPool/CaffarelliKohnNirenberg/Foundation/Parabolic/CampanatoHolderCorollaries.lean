/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.CampanatoHolderFinal

public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn

/-!
# Campanato Holder Corollaries

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic


theorem campanato_holder_local
    {f : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {R α K p : ℝ}
    (hα : 0 < α) (_ : α < 1) (hR : 0 < R) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : LocallyIntegrable f volume)
    (hdata : ParabolicBallLpDataOn f (Metric.ball z₀ R) (8 * R) p)
    (hcamp : ParabolicBallCampanatoBoundOn f (Metric.ball z₀ R) (8 * R) α K p) :
    ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume.restrict (Metric.ball z₀ (R / 2))] f ∧
      ParabolicHolderSeminormLE (Metric.ball z₀ (R / 2)) g α
        (parabolicCampanatoHolderConstant α p * K) := by
  let S : ℝ := 8 * R
  let V : Set ParabolicPoint := Metric.ball z₀ (R / 2)
  let g : ParabolicPoint → ℝ := parabolicBallRepresentative f S
  have hS : 0 < S := by dsimp [S]; positivity
  have hU : ∀ z ∈ V, z ∈ Metric.ball z₀ R := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hz' : dist z₀ z < R / 2 := by simpa [dist_comm] using hz
    linarith only [hz, hR]
  have hdist : ∀ z ∈ V, ∀ z' ∈ V, dist z z' < S / 4 := by
    intro z hz z' hz'
    have hz0 : dist z z₀ < R / 2 := by simpa [V, Metric.mem_ball] using hz
    have hz0' : dist z' z₀ < R / 2 := by simpa [V, Metric.mem_ball] using hz'
    have htri : dist z z' < R := by
      calc
        dist z z' ≤ dist z z₀ + dist z₀ z' := dist_triangle z z₀ z'
        _ < R := by simpa [dist_comm] using add_lt_add hz0 hz0'
    dsimp [S]
    linarith only [htri, hR]
  have hgeq : g =ᵐ[volume.restrict V] f := by
    apply ae_restrict_of_ae
    exact parabolicBallRepresentative_ae_eq_of_locallyIntegrable hS hf
  refine ⟨g, hgeq, ?_⟩
  intro z hz z' hz'
  exact parabolicBallRepresentative_holder_at_scale hα hS hp hK hcamp hdata
    z (hU z hz) z' (hU z' hz') (hdist z hz z' hz')


end CKN.Foundation.Parabolic
