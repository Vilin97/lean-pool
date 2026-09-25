/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-! # Quantitative Morrey improvement for symmetric source carriers

A symmetric parabolic ball lies in a backward cylinder whose top time is
shifted forward. The quantitative potential estimate is independent of this
enlargement, so its numerical coefficient is unchanged.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- Component sources supported in a symmetric metric ball yield the same
numerical Morrey improvement as sources in a backward cylinder. -/
theorem bootstrap_morrey_le_of_component_sources_on_ball
    (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i, AEMeasurable (fun z => h j z i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (25 / 11) (fun z => g z i) ≤ KF)
    (hNG : ∀ j i, morreyNorm 3 (25 / 6) (fun z => h j z i) ≤ KG)
    (hgsupp : ∀ z ∉ Metric.ball z₀ R, g z = 0)
    (hhsupp : ∀ j z, z ∉ Metric.ball z₀ R → h j z = 0)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) ≤
      bootstrapSourceMorreyBound (3 * KF) (3 * KG) := by
  apply bootstrap_morrey_le_of_component_sources KF KG hKF hKG
    (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R) (by positivity)
    hg hh hNF hNG
  · intro z hz
    exact hgsupp z (fun hmem => hz
      (metricBall_subset_parabolicCylinder_doubled z₀ hR hmem))
  · intro j z hz
    exact hhsupp j z (fun hmem => hz
      (metricBall_subset_parabolicCylinder_doubled z₀ hR hmem))
  · exact hrep

end CKN.Core.Endgame
