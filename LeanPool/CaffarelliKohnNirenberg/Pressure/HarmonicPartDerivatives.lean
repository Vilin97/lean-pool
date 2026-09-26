/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationHarmonic

/-!
# Harmonic Part Derivatives

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-- The harmonic pressure part appearing in the local decomposition. -/
@[expose]
def harmonicPressurePart (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (c : ℝ → Vec3) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ :=
  pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
    pressureP5 η p s + pressureP6 η p s

/-- The annular pressure terms are weakly harmonic wherever their source data
vanish. -/
theorem harmonicPressurePart_weaklyHarmonicOn_of_data
    {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3}
    {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hdata : PressureHarmonicPotentialData U η u c p s) :
    WeaklyHarmonicOn U (harmonicPressurePart η u c p s) := by
  simpa only [harmonicPressurePart] using
    pressure_harmonic_potentials_weaklyHarmonicOn_of_data hdata

/-- A weakly harmonic pressure part has the available smooth inner
representative together with its value and gradient estimates. -/
theorem harmonicPressurePart_inner_representative
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (ρ / 2)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))] H ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        |H x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
          1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
  exact pressure_harmonic_part_on_inner hρ hmem hweak

end CKN
