/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.Decay
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.ProductH1
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DeltaPCentred
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials

/-!
# Pressure Gradient Base

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The distributional pressure-Laplacian pairing. -/

/-- Distributional pressure Poisson identity on a spatial domain, retaining the force
contribution. -/
def HasPressureDeltaOn {U : Set Vec3} (p : Vec3 → ℝ)
    (u : Vec3 → Vec3) (f : Vec3 → Vec3) : Prop :=
  ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x in U, p x * spatialLaplacian ψ x =
      -(∫ x in U, ∑ i, ∑ j, u x i * u x j * mixedSecond ψ i j x) -
        (∫ x in U, ∑ i, f x i * spatialDeriv ψ i x)

theorem pressure_gradient_one_scale
    {i : Fin 3} {ρ C_CZ C_H : ℝ} (_ : 0 < ρ)
    {G p : Vec3 → ℝ} {D gp gh : Vec3 → Vec3} {x₀ : Vec3}
    (_ : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (_ : HasCompactSupport G)
    (_ : MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (_ : ∀ (j : Fin 3) (ψ : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        -(∫ x, D x j * ψ x))
    (hrepresentation : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ (ρ / 2)),
      gp x = D x + gh x)
    (hD_bound : eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hgh : eLpNorm gh (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal C_H * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ))) :
    eLpNorm gp (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume +
        ENNReal.ofReal C_H * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  let μ : Measure Vec3 := volume.restrict (euclideanBall x₀ (ρ / 2))
  have hlocal : eLpNorm D
      (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have htri := eLpNorm_add_le (μ := μ)
    (f := D) (g := gh)
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (by norm_num)
  have hrep : eLpNorm gp (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) μ + eLpNorm gh
          (ENNReal.ofReal (6 / 5 : ℝ)) μ := by
    rw [eLpNorm_congr_ae hrepresentation]
    exact htri
  dsimp [μ] at hrep hlocal
  have hpart : eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    hlocal.trans hD_bound
  dsimp [μ] at hpart
  exact hrep.trans (add_le_add hpart hgh)

end CKN.Core.Step4
