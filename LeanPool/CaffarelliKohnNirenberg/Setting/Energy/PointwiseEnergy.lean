/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# Pointwise Energy

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The time derivative on the explicit space-time product carrier. -/
@[expose]
def timePartialProd (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  timePartial (show ParabolicPoint → ℝ from g) z

/-- The spatial derivative on the explicit space-time product carrier. -/
@[expose]
def spatialPartialProd (g : Vec3 × ℝ → ℝ) (i : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  spatialPartial (show ParabolicPoint → ℝ from g) i z

/-- The iterated spatial derivative on the explicit product carrier. -/
@[expose]
def spatialSecondPartialProd (g : Vec3 × ℝ → ℝ)
    (i j : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  spatialSecondPartial (show ParabolicPoint → ℝ from g) i j z

/-- The right-hand energy density in the local energy inequality. -/
@[expose]
def localEnergyRhs
    (u : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → Vec3) (ψ : Vec3 × ℝ → ℝ)
  (z : Vec3 × ℝ) : ℝ :=
  (vec3EuclideanNorm (u z)) ^ 2 *
      (timePartialProd ψ z + ∑ i, spatialSecondPartialProd ψ i i z)
    + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
        ∑ i, u z i * spatialPartialProd ψ i z
    + 2 * (∑ i, f z i * u z i) * ψ z

/-- The suitable-solution energy inequality, with its density named. -/
theorem suitableWeakSolution_energyInequality
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
      ∫ z in spaceTimeSet Ω I, localEnergyRhs u p f ψ z := by
  rcases hsol with ⟨_, _, _, _, _, _, _, _, henergy⟩
  simpa only [localEnergyRhs, timePartialProd, spatialSecondPartialProd,
    spatialPartialProd] using (henergy ψ hψ hψ_nonneg).2.2

end CKN
