/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DissipationIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.EnergyIntegrand

/-!
# The integrability clauses of `def:sws` are redundant

Each of the three identity clauses of `CKN.IsSuitableWeakSolutionIntegrable` pairs an
identity with an integrability side condition on the integrand that identity
tests; the local energy inequality carries two such side conditions, one for
each side.  The four preceding files prove all four of them from the data
clauses alone.  This file puts them together: to exhibit a suitable weak
solution it is enough to supply the data clauses and the three bare identities.

## Why the order of the proof matters

The Bochner integral of a function that is not integrable is `0` by convention.
An identity such as `∫ z in spaceTimeSet Ω I, ∑ i, u z i * ∂ᵢψ z = 0` therefore
says nothing on its own: it also holds, vacuously, when the integrand is not
integrable.  A constructor that consumed such an identity before knowing the
integrand to be integrable would be proving the class from a hypothesis that is
weaker than it looks.

`CKN.isSuitableWeakSolutionIntegrable_of_identities` avoids this.  It calls the four
clause lemmas first, and those lemmas read only the data clauses; they never
look at the value of an integral.  By the time each identity is consumed its
integrand is already known to be integrable, so the integral appearing in it is
a genuine Bochner integral and not the junk value.

For the same reason the identities are stated here with the integral written
exactly as the clauses write it, over `spaceTimeSet Ω I`.  No transport
between forms of the integral is then needed, and the proof below is a plain
rearrangement of conjunctions.  A caller who holds an identity in another form,
for instance over the closed support of the test function or over the whole
space-time, has to transport it, and that transport is legal only once the
integrability is in hand - which is exactly what these lemmas supply.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- The data clauses of `def:sws` together with the three bare identities - the
divergence-free identity, the weak momentum identity and the local energy
inequality, each stated without its integrability side condition - already give
a suitable weak solution.

The four integrability side conditions of the class are supplied by the clause
lemmas, which use the data clauses only.  They are established before any of
`hdiv`, `hmom` and `hlei` is consumed, so no identity here is read at a junk
value of the Bochner integral. -/
theorem isSuitableWeakSolutionIntegrable_of_identities
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    (hmom : ∀ φ : Vec3 × ℝ → Vec3, φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i = 0)
    (hlei : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z) :
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f :=
  ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2.1,
    hdata.2.2.2.2.2,
    fun ψ hψ =>
      ⟨divergenceFree_integrand_integrableOn_of_data hdata hψ, hdiv ψ hψ⟩,
    fun φ hφ =>
      ⟨momentum_integrand_integrableOn_of_data hdata hφ, hmom φ hφ⟩,
    fun ψ hψ hnn =>
      ⟨dissipation_integrand_integrableOn_of_data hdata hψ,
        localEnergy_integrand_integrableOn_of_data hdata hψ,
        hlei ψ hψ hnn⟩⟩

/-- The suitable weak-solution class of `def:sws` is equivalent to its data
clauses together with the three bare identities.  This is the precise sense in
which the four integrability conjuncts of the class are redundant: they are
consequences of the measurability and local integrability recorded by the data
clauses, and carrying them in the definition assumes nothing extra. -/
theorem isSuitableWeakSolutionIntegrable_iff_identities :
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f ↔
      (IsSuitableWeakSolutionData Ω I q u Du p f ∧
      (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0) ∧
      (∀ φ : Vec3 × ℝ → Vec3, φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
        ∫ z in spaceTimeSet Ω I,
          (-(∑ i, u z i * timePartial (fun w => φ w i) z))
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i = 0) ∧
      (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        (∀ z, 0 ≤ ψ z) →
        2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
          ∫ z in spaceTimeSet Ω I,
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψ i z
              + 2 * (∑ i, f z i * u z i) * ψ z)) :=
  ⟨fun h => ⟨h.toData,
      fun ψ hψ => (h.2.2.2.2.2.2.1 ψ hψ).2,
      fun φ hφ => (h.2.2.2.2.2.2.2.1 φ hφ).2,
      fun ψ hψ hnn => (h.2.2.2.2.2.2.2.2 ψ hψ hnn).2.2⟩,
    fun h => isSuitableWeakSolutionIntegrable_of_identities h.1 h.2.1 h.2.2.1 h.2.2.2⟩

end CKN
