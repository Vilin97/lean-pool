/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds

/-!
# The right-hand integrand of the local energy inequality

The local energy inequality of `def:sws` carries a second integrability side
condition, on the integrand of its right-hand side.  That integrand has three
groups of terms, all of them tested against the closed support of the test
function `ψ`:

* the heat-operator term `|u|² (∂ₜψ + Δψ)`;
* the flux term `(|u|² + 2p) (u · ∇ψ)`;
* the force term `2 (f · u) ψ`.

This file proves that side condition from the data clauses alone.

The first group needs only that the velocity is square integrable on a compact
set, which the finite joint energy of the data clauses already gives.  The other
two are the reason the parabolic interpolation of
`CKN/ClassEquivalence/VelocityTenThirds.lean` is needed at all: the cubic
density `|u|² uᵢ` and the pressure-velocity density `p uᵢ` are not controlled by
square integrability, and are obtained there from the local `L³` bound on the
velocity, the pressure exponent `3 / 2` and the Hölder pairing `2 / 3 + 1 / 3 = 1`.
The force term uses the same pairing, the force exponent of `def:sws` being
larger than `3 / 2`.

Each group is then an integrable density times a bounded derivative of the test
function, and the three are added.  The energy density of the paper is the
Euclidean norm `CKN.Foundation.Parabolic.vec3EuclideanNorm`, while the data
clauses are stated with the supremum norm of `Vec3`; only the easy direction of
the equivalence of the two norms is used.

Nothing about the identities of `def:sws` is used, so the conclusion is
available while those identities are still being established.  In particular the
nonnegativity of the test function that the clause also assumes is not
needed for integrability and is omitted here.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
variable {K : Set ParabolicPoint}

/-! ### The densities of the right-hand side on a compact set -/

/-- The squared Euclidean norm is bounded by three times the squared supremum
norm.  This is the easy direction of the equivalence of the two norms of `Vec3`,
in the form the energy density needs. -/
private theorem vec3EuclideanNorm_sq_le_three_mul_norm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ (2 : ℕ) ≤ 3 * ‖v‖ ^ (2 : ℕ) := by
  have hpow : vec3EuclideanNorm v ^ (2 : ℕ) ≤ (Real.sqrt 3 * ‖v‖) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v)
      (vec3EuclideanNorm_le_sqrt_three_mul_norm v) 2
  have hs : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  calc vec3EuclideanNorm v ^ (2 : ℕ) ≤ (Real.sqrt 3 * ‖v‖) ^ (2 : ℕ) := hpow
    _ = 3 * ‖v‖ ^ (2 : ℕ) := by rw [mul_pow, hs]

/-- The energy density `|u|²` of the local energy inequality is integrable on
every compact subset of the space-time carrier: the velocity is square
integrable there by the data clauses. -/
theorem velocity_energyDensity_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) K volume := by
  have hu2 : MemLp u 2 (volume.restrict K) :=
    velocity_memLp_two_on_compact_of_data hdata hK hKsub
  have hsq : Integrable (fun z => ‖u z‖ ^ (2 : ℕ)) (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).1 hu2
  have hmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z) ^ (2 : ℕ))
      (volume.restrict K) :=
    (continuous_vec3EuclideanNorm.pow 2).comp_aestronglyMeasurable hu2.aestronglyMeasurable
  refine (hsq.const_mul 3).mono hmeas (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg _) 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * ‖u z‖ ^ (2 : ℕ))]
  exact vec3EuclideanNorm_sq_le_three_mul_norm_sq (u z)

/-- The cubic density `|u|² uᵢ` of the flux term is integrable on every compact
subset of the space-time carrier: it is bounded in absolute value by `|u|³`,
which the parabolic interpolation controls there. -/
theorem velocity_energyDensity_mul_component_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i : Fin 3) :
    IntegrableOn (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z i) K volume := by
  have hcube := velocity_cube_integrableOn_compact_of_data hdata hK hKsub
  have hu3 := velocity_memLp_three_on_compact_of_data hdata hK hKsub
  have hmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z i)
      (volume.restrict K) :=
    ((continuous_vec3EuclideanNorm.pow 2).comp_aestronglyMeasurable
      hu3.aestronglyMeasurable).mul (memLp_pi_iff.mp hu3 i).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono hcube hmeas
    (Filter.Eventually.of_forall fun z => ?_)
  have hnn := vec3EuclideanNorm_nonneg (u z)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg hnn 2), abs_of_nonneg (pow_nonneg hnn 3)]
  calc vec3EuclideanNorm (u z) ^ (2 : ℕ) * |u z i|
      ≤ vec3EuclideanNorm (u z) ^ (2 : ℕ) * vec3EuclideanNorm (u z) := by
        gcongr
        exact abs_apply_le_vec3EuclideanNorm (u z) i
    _ = vec3EuclideanNorm (u z) ^ (3 : ℕ) := by ring

/-- The whole density `(|u|² + 2p) uᵢ` of the flux term of the local energy
inequality is integrable on every compact subset of the space-time carrier. -/
theorem energyFlux_component_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i : Fin 3) :
    IntegrableOn (fun z => (vec3EuclideanNorm (u z) ^ (2 : ℕ) + 2 * p z) * u z i)
      K volume := by
  have hcubic :=
    velocity_energyDensity_mul_component_integrableOn_compact_of_data hdata hK hKsub i
  have hpress :=
    (pressure_mul_velocity_integrableOn_compact_of_data hdata hK hKsub i).const_mul 2
  refine (hcubic.add hpress).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  ring

/-- The density `f · u` of the force term of the local energy inequality is
integrable on every compact subset of the space-time carrier. -/
theorem force_dot_velocity_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => ∑ i, f z i * u z i) K volume :=
  integrable_finsetSum Finset.univ fun i _ =>
    force_mul_velocity_integrableOn_compact_of_data hdata hK hKsub i i

/-! ### The three groups of terms -/

section Terms

variable (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
  (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
  {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)

include hdata hK hKsub hψ

/-- The heat-operator term `|u|² (∂ₜψ + Δψ)` of the right-hand side is
integrable on a compact subset of the carrier. -/
theorem localEnergy_heatTerm_integrableOn_of_data :
    IntegrableOn (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)) K volume := by
  have hden := velocity_energyDensity_integrableOn_compact_of_data hdata hK hKsub
  have htime : IntegrableOn
      (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) * timePartial ψ z) K volume := by
    obtain ⟨Ct, hCt⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
    exact hden.mul_bdd (c := Ct) (g := fun z : ParabolicPoint => timePartial ψ z)
      (contDiff_timePartial hψ.1).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hCt z)
  have hlaplace : IntegrableOn
      (fun z => ∑ i, vec3EuclideanNorm (u z) ^ (2 : ℕ) * spatialSecondPartial ψ i i z)
      K volume := by
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    obtain ⟨C, hC⟩ := exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ i i
    exact hden.mul_bdd (c := C)
      (g := fun z : ParabolicPoint => spatialSecondPartial ψ i i z)
      (spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i)
        i).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  refine (htime.add hlaplace).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, mul_add, Finset.mul_sum]

/-- The flux term `(|u|² + 2p) (u · ∇ψ)` of the right-hand side is integrable on
a compact subset of the carrier. -/
theorem localEnergy_fluxTerm_integrableOn_of_data :
    IntegrableOn (fun z => (vec3EuclideanNorm (u z) ^ (2 : ℕ) + 2 * p z) *
      ∑ i, u z i * spatialPartial ψ i z) K volume := by
  have hterms : IntegrableOn (fun z => ∑ i,
      (vec3EuclideanNorm (u z) ^ (2 : ℕ) + 2 * p z) * u z i * spatialPartial ψ i z)
      K volume := by
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    exact (energyFlux_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
      (c := C) (g := fun z : ParabolicPoint => spatialPartial ψ i z)
      (spatialPartial_contDiff hψ.1 i).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  refine hterms.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Finset.mul_sum, mul_assoc]

/-- The force term `2 (f · u) ψ` of the right-hand side is integrable on a
compact subset of the carrier. -/
theorem localEnergy_forceTerm_integrableOn_of_data :
    IntegrableOn (fun z => 2 * (∑ i, f z i * u z i) * ψ z) K volume := by
  obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
  exact ((force_dot_velocity_integrableOn_compact_of_data hdata hK hKsub).const_mul
    2).mul_bdd (c := C) (g := fun z : ParabolicPoint => ψ z)
    hψ.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

end Terms

/-! ### The right-hand integrand -/

/-- The integrand of the right-hand side of the local energy inequality of
`def:sws` is integrable on the closed support of the test function.  Only the
data clauses are used, so the conclusion is available while the identities of
`def:sws` are still being established. -/
theorem localEnergy_integrand_integrableOn_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun z =>
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψ i z
          + 2 * (∑ i, f z i * u z i) * ψ z)
      (tsupport ψ) volume := by
  have hK : IsCompact (tsupport (show ParabolicPoint → ℝ from ψ)) :=
    isCompact_tsupport_parabolic hψ.2.1
  have hKsub : tsupport (show ParabolicPoint → ℝ from ψ) ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  exact ((localEnergy_heatTerm_integrableOn_of_data hdata hK hKsub hψ).add
    (localEnergy_fluxTerm_integrableOn_of_data hdata hK hKsub hψ)).add
    (localEnergy_forceTerm_integrableOn_of_data hdata hK hKsub hψ)

end CKN
