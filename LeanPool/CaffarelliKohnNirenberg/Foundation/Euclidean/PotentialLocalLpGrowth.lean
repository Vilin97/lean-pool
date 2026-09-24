/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLp
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayFarField

/-!
# Local `L^{3/2}` membership and linear growth for Newtonian potentials

The uniqueness half of the Newtonian representation `ext:newtonian` of the paper applies
Liouville's theorem to a function that is `L^{3/2}` on every round ball `euclideanBall 0 ρ` with
norm growing at most like `1 + ρ`.  This file produces exactly that pair of statements for the
Newtonian potential `N * g` and for the first-derivative potential `∂ⱼN * g` of data `g` that is
compactly supported and of class `L^q`.

The near-field half is Young's inequality on a ball
(`CKN.Foundation.Euclidean.PotentialLocalLp`); the far-field half is the pointwise decay
`|N * g| ≲ ‖g‖_{L¹} ‖x‖⁻¹`, `|∂ⱼN * g| ≲ ‖g‖_{L¹} ‖x‖⁻²` of
`CKN.Pressure.PotentialDecayFarField`.  The two are combined by the splitting estimate of
`CKN.Pressure.PotentialDecay`, which is where the factor `1 + ρ` comes from: the inverse-distance
profile `‖x‖⁻¹` has `L^{3/2}` norm proportional to `ρ` on the ball of radius `ρ`.

All the estimates are stated for exponents `q ≥ 6/5`, which covers the exponent `3/2` of the
pressure and the exponents `q > 5/2` of the force datum of `def:sws`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! ### The explicit constants -/

/-- The far-field decay constant of the Newtonian potential of `G`: the potential is bounded by
this constant times `‖x‖⁻¹` outside the support ball. -/
def newtonianPotentialDecayConstant (G : Vec3 → ℝ) : ℝ :=
  2 * (4 * Real.pi)⁻¹ * ∫ y, |G y|

/-- The far-field decay constant of the first-derivative Newtonian potential of `G` on the
region `2 * R ≤ ‖x‖`, measured against `‖x‖⁻¹`. -/
def newtonianDerivativePotentialDecayConstant (G : Vec3 → ℝ) (R : ℝ) : ℝ :=
  4 * (4 * Real.pi)⁻¹ * (∫ y, |G y|) / (2 * R)

/-- The linear-growth constant of the Newtonian potential of data supported in the closed ball
of radius `R`: the local `L^{3/2}` norm near the origin plus the far-field decay constant times
the universal ball constant. -/
def newtonianPotentialGrowthConstant (G : Vec3 → ℝ) (R : ℝ) : ℝ :=
  invNormGrowthConstant (pressureNewtonianPotential G) (newtonianPotentialDecayConstant G) R

/-- The linear-growth constant of the first-derivative Newtonian potential of data supported in
the closed ball of radius `R`. -/
def newtonianDerivativePotentialGrowthConstant (i : Fin 3) (G : Vec3 → ℝ) (R : ℝ) : ℝ :=
  invNormGrowthConstant (pressureNewtonianDerivativePotential i G)
    (newtonianDerivativePotentialDecayConstant G R) R

theorem newtonianPotentialDecayConstant_nonneg (G : Vec3 → ℝ) :
    0 ≤ newtonianPotentialDecayConstant G := by
  have hint : (0 : ℝ) ≤ ∫ y, |G y| :=
    integral_nonneg fun _ => abs_nonneg _
  have hpi : (0 : ℝ) ≤ 2 * (4 * Real.pi)⁻¹ := by positivity
  exact mul_nonneg hpi hint

theorem newtonianDerivativePotentialDecayConstant_nonneg {R : ℝ} (hR : 0 < R)
    (G : Vec3 → ℝ) : 0 ≤ newtonianDerivativePotentialDecayConstant G R := by
  have hint : (0 : ℝ) ≤ ∫ y, |G y| :=
    integral_nonneg fun _ => abs_nonneg _
  have hnum : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * ∫ y, |G y| := by
    have hpi : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
    exact mul_nonneg hpi hint
  have hden : (0 : ℝ) < 2 * R := by linarith only [hR]
  exact div_nonneg hnum hden.le

theorem newtonianPotentialGrowthConstant_nonneg (G : Vec3 → ℝ) (R : ℝ) :
    0 ≤ newtonianPotentialGrowthConstant G R :=
  invNormGrowthConstant_nonneg (newtonianPotentialDecayConstant_nonneg G)

theorem newtonianDerivativePotentialGrowthConstant_nonneg (i : Fin 3) {R : ℝ} (hR : 0 < R)
    (G : Vec3 → ℝ) : 0 ≤ newtonianDerivativePotentialGrowthConstant i G R :=
  invNormGrowthConstant_nonneg (newtonianDerivativePotentialDecayConstant_nonneg hR G)

/-! ### The far-field decay in the shape required by the growth estimate -/

/-- Data vanishing off a closed ball has its topological support inside that ball. -/
theorem tsupport_subset_closedBall_of_zero_outside {G : Vec3 → ℝ} {R : ℝ}
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    tsupport G ⊆ closedBall (0 : Vec3) R := by
  refine closure_minimal ?_ isClosed_closedBall
  intro y hy
  by_contra hy'
  exact hy (hGzero y hy')

/-- Inverse-distance decay of the Newtonian potential of compactly supported integrable data. -/
theorem pressureNewtonianPotential_inv_norm_decay {G : Vec3 → ℝ} {R : ℝ} (hR : 0 < R)
    (hG : Integrable G volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ∀ x : Vec3, 2 * R ≤ ‖x‖ →
      |pressureNewtonianPotential G x| ≤ newtonianPotentialDecayConstant G * ‖x‖⁻¹ := by
  intro x hx
  have hsupp := tsupport_subset_closedBall_of_zero_outside hGzero
  have hx' : 2 * R ≤ ‖x - (0 : Vec3)‖ := by simpa only [sub_zero] using hx
  have hb := pressureNewtonianPotential_tail_bound_centre hG hR hsupp hx'
  rw [sub_zero] at hb
  refine hb.trans_eq ?_
  rw [newtonianPotentialDecayConstant, div_eq_mul_inv]
  ring

/-- Inverse-distance decay of the first-derivative Newtonian potential of compactly supported
integrable data.  The kernel decays like `‖x‖⁻²`, which on the far region `2 * R ≤ ‖x‖` is
stronger than the inverse-distance decay used by the growth estimate. -/
theorem pressureNewtonianDerivativePotential_inv_norm_decay {G : Vec3 → ℝ} (i : Fin 3) {R : ℝ}
    (hR : 0 < R) (hG : Integrable G volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    ∀ x : Vec3, 2 * R ≤ ‖x‖ →
      |pressureNewtonianDerivativePotential i G x| ≤
        newtonianDerivativePotentialDecayConstant G R * ‖x‖⁻¹ := by
  have hsupp := tsupport_subset_closedBall_of_zero_outside hGzero
  have hA : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * ∫ y, |G y| := by
    have hint : (0 : ℝ) ≤ ∫ y, |G y| := integral_nonneg fun _ => abs_nonneg _
    have hpi : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
    exact mul_nonneg hpi hint
  have hsq : ∀ x : Vec3, 2 * R ≤ ‖x - (0 : Vec3)‖ →
      |pressureNewtonianDerivativePotential i G x| ≤
        (4 * (4 * Real.pi)⁻¹ * ∫ y, |G y|) / ‖x - (0 : Vec3)‖ ^ 2 := by
    intro x hx
    refine (pressureNewtonianDerivativePotential_tail_bound_centre hG hR hsupp i hx).trans_eq ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hdecay := inv_norm_decay_of_div_norm_sq (h := pressureNewtonianDerivativePotential i G)
    (x₀ := (0 : Vec3)) hR hA hsq
  intro x hx
  have hx' : 2 * R ≤ ‖x - (0 : Vec3)‖ := by simpa only [sub_zero] using hx
  have hb := hdecay x hx'
  rw [sub_zero] at hb
  exact hb

/-! ### Local membership and linear growth, for measurable data -/

/-- The Newtonian potential of compactly supported `L^{6/5}` data is `L^{3/2}` on every round
ball about the origin, with `L^{3/2}` norm at most `C * (1 + ρ)`. -/
theorem pressureNewtonianPotential_memLp_and_lpNorm_growth
    {G : Vec3 → ℝ} {R : ℝ} (hR : 0 < R) (hGmeas : Measurable G)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianPotentialGrowthConstant G R * (1 + ρ) := by
  have hint : Integrable G volume :=
    memLp_one_iff_integrable.1
      (memLp_of_memLp_of_support_closedBall (p := (1 : ℝ≥0∞))
        (ENNReal.one_le_ofReal.2 (by norm_num)) hG hGzero)
  have hnear : MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (ball (0 : Vec3) (2 * R))) := by
    refine pressureNewtonianPotential_memLp_ball ?_ hGmeas hG hGzero
    linarith only [hR]
  exact memLp_and_lpNorm_linear_growth_of_inv_norm_decay
    (newtonianPotentialDecayConstant_nonneg G)
    (aestronglyMeasurable_pressureNewtonianPotential hGmeas) hnear
    (pressureNewtonianPotential_inv_norm_decay hR hint hGzero)

/-- The first-derivative Newtonian potential of compactly supported `L^{6/5}` data is `L^{3/2}`
on every round ball about the origin, with `L^{3/2}` norm at most `C * (1 + ρ)`. -/
theorem pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth
    {G : Vec3 → ℝ} (i : Fin 3) {R : ℝ} (hR : 0 < R) (hGmeas : Measurable G)
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianDerivativePotentialGrowthConstant i G R * (1 + ρ) := by
  have hint : Integrable G volume :=
    memLp_one_iff_integrable.1
      (memLp_of_memLp_of_support_closedBall (p := (1 : ℝ≥0∞))
        (ENNReal.one_le_ofReal.2 (by norm_num)) hG hGzero)
  have hnear : MemLp (pressureNewtonianDerivativePotential i G) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (ball (0 : Vec3) (2 * R))) :=
    pressureNewtonianDerivativePotential_memLp_ball i hR (by linarith only [hR]) hGmeas hG hGzero
  exact memLp_and_lpNorm_linear_growth_of_inv_norm_decay
    (newtonianDerivativePotentialDecayConstant_nonneg hR G)
    (aestronglyMeasurable_pressureNewtonianDerivativePotential i hGmeas) hnear
    (pressureNewtonianDerivativePotential_inv_norm_decay i hR hint hGzero)

/-! ### Local membership and linear growth, for `L^q` data with `q ≥ 6/5`

The force datum of `def:sws` is only almost everywhere strongly measurable, so the estimates are
restated for such data by passing to the measurable representative supported in the same ball;
neither the potentials nor the constants change. -/

/-- Almost-everywhere equal data has the same Newtonian decay constant. -/
theorem newtonianPotentialDecayConstant_congr {G G' : Vec3 → ℝ} (h : G =ᵐ[volume] G') :
    newtonianPotentialDecayConstant G = newtonianPotentialDecayConstant G' := by
  have hint : (∫ y, |G y|) = ∫ y, |G' y| := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  rw [newtonianPotentialDecayConstant, newtonianPotentialDecayConstant, hint]

/-- Almost-everywhere equal data has the same derivative-potential decay constant. -/
theorem newtonianDerivativePotentialDecayConstant_congr {G G' : Vec3 → ℝ} (R : ℝ)
    (h : G =ᵐ[volume] G') :
    newtonianDerivativePotentialDecayConstant G R =
      newtonianDerivativePotentialDecayConstant G' R := by
  have hint : (∫ y, |G y|) = ∫ y, |G' y| := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  rw [newtonianDerivativePotentialDecayConstant, newtonianDerivativePotentialDecayConstant, hint]

/-- The Newtonian potential of compactly supported `L^q` data with `6/5 ≤ q` is `L^{3/2}` on
every round ball about the origin, with `L^{3/2}` norm at most `C * (1 + ρ)`.  This is the pair
of hypotheses consumed by the Liouville step of `ext:newtonian`. -/
theorem pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp
    {G : Vec3 → ℝ} {R q : ℝ} (hR : 0 < R) (hq : 6 / 5 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianPotentialGrowthConstant G R * (1 + ρ) := by
  obtain ⟨G', hG'meas, hGG', hG'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hG.aestronglyMeasurable hGzero
  have hG'q : MemLp G' (ENNReal.ofReal q) volume := hG.ae_eq hGG'
  have hG'65 : MemLp G' (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    memLp_six_fifths_of_memLp_ofReal hq hG'q hG'zero
  have hPeq : pressureNewtonianPotential G = pressureNewtonianPotential G' :=
    pressureNewtonianPotential_congr_of_ae_eq hGG'
  have hCeq : newtonianPotentialGrowthConstant G R = newtonianPotentialGrowthConstant G' R := by
    rw [newtonianPotentialGrowthConstant, newtonianPotentialGrowthConstant, hPeq,
      newtonianPotentialDecayConstant_congr hGG']
  rw [hPeq, hCeq]
  exact pressureNewtonianPotential_memLp_and_lpNorm_growth hR hG'meas hG'65 hG'zero

/-- The first-derivative Newtonian potential of compactly supported `L^q` data with `6/5 ≤ q` is
`L^{3/2}` on every round ball about the origin, with `L^{3/2}` norm at most `C * (1 + ρ)`. -/
theorem pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp
    {G : Vec3 → ℝ} (i : Fin 3) {R q : ℝ} (hR : 0 < R) (hq : 6 / 5 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianDerivativePotentialGrowthConstant i G R * (1 + ρ) := by
  obtain ⟨G', hG'meas, hGG', hG'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hG.aestronglyMeasurable hGzero
  have hG'q : MemLp G' (ENNReal.ofReal q) volume := hG.ae_eq hGG'
  have hG'65 : MemLp G' (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    memLp_six_fifths_of_memLp_ofReal hq hG'q hG'zero
  have hPeq : pressureNewtonianDerivativePotential i G =
      pressureNewtonianDerivativePotential i G' :=
    pressureNewtonianDerivativePotential_congr_of_ae_eq i hGG'
  have hCeq : newtonianDerivativePotentialGrowthConstant i G R =
      newtonianDerivativePotentialGrowthConstant i G' R := by
    rw [newtonianDerivativePotentialGrowthConstant,
      newtonianDerivativePotentialGrowthConstant, hPeq,
      newtonianDerivativePotentialDecayConstant_congr R hGG']
  rw [hPeq, hCeq]
  exact pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth i hR hG'meas hG'65 hG'zero

/-! ### The two exponents used by the pressure decomposition -/

/-- The `q = 3/2` instance, the exponent of the pressure in `def:sws`. -/
theorem pressureNewtonianPotential_memLp_and_lpNorm_growth_three_halves
    {G : Vec3 → ℝ} {R : ℝ} (hR : 0 < R)
    (hG : MemLp G (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianPotentialGrowthConstant G R * (1 + ρ) :=
  pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp hR (by norm_num) hG hGzero

/-- The `5/2 < q` instance, the exponent range of the force datum in `def:sws`. -/
theorem pressureNewtonianPotential_memLp_and_lpNorm_growth_of_five_halves_lt
    {G : Vec3 → ℝ} {R q : ℝ} (hR : 0 < R) (hq : 5 / 2 < q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential G) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianPotentialGrowthConstant G R * (1 + ρ) :=
  pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp hR
    (by linarith only [hq]) hG hGzero

/-- The `q = 3/2` instance for the first-derivative potential. -/
theorem pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_three_halves
    {G : Vec3 → ℝ} (i : Fin 3) {R : ℝ} (hR : 0 < R)
    (hG : MemLp G (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianDerivativePotentialGrowthConstant i G R * (1 + ρ) :=
  pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp i hR (by norm_num)
    hG hGzero

/-- The `5/2 < q` instance for the first-derivative potential. -/
theorem pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_five_halves_lt
    {G : Vec3 → ℝ} (i : Fin 3) {R q : ℝ} (hR : 0 < R) (hq : 5 / 2 < q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          newtonianDerivativePotentialGrowthConstant i G R * (1 + ρ) :=
  pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp i hR
    (by linarith only [hq]) hG hGzero

end CKN.Foundation.Euclidean
