/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials

/-!
# Local `L^{3/2}` membership and linear growth of the force potentials `p₇` and `p₈`

The two force terms of the local pressure decomposition `eq:pk`, estimated
in `lem:pk-bounds`, are

* `p₇ = ∑ⱼ (∂ⱼN) * (η fⱼ)`, a sum of first-derivative Newtonian potentials, and
* `p₈ = -∑ⱼ N * ((∂ⱼη) fⱼ)`, a sum of Newtonian potentials,

where `N = -newtonianKernel`.  In Lean, `pressureNewtonianDerivativePotential`
is convolution with `-∂ⱼN`, so the outer minus in `pressureP7` gives the positive
sign above.  The data use the cutoff `η` and force `f` of a suitable weak solution.  The
cancellation argument for the force feeds `p₇ + p₈` into the Liouville step of `ext:newtonian`,
which needs `p₇ + p₈` to be `L^{3/2}` on every round ball `euclideanBall 0 ρ` with local norm at
most `C * (1 + ρ)`.

This file assembles exactly that pair of statements from the single-potential estimates of
`CKN.Foundation.Euclidean.PotentialLocalLpGrowth`, with the constant an explicit finite sum of
the single-potential constants.  The hypotheses are per-slice: at a fixed time `s`, each of the
six data functions `(∂ⱼη) fⱼ(·, s)` and `η fⱼ(·, s)` is of class `L^q` with `6/5 ≤ q` and
vanishes off a closed ball.  The exponent range `6/5 ≤ q` contains the pressure exponent `3/2`
and the force exponents `q > 5/2` of `def:sws`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! ### Negated finite sums of potentials -/

/-- A negated finite sum of functions that are `L^{3/2}` on every round ball with linear growth
is again of that class, with the sum of the constants. -/
theorem neg_sum_memLp_and_lpNorm_growth {F : Fin 3 → Vec3 → ℝ} {C : Fin 3 → ℝ}
    (hmem : ∀ j : Fin 3, ∀ ρ : ℝ, 0 < ρ → MemLp (F j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hb : ∀ j : Fin 3, ∀ ρ : ℝ, 0 < ρ → lpNorm (F j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C j * (1 + ρ)) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (fun x => -∑ j, F j x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (fun x => -∑ j, F j x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ (∑ j, C j) * (1 + ρ) := by
  classical
  have hfun : (fun x : Vec3 => -∑ j, F j x) = -(∑ j ∈ Finset.univ, F j) := by
    funext x
    simp only [Pi.neg_apply, Finset.sum_apply]
  constructor
  · intro ρ hρ
    rw [hfun]
    exact (memLp_euclideanBall_family_sum (fun j _hj => hmem j) ρ hρ).neg
  · intro ρ hρ
    rw [hfun, lpNorm_neg]
    exact lpNorm_euclideanBall_growth_sum (fun j _hj => hmem j) (fun j _hj => hb j) hρ

/-! ### The explicit growth constants of `p₇` and `p₈` -/

/-- The linear-growth constant of `p₈` at time `s`, for data supported in the closed ball of
radius `R`: the sum over the three components of the Newtonian-potential constants. -/
@[expose]
def pressureP8GrowthConstant (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s R : ℝ) : ℝ :=
  ∑ j : Fin 3, newtonianPotentialGrowthConstant
    (fun y => spatialDeriv η j y * f (y, s) j) R

/-- The linear-growth constant of `p₇` at time `s`, for data supported in the closed ball of
radius `R`: the sum over the three components of the derivative-potential constants. -/
@[expose]
def pressureP7GrowthConstant (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s R : ℝ) : ℝ :=
  ∑ j : Fin 3, newtonianDerivativePotentialGrowthConstant j
    (fun y => η y * f (y, s) j) R

theorem pressureP8GrowthConstant_nonneg (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s R : ℝ) :
    0 ≤ pressureP8GrowthConstant η f s R :=
  Finset.sum_nonneg fun _j _hj => newtonianPotentialGrowthConstant_nonneg _ R

theorem pressureP7GrowthConstant_nonneg (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ)
    {R : ℝ} (hR : 0 < R) : 0 ≤ pressureP7GrowthConstant η f s R :=
  Finset.sum_nonneg fun j _hj => newtonianDerivativePotentialGrowthConstant_nonneg j hR _

/-! ### The force potentials on every round ball -/

/-- `p₈` is `L^{3/2}` on every round ball about the origin, with local norm at most
`pressureP8GrowthConstant η f s R * (1 + ρ)`. -/
theorem pressureP8_memLp_and_lpNorm_growth
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s R q : ℝ} (hR : 0 < R) (hq : 6 / 5 ≤ q)
    (hdata : ∀ j : Fin 3, MemLp (fun y => spatialDeriv η j y * f (y, s) j)
      (ENNReal.ofReal q) volume)
    (hsupp : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R →
      spatialDeriv η j y * f (y, s) j = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureP8 η f s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureP8 η f s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          pressureP8GrowthConstant η f s R * (1 + ρ) := by
  have hcomp : ∀ j : Fin 3,
      (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
        ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
            newtonianPotentialGrowthConstant
              (fun y => spatialDeriv η j y * f (y, s) j) R * (1 + ρ) := fun j =>
    pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp hR hq (hdata j) (hsupp j)
  have hP8 : pressureP8 η f s =
      fun x => -∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x := rfl
  rw [hP8, pressureP8GrowthConstant]
  exact neg_sum_memLp_and_lpNorm_growth (fun j => (hcomp j).1) (fun j => (hcomp j).2)

/-- `p₇` is `L^{3/2}` on every round ball about the origin, with local norm at most
`pressureP7GrowthConstant η f s R * (1 + ρ)`. -/
theorem pressureP7_memLp_and_lpNorm_growth
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s R q : ℝ} (hR : 0 < R) (hq : 6 / 5 ≤ q)
    (hdata : ∀ j : Fin 3, MemLp (fun y => η y * f (y, s) j) (ENNReal.ofReal q) volume)
    (hsupp : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R →
      η y * f (y, s) j = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureP7 η f s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureP7 η f s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          pressureP7GrowthConstant η f s R * (1 + ρ) := by
  have hcomp : ∀ j : Fin 3,
      (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
        ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
            newtonianDerivativePotentialGrowthConstant j
              (fun y => η y * f (y, s) j) R * (1 + ρ) := fun j =>
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp j hR hq
      (hdata j) (hsupp j)
  have hP7 : pressureP7 η f s =
      fun x => -∑ j, pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x := rfl
  rw [hP7, pressureP7GrowthConstant]
  exact neg_sum_memLp_and_lpNorm_growth (fun j => (hcomp j).1) (fun j => (hcomp j).2)

/-! ### The pair of hypotheses consumed by the force cancellation argument -/

/-- The local `L^{3/2}` membership and the linear growth of `p₇ + p₈` on the round balls: this
is the exact pair of hypotheses that the force cancellation of `lem:pk-bounds` feeds to the
Liouville step of `ext:newtonian`. -/
theorem pressureP7_add_pressureP8_memLp_and_lpNorm_growth
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s R q : ℝ} (hR : 0 < R) (hq : 6 / 5 ≤ q)
    (hdata₇ : ∀ j : Fin 3, MemLp (fun y => η y * f (y, s) j) (ENNReal.ofReal q) volume)
    (hsupp₇ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R →
      η y * f (y, s) j = 0)
    (hdata₈ : ∀ j : Fin 3, MemLp (fun y => spatialDeriv η j y * f (y, s) j)
      (ENNReal.ofReal q) volume)
    (hsupp₈ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R →
      spatialDeriv η j y * f (y, s) j = 0) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          (pressureP7GrowthConstant η f s R + pressureP8GrowthConstant η f s R) * (1 + ρ) := by
  obtain ⟨hmem₇, hb₇⟩ := pressureP7_memLp_and_lpNorm_growth hR hq hdata₇ hsupp₇
  obtain ⟨hmem₈, hb₈⟩ := pressureP8_memLp_and_lpNorm_growth hR hq hdata₈ hsupp₈
  exact ⟨memLp_euclideanBall_family_add hmem₇ hmem₈,
    fun ρ hρ => lpNorm_euclideanBall_growth_add hmem₇ hb₇ hb₈ hρ⟩

/-- The growth constant of `p₇ + p₈` is nonnegative, which is the remaining component of the
force cancellation hypothesis. -/
theorem pressureP7_add_pressureP8_growthConstant_nonneg
    (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) {R : ℝ} (hR : 0 < R) :
    0 ≤ pressureP7GrowthConstant η f s R + pressureP8GrowthConstant η f s R := by
  have h₇ := pressureP7GrowthConstant_nonneg η f s hR
  have h₈ := pressureP8GrowthConstant_nonneg η f s R
  linarith only [h₇, h₈]

end CKN.Foundation.Euclidean
