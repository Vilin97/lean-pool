/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteRadiusAdapter
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryFrozenInputL0
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleFiniteRadiusLimit

/-!
# Applying a finite sparse maximum to the genuine frozen block

This module contains the exact adapter between the abstract finite sparse
maximal theorem and the frozen quadratic-Hilbert block in the paper.  It
indexes the modulation block `Q B τ` by a finite type, applies the resulting
finite maximum to the genuine compactly supported frozen input, and passes a
uniform finite-radius weak bound to the full real-radius supremum.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace LacunaryMiddleSparseAdapter

open ExtendedWeakL1Combinators KaltonPaperApplication
open KrauseLaceyFiniteRadiusAdapter LacunaryFrozenInputL0
open LacunaryMiddleFiniteRadiusLimit LacunaryMiddleOperator LacunaryMiddleRange
open QuadraticHilbertMaximalMeasurable
open PositiveEndpointOptimization CalderonZygmundDyadicStopping
open CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate


noncomputable section

/-- Canonical enumeration of the finite modulation block. -/
def modulationBlockIndex (B : ℕ) (τ : ℤ) (j : Fin (Q B τ).card) : ℤ :=
  ((Q B τ).equivFin.symm j).1

theorem modulationBlockIndex_mem (B : ℕ) (τ : ℤ) (j : Fin (Q B τ).card) :
    modulationBlockIndex B τ j ∈ Q B τ :=
  ((Q B τ).equivFin.symm j).2

/-- The family, indexed only by the paper's modulation block, whose members
are finite maxima over the chosen sharp truncation radii. -/
def finiteRadiusQuadraticHilbertBlockFamily
    (B : ℕ) (τ : ℤ) (s : Finset densePositiveRadii) :
    Fin (Q B τ).card → TestOperator :=
  fun j ↦ finiteRadiusQuadraticHilbertMaxTestOperator
    (dyadicModulation (modulationBlockIndex B τ j)) s

theorem finiteRadiusQuadraticHilbertBlockFamily_isSublinear
    (B : ℕ) (τ : ℤ) (s : Finset densePositiveRadii)
    (j : Fin (Q B τ).card) :
    IsSublinear (finiteRadiusQuadraticHilbertBlockFamily B τ s j) :=
  finiteRadiusQuadraticHilbertMaxTestOperator_isSublinear _ _

/-- The finite sparse-family maximum dominates the exact finite-radius
frozen block pointwise. -/
theorem finiteRadiusFrozenBlockHilbertMaxEnorm_le_finiteMax
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ)
    (s : Finset densePositiveRadii) (x : ℝ) :
    finiteRadiusFrozenBlockHilbertMaxEnorm
        lacunaryAmplitude f k B c τ s x ≤
      ENNReal.ofReal (finiteMax
        (finiteRadiusQuadraticHilbertBlockFamily B τ s)
        (frozenBlockInputL0 f k B c τ) x) := by
  classical
  unfold finiteRadiusFrozenBlockHilbertMaxEnorm
  apply Finset.sup_le
  intro m hm
  apply Finset.sup_le
  intro ε hε
  let j : Fin (Q B τ).card := (Q B τ).equivFin ⟨m, hm⟩
  have hj : modulationBlockIndex B τ j = m := by
    dsimp only [j, modulationBlockIndex]
    simp
  calc
    ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
        (frozenBlockInput lacunaryAmplitude f k B c τ) x‖ₑ ≤
        ENNReal.ofReal ‖finiteRadiusQuadraticHilbertMaxTestOperator
          (dyadicModulation m) s (frozenBlockInputL0 f k B c τ) x‖ := by
      have h := quadraticHilbertTrunc_enorm_le_finiteRadiusTestOperator
        (dyadicModulation m) s hε (frozenBlockInputL0 f k B c τ) x
      change
        ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
            (frozenBlockInput lacunaryAmplitude f k B c τ) x‖ₑ ≤
          ENNReal.ofReal ‖finiteRadiusQuadraticHilbertMaxTestOperator
            (dyadicModulation m) s (frozenBlockInputL0 f k B c τ) x‖ at h
      exact h
    _ ≤ ENNReal.ofReal (finiteMax
        (finiteRadiusQuadraticHilbertBlockFamily B τ s)
        (frozenBlockInputL0 f k B c τ) x) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [finiteRadiusQuadraticHilbertBlockFamily, hj] using
        le_finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s)
          (frozenBlockInputL0 f k B c τ) x j

/-- An ordinary weak `(1,1)` estimate for the indexed finite maximum gives
the extended-valued weak estimate for the exact finite-radius frozen block,
with its true `L¹` mass. -/
theorem hasExtendedWeakL1Bound_finiteRadiusFrozenBlock_of_hasWeakOneOneBound
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ)
    (s : Finset densePositiveRadii) {D : ℝ} (hD : 0 ≤ D)
    (hweak : HasWeakOneOneBound D
      (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s))) :
    HasExtendedWeakL1Bound volume
      (D * (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal)
      (finiteRadiusFrozenBlockHilbertMaxEnorm
        lacunaryAmplitude f k B c τ s) := by
  let g := frozenBlockInputL0 f k B c τ
  let mass := frozenBlockInputL1Mass lacunaryAmplitude f k B c τ
  have hmass_ne : mass ≠ ∞ := by
    simpa only [mass, ← lintegral_enorm_frozenBlockInputL0_eq] using
      (integrable_frozenBlockInputL0 f k B c τ).hasFiniteIntegral.ne
  refine ⟨mul_nonneg hD ENNReal.toReal_nonneg, ?_⟩
  intro a ha
  have hsub :
      {x | ENNReal.ofReal a < finiteRadiusFrozenBlockHilbertMaxEnorm
        lacunaryAmplitude f k B c τ s x} ⊆
      {x | a < finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s) g x} := by
    intro x hx
    have hx' := hx.trans_le
      (finiteRadiusFrozenBlockHilbertMaxEnorm_le_finiteMax f k B c τ s x)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mp hx'
  calc
    ENNReal.ofReal a * volume
        {x | ENNReal.ofReal a < finiteRadiusFrozenBlockHilbertMaxEnorm
          lacunaryAmplitude f k B c τ s x} ≤
        ENNReal.ofReal a * volume
          {x | a < finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s) g x} :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ENNReal.ofReal D * ∫⁻ x, ‖g x‖ₑ := hweak g a ha
    _ = ENNReal.ofReal
        (D * (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal) := by
      rw [show (∫⁻ x, ‖g x‖ₑ) = mass by
        simpa only [g, mass] using
          lintegral_enorm_frozenBlockInputL0_eq f k B c τ]
      rw [ENNReal.ofReal_mul hD, ENNReal.ofReal_toReal hmass_ne]

/-- If the same finite-maximal weak constant is available for every finite
radius subset, then the genuine all-radius frozen block has exactly that
constant times its true `L¹` mass. -/
theorem hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_of_uniform_finiteRadii
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hweak : ∀ s : Finset densePositiveRadii,
      HasWeakOneOneBound D
        (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s))) :
    HasExtendedWeakL1Bound volume
      (D * (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal)
      (frozenBlockHilbertMaxEnorm lacunaryAmplitude f k B c τ) := by
  apply hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_of_finiteRadii
    f.measurable_toFun f.integrable (lacunaryAmplitude_pos k).le B c τ
  intro s
  exact hasExtendedWeakL1Bound_finiteRadiusFrozenBlock_of_hasWeakOneOneBound
    f k B c τ s hD (hweak s)

/-- The same conclusion on the complement of the fivefold exceptional set,
which is the exact measure used by the paper's Kalton assembly. -/
theorem hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_restrict_of_uniform_finiteRadii
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hweak : ∀ s : Finset densePositiveRadii,
      HasWeakOneOneBound D
        (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B τ s))) :
    HasExtendedWeakL1Bound
      (volume.restrict (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ)
      (D * (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal)
      (frozenBlockHilbertMaxEnorm lacunaryAmplitude f k B c τ) :=
  HasExtendedWeakL1Bound.restrict
    (hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_of_uniform_finiteRadii
      f k B c τ hD hweak) _


end
end LacunaryMiddleSparseAdapter
end QuadraticCarleson
