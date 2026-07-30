/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeThetaPeriodicity

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A logarithmic mellin weight used in the Odlyzko-bound argument. -/
noncomputable def logarithmicMellinWeight
    (s : ℂ) (y : mixedEmbedding.realSpace K) : ℂ :=
  Complex.exp
    (((y w₀ * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s)

omit [IsTotallyComplex K] in
open Classical in
@[simp]
theorem logarithmicMellinWeight_apply
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s y =
      Complex.exp
        (((y w₀ * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s) :=
  rfl

open Classical in
theorem exp_denominatorLogCoordinates_mul_finrank
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Real.exp
        (denominatorLogCoordinates K I w₀ *
          (Module.finrank ℚ K : ℝ)) =
      (((|Algebra.norm ℚ
        (algebraMap (𝓞 K) K
          ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))| : ℚ) : ℝ)) := by
  let d : K := algebraMap (𝓞 K) K
    ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)
  have hcoords :=
    expMapBasis_denominatorLogCoordinates K I
  have hprod := congrArg
    (fun q : InfinitePlace K → ℝ ↦ ∏ w, q w) hcoords
  have hprod' :
      Real.exp
          (denominatorLogCoordinates K I w₀ *
            (Module.finrank ℚ K : ℝ) / 2) =
        ∏ w : InfinitePlace K, w d := by
    simpa only [prod_expMapBasis_eq_exp_half_finrank, d] using hprod
  have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hprod'
  have hexp :
      Real.exp
          (denominatorLogCoordinates K I w₀ *
            (Module.finrank ℚ K : ℝ) / 2) ^ 2 =
        Real.exp
          (denominatorLogCoordinates K I w₀ *
            (Module.finrank ℚ K : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    simp
  rw [hexp] at hsquare
  rw [← Finset.prod_pow] at hsquare
  have hnorm := NumberField.InfinitePlace.prod_eq_abs_norm d
  simp only [IsTotallyComplex.mult_eq] at hnorm
  grind

omit [IsTotallyComplex K] in
open Classical in
theorem logarithmicMellinWeight_vadd_unitCoordinateLattice
    (s : ℂ) (g : unitCoordinateLattice (K := K))
    (y : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s
        ((g : mixedEmbedding.realSpace K) + y) =
      logarithmicMellinWeight K s y := by
  rw [logarithmicMellinWeight]
  simp only [Pi.add_apply, unitCoordinateLattice_apply_w₀, zero_add]
  simp

omit [IsTotallyComplex K] in
open Classical in
theorem logarithmicMellinWeight_add
    (s : ℂ) (y a : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s (y + a) =
      logarithmicMellinWeight K s a *
        logarithmicMellinWeight K s y := by
  rw [logarithmicMellinWeight, logarithmicMellinWeight,
    logarithmicMellinWeight, ← Complex.exp_add]
  simp only [Pi.add_apply]
  push_cast
  ring_nf

end NumberField.Odlyzko
