/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaPoisson
public import LeanPool.Odlyzko.CompletedZeta.UnitSlabRadial

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A nonzero shape theta mellin kernel used in the Odlyzko-bound argument. -/
noncomputable def nonzeroShapeThetaMellinKernel
    (J : (Ideal (𝓞 K))⁰) (s : ℂ)
    (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s y * nonzeroIdealShapeTheta K J y

open Classical in
/-- A nonzero fractional shape theta mellin kernel used in the Odlyzko-bound argument. -/
noncomputable def nonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s y *
    (fractionalShapeIdealTheta K I (expMapBasis y)
      (fun w ↦ (expMapBasis_pos y w).ne') - 1)

open Classical in
theorem integrableOn_nonzeroShapeThetaMellinKernel
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (nonzeroShapeThetaMellinKernel K J s)
      (unitFundamentalParamSet K) := by
  apply IntegrableOn.congr_fun
    (integrableOn_logarithmicMellinWeight_mul_nonzeroIdealShapeTheta K J hs)
    _ measurableSet_unitFundamentalParamSet
  intro y _
  rw [nonzeroShapeThetaMellinKernel, logarithmicMellinWeight]

end NumberField.Odlyzko
