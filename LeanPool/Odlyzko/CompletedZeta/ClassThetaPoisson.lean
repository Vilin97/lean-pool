/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaIntegral
public import LeanPool.Odlyzko.CompletedZeta.TraceDualClass

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A fractional shape covolume constant used in the Odlyzko-bound argument. -/
noncomputable def fractionalShapeCovolumeConstant
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  FractionalIdeal.absNorm
      (I : FractionalIdeal (𝓞 K)⁰ K) *
    √|discr K|

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeCovolumeConstant_traceDual
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalShapeCovolumeConstant K (traceDualIdealUnit K I) =
      (fractionalShapeCovolumeConstant K I)⁻¹ := by
  rw [fractionalShapeCovolumeConstant,
    fractionalShapeCovolumeConstant,
    absNorm_traceDualIdealUnit, absNorm_traceDual_one]
  push_cast
  grind

end NumberField.Odlyzko
