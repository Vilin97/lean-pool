/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Convergence
public import Mathlib.NumberTheory.LSeries.Deriv

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex LSeries

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem abscissaOfAbsConv_idealNormCount_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (idealNormCount K n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact lSeriesSummable_idealNormCount K (by simpa using hy)

theorem hasDerivAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (NumberField.dedekindZeta K)
      (-LSeries (LSeries.logMul fun n ↦ (idealNormCount K n : ℂ)) s) s := by
  change HasDerivAt (LSeries fun n ↦ (idealNormCount K n : ℂ)) _ s
  exact LSeries_hasDerivAt ((abscissaOfAbsConv_idealNormCount_le_one K).trans_lt <| by
    exact_mod_cast hs)

theorem differentiableAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
  (hasDerivAt_dedekindZeta K hs).differentiableAt

end NumberField.Odlyzko
