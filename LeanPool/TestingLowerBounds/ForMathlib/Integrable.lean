/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Integrability of an `rnDeriv`-smul

The other integrability lemmas that previously lived here are all in Mathlib now; only
`Integrable.rnDeriv_smul`, the convenience wrapper that the divergence files import, remains.
-/

open scoped ENNReal

namespace MeasureTheory

namespace Integrable

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end Integrable

end MeasureTheory
