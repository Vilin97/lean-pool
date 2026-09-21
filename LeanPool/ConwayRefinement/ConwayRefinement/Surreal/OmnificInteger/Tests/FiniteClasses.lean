/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.FiniteClasses
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.OneRowPrime

/-!
# A downstream client of finite-class omnific primality

Conway's one-row omnific integer has support order type `ω + 1`, so this client uses a genuinely
infinite support. Its reducedness supplies the finite support-class hypothesis. The stronger
prime theorem for this example is not used to obtain the primality conclusion here.
-/

public noncomputable section

namespace Tests

open Surreal.OmnificInteger.OneRowExample

/-- The infinite Conway normal form meets finitely many classes, in the same orientation as
the paper's hypothesis. -/
theorem oneRow_normalForm_classes_finite :
    (ArchimedeanClass.mk '' (oneRowOz : Surreal).support).Finite := by
  rw [← Surreal.OmnificInteger.supportArchimedeanClasses_toSignedNonpositiveHahn]
  exact oneRowOz_isReduced.supportArchimedeanClasses_finite

/-- The one-row omnific integer is primal by the finite-class theorem. -/
theorem oneRow_primal_of_finite_classes : IsPrimal oneRowOz :=
  Surreal.OmnificInteger.isPrimal_of_supportArchimedeanClasses_finite oneRowOz
    oneRowOz_isReduced.supportArchimedeanClasses_finite

end Tests
