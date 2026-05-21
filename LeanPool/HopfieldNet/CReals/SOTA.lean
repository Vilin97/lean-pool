/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealAQBackendEquiv
import LeanPool.HopfieldNet.CReals.CRealAQOrder
import LeanPool.HopfieldNet.CReals.CRealCCLOF
import LeanPool.HopfieldNet.CReals.CRealRealEquiv
import LeanPool.HopfieldNet.CReals.CRealsFastBackend

/-!
# SOTA CReals façade (spec vs implementation)

This file is a **consolidation layer** intended to present the computable reals stack in a
single place, in a style aligned with "SOTA" developments (CoRN / O'Connor / Spitters):

- **Specification model**: `Computable.CReal` (an extensional quotient of regular Cauchy sequences).
- **Implementation-parameterized extensional model**: `Computable.CRealAQ AQ`, where `AQ` is an
  `ApproxRationals` backend (e.g. fast dyadics).
- **Computational representatives**: `Computable.CRealRep AQ`, which actually carries an
  approximation function `ℕ → AQ`.

The guiding principle is: *prove against the spec model once; run algorithms against a concrete
backend via representatives or backend-specific evaluators*.
-/

namespace Computable

namespace CRealsSOTA

/-! ## Canonical names -/

abbrev RealSpec : Type := Computable.CReal

abbrev RealImpl (AQ : Type) [ApproxRationals AQ] : Type := Computable.CRealAQ AQ

abbrev RealRep (AQ : Type) [ApproxRationals AQ] : Type := Computable.CRealRep AQ

/-!
## Denotation maps

`RealImpl AQ` is *definitionally* a quotient of `RealRep AQ`. The denotation to the spec
model is `CRealAQ.toCReal`.
-/

variable {AQ : Type} [ApproxRationals AQ]

def toSpec : RealImpl AQ →+* RealSpec :=
  (Computable.CRealAQ.ringEquivCReal (AQ := AQ)).toRingHom

@[simp] theorem toSpec_apply (x : RealImpl AQ) :
    toSpec (AQ := AQ) x = Computable.CRealAQ.toCReal (AQ := AQ) x := rfl

/-!
## Bridge to `ℝ`

For theorem transfer, we typically want a ring hom `RealImpl AQ →+* ℝ`.
We get it by composing `toSpec` with the existing `Computable.CReal.toRealRingHom`.
-/

noncomputable def toRealRingHom : RealImpl AQ →+* ℝ :=
  Computable.CReal.toRealRingHom.comp (toSpec (AQ := AQ))

theorem toReal_mono {a b : RealImpl AQ} (hab : a ≤ b) :
    toRealRingHom (AQ := AQ) a ≤ toRealRingHom (AQ := AQ) b := by
  -- `≤` on `CRealAQ` is pulled back along `toCReal`, so `hab` is already a `CReal` inequality.
  -- Then use monotonicity of `CReal.toReal`.
  -- Unfold once to expose the pulled-back order.
  change Computable.CReal.toRealRingHom (Computable.CRealAQ.toCReal (AQ := AQ) a)
      ≤ Computable.CReal.toRealRingHom (Computable.CRealAQ.toCReal (AQ := AQ) b)
  exact Computable.CReal.toReal_mono (by simpa using hab)

end CRealsSOTA

end Computable
