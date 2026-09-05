/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Primitive additive-character infrastructure

The Fourier arguments in this development are run against a fixed primitive
complex additive character of the finite field. Mathlib supplies one, so no
choice principle beyond Mathlib's own construction is needed. This module also
records the elementary fact that any primitive complex additive character is
nonprincipal.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Mathlib's canonical primitive complex additive character on a finite
field. -/
noncomputable def primitiveAddChar (K : Type*) [Field K] [Fintype K] : AddChar K ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex K

omit [DecidableEq K] in
/-- The canonical complex additive character is primitive. -/
theorem primitiveAddChar_isPrimitive : (primitiveAddChar K).IsPrimitive := by
  simpa [primitiveAddChar] using AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive K

omit [Fintype K] [DecidableEq K] in
/-- A primitive additive character is not the principal character. -/
lemma ne_one_of_isPrimitive {psi : AddChar K ℂ} (hpsi : psi.IsPrimitive) : psi ≠ 1 := by
  have h := hpsi (a := 1) one_ne_zero
  rwa [AddChar.mulShift_one] at h

end KasamiCyclicAdditive
