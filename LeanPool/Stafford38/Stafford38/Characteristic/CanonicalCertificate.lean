/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.EmptySupportVanishing

/-!
# Certificate extraction from empty canonical characteristic support

This file closes the algebraic end of the characteristic-support route.  If
the order-characteristic support of the literal canonical quotient is empty,
then that quotient vanishes and membership of `1` in its two-generator right
ideal yields the exact fixed-source Stafford certificate.

No theorem proving that the support is empty is assumed or supplied here.
-/

namespace Stafford38.CharacteristicCanonicalCertificate

open Stafford38.CharacteristicEmptySupportVanishing
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Empty order-characteristic support of the canonical right ideal gives the
literal fixed-source certificate with source `x^N`. -/
theorem exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hsupport : orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N) = ∅) :
    ∃ R S : PresentedWeyl k (n + 1),
      (1 : PresentedWeyl k (n + 1)) =
        d * R + (presentedCoordinate k n) ^ N * d * S := by
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  have hquotient : Subsingleton (RightQuotient I) :=
    rightQuotient_subsingleton_of_orderCharacteristicSupport_eq_empty
      k I hsupport
  have htop : I = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hquotient
  have hone : (1 : PresentedWeyl k (n + 1)) ∈ I := by
    rw [htop]
    trivial
  change (1 : PresentedWeyl k (n + 1)) ∈
    Submodule.span (PresentedWeyl k (n + 1))ᵐᵒᵖ
      ({d, (presentedCoordinate k n) ^ N * d} :
        Set (PresentedWeyl k (n + 1))) at hone
  rcases Submodule.mem_span_pair.mp hone with ⟨r, s, hrs⟩
  refine ⟨r.unop, s.unop, ?_⟩
  simpa [op_smul_eq_mul] using hrs.symm


end

end Stafford38.CharacteristicCanonicalCertificate
