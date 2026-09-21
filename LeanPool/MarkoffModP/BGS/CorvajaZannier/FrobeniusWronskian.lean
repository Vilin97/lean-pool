/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Algebra.DifferentialWronskian
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FrobeniusSubfield

/-!
# Frobenius constants and ordinary Wronskians

A Frobenius-separating parameter supplies a derivation whose exact constant
field is the Frobenius subfield.  Combining that construction with the
ordinary differential-field Wronskian criterion gives the algebraic
Wronskian boundary used in the Corvaja--Zannier argument.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- A Frobenius-separating parameter gives a derivation normalized by
`D z = 1`, with exact constant field `L^p`, for which every finite family has
nonzero ordinary Wronskian exactly when it is linearly independent over
`L^p`. -/
theorem exists_derivation_with_exact_constants_and_wronskian_criterion
    (z : L) (hz : z ∉ frobeniusSubfield L p)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    ∃ D : Derivation (frobeniusSubfield L p) L L,
      D z = 1 ∧
        (∀ x : L, D x = 0 ↔
          ∃ c : frobeniusSubfield L p,
            algebraMap (frobeniusSubfield L p) L c = x) ∧
        ∀ (n : ℕ) (f : Fin n → L),
          (BGS.Algebra.derivationWronskian D f).det ≠ 0 ↔
            LinearIndependent (frobeniusSubfield L p) f := by
  obtain ⟨D, hDz, hconstants⟩ :=
    exists_derivation_with_exact_frobenius_constants p z hz
  refine ⟨D, hDz, hconstants, ?_⟩
  intro n f
  exact BGS.Algebra.derivationWronskian_det_ne_zero_iff_linearIndependent D
    (fun x hx ↦ (hconstants x).mp hx) f

end

end BGS.CorvajaZannier
