/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FrobeniusSubfield
public import Mathlib.FieldTheory.Perfect

/-!
# Perfect constants inside the Frobenius subfield

The Section 5 specialization of Corvaja--Zannier works over a perfect
constant field.  Consequently every constant, after embedding in the curve
function field, is a `p`-th power and belongs to the Frobenius subfield.
This file records that compatibility without identifying the two fields.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

variable {K L : Type*} [Field K] [Field L] {p : ℕ}
  [Fact p.Prime] [CharP K p] [CharP L p] [PerfectField K] [Algebra K L]

/-- Constants from a perfect field land in the Frobenius subfield of every
field extension of the same prime characteristic. -/
theorem algebraMap_mem_frobeniusSubfield (c : K) :
    algebraMap K L c ∈ frobeniusSubfield L p := by
  refine ⟨algebraMap K L ((frobeniusEquiv K p).symm c), ?_⟩
  simp only [frobenius_def]
  rw [← map_pow, frobeniusEquiv_symm_pow_p]

/-- The constant-field embedding, with codomain restricted to the Frobenius
subfield. -/
def perfectConstantsToFrobeniusSubfield : K →+* frobeniusSubfield L p :=
  (algebraMap K L).codRestrict (frobeniusSubfield L p)
    (fun c ↦ algebraMap_mem_frobeniusSubfield c)

@[simp]
theorem coe_perfectConstantsToFrobeniusSubfield (c : K) :
    ((perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p) c :
      frobeniusSubfield L p) : L) = algebraMap K L c :=
  rfl

theorem perfectConstantsToFrobeniusSubfield_injective :
    Function.Injective
      (perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)) :=
  (perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)).injective

end

end BGS.CorvajaZannier
