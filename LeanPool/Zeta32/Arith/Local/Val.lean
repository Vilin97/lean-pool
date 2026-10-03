/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta5Irrational.Arith.IntPoly

/-!
# Shared rational and polynomial valuation bounds

The local API reuses the existing `Zeta5Irrational` valuation and integral-polynomial toolkit.
Only the product identity and the inverse bound without a nonzero premise are specific here.
-/

public section

open Finset Polynomial

namespace Zeta32.Arith.Local

variable {p : ℕ}

/-- Valuation is additive on a finite product of nonzero rational factors. -/
lemma padicValRat_finset_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hf a (Finset.mem_insert_self _ _))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

export Zeta5Irrational (VG GV det_GV factor_roots)

namespace VG

export Zeta5Irrational.VG (zero mono neg add sub mul sum prod intCast natCast one
  of_eq primePow pow inv_nat eval eval_zero)

lemma inv [Fact p.Prime] {q r : ℚ} (hv : (padicValRat p q : ℚ) ≤ r) :
    VG p q⁻¹ (-r) := by
  by_cases hq : q = 0
  · simp only [hq, inv_zero]; exact zero _
  · exact Zeta5Irrational.VG.inv hq hv

end VG

namespace GV

export Zeta5Irrational.GV (zero mono add neg sub C X mul C_mul sum prod pow comp
  divByMonic_X_sub_C)

end GV

end Zeta32.Arith.Local

end
