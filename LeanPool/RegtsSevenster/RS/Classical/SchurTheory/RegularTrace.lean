/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PowerSurj

/-!
# The trace of left multiplication on a group algebra

Left multiplication by `y` on `ℂ[G]` has trace `|G| · y 1` — the
regular character.  Combined with rank-equals-trace for
idempotents this computes block dimensions without any
decomposition theory.
-/

namespace RS

open Finset LinearMap Module

variable {G : Type*}

/-- **The regular trace**: left multiplication by `y` has trace
`|G| · y 1`. -/
theorem trace_mulLeft [Group G] [Fintype G]
    (y : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G) (mulLeft ℂ y) =
      (Fintype.card G : ℂ) * y.coeff 1 := by
  classical
  rw [trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
  rw [Matrix.trace]
  rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => show
      (toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
        (mulLeft ℂ y)).diag g = y.coeff 1 from by
    rw [Matrix.diag_apply, toMatrix_apply, mulLeft_apply,
      MonoidAlgebra.basis_apply]
    rw [show ((MonoidAlgebra.basis G ℂ).repr
        (y * MonoidAlgebra.single g 1)) g =
      (y * MonoidAlgebra.single g 1).coeff g from rfl]
    rw [show (y * MonoidAlgebra.single g (1 : ℂ)).coeff g =
        y.coeff (g * g⁻¹) * 1 from
      MonoidAlgebra.coeff_mul_single_apply y 1 g g]
    rw [mul_inv_cancel, mul_one])]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Rank of an idempotent multiplication equals the regular
trace: the block dimension formula. -/
theorem finrank_range_mulLeft [Group G] [Fintype G]
    (y : MonoidAlgebra ℂ G)
    (hy : y * y = y) :
    (Module.finrank ℂ (LinearMap.range (mulLeft ℂ y)) : ℂ) =
      (Fintype.card G : ℂ) * y.coeff 1 := by
  classical
  have hproj : IsProj (LinearMap.range (mulLeft ℂ y))
      (mulLeft ℂ y) := by
    constructor
    · intro z
      exact LinearMap.mem_range_self _ z
    · rintro z ⟨w, rfl⟩
      rw [mulLeft_apply, mulLeft_apply, ← mul_assoc, hy]
  rw [← hproj.trace, trace_mulLeft]

end RS
