/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Directed

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Directed`.
-/

namespace Subalgebra
variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {K : ι → Subalgebra R A}
  {s : Set ι}

lemma coe_biSup_of_directedOn (hs : s.Nonempty) (dir : DirectedOn (K · ≤ K ·) s) :
    ↑(⨆ i ∈ s, K i) = ⨆ i ∈ s, (K i : Set A) := by
  have := hs.to_subtype
  rw [← iSup_subtype'', ← iSup_subtype'', coe_iSup_of_directed, Set.iSup_eq_iUnion]
  rwa [← Function.comp_def, directed_comp, ← directedOn_iff_directed]

end Subalgebra
