/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.Subfield.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# LeanPool.BrauerGroupNew.Subfield.FiniteDimensional

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Subfield.FiniteDimensional`.
-/

namespace SubField
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {L : SubField K A}

instance [FiniteDimensional K A] : FiniteDimensional K L := .finiteDimensional_subalgebra L.1

end SubField
