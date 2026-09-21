/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SubadditivityScaling

/-! # Subadditivity Scaling -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem for `l.cg.subadditivity.basic.definitions`. -/
theorem responseSubadditivityAndScalingTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ResponseSubadditivityAndScalingTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseSubadditivityAndScalingTheory U a

end

end Ch02
end Book
end Homogenization
