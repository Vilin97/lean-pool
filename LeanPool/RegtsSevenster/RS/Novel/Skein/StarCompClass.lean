/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StarTrace
import LeanPool.RegtsSevenster.RS.Novel.Skein.ScalarFunctional
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.ScalarClass

/-!
# The star composite in the category

The accompanying paper's (★) in categorical form: composing the star-union
class `Hom(0, 2m)` with the strand-bundle class `Hom(2m, 0)` is
the parameter value times the empty class — the identity that the
fibre functor transports into the standard model.
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The star-union class as a `(0, 2m)`-morphism. -/
noncomputable def starClass (W : ClosedFragment) :
    HomSpace f.val (0 + (edgeCount W + edgeCount W)) :=
  HomSpace.ofFragment f.val
    ((starUnion W).relabel (finCongr
      (by omega : edgeCount W + edgeCount W =
        0 + (edgeCount W + edgeCount W))))

/-- The strand-bundle class as a `(2m, 0)`-morphism. -/
noncomputable def bundleCapClass (m : ℕ) :
    HomSpace f.val ((m + m) + 0) :=
  HomSpace.ofFragment f.val
    ((strandBundle m).relabel (finCongr
      (by omega : m + m = (m + m) + 0)))

/-- **The categorical (★)**: the star composite is the parameter
value times the empty class. -/
theorem star_comp_class (W : ClosedFragment) :
    HomSpace.comp f 0 (edgeCount W + edgeCount W) 0
        (starClass f W) (bundleCapClass f (edgeCount W)) =
      f.val W •
        HomSpace.ofFragment f.val emptyClosedFragment := by
  rw [starClass, bundleCapClass, HomSpace.comp_ofFragment]
  rw [show ((starUnion W).relabel (finCongr
      (by omega : edgeCount W + edgeCount W =
        0 + (edgeCount W + edgeCount W)))).compose
      ((strandBundle (edgeCount W)).relabel (finCongr
        (by omega : edgeCount W + edgeCount W =
          (edgeCount W + edgeCount W) + 0))) =
      pairClose (starUnion W) (strandBundle (edgeCount W))
    from rfl]
  rw [HomSpace.ofFragment_congr f (starUnionPairClose W)]
  exact ofFragment_eq_smul_empty f W

end RS
