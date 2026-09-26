/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtension

/-!
# Lp Extension Input Cast

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped ENNReal

namespace CKN.Foundation.Euclidean

/-- Transporting an `LpExtensionInput` along an equality of its constant does not
change its operator. -/
theorem lpExtensionInput_mp_T {p : ℝ≥0∞} {C D : ℝ}
    (hCD : C = D) (h : LpExtensionInput p C)
    (e : LpExtensionInput p C = LpExtensionInput p D) :
    (e.mp h).T = h.T := by
  subst hCD
  rfl

end CKN.Foundation.Euclidean
