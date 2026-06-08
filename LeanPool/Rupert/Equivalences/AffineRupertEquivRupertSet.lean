/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic
import LeanPool.Rupert.Set
import LeanPool.Rupert.Affine

/-!
# LeanPool.Rupert.Equivalences.AffineRupertEquivRupertSet

Imported Lean Pool material for `LeanPool.Rupert.Equivalences.AffineRupertEquivRupertSet`.
-/

proof_wanted affine_rupert_iff_rupert_set
    (X : Set (EuclideanSpace ℝ (Fin 3))) :
    IsAffineRupertSet X ↔ IsRupertSet X
