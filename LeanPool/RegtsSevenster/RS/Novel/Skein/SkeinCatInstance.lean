/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceNondegenerate

/-!
# The skein category, packaged

The accompanying paper's connection category `𝒞_f` as a
`CategoryTheory.Category` instance: objects are arities, morphisms
are Hom-space classes, identities are strand bundle classes,
composition is the descended bilinear composition.  All axioms were proven in
`SkeinCategory.lean`; this file only packages them.
-/

namespace RS

/-- An object of the skein category of a parameter: an arity. -/
structure SkeinObj {R : ℕ} (f : EdgeRankParameter R) where
  /-- The arity: the number of open ends. -/
  arity : ℕ

/-- **The skein category**: the accompanying paper's connection
category `𝒞_f` (§3.2). -/
noncomputable instance skeinCategory {R : ℕ}
    (f : EdgeRankParameter R) :
    CategoryTheory.Category (SkeinObj f) where
  Hom X Y := HomSpace f.val (X.arity + Y.arity)
  id X := HomSpace.ofFragment f.val (strandBundle X.arity)
  comp {X Y Z} p q :=
    HomSpace.comp f X.arity Y.arity Z.arity p q
  id_comp {X Y} p := HomSpace.comp_id_left f X.arity Y.arity p
  comp_id {X Y} p := HomSpace.comp_id_right f X.arity Y.arity p
  assoc {W X Y Z} p q r :=
    HomSpace.comp_assoc f W.arity X.arity Y.arity Z.arity p q r

end RS
