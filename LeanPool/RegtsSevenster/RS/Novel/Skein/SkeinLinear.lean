/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance

/-!
# The skein category is ℂ-linear

Hom spaces are ℂ-modules and the descended composition is
bilinear, so the skein category is preadditive and ℂ-linear —
two of the instance hypotheses of the Deligne package carrier.
-/

namespace RS

open CategoryTheory

/-- Skein hom-spaces are abelian groups. -/
noncomputable instance skeinHomAddCommGroup {R : ℕ}
    (f : EdgeRankParameter R) (X Y : SkeinObj f) :
    AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup
    (HomSpace f.val (X.arity + Y.arity)))

/-- And ℂ-modules. -/
noncomputable instance skeinHomModule {R : ℕ}
    (f : EdgeRankParameter R) (X Y : SkeinObj f) :
    Module ℂ (X ⟶ Y) :=
  inferInstanceAs (Module ℂ
    (HomSpace f.val (X.arity + Y.arity)))

/-- Composition is additive in each argument, so the category is
preadditive. -/
noncomputable instance skeinPreadditive {R : ℕ}
    (f : EdgeRankParameter R) : Preadditive (SkeinObj f) where
  homGroup := skeinHomAddCommGroup f
  add_comp X Y Z p p' q :=
    congrArg (fun g : HomSpace f.val (Y.arity + Z.arity) →ₗ[ℂ]
        HomSpace f.val (X.arity + Z.arity) => g q)
      (map_add (HomSpace.comp f X.arity Y.arity Z.arity)
        (p : HomSpace f.val (X.arity + Y.arity))
        (p' : HomSpace f.val (X.arity + Y.arity)))
  comp_add X Y Z p q q' :=
    map_add (HomSpace.comp f X.arity Y.arity Z.arity
        (p : HomSpace f.val (X.arity + Y.arity)))
      (q : HomSpace f.val (Y.arity + Z.arity))
      (q' : HomSpace f.val (Y.arity + Z.arity))

/-- And bilinear, so it is ℂ-linear. -/
noncomputable instance skeinLinear {R : ℕ}
    (f : EdgeRankParameter R) : Linear ℂ (SkeinObj f) where
  homModule := skeinHomModule f
  smul_comp X Y Z c p q :=
    congrArg (fun g : HomSpace f.val (Y.arity + Z.arity) →ₗ[ℂ]
        HomSpace f.val (X.arity + Z.arity) => g q)
      (map_smul (HomSpace.comp f X.arity Y.arity Z.arity) c
        (p : HomSpace f.val (X.arity + Y.arity)))
  comp_smul X Y Z p c q :=
    map_smul (HomSpace.comp f X.arity Y.arity Z.arity
        (p : HomSpace f.val (X.arity + Y.arity))) c
      (q : HomSpace f.val (Y.arity + Z.arity))

end RS
