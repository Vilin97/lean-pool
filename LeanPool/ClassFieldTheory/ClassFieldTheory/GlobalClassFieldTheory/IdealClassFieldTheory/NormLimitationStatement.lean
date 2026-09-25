/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormLimitation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap
/-!
# Statement boundary for ideal norm limitation

This leaf packages the ideal norm-limitation equality behind a named
proposition.  Keeping the expanded normal-closure expression out of later
declaration signatures avoids repeatedly normalizing the full finite tower.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The proposition asserting ideal norm limitation for one defining
modulus. -/
@[irreducible] noncomputable def idealNormSubgroupMaximalAbelianStatement
    (m : RayClass.Modulus K)
    (_hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) : Prop :=
  RayClass.idealNormSubgroup (K := K) (L := L) m =
    RayClass.idealNormSubgroup
      (K := K)
      (L := finiteNormalClosureMaximalAbelianSubfield K L)
      m

end IdealClassFieldTheory
end GlobalClassFieldTheory
