/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Basic

/-!
# Canonical chosen analytic representatives

Abstract germs cannot be evaluated away from the origin.  For finite
specialization arguments it is convenient to choose one analytic
representative for each germ and retain the theorem identifying its raw
function germ.
-/


namespace LocalComplexGeometry

noncomputable section

/-- A chosen analytic representative of a holomorphic germ. -/
def HolomorphicGerm.representative {n : ℕ}
    (f : HolomorphicGerm n) : ComplexEuclidean n → ℂ :=
  Classical.choose (HolomorphicGerm.exists_rep f)

/-- The chosen representative is analytic at the origin. -/
theorem HolomorphicGerm.analyticAt_representative {n : ℕ}
    (f : HolomorphicGerm n) :
    AnalyticAt ℂ (HolomorphicGerm.representative f) 0 :=
  (Classical.choose_spec (HolomorphicGerm.exists_rep f)).1

/-- The chosen representative represents the original germ. -/
theorem HolomorphicGerm.coe_representative {n : ℕ}
    (f : HolomorphicGerm n) :
    (HolomorphicGerm.representative f : FunctionGerm n) =
      (f : FunctionGerm n) :=
  (Classical.choose_spec (HolomorphicGerm.exists_rep f)).2

/-- Chosen representatives of a finite coefficient vector. -/
def HolomorphicGerm.coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) :
    Fin k → ComplexEuclidean n → ℂ :=
  fun i ↦ HolomorphicGerm.representative (c i)

theorem HolomorphicGerm.analyticAt_coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) (i : Fin k) :
    AnalyticAt ℂ (HolomorphicGerm.coefficientRepresentatives c i) 0 :=
  HolomorphicGerm.analyticAt_representative (c i)

theorem HolomorphicGerm.coe_coefficientRepresentatives {n k : ℕ}
    (c : Fin k → HolomorphicGerm n) (i : Fin k) :
    (HolomorphicGerm.coefficientRepresentatives c i : FunctionGerm n) =
      (c i : FunctionGerm n) :=
  HolomorphicGerm.coe_representative (c i)

end

end LocalComplexGeometry
