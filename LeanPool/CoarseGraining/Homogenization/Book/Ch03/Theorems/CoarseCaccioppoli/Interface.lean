/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZero

/-! # Interface -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Coarse Caccioppoli interface

This file keeps the public Prop structure for the arbitrary-scale Caccioppoli
surface.  The final unconditional public apex theorem is declared in
`Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliDilationTransport` and
re-exported by `Homogenization.Book.Ch03.Theorems.CoarseCaccioppoli`.

## Audit tag

Claim: define the single public arbitrary-scale Caccioppoli package consumed by
the scale-normalization proof from the scale-zero theorem.

Downstream target: `CoarseCaccioppoli.lean` and `CoarseCaccioppoliRHS/Theory.lean`.
New public Caccioppoli variants must amend the Ch3 surface contract first.
-/

noncomputable section

open scoped ENNReal

/-- Public theorem package for the boundary and interior coarse-grained
Caccioppoli inequalities.  The constant is dimension-only; all exponent
dependence on `s,t` is displayed in the public RHS definitions.  The boundary
theorem is local in a center `x ∈ Q`; the interior theorem is the centered cube
estimate from the notes, with arbitrary translated cubes represented by the
choice of `Q`. -/
structure CoarseCaccioppoliTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        (u : BoundaryCaccioppoliDatum Q a x),
        0 < s → 0 < t → s + t < 1 → x ∈ openCubeSet Q →
          boundaryCaccioppoliCoreEnergy u ≤
            boundaryCaccioppoliRHS C s t u) ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        (u : CubeSolution Q a),
        0 < s → 0 < t → s + t < 1 →
          interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
            interiorCaccioppoliRHS C Q a s t u)

end

end Ch03
end Book
end Homogenization
