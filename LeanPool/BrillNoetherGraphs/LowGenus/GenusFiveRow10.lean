/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberOne
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10ChamberTwo

/-!
# The Atanasov--Ranganathan construction on row 10

Row 10 is AR's *ninth* genus-five family: a triangle `{0, 1, 2}` with one spoke
from each corner, an apex `3` joining two of the spoke ends, and a banana
`{6, 7}` reached from the other two.

```
 e0 : 0 -> 2   e1 : 2 -> 1   e2 : 1 -> 0            the triangle
 e10 : 0 -> 3   e4 : 1 -> 4   e3 : 2 -> 5           the spokes  a, b, c
 e5 : 3 -> 4   e9 : 5 -> 3                          the apex
 e6 : 4 -> 6   e11 : 5 -> 7   e7, e8 : 6 == 7       the banana
```

The displayed divisor has one of its four chips at
an interior point of a spoke, at an offset equal to another spoke's length.  The
certificate is therefore a *marked* script
(`Utilities/Subdivision/SplitRampScript.lean`), which bends downward
at the chip and lets the chip pay for the kink.

The two displayed scopes are "`a = min(a,b,c)`" and "`b = min(a,b,c)`". The
remaining case, `c = min`, is the image of the second under the core
automorphism `sigma = (1 2)(4 5)(6 7)`.  So exactly the two drawn scopes have to
be proved:

* `GenusFiveRow10ChamberOne` -- `|e10| ≤ |e4|, |e3|`, the mark on `e4`;
* `GenusFiveRow10ChamberTwo` -- `|e4| ≤ |e10|, |e3|`, the mark on `e10`.

Both decompose the five chip-free vertices as one `ConfigurationMarkedTripod`
centre plus **AR's eleventh picture** (`ConfigurationEleven`) on the remaining
four, in the special position `alpha = gamma ≤ beta` that the chamber's two
inequalities supply.  `GenusFiveRow10Symmetry.chamber_covers` and
`ClosedOrbit.closedConstruction_of_chamber` then finish the closed orthant.
-/

namespace AtanasovRanganathan.GenusFiveRow10

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas

/-- Either scope AR draw gives a degree-four Dhar pencil on its own face. -/
theorem chamber_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row10Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row10Core (zeroSlots length))
    (hP : GenusFiveRow10Symmetry.Chamber length) :
    Nonempty (DegreeFourDharPencil
      (faceSpec row10Core (by norm_num) length forest notLoopy).graph) := by
  rcases hP with h1 | h2
  · exact GenusFiveRow10ChamberOne.chamberOne_pencil length forest notLoopy h1
  · exact GenusFiveRow10ChamberTwo.chamberTwo_pencil length forest notLoopy h2

/-- **AR's ninth family on row 10.**  The paper's own divisor -- two triangle
vertices, one banana vertex, and one chip inside the marked spoke -- has rank at
least one on every nonloopy forest face, all three chambers at once. -/
theorem row10_closedConstruction :
    ClosedSubdivisionDharConstruction row10Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row10Core (by norm_num)
    GenusFiveRow10Symmetry.Chamber
    (fun length _ _ => GenusFiveRow10Symmetry.chamber_covers length)
    chamber_pencil

end AtanasovRanganathan.GenusFiveRow10
