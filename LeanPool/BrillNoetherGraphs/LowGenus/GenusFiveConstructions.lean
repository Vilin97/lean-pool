/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow05
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow09
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow10
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow11
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Guarding
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow14
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow15
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow16

/-!
# The sixteen Atanasov--Ranganathan genus-five constructions

This file is the proof ledger for the hard cubic cores.  Each theorem below is
one complete construction from AR's genus-five section: it must choose a
degree-four divisor throughout the genus-preserving closed length orthant and
supply a tagged, explicit Dhar move at every off-support vertex.  Thus the
same obligation includes the positive row and all its nonloopy forest faces.

Each displayed core construction has its own theorem.  The length-independent
rows and the named length-dependent families are kept separate so that filling
one theorem is a genuine, reportable unit of progress.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveConstructions

open Utilities

open GenusFiveCoreAtlas
open Configurations

/-- The exact checked obligation for one of the displayed `8`-vertex,
`12`-edge cubic cores, authored on its whole genus-preserving closed orthant.
Looplessness is needed only when recovering the positive interior. -/
abbrev RowConstruction (core : Core) : Prop :=
  ClosedSubdivisionDharConstruction core (by norm_num)

/-- Every closed row construction supplies the original positive-subdivision
pencil expected by the public AR reduction. -/
theorem RowConstruction.toPositiveSubdivisionPencil {core : Core}
    (hLoopless : Loopless core) (construction : RowConstruction core) :
    PositiveSubdivisionPencil core (by norm_num) hLoopless 4 :=
  ClosedSubdivisionDharConstruction.toPositiveSubdivisionPencil
    hLoopless construction

/-! ## The six length-dependent families -/

/-- AR's first family (Figure-8 row 01). Two genus-two canonical divisors
give the positive construction; integer rounding closes every forest face. -/
theorem row01_firstFamily : RowConstruction row01Core := by
  exact GenusFiveTwoPoleClosed.row01_closedConstruction

/-- AR's second family, including its exceptional contraction face, follows
from the common canonical construction and discrete specialization. -/
theorem row02_secondFamily : RowConstruction row02Core := by
  exact GenusFiveTwoPoleClosed.row02_closedConstruction

/-- AR's fourth family (“loops of loops”) uses the common canonical
construction and discrete specialization on the entire closed orthant. -/
theorem row04_fourthFamily : RowConstruction row04Core := by
  exact GenusFiveTwoPoleClosed.row04_closedConstruction

/-- AR's sixth family (Figure-8 row 05).  The readable proof follows the
paper's figure: two banana pairs and a marked configuration-3 pair, with the
interior chips carried by kinked split-ramp scripts.  One chamber is proved
and the figure's remaining chambers are its orbit under the two involutions. -/
theorem row05_sixthFamily : RowConstruction row05Core := by
  exact GenusFiveRow05.row05_closedConstruction

/-- AR's seventh family (Figure-8 row 08).  The readable proof follows the
paper's chambers: banana pairs, the double-chip banana pair, and the chipped
triangle, with interior chips on kinked split-ramp scripts; the fourth
chamber is the sigma image of the third. -/
theorem row08_seventhFamily : RowConstruction row08Core := by
  exact GenusFiveRow08.row08_closedConstruction

/-- AR's ninth family (Figure-8 row 10).  Each chamber of the displayed
minimum is one marked tripod and one instance of AR's eleventh picture,
formalized in `ConfigurationEleven`; the third chamber is the sigma image
of the second. -/
theorem row10_ninthFamily : RowConstruction row10Core := by
  exact GenusFiveRow10.row10_closedConstruction

/-! ## The ten length-independent constructions -/

/-- Third displayed core, closed by the common canonical construction and
discrete specialization. -/
theorem row03_straightforward : RowConstruction row03Core := by
  exact GenusFiveTwoPoleClosed.row03_closedConstruction

/-- Sixth displayed core, one of AR's straightforward constructions.  The
readable proof is a **guarding set**: chips at `0, 3, 4, 7`, the hub `2`
covered by a configuration-2 tripod and the far end of each of the three
bananas by AR's sixth picture, with `Guarding.GuardingSet.closedConstruction`
doing the closing.  The generated eight-module fixed cover is retired to the
archival root. -/
theorem row06_straightforward : RowConstruction row06Core := by
  exact GenusFiveRow06.row06_closedConstruction

/-- Seventh displayed core, closed by the common canonical construction and
discrete specialization. -/
theorem row07_straightforward : RowConstruction row07Core := by
  exact GenusFiveTwoPoleClosed.row07_closedConstruction

/-- Ninth displayed core. The formalization uses the length-independent divisor with chips at
`1,2,3,7`, read as one chipped triangle and one fifth-configuration
picture, uniform on the whole closed orthant. -/
theorem row09_straightforward : RowConstruction row09Core := by
  exact GenusFiveRow09.row09_closedConstruction

/-- Eleventh displayed core, one of AR's straightforward constructions. -/
theorem row11_straightforward : RowConstruction row11Core := by
  exact GenusFiveRow11.row11_closedConstruction

/-- Twelfth displayed core, one of AR's straightforward constructions.  The
canonical proof is the guarding set of `GenusFiveRow12Guarding`: the row's two
`isCenter` tables are fed into the `guard` field and
`Guarding.GuardingSet.closedConstruction` does the rest. -/
theorem row12_straightforward : RowConstruction row12Core := by
  exact GenusFiveRow12Guarding.row12_closedConstruction

/-- Thirteenth displayed core, closed by the common canonical construction
and discrete specialization. -/
theorem row13_straightforward : RowConstruction row13Core := by
  exact GenusFiveTwoPoleClosed.row13_closedConstruction

/-- Fourteenth displayed core.  The readable proof uses AR's own divisor and
decomposition: three tripod centres and one banana-tail centre, the latter
being AR's sixth local picture, formalized in `ConfigurationBananaTail`.
The generated fixed cover is retired to the archival root. -/
theorem row14_straightforward : RowConstruction row14Core := by
  exact GenusFiveRow14.row14_closedConstruction

/-- Fifteenth displayed core, one of AR's straightforward constructions. -/
theorem row15_straightforward : RowConstruction row15Core := by
  exact GenusFiveRow15.row15_closedConstruction

/-- Sixteenth displayed core, one of AR's straightforward constructions. -/
theorem row16_straightforward : RowConstruction row16Core := by
  exact GenusFiveRow16.row16_closedConstruction

/-! ## A single aggregate for downstream closed-face classification -/

/-- All sixteen closed source constructions, without yet asserting that they
exhaust the cubic cores or that every residual pseudocore is one of their
nonloopy forest faces or an already solved structural case. -/
structure CubicAtlasConstructions : Prop where
  row01 : RowConstruction row01Core
  row02 : RowConstruction row02Core
  row03 : RowConstruction row03Core
  row04 : RowConstruction row04Core
  row05 : RowConstruction row05Core
  row06 : RowConstruction row06Core
  row07 : RowConstruction row07Core
  row08 : RowConstruction row08Core
  row09 : RowConstruction row09Core
  row10 : RowConstruction row10Core
  row11 : RowConstruction row11Core
  row12 : RowConstruction row12Core
  row13 : RowConstruction row13Core
  row14 : RowConstruction row14Core
  row15 : RowConstruction row15Core
  row16 : RowConstruction row16Core

/-- The hand-coded AR construction ledger, assembled from the sixteen
independently replaceable proofs above. -/
theorem cubicAtlasConstructions : CubicAtlasConstructions where
  row01 := row01_firstFamily
  row02 := row02_secondFamily
  row03 := row03_straightforward
  row04 := row04_fourthFamily
  row05 := row05_sixthFamily
  row06 := row06_straightforward
  row07 := row07_straightforward
  row08 := row08_seventhFamily
  row09 := row09_straightforward
  row10 := row10_ninthFamily
  row11 := row11_straightforward
  row12 := row12_straightforward
  row13 := row13_straightforward
  row14 := row14_straightforward
  row15 := row15_straightforward
  row16 := row16_straightforward

/-! ## The separate degeneration boundary -/

/-- The remaining non-construction part of AR's genus-five argument: classify
every valid loop-aware pseudocore as a face of one of the sixteen closed cubic
constructions or as one of the already available structural cases.

The row constructions themselves now include nonloopy forest contractions.
Thus this interface contains classification and structural exits, not a new
rank-transport theorem.  The exceptional second- and fourth-family boundary
divisors belong inside those two closed constructions. -/
def CubicAtlasClosedCoverage : Prop :=
  CubicAtlasConstructions → GenusFivePseudocorePencils

/-- Once the independent degeneration/classification boundary is supplied,
the sixteen construction proofs feed the public genus-five reduction. -/
theorem genusFivePseudocorePencils_of_cubicAtlasClosedCoverage
    (coverage : CubicAtlasClosedCoverage) :
    GenusFivePseudocorePencils :=
  coverage cubicAtlasConstructions

/-- The closed atlas coverage, together with the sixteen row constructions,
supplies the critical genus-five degree-four pencil on every connected graph.
This is the complete public composition from the finite boundary to the
semantic graph statement. -/
theorem genusFiveRankOneExistence_of_cubicAtlasClosedCoverage
    (coverage : CubicAtlasClosedCoverage) :
    GenusFiveRankOneExistence :=
  AtanasovRanganathan.genusFiveRankOneExistence_of_pseudocorePencils
    (genusFivePseudocorePencils_of_cubicAtlasClosedCoverage coverage)

/-- Public end-to-end assembly.  The genus-four pencil and the finite closed
atlas coverage are the only explicit inputs; the sixteen row constructions
are the sixteen declarations above. -/
theorem brillNoetherExistenceThroughFive_of_cubicAtlasClosedCoverage
    (genusFour : GenusFourRankOneExistence)
    (coverage : CubicAtlasClosedCoverage) :
    BrillNoetherExistenceThroughFive :=
  AtanasovRanganathan.brillNoetherExistenceThroughFive_of_geometricInputs
    { genusFour := genusFour
      genusFivePseudocores :=
        genusFivePseudocorePencils_of_cubicAtlasClosedCoverage coverage }

end AtanasovRanganathan.GenusFiveConstructions
