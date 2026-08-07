/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers00
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers01
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers02
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers03
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers04
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers05
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers06
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers07
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers08
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers09
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers10
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers11
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers12
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers13
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers14
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers15
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers16
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers17
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers18
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers19
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers20
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers21

/-! # Deduplicated repeated-pair row-mask covers -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Conflict covers in shallow 64-entry groups. -/
def conflictCoverGroups : Array (Array ConflictCover) :=
  #[conflictCovers00, conflictCovers01, conflictCovers02, conflictCovers03, conflictCovers04,
  conflictCovers05, conflictCovers06, conflictCovers07, conflictCovers08, conflictCovers09,
  conflictCovers10, conflictCovers11, conflictCovers12, conflictCovers13, conflictCovers14,
  conflictCovers15, conflictCovers16, conflictCovers17, conflictCovers18, conflictCovers19,
  conflictCovers20, conflictCovers21, conflictCovers22, conflictCovers23, conflictCovers24,
  conflictCovers25, conflictCovers26, conflictCovers27, conflictCovers28, conflictCovers29,
  conflictCovers30, conflictCovers31, conflictCovers32, conflictCovers33, conflictCovers34,
  conflictCovers35, conflictCovers36, conflictCovers37, conflictCovers38, conflictCovers39,
  conflictCovers40, conflictCovers41, conflictCovers42, conflictCovers43, conflictCovers44,
  conflictCovers45, conflictCovers46, conflictCovers47, conflictCovers48, conflictCovers49,
  conflictCovers50, conflictCovers51, conflictCovers52, conflictCovers53, conflictCovers54,
  conflictCovers55, conflictCovers56, conflictCovers57, conflictCovers58, conflictCovers59,
  conflictCovers60, conflictCovers61, conflictCovers62, conflictCovers63, conflictCovers64,
  conflictCovers65, conflictCovers66, conflictCovers67, conflictCovers68, conflictCovers69,
  conflictCovers70, conflictCovers71, conflictCovers72, conflictCovers73, conflictCovers74,
  conflictCovers75, conflictCovers76, conflictCovers77, conflictCovers78, conflictCovers79,
  conflictCovers80, conflictCovers81, conflictCovers82, conflictCovers83, conflictCovers84,
  conflictCovers85, conflictCovers86, conflictCovers87]

/-- The generated table has all 88 shallow conflict-cover groups. -/
theorem conflictCoverGroups_size : conflictCoverGroups.size = 88 := by
  rfl

/-- Number of globally deduplicated conflict covers. -/
def conflictCoverCount : Nat := 5589

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
