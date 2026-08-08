/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15

/-! # Exhaustive fixed-branch coverage-certificate manifest -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Certificate claim for each of the 245 canonical fixed-row branches. -/
def coverageBranchClaim (orbit : Fin 7) (rowTwo : Fin 35) : BranchClaim :=
  match orbit.val, rowTwo.val with
  | 0, 0 => .patternTwo 0
  | 0, 1 => .patternTwo 0
  | 0, 2 => .patternTwo 0
  | 0, 3 => .patternTwo 0
  | 0, 4 => .patternTwo 0
  | 0, 5 => .patternTwo 0
  | 0, 6 => .patternTwo 0
  | 0, 7 => .patternTwo 0
  | 0, 8 => .patternTwo 0
  | 0, 9 => .patternTwo 0
  | 0, 10 => .patternTwo 0
  | 0, 11 => .patternTwo 0
  | 0, 12 => .patternTwo 0
  | 0, 13 => .patternTwo 0
  | 0, 14 => .patternTwo 0
  | 0, 15 => .patternTwo 0
  | 0, 16 => .patternTwo 0
  | 0, 17 => .patternTwo 0
  | 0, 18 => .patternTwo 0
  | 0, 19 => .patternTwo 0
  | 0, 20 => .patternTwo 0
  | 0, 21 => .patternTwo 0
  | 0, 22 => .patternTwo 0
  | 0, 23 => .patternTwo 0
  | 0, 24 => .patternTwo 0
  | 0, 25 => .patternTwo 0
  | 0, 26 => .patternTwo 0
  | 0, 27 => .patternTwo 0
  | 0, 28 => .patternTwo 0
  | 0, 29 => .patternTwo 0
  | 0, 30 => .patternTwo 0
  | 0, 31 => .patternTwo 0
  | 0, 32 => .patternTwo 0
  | 0, 33 => .patternTwo 0
  | 0, 34 => .patternTwo 0
  | 1, 0 => .patternThree 1
  | 1, 1 => .patternThree 178
  | 1, 2 => .patternThree 178
  | 1, 3 => .patternThree 178
  | 1, 4 => .search branchClaims1Row4
  | 1, 5 => .search branchClaims1Row5
  | 1, 6 => .search branchClaims1Row6
  | 1, 7 => .search branchClaims1Row7
  | 1, 8 => .search branchClaims1Row8
  | 1, 9 => .search branchClaims1Row9
  | 1, 10 => .patternThree 178
  | 1, 11 => .patternThree 178
  | 1, 12 => .patternThree 178
  | 1, 13 => .patternThree 178
  | 1, 14 => .patternThree 178
  | 1, 15 => .patternThree 178
  | 1, 16 => .search branchClaims1Row16
  | 1, 17 => .search branchClaims1Row17
  | 1, 18 => .search branchClaims1Row18
  | 1, 19 => .search branchClaims1Row19
  | 1, 20 => .patternThree 1
  | 1, 21 => .patternThree 1
  | 1, 22 => .patternThree 1
  | 1, 23 => .patternThree 179
  | 1, 24 => .patternThree 179
  | 1, 25 => .patternThree 179
  | 1, 26 => .search branchClaims1Row26
  | 1, 27 => .search branchClaims1Row27
  | 1, 28 => .search branchClaims1Row28
  | 1, 29 => .search branchClaims1Row29
  | 1, 30 => .search branchClaims1Row30
  | 1, 31 => .search branchClaims1Row31
  | 1, 32 => .search branchClaims1Row32
  | 1, 33 => .search branchClaims1Row33
  | 1, 34 => .search branchClaims1Row34
  | 2, 0 => .patternThree 1
  | 2, 1 => .search branchClaims2Row1
  | 2, 2 => .search branchClaims2Row2
  | 2, 3 => .search branchClaims2Row3
  | 2, 4 => .search branchClaims2Row4
  | 2, 5 => .search branchClaims2Row5
  | 2, 6 => .search branchClaims2Row6
  | 2, 7 => .patternThree 2
  | 2, 8 => .search branchClaims2Row8
  | 2, 9 => .search branchClaims2Row9
  | 2, 10 => .search branchClaims2Row10
  | 2, 11 => .search branchClaims2Row11
  | 2, 12 => .search branchClaims2Row12
  | 2, 13 => .patternThree 2
  | 2, 14 => .search branchClaims2Row14
  | 2, 15 => .search branchClaims2Row15
  | 2, 16 => .patternThree 2
  | 2, 17 => .search branchClaims2Row17
  | 2, 18 => .search branchClaims2Row18
  | 2, 19 => .patternThree 2
  | 2, 20 => .patternThree 1
  | 2, 21 => .patternThree 1
  | 2, 22 => .patternThree 1
  | 2, 23 => .search branchClaims2Row23
  | 2, 24 => .search branchClaims2Row24
  | 2, 25 => .search branchClaims2Row25
  | 2, 26 => .search branchClaims2Row26
  | 2, 27 => .search branchClaims2Row27
  | 2, 28 => .search branchClaims2Row28
  | 2, 29 => .search branchClaims2Row29
  | 2, 30 => .search branchClaims2Row30
  | 2, 31 => .search branchClaims2Row31
  | 2, 32 => .search branchClaims2Row32
  | 2, 33 => .search branchClaims2Row33
  | 2, 34 => .search branchClaims2Row34
  | 3, 0 => .patternThree 1
  | 3, 1 => .search branchClaims3Row1
  | 3, 2 => .search branchClaims3Row2
  | 3, 3 => .search branchClaims3Row3
  | 3, 4 => .search branchClaims3Row4
  | 3, 5 => .search branchClaims3Row5
  | 3, 6 => .search branchClaims3Row6
  | 3, 7 => .patternThree 2
  | 3, 8 => .patternThree 4
  | 3, 9 => .patternThree 5
  | 3, 10 => .search branchClaims3Row10
  | 3, 11 => .search branchClaims3Row11
  | 3, 12 => .search branchClaims3Row12
  | 3, 13 => .patternThree 2
  | 3, 14 => .patternThree 4
  | 3, 15 => .patternThree 5
  | 3, 16 => .patternThree 2
  | 3, 17 => .patternThree 4
  | 3, 18 => .patternThree 5
  | 3, 19 => .patternThree 2
  | 3, 20 => .patternThree 1
  | 3, 21 => .patternThree 1
  | 3, 22 => .patternThree 1
  | 3, 23 => .search branchClaims3Row23
  | 3, 24 => .search branchClaims3Row24
  | 3, 25 => .search branchClaims3Row25
  | 3, 26 => .search branchClaims3Row26
  | 3, 27 => .search branchClaims3Row27
  | 3, 28 => .search branchClaims3Row28
  | 3, 29 => .patternThree 6
  | 3, 30 => .search branchClaims3Row30
  | 3, 31 => .search branchClaims3Row31
  | 3, 32 => .search branchClaims3Row32
  | 3, 33 => .patternThree 6
  | 3, 34 => .patternThree 6
  | 4, 0 => .patternTwo 0
  | 4, 1 => .patternTwo 0
  | 4, 2 => .patternTwo 0
  | 4, 3 => .patternTwo 0
  | 4, 4 => .patternTwo 0
  | 4, 5 => .patternTwo 0
  | 4, 6 => .patternTwo 0
  | 4, 7 => .patternTwo 0
  | 4, 8 => .patternTwo 0
  | 4, 9 => .patternTwo 0
  | 4, 10 => .patternTwo 0
  | 4, 11 => .patternTwo 0
  | 4, 12 => .patternTwo 0
  | 4, 13 => .patternTwo 0
  | 4, 14 => .patternTwo 0
  | 4, 15 => .patternTwo 0
  | 4, 16 => .patternTwo 0
  | 4, 17 => .patternTwo 0
  | 4, 18 => .patternTwo 0
  | 4, 19 => .patternTwo 0
  | 4, 20 => .patternTwo 0
  | 4, 21 => .patternTwo 0
  | 4, 22 => .patternTwo 0
  | 4, 23 => .patternTwo 0
  | 4, 24 => .patternTwo 0
  | 4, 25 => .patternTwo 0
  | 4, 26 => .patternTwo 0
  | 4, 27 => .patternTwo 0
  | 4, 28 => .patternTwo 0
  | 4, 29 => .patternTwo 0
  | 4, 30 => .patternTwo 0
  | 4, 31 => .patternTwo 0
  | 4, 32 => .patternTwo 0
  | 4, 33 => .patternTwo 0
  | 4, 34 => .patternTwo 0
  | 5, 0 => .patternThree 1
  | 5, 1 => .patternThree 180
  | 5, 2 => .patternThree 180
  | 5, 3 => .patternThree 180
  | 5, 4 => .search branchClaims5Row4
  | 5, 5 => .search branchClaims5Row5
  | 5, 6 => .search branchClaims5Row6
  | 5, 7 => .search branchClaims5Row7
  | 5, 8 => .search branchClaims5Row8
  | 5, 9 => .search branchClaims5Row9
  | 5, 10 => .search branchClaims5Row10
  | 5, 11 => .search branchClaims5Row11
  | 5, 12 => .search branchClaims5Row12
  | 5, 13 => .patternThree 3
  | 5, 14 => .search branchClaims5Row14
  | 5, 15 => .search branchClaims5Row15
  | 5, 16 => .search branchClaims5Row16
  | 5, 17 => .search branchClaims5Row17
  | 5, 18 => .search branchClaims5Row18
  | 5, 19 => .search branchClaims5Row19
  | 5, 20 => .patternThree 1
  | 5, 21 => .patternThree 1
  | 5, 22 => .patternThree 1
  | 5, 23 => .patternThree 3
  | 5, 24 => .search branchClaims5Row24
  | 5, 25 => .search branchClaims5Row25
  | 5, 26 => .search branchClaims5Row26
  | 5, 27 => .search branchClaims5Row27
  | 5, 28 => .search branchClaims5Row28
  | 5, 29 => .search branchClaims5Row29
  | 5, 30 => .patternThree 3
  | 5, 31 => .search branchClaims5Row31
  | 5, 32 => .search branchClaims5Row32
  | 5, 33 => .patternThree 3
  | 5, 34 => .search branchClaims5Row34
  | 6, 0 => .patternThree 1
  | 6, 1 => .search branchClaims6Row1
  | 6, 2 => .search branchClaims6Row2
  | 6, 3 => .search branchClaims6Row3
  | 6, 4 => .search branchClaims6Row4
  | 6, 5 => .search branchClaims6Row5
  | 6, 6 => .search branchClaims6Row6
  | 6, 7 => .search branchClaims6Row7
  | 6, 8 => .search branchClaims6Row8
  | 6, 9 => .search branchClaims6Row9
  | 6, 10 => .search branchClaims6Row10
  | 6, 11 => .search branchClaims6Row11
  | 6, 12 => .search branchClaims6Row12
  | 6, 13 => .search branchClaims6Row13
  | 6, 14 => .search branchClaims6Row14
  | 6, 15 => .search branchClaims6Row15
  | 6, 16 => .search branchClaims6Row16
  | 6, 17 => .search branchClaims6Row17
  | 6, 18 => .search branchClaims6Row18
  | 6, 19 => .patternThree 6
  | 6, 20 => .patternThree 1
  | 6, 21 => .patternThree 1
  | 6, 22 => .patternThree 1
  | 6, 23 => .search branchClaims6Row23
  | 6, 24 => .search branchClaims6Row24
  | 6, 25 => .search branchClaims6Row25
  | 6, 26 => .search branchClaims6Row26
  | 6, 27 => .search branchClaims6Row27
  | 6, 28 => .search branchClaims6Row28
  | 6, 29 => .patternThree 6
  | 6, 30 => .search branchClaims6Row30
  | 6, 31 => .search branchClaims6Row31
  | 6, 32 => .search branchClaims6Row32
  | 6, 33 => .patternThree 6
  | 6, 34 => .patternThree 6
  | _, _ => .patternTwo 0

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
