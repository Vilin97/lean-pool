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
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData16
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData17
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData18
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData19
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData20
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData21

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
  | 1, 4 => .search branchClaims_1_4
  | 1, 5 => .search branchClaims_1_5
  | 1, 6 => .search branchClaims_1_6
  | 1, 7 => .search branchClaims_1_7
  | 1, 8 => .search branchClaims_1_8
  | 1, 9 => .search branchClaims_1_9
  | 1, 10 => .patternThree 178
  | 1, 11 => .patternThree 178
  | 1, 12 => .patternThree 178
  | 1, 13 => .patternThree 178
  | 1, 14 => .patternThree 178
  | 1, 15 => .patternThree 178
  | 1, 16 => .search branchClaims_1_16
  | 1, 17 => .search branchClaims_1_17
  | 1, 18 => .search branchClaims_1_18
  | 1, 19 => .search branchClaims_1_19
  | 1, 20 => .patternThree 1
  | 1, 21 => .patternThree 1
  | 1, 22 => .patternThree 1
  | 1, 23 => .patternThree 179
  | 1, 24 => .patternThree 179
  | 1, 25 => .patternThree 179
  | 1, 26 => .search branchClaims_1_26
  | 1, 27 => .search branchClaims_1_27
  | 1, 28 => .search branchClaims_1_28
  | 1, 29 => .search branchClaims_1_29
  | 1, 30 => .search branchClaims_1_30
  | 1, 31 => .search branchClaims_1_31
  | 1, 32 => .search branchClaims_1_32
  | 1, 33 => .search branchClaims_1_33
  | 1, 34 => .search branchClaims_1_34
  | 2, 0 => .patternThree 1
  | 2, 1 => .search branchClaims_2_1
  | 2, 2 => .search branchClaims_2_2
  | 2, 3 => .search branchClaims_2_3
  | 2, 4 => .search branchClaims_2_4
  | 2, 5 => .search branchClaims_2_5
  | 2, 6 => .search branchClaims_2_6
  | 2, 7 => .patternThree 2
  | 2, 8 => .search branchClaims_2_8
  | 2, 9 => .search branchClaims_2_9
  | 2, 10 => .search branchClaims_2_10
  | 2, 11 => .search branchClaims_2_11
  | 2, 12 => .search branchClaims_2_12
  | 2, 13 => .patternThree 2
  | 2, 14 => .search branchClaims_2_14
  | 2, 15 => .search branchClaims_2_15
  | 2, 16 => .patternThree 2
  | 2, 17 => .search branchClaims_2_17
  | 2, 18 => .search branchClaims_2_18
  | 2, 19 => .patternThree 2
  | 2, 20 => .patternThree 1
  | 2, 21 => .patternThree 1
  | 2, 22 => .patternThree 1
  | 2, 23 => .search branchClaims_2_23
  | 2, 24 => .search branchClaims_2_24
  | 2, 25 => .search branchClaims_2_25
  | 2, 26 => .search branchClaims_2_26
  | 2, 27 => .search branchClaims_2_27
  | 2, 28 => .search branchClaims_2_28
  | 2, 29 => .search branchClaims_2_29
  | 2, 30 => .search branchClaims_2_30
  | 2, 31 => .search branchClaims_2_31
  | 2, 32 => .search branchClaims_2_32
  | 2, 33 => .search branchClaims_2_33
  | 2, 34 => .search branchClaims_2_34
  | 3, 0 => .patternThree 1
  | 3, 1 => .search branchClaims_3_1
  | 3, 2 => .search branchClaims_3_2
  | 3, 3 => .search branchClaims_3_3
  | 3, 4 => .search branchClaims_3_4
  | 3, 5 => .search branchClaims_3_5
  | 3, 6 => .search branchClaims_3_6
  | 3, 7 => .patternThree 2
  | 3, 8 => .patternThree 4
  | 3, 9 => .patternThree 5
  | 3, 10 => .search branchClaims_3_10
  | 3, 11 => .search branchClaims_3_11
  | 3, 12 => .search branchClaims_3_12
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
  | 3, 23 => .search branchClaims_3_23
  | 3, 24 => .search branchClaims_3_24
  | 3, 25 => .search branchClaims_3_25
  | 3, 26 => .search branchClaims_3_26
  | 3, 27 => .search branchClaims_3_27
  | 3, 28 => .search branchClaims_3_28
  | 3, 29 => .patternThree 6
  | 3, 30 => .search branchClaims_3_30
  | 3, 31 => .search branchClaims_3_31
  | 3, 32 => .search branchClaims_3_32
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
  | 5, 4 => .search branchClaims_5_4
  | 5, 5 => .search branchClaims_5_5
  | 5, 6 => .search branchClaims_5_6
  | 5, 7 => .search branchClaims_5_7
  | 5, 8 => .search branchClaims_5_8
  | 5, 9 => .search branchClaims_5_9
  | 5, 10 => .search branchClaims_5_10
  | 5, 11 => .search branchClaims_5_11
  | 5, 12 => .search branchClaims_5_12
  | 5, 13 => .patternThree 3
  | 5, 14 => .search branchClaims_5_14
  | 5, 15 => .search branchClaims_5_15
  | 5, 16 => .search branchClaims_5_16
  | 5, 17 => .search branchClaims_5_17
  | 5, 18 => .search branchClaims_5_18
  | 5, 19 => .search branchClaims_5_19
  | 5, 20 => .patternThree 1
  | 5, 21 => .patternThree 1
  | 5, 22 => .patternThree 1
  | 5, 23 => .patternThree 3
  | 5, 24 => .search branchClaims_5_24
  | 5, 25 => .search branchClaims_5_25
  | 5, 26 => .search branchClaims_5_26
  | 5, 27 => .search branchClaims_5_27
  | 5, 28 => .search branchClaims_5_28
  | 5, 29 => .search branchClaims_5_29
  | 5, 30 => .patternThree 3
  | 5, 31 => .search branchClaims_5_31
  | 5, 32 => .search branchClaims_5_32
  | 5, 33 => .patternThree 3
  | 5, 34 => .search branchClaims_5_34
  | 6, 0 => .patternThree 1
  | 6, 1 => .search branchClaims_6_1
  | 6, 2 => .search branchClaims_6_2
  | 6, 3 => .search branchClaims_6_3
  | 6, 4 => .search branchClaims_6_4
  | 6, 5 => .search branchClaims_6_5
  | 6, 6 => .search branchClaims_6_6
  | 6, 7 => .search branchClaims_6_7
  | 6, 8 => .search branchClaims_6_8
  | 6, 9 => .search branchClaims_6_9
  | 6, 10 => .search branchClaims_6_10
  | 6, 11 => .search branchClaims_6_11
  | 6, 12 => .search branchClaims_6_12
  | 6, 13 => .search branchClaims_6_13
  | 6, 14 => .search branchClaims_6_14
  | 6, 15 => .search branchClaims_6_15
  | 6, 16 => .search branchClaims_6_16
  | 6, 17 => .search branchClaims_6_17
  | 6, 18 => .search branchClaims_6_18
  | 6, 19 => .patternThree 6
  | 6, 20 => .patternThree 1
  | 6, 21 => .patternThree 1
  | 6, 22 => .patternThree 1
  | 6, 23 => .search branchClaims_6_23
  | 6, 24 => .search branchClaims_6_24
  | 6, 25 => .search branchClaims_6_25
  | 6, 26 => .search branchClaims_6_26
  | 6, 27 => .search branchClaims_6_27
  | 6, 28 => .search branchClaims_6_28
  | 6, 29 => .patternThree 6
  | 6, 30 => .search branchClaims_6_30
  | 6, 31 => .search branchClaims_6_31
  | 6, 32 => .search branchClaims_6_32
  | 6, 33 => .patternThree 6
  | 6, 34 => .patternThree 6
  | _, _ => .patternTwo 0

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
