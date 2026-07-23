/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsCertificateData0
import LeanPool.HadwigerNelsonBounds.PartsCertificateData1
import LeanPool.HadwigerNelsonBounds.PartsCertificateData2
import LeanPool.HadwigerNelsonBounds.PartsCertificateData3
import LeanPool.HadwigerNelsonBounds.PartsCertificateData4
import LeanPool.HadwigerNelsonBounds.PartsCertificateData5
import LeanPool.HadwigerNelsonBounds.PartsCertificateData6

/-!
# Parts certificate roots and exact graph symmetries

The six permutations are the stabilizer of the normalized 2-Golomb root.
Together with swapping the two unused color names, they expand 36 orbit
representatives to all 432 proper normalized root colorings.
-/

namespace HadwigerNelsonBounds

/-- The 36 normalized coloring-tree representatives. -/
def partsBaseCertificates : Array PartsCertificate := #[
  partsBaseCertificate0,
  partsBaseCertificate1,
  partsBaseCertificate2,
  partsBaseCertificate3,
  partsBaseCertificate4,
  partsBaseCertificate5,
  partsBaseCertificate6,
  partsBaseCertificate7,
  partsBaseCertificate8,
  partsBaseCertificate9,
  partsBaseCertificate10,
  partsBaseCertificate11,
  partsBaseCertificate12,
  partsBaseCertificate13,
  partsBaseCertificate14,
  partsBaseCertificate15,
  partsBaseCertificate16,
  partsBaseCertificate17,
  partsBaseCertificate18,
  partsBaseCertificate19,
  partsBaseCertificate20,
  partsBaseCertificate21,
  partsBaseCertificate22,
  partsBaseCertificate23,
  partsBaseCertificate24,
  partsBaseCertificate25,
  partsBaseCertificate26,
  partsBaseCertificate27,
  partsBaseCertificate28,
  partsBaseCertificate29,
  partsBaseCertificate30,
  partsBaseCertificate31,
  partsBaseCertificate32,
  partsBaseCertificate33,
  partsBaseCertificate34,
  partsBaseCertificate35,
]

end HadwigerNelsonBounds
