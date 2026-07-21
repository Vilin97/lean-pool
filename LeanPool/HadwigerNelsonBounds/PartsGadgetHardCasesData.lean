/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData0
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData1
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData2
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData3
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData4
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData5
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData6

/-! Generated aggregation and routing for the hard normalized cases. -/

namespace HadwigerNelsonBounds

/-- All independently checked hard-case certificates. -/
def partsGadgetHardCertificates (index : Fin 31) : PartsGadgetCertificate :=
  match index.val with
  | 0 => partsGadgetHardCertificate0
  | 1 => partsGadgetHardCertificate1
  | 2 => partsGadgetHardCertificate2
  | 3 => partsGadgetHardCertificate3
  | 4 => partsGadgetHardCertificate4
  | 5 => partsGadgetHardCertificate5
  | 6 => partsGadgetHardCertificate6
  | 7 => partsGadgetHardCertificate7
  | 8 => partsGadgetHardCertificate8
  | 9 => partsGadgetHardCertificate9
  | 10 => partsGadgetHardCertificate10
  | 11 => partsGadgetHardCertificate11
  | 12 => partsGadgetHardCertificate12
  | 13 => partsGadgetHardCertificate13
  | 14 => partsGadgetHardCertificate14
  | 15 => partsGadgetHardCertificate15
  | 16 => partsGadgetHardCertificate16
  | 17 => partsGadgetHardCertificate17
  | 18 => partsGadgetHardCertificate18
  | 19 => partsGadgetHardCertificate19
  | 20 => partsGadgetHardCertificate20
  | 21 => partsGadgetHardCertificate21
  | 22 => partsGadgetHardCertificate22
  | 23 => partsGadgetHardCertificate23
  | 24 => partsGadgetHardCertificate24
  | 25 => partsGadgetHardCertificate25
  | 26 => partsGadgetHardCertificate26
  | 27 => partsGadgetHardCertificate27
  | 28 => partsGadgetHardCertificate28
  | 29 => partsGadgetHardCertificate29
  | 30 => partsGadgetHardCertificate30
  | _ => partsGadgetHardCertificate0

/-- Routing nodes covering every unblocked hard normalized coloring. -/
def partsGadgetHardCaseNodes : Array (PartsGadgetCaseNode 31) := #[
  PartsGadgetCaseNode.branch 19 ![0, 0, 2, 29],
  PartsGadgetCaseNode.branch 12 ![0, 3, 0, 4],
  PartsGadgetCaseNode.leaf 0,
  PartsGadgetCaseNode.branch 7 ![5, 27, 28, 0],
  PartsGadgetCaseNode.branch 17 ![0, 6, 10, 26],
  PartsGadgetCaseNode.branch 4 ![0, 7, 8, 9],
  PartsGadgetCaseNode.leaf 1,
  PartsGadgetCaseNode.leaf 2,
  PartsGadgetCaseNode.leaf 3,
  PartsGadgetCaseNode.branch 16 ![11, 24, 0, 25],
  PartsGadgetCaseNode.branch 1 ![0, 12, 16, 17],
  PartsGadgetCaseNode.branch 22 ![0, 13, 14, 15],
  PartsGadgetCaseNode.leaf 4,
  PartsGadgetCaseNode.leaf 5,
  PartsGadgetCaseNode.leaf 6,
  PartsGadgetCaseNode.leaf 7,
  PartsGadgetCaseNode.branch 9 ![0, 18, 22, 23],
  PartsGadgetCaseNode.branch 22 ![0, 19, 20, 21],
  PartsGadgetCaseNode.leaf 8,
  PartsGadgetCaseNode.leaf 9,
  PartsGadgetCaseNode.leaf 10,
  PartsGadgetCaseNode.leaf 11,
  PartsGadgetCaseNode.leaf 12,
  PartsGadgetCaseNode.leaf 13,
  PartsGadgetCaseNode.leaf 14,
  PartsGadgetCaseNode.leaf 15,
  PartsGadgetCaseNode.leaf 16,
  PartsGadgetCaseNode.leaf 17,
  PartsGadgetCaseNode.branch 12 ![0, 30, 34, 0],
  PartsGadgetCaseNode.branch 1 ![0, 31, 32, 33],
  PartsGadgetCaseNode.leaf 18,
  PartsGadgetCaseNode.leaf 19,
  PartsGadgetCaseNode.leaf 20,
  PartsGadgetCaseNode.branch 6 ![0, 35, 0, 36],
  PartsGadgetCaseNode.leaf 21,
  PartsGadgetCaseNode.branch 7 ![37, 49, 0, 0],
  PartsGadgetCaseNode.branch 1 ![0, 38, 39, 0],
  PartsGadgetCaseNode.leaf 22,
  PartsGadgetCaseNode.branch 4 ![0, 40, 44, 45],
  PartsGadgetCaseNode.branch 8 ![0, 41, 42, 43],
  PartsGadgetCaseNode.leaf 23,
  PartsGadgetCaseNode.leaf 24,
  PartsGadgetCaseNode.leaf 25,
  PartsGadgetCaseNode.leaf 26,
  PartsGadgetCaseNode.branch 8 ![0, 46, 47, 48],
  PartsGadgetCaseNode.leaf 27,
  PartsGadgetCaseNode.leaf 28,
  PartsGadgetCaseNode.leaf 29,
  PartsGadgetCaseNode.leaf 30,
]

/-- The complete hard-case routing tree. -/
def partsGadgetHardCaseTree : PartsGadgetCaseTree 31 := {
  roots := [⟨5, 0⟩, ⟨31, 3⟩, ⟨18, 0⟩, ⟨25, 1⟩]
  nodeCount := 49
  nodes := partsGadgetHardCaseNodes
}

end HadwigerNelsonBounds
