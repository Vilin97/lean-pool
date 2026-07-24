/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification0
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification1
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification2
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification3
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification4
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification5
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification6
import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification7

/-! Aggregated kernel and routing checks for the hard normalized cases. -/

namespace HadwigerNelsonBounds

/-- Every hard-case leaf certificate has been kernel checked. -/
theorem partsGadgetHardCertificates_verify (index : Fin 31) :
    (partsGadgetHardCertificates index).Verifies := by
  fin_cases index
  · exact partsGadgetHardCertificate0_verifies
  · exact partsGadgetHardCertificate1_verifies
  · exact partsGadgetHardCertificate2_verifies
  · exact partsGadgetHardCertificate3_verifies
  · exact partsGadgetHardCertificate4_verifies
  · exact partsGadgetHardCertificate5_verifies
  · exact partsGadgetHardCertificate6_verifies
  · exact partsGadgetHardCertificate7_verifies
  · exact partsGadgetHardCertificate8_verifies
  · exact partsGadgetHardCertificate9_verifies
  · exact partsGadgetHardCertificate10_verifies
  · exact partsGadgetHardCertificate11_verifies
  · exact partsGadgetHardCertificate12_verifies
  · exact partsGadgetHardCertificate13_verifies
  · exact partsGadgetHardCertificate14_verifies
  · exact partsGadgetHardCertificate15_verifies
  · exact partsGadgetHardCertificate16_verifies
  · exact partsGadgetHardCertificate17_verifies
  · exact partsGadgetHardCertificate18_verifies
  · exact partsGadgetHardCertificate19_verifies
  · exact partsGadgetHardCertificate20_verifies
  · exact partsGadgetHardCertificate21_verifies
  · exact partsGadgetHardCertificate22_verifies
  · exact partsGadgetHardCertificate23_verifies
  · exact partsGadgetHardCertificate24_verifies
  · exact partsGadgetHardCertificate25_verifies
  · exact partsGadgetHardCertificate26_verifies
  · exact partsGadgetHardCertificate27_verifies
  · exact partsGadgetHardCertificate28_verifies
  · exact partsGadgetHardCertificate29_verifies
  · exact partsGadgetHardCertificate30_verifies

/-- The case router covers every unblocked normalized color. -/
theorem partsGadgetHardCaseTree_verifiesRouting :
    partsGadgetHardCaseTree.VerifiesRouting partsGadgetHardCertificates := by
  decide

end HadwigerNelsonBounds
