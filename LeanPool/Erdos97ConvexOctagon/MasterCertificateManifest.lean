/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.LRAT.Format

/-! # Generated master-certificate manifest -/

namespace Erdos97Octagon.RawIncidence

/-- Packed certificate format version. -/
def masterCertificateFormatVersion : ℕ := 1

/-- Number of initial clauses. -/
def masterCertificateInitialClauses : ℕ := 6582

/-- Number of retained LRAT additions. -/
def masterCertificateAdditions : ℕ := 11139

/-- Number of omitted LRAT deletion records. -/
def masterCertificateDeletions : ℕ := 8677

/-- Total number of actions in the generated LRAT text. -/
def masterCertificateActions : ℕ := 19816

/-- Number of packed bytes. -/
def masterCertificatePackedBytes : ℕ := 542830

/-- Number of base64 characters. -/
def masterCertificateEncodedCharacters : ℕ := 723774

/-- Number of generated data modules. -/
def masterCertificateDataModules : ℕ := 17

/-- Number of sequential proof-stage modules. -/
def masterCertificateStageModules : ℕ := 16

/-- Maximum retained additions reconstructed in one proof stage. -/
def masterCertificateMaximumAdditionsPerStage : ℕ := 700

/-- Retained additions reconstructed by each sequential proof stage. -/
def masterCertificateStageAdditionCounts : List ℕ :=
  [700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 700, 639]

/-- Zero-based addition boundaries of the sequential proof stages. -/
def masterCertificateStageBoundaries : List ℕ :=
  [0, 700, 1400, 2100, 2800, 3500, 4200, 4900, 5600] ++
    [6300, 7000, 7700, 8400, 9100, 9800, 10500, 11139]

/-- Maximum measured bytes used by one packed natural number. -/
def masterCertificateMaximumVarintBytes : ℕ := 3

/-- Decoder byte bound for one packed natural number. -/
def masterCertificateVarintByteBound : ℕ := 16

/-- Maximum string literals emitted in one generated data part. -/
def masterCertificateMaximumStringsPerPart : ℕ := 500

/-- Maximum measured compiled-expression steps used by one generated data part. -/
def masterCertificateMaximumStringListExpressionSteps : ℕ := 616

/-- Structural fuel used to decode one generated string-list part. -/
def masterCertificateStringListFuel : ℕ := 640

/-- SHA-256 of the generated DIMACS formula. -/
def masterCertificateCnfSha256 : String :=
  "08c463f6ab9db9cc6925f59fe09a5db880c0b8e4acbecb36258b2e92572c3ae4"

/-- SHA-256 of the normalized LRAT text. -/
def masterCertificateLratSha256 : String :=
  "9775d8f16020ea79871936dcdc064a45e4f8097e054c7322c76a5f049e8551e7"

/-- SHA-256 of the packed certificate bytes. -/
def masterCertificatePackedSha256 : String :=
  "d5646632bb06c66f6f8caf638cbc7cdcdcd127e81ae88b2985b6d3990a4bf932"

/-- Pinned CaDiCaL source commit. -/
def masterCertificateCadicalCommit : String :=
  "c60730422e758ef1cebe7aeddf2dda31c996bf04"

/-- Pinned drat-trim source commit. -/
def masterCertificateDratTrimCommit : String :=
  "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"

end Erdos97Octagon.RawIncidence
