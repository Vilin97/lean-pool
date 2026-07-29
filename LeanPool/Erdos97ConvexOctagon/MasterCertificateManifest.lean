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
def masterCertificateInitialClauses : ℕ := 3263

/-- Number of retained LRAT additions. -/
def masterCertificateAdditions : ℕ := 4294

/-- Number of omitted LRAT deletion records. -/
def masterCertificateDeletions : ℕ := 3145

/-- Total number of actions in the generated LRAT text. -/
def masterCertificateActions : ℕ := 7439

/-- Number of packed bytes. -/
def masterCertificatePackedBytes : ℕ := 316443

/-- Number of base64 characters. -/
def masterCertificateEncodedCharacters : ℕ := 421924

/-- Number of generated data modules. -/
def masterCertificateDataModules : ℕ := 10

/-- Number of sequential proof-stage modules. -/
def masterCertificateStageModules : ℕ := 3

/-- Maximum retained additions reconstructed in one proof stage. -/
def masterCertificateMaximumAdditionsPerStage : ℕ := 1432

/-- Retained additions reconstructed by each sequential proof stage. -/
def masterCertificateStageAdditionCounts : List ℕ :=
  [1432, 1432, 1430]

/-- Zero-based addition boundaries of the sequential proof stages. -/
def masterCertificateStageBoundaries : List ℕ :=
  [0, 1432] ++
    [2864, 4294]

/-- Maximum measured bytes used by one packed natural number. -/
def masterCertificateMaximumVarintBytes : ℕ := 2

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
  "e793eacb1b67901daad1a61d11e9c6f20ccc7ad832b67d16fe7550c1ea292e83"

/-- SHA-256 of the packed certificate bytes. -/
def masterCertificatePackedSha256 : String :=
  "55a6fad508976f2ccb1a0ee412ca941564df743a4d6cf4552be1bd3c3360ccae"

/-- Pinned CaDiCaL source commit. -/
def masterCertificateCadicalCommit : String :=
  "c60730422e758ef1cebe7aeddf2dda31c996bf04"

/-- Pinned drat-trim source commit. -/
def masterCertificateDratTrimCommit : String :=
  "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"

end Erdos97Octagon.RawIncidence
