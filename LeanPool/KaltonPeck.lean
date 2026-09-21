/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/

import LeanPool.KaltonPeck.KaltonPeck.Basic
import LeanPool.KaltonPeck.KaltonPeck.Support.CanonicalPairing
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpBlockExtraction
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpCompactRestriction
import LeanPool.KaltonPeck.KaltonPeck.Support.CgpStrictlySingularLifting
import LeanPool.KaltonPeck.KaltonPeck.Support.Coordinates
import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity
import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
import LeanPool.KaltonPeck.KaltonPeck.Support.GeneralRank
import LeanPool.KaltonPeck.KaltonPeck.Support.GraphFredholm
import LeanPool.KaltonPeck.KaltonPeck.Support.HilbertGlidingHump
import LeanPool.KaltonPeck.KaltonPeck.Support.KernelNuclearCorrection
import LeanPool.KaltonPeck.KaltonPeck.Support.PathParity
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingular
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularAdd
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbert
import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbertCompact
import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic
import LeanPool.KaltonPeck.KaltonPeck.Support.TargetSupport
import LeanPool.KaltonPeck.KaltonPeck.Support
import LeanPool.KaltonPeck.KaltonPeck

/-!
# Rank parity and complex structures on the Kalton–Peck space

Source: url:https://github.com/adas1236/KaltonPeck
Authors: Avik Das
Status: verified
Main declarations: `KaltonPeck.rankParityGeneral`, `KaltonPeck.rankParityZ2`, `KaltonPeck.noHyperplaneComplexStructure`
Tags: functional-analysis, banach-spaces, fredholm-theory
MSC: 46B03, 47A53
-/
