/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module


public import LeanPool.KaltonPeck.KaltonPeck
public import LeanPool.KaltonPeck.KaltonPeck.Basic
public import LeanPool.KaltonPeck.KaltonPeck.Support
public import LeanPool.KaltonPeck.KaltonPeck.Support.CanonicalPairing
public import LeanPool.KaltonPeck.KaltonPeck.Support.CgpBlockExtraction
public import LeanPool.KaltonPeck.KaltonPeck.Support.CgpCompactRestriction
public import LeanPool.KaltonPeck.KaltonPeck.Support.CgpStrictlySingularLifting
public import LeanPool.KaltonPeck.KaltonPeck.Support.Coordinates
public import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.QuotientSum
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.RadicalQuotient
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.StrongQuotient
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity
public import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
public import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.GeneralRank
public import LeanPool.KaltonPeck.KaltonPeck.Support.GraphFredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.HilbertGlidingHump
public import LeanPool.KaltonPeck.KaltonPeck.Support.KernelNuclearCorrection
public import LeanPool.KaltonPeck.KaltonPeck.Support.PathParity
public import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingular
public import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularAdd
public import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbert
public import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingularHilbertCompact
public import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic
public import LeanPool.KaltonPeck.KaltonPeck.Support.TargetSupport

/-!
# Rank parity and complex structures on the Kalton–Peck space

Source: url:https://github.com/adas1236/KaltonPeck
Authors: Avik Das
Status: verified
Main declarations: `KaltonPeck.noHyperplaneComplexStructure`
Tags: functional-analysis, banach-spaces, fredholm-theory
MSC: 46B03, 47A53
-/
