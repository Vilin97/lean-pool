/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.BarrierPotential
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ColoringFramework
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.DynamicColoring
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LaplacianBasics
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LoewnerPullback
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.OneSidedBarrier
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ResolventBound

/-!
# Problem 6 — auxiliary modules

Re-exports all auxiliary sub-modules used by `Problem6`:

- `LaplacianBasics`: edge / graph / induced Laplacians, `IsEpsLight`
- `BarrierPotential`: BSS barrier potential `barrierPotential`
- `ResolventBound`: PSD resolvent trace inequality
- `OneSidedBarrier`: one-sided barrier lemma (Lemma 6.1)
- `ColoringFramework`: `PartialColoring`, pigeonhole bounds
- `DynamicColoring`: induced-Laplacian monotonicity and positive semidefiniteness
- `LoewnerPullback`: Loewner pullback to `ε`-lightness
-/
