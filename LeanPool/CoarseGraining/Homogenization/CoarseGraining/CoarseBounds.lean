/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.LawObservable

/-!
# Coarse sandwich, a.e. bridge, and law-level measurability

Root facade for the remaining parts of Proposition 2.2 of the high-moment paper
(Armstrong–Kuusi–Loher, to appear).

Submodules:

* `CoarseBounds.Sandwich` — item **C1** (the coarse diagonal block-Loewner
  sandwich `blockDiag (½•1) ((2Θ)⁻¹•1) ≤ 𝐀(U;a) ≤ blockDiag ((2Θ)•1) (2•1)`)
  and **C1′** (its scalar corollaries), together with the mean-zero
  average-recovery identities for admissible corrections.
* `CoarseBounds.AeBridge` — item **C2**: the `Mu`/`coarseBlockMatrix`
  a.e.-congruence (C2 i), the measurability of the elliptic locus via the
  inverse-free closed-set reformulation (C2 ii), the elliptic truncation
  (C2 iii), and the consumer-facing bridge packaging (C2 iv).
* `CoarseBounds.LawObservable` — item **C3**: a.e.-strong measurability of the
  scalar coarse observable under a `RestrictionLawCarrier`, plus its a.s. bounds and
  integrability under an a.s.-elliptic law.

All matrix/vector work is on `Vec d = Fin d → ℝ` / `Mat d`; no `EuclideanSpace`.
-/

@[expose] public section
