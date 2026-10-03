/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolev
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.Limit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient

/-! # Cube Embedding -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

/-!
# The cube Sobolev embedding

The single theorem below, `cube_sobolev_embedding`, is the cube Sobolev
embedding at the critical exponent `2* = 2d/(d−2)`, stated against the ambient
`H1Function` / `volumeMeasureOn` / `axisCube` types and proved via
`cubeSobolevEmbedding`.

For `u ∈ H¹(U)` on an open axis cube `U = axisCube z L` (no boundary vanishing
assumed), the route is: even-reflection extension across each face, a smooth
cutoff to compact support inside the tripled box, mathlib's
Gagliardo–Nirenberg–Sobolev inequality on each smooth compactly supported
approximant, and passage to the limit, with the reflection/cutoff constants and
the `L⁻¹` factor collected into a single dimensional constant.

Norms are in `eLpNorm` house style against `volumeMeasureOn U`, critical
exponent `twoStar d = 2d/(d−2)`, and gradient term the sum of the coordinate
`L²` norms `∑ i ‖∂ᵢu‖_{L²(U)}`.
-/

noncomputable section

/-- **E1 (cube Sobolev embedding, critical exponent `2* = 2d/(d−2)`).**

For `d ≥ 3` there is a constant `C = C(d) > 0` such that for every open axis cube
`U = axisCube z L` of side `L > 0` and every `u ∈ H¹(U)` (the library's `H1Function U`, no
boundary vanishing),
`‖u‖_{L^{2*}(U)} ≤ C (‖∇u‖_{L²(U)} + L⁻¹ ‖u‖_{L²(U)})`,
with `‖u‖_{L^{2*}(U)} = eLpNorm u.toFun (twoStar d) (volumeMeasureOn U)` and the
gradient term the sum of the coordinate `L²(U)` norms of `u.grad`.

Proved via `cubeSobolevEmbedding` (`CubeEmbedding/Limit.lean`). -/
theorem cube_sobolev_embedding {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun (twoStar d) (volumeMeasureOn (axisCube z L))
          ≤ (C : ℝ≥0∞) *
              ((∑ i : Fin d,
                    eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)))
                + ENNReal.ofReal L⁻¹
                    * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))) :=
  cubeSobolevEmbedding hd

end

end Homogenization
