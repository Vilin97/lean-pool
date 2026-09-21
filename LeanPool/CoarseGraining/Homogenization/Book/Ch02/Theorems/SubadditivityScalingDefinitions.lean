/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction

/-! # Subadditivity Scaling Definitions -/

open scoped BigOperators

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public triadic partition scaffold for the Chapter 2 subadditivity theorem.

The LaTeX statement is over triadic subcubes of a larger cube. The public
Book-layer theorem keeps a small abstraction here, but the abstraction carries a
triadic realization: cells enumerate descendants of one parent triadic cube, and
the weights are the uniform `\avsum` weights from the notes. -/
structure DomainPartition {d : ℕ} (U : Domain d) where
  Cell : Type
  [instFintype : Fintype Cell]
  cell : Cell → Domain d
  cell_subset_parent : ∀ i : Cell, (cell i : Set (Vec d)) ⊆ (U : Set (Vec d))
  weight : Cell → ℝ
  weight_nonneg : ∀ i : Cell, 0 ≤ weight i
  weight_sum_one : ∑ i : Cell, weight i = 1
  triadic_realization :
    ∃ root : TriadicCube d, ∃ depth : ℕ,
      (U : Set (Vec d)) = openCubeSet root ∧
        ∃ e : Cell ≃ {R : TriadicCube d // R ∈ descendantsAtDepth root depth},
          ∀ i : Cell,
            (cell i : Set (Vec d)) = openCubeSet ((e i).1) ∧
              weight i = ((Fintype.card Cell : ℝ)⁻¹)

namespace DomainPartition

/-- Weighted average over the cells of a public finite partition. -/
noncomputable def weightedAverage {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (f : P.Cell → ℝ) : ℝ := by
  classical
  letI : Fintype P.Cell := P.instFintype
  exact ∑ i : P.Cell, P.weight i * f i

/-- Weighted matrix average over the cells of a public finite partition. -/
noncomputable def weightedMatAverage {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (F : P.Cell → Mat d) : Mat d :=
  fun i j => P.weightedAverage fun c => F c i j

/-- Weighted block-matrix average over the cells of a public finite partition. -/
noncomputable def weightedBlockAverage {d : ℕ} {U : Domain d}
    (P : DomainPartition U) (F : P.Cell → BlockMat d) : BlockMat d :=
  { upperLeft := P.weightedMatAverage fun c => (F c).upperLeft
    upperRight := P.weightedMatAverage fun c => (F c).upperRight
    lowerLeft := P.weightedMatAverage fun c => (F c).lowerLeft
    lowerRight := P.weightedMatAverage fun c => (F c).lowerRight }

end DomainPartition

/-- Public theorem package for `l.cg.subadditivity.basic.definitions`.

Coefficient rescaling is stated a.e. by `CoeffOn.AEScaled`, not by pointwise
equality of representatives. The canonical public theorem proving this package
is `responseSubadditivityAndScalingTheory` in `SubadditivityScaling.lean`. -/
structure ResponseSubadditivityAndScalingTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) : Prop where
  responseJ_subadditive :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i))
      (_hCell : ∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i))
      (p q : Vec d),
      responseJ U a p q ≤
        P.weightedAverage fun i => responseJ (P.cell i) (aCell i) p q
  responseJ_homogeneous :
    ∀ {lam : ℝ}, 0 < lam → ∀ {b : CoeffOn U},
      CoeffOn.AEScaled lam a b →
        ∀ p q : Vec d,
          responseJ U b p q =
            responseJ U a ((Real.sqrt lam) • p) ((Real.sqrt lam)⁻¹ • q)
  sigma_homogeneous :
    ∀ {lam : ℝ}, 0 < lam → ∀ {b : CoeffOn U},
      CoeffOn.AEScaled lam a b →
        sigmaCoarse U b = lam • sigmaCoarse U a
  sigmaStar_homogeneous :
    ∀ {lam : ℝ}, 0 < lam → ∀ {b : CoeffOn U},
      CoeffOn.AEScaled lam a b →
        sigmaStarCoarse U b = lam • sigmaStarCoarse U a
  kappa_homogeneous :
    ∀ {lam : ℝ}, 0 < lam → ∀ {b : CoeffOn U},
      CoeffOn.AEScaled lam a b →
        kappaCoarse U b = lam • kappaCoarse U a

end

end Ch02
end Book
end Homogenization
