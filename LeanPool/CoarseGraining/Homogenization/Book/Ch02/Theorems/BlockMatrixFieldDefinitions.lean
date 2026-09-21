/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Block

/-! # Block Matrix Field Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for `l.block.matrix.field.basic.definitions`.

All coefficient-field conclusions are a.e. on the Chapter 2 domain, preserving
the public a.e.-native coefficient interface. The canonical public theorem
proving this package is `blockMatrixFieldAlgebraTheory` in
`BlockMatrixField.lean`. -/
structure BlockMatrixFieldAlgebraTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Prop where
  field_symmetric :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      IsSymmetricBlockMat (blockMatrixField a x)
  field_posDef :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      BlockPosDef (blockMatrixField a x)
  factorization :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      blockMatrixField a x =
        blockMatMul (blockMatTranspose (blockG (-skewPart (a.toCoeffField x))))
          (blockMatMul
            (blockDiag (symmPart (a.toCoeffField x))
              ((symmPart (a.toCoeffField x))⁻¹))
            (blockG (-skewPart (a.toCoeffField x))))
  inverse_formula :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      blockMatrixInverseField a x = blockReflect (blockMatrixField a x)
  energy_density :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      ∀ X : BlockVec d,
        blockEnergyDensityAt a X x =
          (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockMatrixField a x) X)

end

end Ch02
end Book
end Homogenization
