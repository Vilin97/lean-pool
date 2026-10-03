/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.FirstVariationDefinitions
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence

/-! # First Variation -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-- Internal pointwise-coefficient first-variation theorem.

This is the proof-engine bridge only. The public theorem below first replaces
the public a.e. coefficient by a pointwise-good representative, uses this
bridge, and transports the result back across a.e. equality. -/
theorem responseFirstVariationTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseFirstVariationTheory U a where
  first_variation := by
    intro p q v hv w
    let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hfirst :=
      basic_cg_identities_first_variation_of_isResponseMaximizer
        (U : Set (Vec d)) a.toCoeffField p q v hv w
        (hInt.weakFlux v) (hInt.weakFlux w)
        (hInt.response p q v) (hInt.firstVariation p q v w) (hInt.energy w)
    change
      volumeAverage (U : Set (Vec d))
        (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField p q v w) = 0
    exact hfirst

/-- Note-facing Chapter 2 first variation from the public a.e. coefficient
interface. No public pointwise ellipticity, integrability package, or
representative choice is exposed. -/
theorem responseFirstVariationTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseFirstVariationTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : ResponseFirstVariationTheory U b :=
    responseFirstVariationTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseFirstVariationTheory.ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
