/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarConstructionAffinePullback

/-!
# Unconditional full-collar origin margin from the affine-pullback construction

This file instantiates the generic compactness theorem of
`StableFullCollarOriginMargin` with the concrete Step 4 collar constructed in
`StableFullCollarConstructionAffinePullback`.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarOriginMarginAffinePullback

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open StableFullCollarOriginMargin
open StableFullCollarConstructionAffinePullback

variable {p : Nat}

/-- Concrete quantitative origin-margin data attached to the affine-pullback
full collar. -/
noncomputable def fullCollarOriginMarginData_affinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    FullCollarOriginMarginData hp H A₀ A₁ :=
  FullCollarOriginMarginData.ofFineFullCollarData
    (fineFullCollarData hp F₀ F₁ H A₀ A₁)

/-- Step 5, specialized to the concrete Step 4 construction. -/
theorem fullCollarOriginMargin_affinePullback :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (F₀ F₁ : ZeroFreeMap hp)
      (H : ZeroFreeHomotopy hp F₀ F₁)
      (A₀ : StableRegularApproximation hp F₀.map)
      (A₁ : StableRegularApproximation hp F₁.map),
        Nonempty (FullCollarOriginMarginData hp H A₀ A₁) := by
  intro p hp F₀ F₁ H A₀ A₁
  exact ⟨fullCollarOriginMarginData_affinePullback hp F₀ F₁ H A₀ A₁⟩

/-- The concrete collar has a positive coordinate norm margin. -/
theorem affinePullback_margin_pos
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    0 < (fullCollarOriginMarginData_affinePullback hp F₀ F₁ H A₀ A₁).margin :=
  (fullCollarOriginMarginData_affinePullback hp F₀ F₁ H A₀ A₁).margin_pos

end StableFullCollarOriginMarginAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
