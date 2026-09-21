/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.SeparatorCertificate

/-!
# Model-independent prime-refinement steps

The geometric obstruction may be represented by any compact prime-equivariant configuration model.
The recursive partition construction uses only that model's site family and the separator lifting
property, independently of a particular top-cell atlas.
-/

namespace NRR

open Geometry

variable {p : Nat}
variable {K : Geometry.ConvexBody Plane} {A : Real}

/-- One prime-refinement step together with the concrete configuration model that realizes it. -/
structure FlexiblePrimeRefinementStep
    (hp : Nat.Prime p)
    (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real)))) where
  /-- The prime configuration model selected for the refinement step. -/
  model : PrimeConfigurationModel hp
  /-- The separator certificate for the selected model and multivalued observable. -/
  certificate : PrimeRefinementSeparator model hA phi

/-- Model-independent prime-refinement theorem. -/
def FlexiblePrimeRefinementTheorem : Prop :=
  ∀ (p : Nat) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : Real) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (phi : NiceMV (BodySpace K (A / (p : Real)))),
      Nonempty (FlexiblePrimeRefinementStep hp hA phi)

namespace FlexiblePrimeRefinementTheorem

/-- A flexible step yields the next nice multivalued function and its complete partition decoder. -/
theorem refinedNiceMV
    (H : FlexiblePrimeRefinementTheorem)
    (p : Nat) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : Real) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (phi : NiceMV (BodySpace K (A / (p : Real)))) :
    ∃ psi : NiceMV (BodySpace K A),
      ∀ C : BodySpace K A, ∀ y : SignedInterval,
        psi.Zero C y →
          ∃ (M : PrimeConfigurationModel hp) (x : M.Point),
            ∃ W : EMP.VariableBody.Witness M.sites hA hp.pos (C, x),
              ∀ i : Fin p, phi.Zero (W.child i) y := by
  let S := Classical.choice (H p hp K A hA phi)
  refine ⟨S.certificate.toNiceMV, ?_⟩
  intro C y hy
  obtain ⟨x, W, hW⟩ := S.certificate.zero_lifts_to_partition_witness hy
  exact ⟨S.model, x, W, hW⟩

end FlexiblePrimeRefinementTheorem

end NRR
