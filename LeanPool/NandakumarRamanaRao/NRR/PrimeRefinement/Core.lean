/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.SeparatorCertificate
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth

/-!
# Prime-refinement separator interface and consequences

`PrimeRefinementTheorem` states the separator property for the concrete Fox--Neuwirth model.
This file derives the functional prime-refinement consequences from that proposition.
-/

@[expose] public section

namespace NRR

open Geometry

/-- For every prime and every nice multivalued function on the child-body hyperspace, the
concrete Fox--Neuwirth model produces a top--bottom separator whose points lift to simultaneous
child zeros. -/
def PrimeRefinementTheorem : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : ℝ) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))),
      Nonempty
        (PrimeRefinementSeparator
          (foxNeuwirthTopCellModel hp) hA φ)

namespace PrimeRefinementTheorem

/-- A prime-refinement separator witness yields the refined nice multivalued function together with
its
complete child-partition lifting property. -/
theorem refinedNiceMV
    (H : PrimeRefinementTheorem)
    (p : ℕ) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : ℝ) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    ∃ ψ : NiceMV (BodySpace K A),
      ∀ C : BodySpace K A, ∀ y : SignedInterval,
        ψ.Zero C y →
          ∃ x : (foxNeuwirthTopCellModel hp).Point,
            ∃ W : EMP.VariableBody.Witness
                (foxNeuwirthTopCellModel hp).sites hA hp.pos (C, x),
              ∀ i : Fin p, φ.Zero (W.child i) y := by
  let S := Classical.choice (H p hp K A hA φ)
  refine ⟨S.toNiceMV, ?_⟩
  intro C y hy
  exact S.zero_lifts_to_partition_witness hy

/-- Fiberwise existence form: for every parent body, a separator witness supplies a common
parameter and a canonical equal-area `p`-partition whose children are all input zeros. -/
theorem exists_common_zero_partition
    (H : PrimeRefinementTheorem)
    (p : ℕ) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : ℝ) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (C : BodySpace K A) :
    ∃ y : SignedInterval,
      ∃ x : (foxNeuwirthTopCellModel hp).Point,
        ∃ W : EMP.VariableBody.Witness
            (foxNeuwirthTopCellModel hp).sites hA hp.pos (C, x),
          ∀ i : Fin p, φ.Zero (W.child i) y := by
  let S := Classical.choice (H p hp K A hA φ)
  obtain ⟨y, _, x, W, hW⟩ := S.exists_zero_with_partition_witness C
  exact ⟨y, x, W, hW⟩

end PrimeRefinementTheorem

end NRR
