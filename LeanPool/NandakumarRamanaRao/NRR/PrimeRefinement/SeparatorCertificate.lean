/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildTestMap
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.ToNiceMV
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Fibers
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Partition

/-!
# Prime-refinement separator certificates

This module isolates the exact output required from the mod-`p` Fox--Neuwirth argument.
A certificate consists of a top--bottom separator over the parent-body hyperspace and a lifting
property: every point of the separator is represented by a prime configuration for which all
canonical equal-area children are zeros of the input nice multivalued function.

The definition contains no orbit-count or transversality axiom. Those belong to the geometric
prime-refinement theorem that constructs such a certificate. Once a certificate is available, the
conversion to a new nice multivalued function is formal and is proved here directly.
-/

namespace NRR

open Geometry

variable {p : ℕ} {hp : Nat.Prime p}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- The proof-carrying separator produced by one prime-refinement step.

For every carrier point `(C,y)`, `lifts` supplies a configuration parameter whose canonical
`p`-piece equal-area partition of `C` consists entirely of zeros of `φ` at the common parameter
`y`. -/
structure PrimeRefinementSeparator
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) where
  /-- The separator in the parent-body/parameter cylinder. -/
  separator : TopBottomSeparator (BodySpace K A)
  /-- Every point of the separator lifts to a simultaneous child zero. -/
  lifts :
    ∀ C : BodySpace K A, ∀ y : SignedInterval,
      (C, y) ∈ separator.carrier →
        ∃ x : M.Point,
          ((C, x), y) ∈ M.allChildrenZeroSet hA φ

namespace PrimeRefinementSeparator

variable {M : PrimeConfigurationModel hp} {hA : 0 < A}
variable {φ : NiceMV (BodySpace K (A / (p : ℝ)))}

variable (S : PrimeRefinementSeparator (hp := hp) (K := K) (A := A)
  (M := M) (hA := hA) φ)

/-- The output nice multivalued function associated with the separator. -/
noncomputable def toNiceMV
    [Nonempty (BodySpace K A)] :
    NiceMV (BodySpace K A) :=
  S.separator.toNiceMV

/-- A zero of the output function is exactly a point of the separator carrier. -/
theorem zero_toNiceMV_iff
    [Nonempty (BodySpace K A)]
    (C : BodySpace K A) (y : SignedInterval) :
    S.toNiceMV.Zero C y ↔ (C, y) ∈ S.separator.carrier :=
  S.separator.zero_toNiceMV_iff C y

/-- Every zero of the output nice multivalued function lifts to a configuration at which all
canonical equal-area children are zeros of the input function. -/
theorem zero_lifts_to_all_children
    [Nonempty (BodySpace K A)]
    {C : BodySpace K A} {y : SignedInterval}
    (hy : S.toNiceMV.Zero C y) :
    ∃ x : M.Point,
      ∀ i : Fin p,
        φ.Zero (EMP.VariableBody.child M.sites hA hp.pos (C, x) i) y := by
  have hcarrier : (C, y) ∈ S.separator.carrier :=
    (S.zero_toNiceMV_iff C y).mp hy
  obtain ⟨x, hx⟩ := S.lifts C y hcarrier
  refine ⟨x, ?_⟩
  exact (M.mem_allChildrenZeroSet_iff hA φ ((C, x), y)).mp hx

/-- The stronger witness form of `zero_lifts_to_all_children`, retaining the canonical power
partition and its cover/null-overlap/equal-area proofs. -/
theorem zero_lifts_to_partition_witness
    [Nonempty (BodySpace K A)]
    {C : BodySpace K A} {y : SignedInterval}
    (hy : S.toNiceMV.Zero C y) :
    ∃ x : M.Point,
      ∃ W : EMP.VariableBody.Witness M.sites hA hp.pos (C, x),
        ∀ i : Fin p, φ.Zero (W.child i) y := by
  obtain ⟨x, hx⟩ := S.zero_lifts_to_all_children hy
  let W := EMP.VariableBody.witness M.sites hA hp.pos (C, x)
  refine ⟨x, W, ?_⟩
  intro i
  exact hx i

/-- Every parent body has at least one parameter value on the refined zero set, and that value
comes with a simultaneous child-zero configuration. -/
theorem exists_zero_with_partition_witness
    [Nonempty (BodySpace K A)]
    (C : BodySpace K A) :
    ∃ y : SignedInterval,
      S.toNiceMV.Zero C y ∧
        ∃ x : M.Point,
          ∃ W : EMP.VariableBody.Witness M.sites hA hp.pos (C, x),
            ∀ i : Fin p, φ.Zero (W.child i) y := by
  obtain ⟨y, hy⟩ := S.separator.exists_mem_fiber C
  have hzero : S.toNiceMV.Zero C y :=
    (S.zero_toNiceMV_iff C y).mpr hy
  exact ⟨y, hzero, S.zero_lifts_to_partition_witness hzero⟩

end PrimeRefinementSeparator

end NRR
