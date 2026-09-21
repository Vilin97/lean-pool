/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildEquivariance

/-!
# Equivariant child-evaluation test map

An arbitrary nice multivalued function is evaluated on all equal-area children. The resulting
coordinate vector is continuous and transforms by coordinate relabelling.
-/

namespace NRR

open Geometry

variable {p : ℕ} {hp : Nat.Prime p}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

namespace PrimeConfigurationModel

noncomputable def childTestMap
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    ((BodySpace K A × M.Point) × SignedInterval) → (Fin p → ℝ) :=
  fun z i => φ.eval
    (EMP.VariableBody.child M.sites hA hp.pos z.1 i) z.2

 theorem continuous_childTestMap
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Continuous (M.childTestMap hA φ) :=
  φ.continuous_childEvalVec M.sites hA hp.pos

 theorem childTestMap_smul
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (g : PrimeSymmetry hp)
    (z : (BodySpace K A × M.Point) × SignedInterval) :
    M.childTestMap hA φ
      (M.smulBodyPointInterval (K := K) (A := A) g z) =
      g • M.childTestMap hA φ z := by
  rcases z with ⟨⟨C, x⟩, t⟩
  funext i
  simp only [childTestMap, smulBodyPointInterval,
    PrimeSymmetry.smul_coordinate_apply]
  rw [M.child_smul hA C g x i]

/-- The simultaneous child-zero set. -/
def allChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Set ((BodySpace K A × M.Point) × SignedInterval) :=
  {z | M.childTestMap hA φ z = 0}

 theorem mem_allChildrenZeroSet_iff
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (z : (BodySpace K A × M.Point) × SignedInterval) :
    z ∈ M.allChildrenZeroSet hA φ ↔
      ∀ i : Fin p,
        φ.Zero (EMP.VariableBody.child M.sites hA hp.pos z.1 i) z.2 := by
  constructor
  · intro hz i
    change M.childTestMap hA φ z = 0 at hz
    have hi := congrFun hz i
    simpa [allChildrenZeroSet, childTestMap, NiceMV.Zero] using hi
  · intro hz
    change M.childTestMap hA φ z = 0
    funext i
    simpa [childTestMap, NiceMV.Zero] using hz i

 theorem isClosed_allChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    IsClosed (M.allChildrenZeroSet hA φ) :=
  isClosed_eq (M.continuous_childTestMap hA φ) continuous_const

 theorem allChildrenZeroSet_invariant
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    ∀ g : PrimeSymmetry hp,
      ∀ z ∈ M.allChildrenZeroSet hA φ,
        M.smulBodyPointInterval (K := K) (A := A) g z ∈
          M.allChildrenZeroSet hA φ := by
  intro g z hz
  change M.childTestMap hA φ
    (M.smulBodyPointInterval (K := K) (A := A) g z) = 0
  rw [M.childTestMap_smul hA φ g z, hz, smul_zero]

end PrimeConfigurationModel

end NRR
