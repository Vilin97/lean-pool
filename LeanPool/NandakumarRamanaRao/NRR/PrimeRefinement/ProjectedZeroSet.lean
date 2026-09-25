/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.SeparatorCertificate
public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Complement

/-!
# Projection of the simultaneous child-zero set

For a compact prime configuration model, the simultaneous child-zero locus is closed in a compact
space.  Its projection to the parent-body/parameter cylinder is therefore compact and closed.  The
strict endpoint signs of a nice multivalued function show that this projection misses both endpoint
boundaries.  These facts provide the analytic and point-set-topological input to the separator
construction. The cobordism theorem establishes the required lower and upper regions of the
complement.
-/

@[expose] public section

namespace NRR

open Geometry

variable {p : ℕ} {hp : Nat.Prime p}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

namespace PrimeConfigurationModel

/-- Projection of the simultaneous child-zero locus to the parent-body/parameter cylinder. -/
def projectedAllChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Set (BodySpace K A × SignedInterval) :=
  {z | ∃ x : M.Point, ((z.1, x), z.2) ∈ M.allChildrenZeroSet hA φ}

/-- Membership in the projected zero set is exactly the existence of one configuration for which
all canonical children are zeros at the common parameter. -/
theorem mem_projectedAllChildrenZeroSet_iff
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (z : BodySpace K A × SignedInterval) :
    z ∈ M.projectedAllChildrenZeroSet hA φ ↔
      ∃ x : M.Point,
        ∀ i : Fin p,
          φ.Zero (EMP.VariableBody.child M.sites hA hp.pos (z.1, x) i) z.2 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (M.mem_allChildrenZeroSet_iff hA φ ((z.1, x), z.2)).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (M.mem_allChildrenZeroSet_iff hA φ ((z.1, x), z.2)).mpr hx⟩

/-- The simultaneous zero locus in the total configuration cylinder is compact. -/
theorem isCompact_allChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    IsCompact (M.allChildrenZeroSet hA φ) :=
  (M.isClosed_allChildrenZeroSet hA φ).isCompact

/-- The projected simultaneous-zero set is compact. -/
theorem isCompact_projectedAllChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    IsCompact (M.projectedAllChildrenZeroSet hA φ) := by
  let q : ((BodySpace K A × M.Point) × SignedInterval) →
      (BodySpace K A × SignedInterval) :=
    fun z => (z.1.1, z.2)
  have hq : Continuous q :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have himage :
      q '' M.allChildrenZeroSet hA φ =
        M.projectedAllChildrenZeroSet hA φ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.1.2, hw⟩
    · rintro ⟨x, hx⟩
      exact ⟨((z.1, x), z.2), hx, rfl⟩
  rw [← himage]
  exact (M.isCompact_allChildrenZeroSet hA φ).image hq

/-- The projected simultaneous-zero set is closed. -/
theorem isClosed_projectedAllChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    IsClosed (M.projectedAllChildrenZeroSet hA φ) :=
  (M.isCompact_projectedAllChildrenZeroSet hA φ).isClosed

/-- No projected simultaneous zero occurs at the lower endpoint. -/
theorem not_mem_projectedAllChildrenZeroSet_left
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (C : BodySpace K A) :
    (C, SignedInterval.left) ∉ M.projectedAllChildrenZeroSet hA φ := by
  intro hz
  obtain ⟨x, hx⟩ :=
    (M.mem_projectedAllChildrenZeroSet_iff hA φ
      (C, SignedInterval.left)).mp hz
  let i : Fin p := ⟨0, hp.pos⟩
  exact φ.not_zero_left _ (hx i)

/-- No projected simultaneous zero occurs at the upper endpoint. -/
theorem not_mem_projectedAllChildrenZeroSet_right
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ))))
    (C : BodySpace K A) :
    (C, SignedInterval.right) ∉ M.projectedAllChildrenZeroSet hA φ := by
  intro hz
  obtain ⟨x, hx⟩ :=
    (M.mem_projectedAllChildrenZeroSet_iff hA φ
      (C, SignedInterval.right)).mp hz
  let i : Fin p := ⟨0, hp.pos⟩
  exact φ.not_zero_right _ (hx i)

/-- The bottom boundary is disjoint from the projected simultaneous-zero set. -/
theorem disjoint_signedBottom_projectedAllChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Disjoint (signedBottom (BodySpace K A))
      (M.projectedAllChildrenZeroSet hA φ) := by
  rw [Set.disjoint_left]
  rintro ⟨C, y⟩ hy hzero
  change y = SignedInterval.left at hy
  subst y
  exact M.not_mem_projectedAllChildrenZeroSet_left hA φ C hzero

/-- The top boundary is disjoint from the projected simultaneous-zero set. -/
theorem disjoint_signedTop_projectedAllChildrenZeroSet
    (M : PrimeConfigurationModel hp)
    (hA : 0 < A)
    (φ : NiceMV (BodySpace K (A / (p : ℝ)))) :
    Disjoint (signedTop (BodySpace K A))
      (M.projectedAllChildrenZeroSet hA φ) := by
  rw [Set.disjoint_left]
  rintro ⟨C, y⟩ hy hzero
  change y = SignedInterval.right at hy
  subst y
  exact M.not_mem_projectedAllChildrenZeroSet_right hA φ C hzero

end PrimeConfigurationModel

end NRR
