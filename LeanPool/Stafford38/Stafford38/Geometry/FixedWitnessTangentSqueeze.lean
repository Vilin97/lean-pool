/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalSpan

/-!
# A finite family determines the tangent space at full rank

If a finite linearly independent family consists of Zariski tangent vectors
and the tangent space has dimension at most the size of the family, then the
tangent space is exactly their span.  This is only the finite-dimensional
linear-algebra consumer; it does not construct tangent vectors or establish a
smoothness or dimension bound.
-/

namespace Stafford38.Geometry.FixedWitnessTangentSqueeze

open Stafford38.Geometry.AffineConormalSpan

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- A fixed independent tangent family spans the whole Zariski tangent space
once the tangent dimension is bounded by the cardinality of that family. -/
theorem fixedWitnessTangentSqueeze
    {κ : Type*} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin n) K))
    (y : Fin n → K)
    (b : κ → AffineTangentVector K n)
    (hb : ∀ j, b j ∈ zariskiTangentSpace y I)
    (hindependent : LinearIndependent K b)
    (hfinrank : Module.finrank K (zariskiTangentSpace y I) ≤ Fintype.card κ) :
    zariskiTangentSpace y I = Submodule.span K (Set.range b) := by
  classical
  have hspan_le :
      Submodule.span K (Set.range b) ≤ zariskiTangentSpace y I := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hb j
  have hrank :
      Module.finrank K (zariskiTangentSpace y I) ≤
        Module.finrank K (Submodule.span K (Set.range b)) := by
    rw [finrank_span_eq_card hindependent]
    exact hfinrank
  exact (Submodule.eq_of_le_of_finrank_le hspan_le hrank).symm

/-- The reverse inclusion needed by the conormal consumer. -/
theorem fixedWitnessTangent_le_span
    {κ : Type*} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin n) K))
    (y : Fin n → K)
    (b : κ → AffineTangentVector K n)
    (hb : ∀ j, b j ∈ zariskiTangentSpace y I)
    (hindependent : LinearIndependent K b)
    (hfinrank : Module.finrank K (zariskiTangentSpace y I) ≤ Fintype.card κ) :
    zariskiTangentSpace y I ≤ Submodule.span K (Set.range b) := by
  rw [fixedWitnessTangentSqueeze I y b hb hindependent hfinrank]


end

end Stafford38.Geometry.FixedWitnessTangentSqueeze
