/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Matrix coordinates for a finite-rank direct summand

This file contains the coordinate-free-to-matrix step used by the general
tangent-limit criterion.  A complemented submodule of a finite coordinate
module over a local ring is finite projective, hence finite free.  Choosing a
basis only inside the proof produces a column matrix and a retraction matrix.
The matrices split, and their columns span exactly the original submodule.
-/

namespace AlgebraicAnalysis.SplitLatticePresentation

noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix presentation constructed from a direct summand, with no chosen
basis or retraction in the input. -/
structure SplitMatrixPresentation
    (L : Submodule R (ι → R)) (r : ℕ) where
  /-- Column matrix for the inclusion of the summand. -/
  B : Matrix ι (Fin r) R
  /-- Retraction matrix for the chosen summand coordinates. -/
  C : Matrix (Fin r) ι R
  leftInverse : C * B = 1
  columnsSpan :
    Submodule.span R (Set.range fun j => fun i => B i j) = L

omit [DecidableEq ι] in
/-- A finite-rank complemented submodule of a finite coordinate module over a
local ring has split matrix coordinates.  Finiteness descends along the
projection onto the summand, projectivity comes from the split inclusion, and
finite flat modules over local rings are free. -/
theorem exists_splitMatrixPresentation
    (L L' : Submodule R (ι → R)) (hcompl : IsCompl L L') (r : ℕ)
    (hrank : Module.finrank R L = r) :
    Nonempty (SplitMatrixPresentation L r) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let p : (ι → R) →ₗ[R] L := L.projectionOnto L' hcompl
  let : Module.Finite R L :=
    Module.Finite.of_surjective p (Submodule.projectionOnto_surjective hcompl)
  let : Module.Projective R L :=
    Module.Projective.of_split L.subtype p
      (Submodule.projectionOnto_comp_subtype hcompl)
  let : Module.Flat R L := Module.Flat.of_projective
  let : Module.Free R L := Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Fin r) R L :=
    Module.finBasisOfFinrankEq R L hrank
  let e : Module.Basis ι R (ι → R) := Pi.basisFun R ι
  let B : Matrix ι (Fin r) R := LinearMap.toMatrix b e L.subtype
  let C : Matrix (Fin r) ι R := LinearMap.toMatrix e b p
  refine ⟨{
    B := B
    C := C
    leftInverse := ?_
    columnsSpan := ?_ }⟩
  · have hmatrix := LinearMap.toMatrix_comp b e b p L.subtype
    rw [Submodule.projectionOnto_comp_subtype hcompl,
      LinearMap.toMatrix_id] at hmatrix
    simpa [B, C] using hmatrix.symm
  · have hcolumns :
        (fun j : Fin r => fun i => B i j) =
          fun j => (b j : ι → R) := by
      funext j i
      simp [B, e, LinearMap.toMatrix_apply, Pi.basisFun_repr]
    rw [hcolumns]
    have himage :
        L.subtype '' Set.range b =
          Set.range (fun j => (b j : ι → R)) := by
      ext x
      simp only [Set.mem_image, Set.mem_range, Submodule.coe_subtype,
        exists_exists_eq_and]
    rw [← himage, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    exact Submodule.range_subtype (p := L)

omit [DecidableEq ι] in
/-- Property-valued form: no particular complement is part of the input. -/
theorem exists_splitMatrixPresentation_of_isComplemented
    (L : Submodule R (ι → R)) (hcompl : IsComplemented L) (r : ℕ)
    (hrank : Module.finrank R L = r) :
    Nonempty (SplitMatrixPresentation L r) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  obtain ⟨L', hLL'⟩ := hcompl
  exact exists_splitMatrixPresentation L L' hLL' r hrank


end
end AlgebraicAnalysis.SplitLatticePresentation
