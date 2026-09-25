/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineBarycentricSubdivision
/-!
# Last-face affine identity for barycentric subdivision

This file isolates the affine part of the last-face calculation in the proof
that barycentric subdivision commutes with the singular boundary.

The theorem is stated in a face-data form. Suppose

* `π : Equiv.Perm (Fin (n+2))` is a top-dimensional subdivision summand;
* `ι : Fin (n+1) -> Fin (n+2)` is the vertex inclusion of the codimension-one
 face missing the last vertex `π last`;
* `ρ : Equiv.Perm (Fin (n+1))` is the induced permutation on that face;
* `ι (ρ t) = π (Fin.castSucc t)` for every `t`.

Then the restriction of the affine subdivision map for `π` to the final domain
face is the inclusion of the affine subdivision map for `ρ` on the boundary
face.

This deliberately avoids fixing the library's eventual coface-map API. Later,
one instantiates `ι` with the ordinary order-preserving injection missing
`π last`, and `ρ` with the induced ordering of the remaining vertices.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-
Compatibility of prefix barycenters with the last-face boundary data.

If the first `n+1` values of `π` factor through a face inclusion `ι` by an
induced permutation `ρ`, then the `k`-th prefix barycenter of the
`π`-subdivision of `Δ^(n+1)` is the image under `ι` of the corresponding
`k`-th prefix barycenter of the `ρ`-subdivision of the boundary `Δ^n`.
-/
theorem prefixBarycenter_castSucc_eq_map_of_prefix {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (k : Fin (n + 1)) :
    prefixBarycenter (n + 1) π (Fin.castSucc k)
      = SphereOddDegree.FiniteSimplex.map (S := ℝ) ι (prefixBarycenter n ρ k) := by
  have h_comp : prefixVertex (n + 1) π (Fin.castSucc k) = ι ∘ prefixVertex n ρ k := by
    ext ⟨i, hi_val⟩
    have hi : i < n + 1 := by
      have : i < k.val + 1 := by simpa using hi_val
      have := k.isLt
      omega
    have h1 : prefixVertex (n + 1) π (Fin.castSucc k) ⟨i, hi_val⟩ = π (Fin.castSucc ⟨i, hi⟩) := rfl
    have h2 : (ι ∘ prefixVertex n ρ k) ⟨i, hi_val⟩ = ι (ρ ⟨i, hi⟩) := rfl
    rw [h1, h2, ← hιρ ⟨i, hi⟩]
  rw [prefixBarycenter_def, h_comp, ← SphereOddDegree.FiniteSimplex.map_comp_apply,
    prefixBarycenter_def]

/-
Last-face affine identity, in coordinate-face form.

Let `x : Δ^(n+1)` lie on the final domain face, so its last coordinate is zero.
Let `y : Δ^n` be the point obtained by deleting that last coordinate, expressed
here by the coordinate equality `hy`.

Under face data `(ι,ρ)` satisfying `ι (ρ t) = π (Fin.castSucc t)`, the affine
subdivision map for `π` on `x` equals the face inclusion `ι` applied to the
affine subdivision map for `ρ` on `y`.
-/
theorem affineSubdiv_face_last_eq_boundary_subdiv_of_faceData {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (x : Delta (n + 1)) (y : Delta n)
    (hxlast : x ⟨n + 1, by omega⟩ = 0)
    (hy : ∀ k : Fin (n + 1), y k = x (Fin.castSucc k)) :
    affineSubdivMap (n + 1) π x
      = SphereOddDegree.FiniteSimplex.map (S := ℝ) ι (affineSubdivMap n ρ y) := by
  classical
  ext j;
  simp +decide only
      [affineSubdivMap_apply, FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply, hy];
  rw [ Fin.sum_univ_castSucc ];
  simp +decide only [← hy, prefixBarycenter_castSucc_eq_map_of_prefix π ι ρ hιρ,
    FiniteSimplex.map_coe, affineSubdivMap_apply];
  simp +decide only [FunOnFinite.linearMap_apply_apply, sum_filter, Finset.mul_sum _ _ _,
    mul_ite, mul_comm, zero_mul, affineSubdivMap_apply];
  rw [ Finset.sum_comm ];
  simp +decide only [sum_ite_irrel, sum_const_zero, add_eq_left, mul_eq_zero];
  exact Or.inl hxlast

/-- A slightly shorter alias for the last-face affine identity. -/
theorem affineSubdiv_face_last_eq_boundary_subdiv {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2)))
    (ι : Fin (n + 1) → Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hιρ : ∀ t : Fin (n + 1), ι (ρ t) = π (Fin.castSucc t))
    (x : Delta (n + 1)) (y : Delta n)
    (hxlast : x ⟨n + 1, by omega⟩ = 0)
    (hy : ∀ k : Fin (n + 1), y k = x (Fin.castSucc k)) :
    affineSubdivMap (n + 1) π x
      = SphereOddDegree.FiniteSimplex.map (S := ℝ) ι (affineSubdivMap n ρ y) :=
  affineSubdiv_face_last_eq_boundary_subdiv_of_faceData π ι ρ hιρ x y hxlast hy

end AffineBarycentricSubdivision
end SphereOddDegree
