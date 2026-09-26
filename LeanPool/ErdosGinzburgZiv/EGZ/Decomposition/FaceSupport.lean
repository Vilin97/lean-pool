/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces

/-!
# Faces as hulls of lifted support points

The stored generators of a polytope need not be the stored lifted support.
The support/polytope invariant nevertheless identifies every face with the
convex hull of precisely the lifted support points lying on that face.
-/

@[expose] public section


namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

open Classical in
theorem face_eq_convexHull_liftedSupport (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) :
    Γ.carrier = convexHull ℝ (IntCoord.real ''
      (↑((Φ.liftedSupport x).filter (fun q ↦ q.real ∈ Γ.carrier)) :
        Set (IntCoord (Φ.flag.rank x)))) := by
  obtain ⟨ξ, c, hle, hcarrier⟩ := Γ.is_exposed
  let S := (Φ.liftedSupport x).image IntCoord.real
  have hpoly : (Φ.flag.polytope x).carrier = convexHull ℝ (S : Set _) := by
    simpa only [S, Finset.coe_image] using Φ.polytope_eq_liftedSupport x
  have hleS : ∀ q ∈ S, ξ q ≤ c := by
    intro q hq
    apply hle q
    rw [hpoly]
    exact subset_convexHull ℝ _ hq
  have hfilter :
      (S.filter (fun q ↦ ξ q = c) : Set (RealCoord (Φ.flag.rank x))) =
        IntCoord.real ''
          (↑((Φ.liftedSupport x).filter (fun q ↦ q.real ∈ Γ.carrier)) :
            Set (IntCoord (Φ.flag.rank x))) := by
    ext q
    constructor
    · intro hq
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
      refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩, rfl⟩
      rw [hcarrier]
      refine ⟨?_, (Finset.mem_filter.mp hq).2⟩
      rw [hpoly]
      exact subset_convexHull ℝ _ ((Finset.mem_filter.mp hq).1)
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hz, hzface⟩ := Finset.mem_filter.mp hz
      rw [hcarrier] at hzface
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, hzface.2⟩
  calc
    Γ.carrier = {q | q ∈ convexHull ℝ (S : Set _) ∧ ξ q = c} := by
      rw [hcarrier, hpoly]
    _ = convexHull ℝ (↑(S.filter (fun q ↦ ξ q = c)) : Set _) :=
      RationalPolytope.convexHull_supportingLevel_eq S ξ c hleS
    _ = _ := by rw [hfilter]

open Classical in
theorem liftedSupport_face_nonempty (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) :
    ((Φ.liftedSupport x).filter (fun q ↦ q.real ∈ Γ.carrier)).Nonempty := by
  by_contra h
  have heq := Finset.not_nonempty_iff_eq_empty.mp h
  have hne := Γ.nonempty
  rw [Φ.face_eq_convexHull_liftedSupport x Γ, heq] at hne
  simp at hne

end EGZ.FlagDecomposition
