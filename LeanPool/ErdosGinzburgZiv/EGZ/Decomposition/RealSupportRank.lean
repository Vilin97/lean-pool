/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceGeometry

/-!
# Real affine dimension of support-generated lattice coordinates

Integer affine generation implies full real affine span. Consequently a
support-generated chart has rank equal to the real affine dimension of its
support polytope. A chart for support in a proper face of a minimal node has
strictly smaller rank.
-/

@[expose] public section

namespace EGZ

/-- Real affine hulls contain real realizations of integer affine spans. -/
theorem real_mem_affineSpan_of_mem_int_affineSpan {n : ℕ} {S : Set (IntCoord n)}
    {q : IntCoord n} (hq : q ∈ affineSpan ℤ S) :
    q.real ∈ affineSpan ℝ (IntCoord.real '' S) := by
  refine affineSpan_induction hq (fun z hz ↦ subset_affineSpan ℝ _ ⟨z, hz, rfl⟩) ?_
  intro c u v w hu hv hw
  have h := (affineSpan ℝ (IntCoord.real '' S)).smul_vsub_vadd_mem (c : ℝ) hu hv hw
  simpa only [vsub_eq_sub, vadd_eq_add, IntCoord.real_add, IntCoord.real_sub,
    IntCoord.real_zsmul, Int.cast_smul_eq_zsmul] using h

/-- The integer coordinate lattice spans the entire real affine space. -/
theorem IntCoord.affineSpan_real_range (n : ℕ) :
    affineSpan ℝ (Set.range (@IntCoord.real n)) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range (@IntCoord.real n))
  have hzero : (0 : RealCoord n) ∈ A := subset_affineSpan ℝ _ ⟨0, IntCoord.real_zero⟩
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, hzero⟩).mp
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi : (Pi.basisFun ℝ (Fin n)) i ∈ A := by
    apply subset_affineSpan ℝ _
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    by_cases hj : j = i <;> simp [Pi.basisFun_apply, IntCoord.real, hj]
  simpa using A.vsub_mem_direction hi hzero

theorem FlagDecomposition.AffineIntSpans.affineSpan_real_eq_top {n : ℕ}
    {S : Finset (IntCoord n)} (hS : FlagDecomposition.AffineIntSpans S) :
    affineSpan ℝ (IntCoord.real '' (S : Set (IntCoord n))) = ⊤ := by
  have hi := (FlagDecomposition.affineIntSpans_iff_affineSpan_eq_top S).mp hS
  have hsub : Set.range (@IntCoord.real n) ⊆
      (affineSpan ℝ (IntCoord.real '' (S : Set (IntCoord n))) : Set (RealCoord n)) := by
    rintro _ ⟨q, rfl⟩
    exact real_mem_affineSpan_of_mem_int_affineSpan (by rw [hi]; trivial)
  apply top_unique
  rw [← IntCoord.affineSpan_real_range n]
  exact affineSpan_le.mpr hsub

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

theorem polytope_affineSpan_eq_top (Φ : FlagDecomposition p d f) (hΦ : Φ.IsMinimal)
    (x : Φ.flag.Node) : affineSpan ℝ (Φ.flag.polytope x).carrier = ⊤ := by
  rw [Φ.polytope_eq_liftedSupport, affineSpan_convexHull]
  exact (hΦ x).2.affineSpan_real_eq_top

namespace Rechart

variable (Φ : FlagDecomposition p d f) (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))

theorem polytope_affineSpan_eq_top (x : Φ.flag.Node) :
    affineSpan ℝ (polytope Φ C x).carrier = ⊤ := by
  rw [polytope_carrier, affineSpan_convexHull]
  exact (C x).coordinateSupport_affineIntSpans.affineSpan_real_eq_top

/-- The new lattice rank is exactly the real affine dimension of the old
support polytope, including when the old coordinates were not minimal. -/
theorem rank_eq_polytope_dimension (x : Φ.flag.Node) :
    (C x).rank = Module.finrank ℝ (affineSpan ℝ (Φ.flag.polytope x).carrier).direction := by
  have hm : (⊤ : AffineSubspace ℝ (RealCoord (C x).rank)).map (chart Φ C x).real =
      affineSpan ℝ (Φ.flag.polytope x).carrier := by
    rw [← polytope_affineSpan_eq_top Φ C x, AffineSubspace.map_span, chart_image_polytope]
  rw [← hm, AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  simpa using (LinearMap.finrank_range_of_inj
    ((chart Φ C x).real.linear_injective_iff.mpr (chart_real_injective Φ C x))).symm

theorem rank_eq_of_isMinimal (hΦ : Φ.IsMinimal) (x : Φ.flag.Node) :
    (C x).rank = Φ.flag.rank x := by
  rw [rank_eq_polytope_dimension, Φ.polytope_affineSpan_eq_top hΦ,
    AffineSubspace.direction_top]
  simp

end Rechart
end FlagDecomposition

end EGZ
