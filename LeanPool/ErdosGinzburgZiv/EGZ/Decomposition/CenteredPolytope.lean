/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction

/-!
# Support polytopes stay in the centered box

Every lifted support point is centered by definition.  The centered real
box is convex, so the whole support polytope lies in it.  In particular,
integer transitions of nonzero local lifts are centered without any
additional coordinate bound or large-modulus hypothesis.
-/

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- The real support polytope is contained in the centered coordinate box. -/
theorem polytope_subset_centeredBox (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    (Φ.flag.polytope x).carrier ⊆
      Set.Icc (fun _ : Fin (Φ.flag.rank x) ↦ -(((p - 1) / 2 : ℕ) : ℝ))
        (fun _ ↦ (((p - 1) / 2 : ℕ) : ℝ)) := by
  rw [Φ.polytope_eq_liftedSupport]
  apply convexHull_min _ (convex_Icc _ _)
  rintro _ ⟨z, hz, rfl⟩
  have hc : IsCenteredLift p z := by
    by_contra hc
    have hz' := (Φ.liftedSupport_spec x z).mp hz
    exact hz' (ite_eq_right hc)
  constructor
  · intro i
    have hi := isCenteredLift_iff.mp hc i
    have hlow : -(((p - 1) / 2 : ℕ) : ℤ) ≤ z i := by omega
    change -(((p - 1) / 2 : ℕ) : ℝ) ≤ (z i : ℝ)
    exact_mod_cast hlow
  · intro i
    have hi := isCenteredLift_iff.mp hc i
    have hupp : z i ≤ (((p - 1) / 2 : ℕ) : ℤ) := by omega
    change (z i : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ)
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hupp

/-- Every integer point of a decomposition polytope is already centered. -/
theorem isCenteredLift_of_mem_polytope (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x))
    (hq : q.real ∈ (Φ.flag.polytope x).carrier) : IsCenteredLift p q := by
  have hb := Φ.polytope_subset_centeredBox x hq
  rw [isCenteredLift_iff]
  intro i
  have hlow : -(((p - 1) / 2 : ℕ) : ℤ) ≤ q i := by
    have h := hb.1 i
    change -(((p - 1) / 2 : ℕ) : ℝ) ≤ (q i : ℝ) at h
    exact_mod_cast h
  have hupp : q i ≤ (((p - 1) / 2 : ℕ) : ℤ) := by
    have h := hb.2 i
    change (q i : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ) at h
    exact (Int.cast_le (R := ℝ)).mp (by simpa only [Int.cast_natCast] using h)
  omega

/-- Centeredness is preserved by a flag transition on integer polytope points. -/
theorem isCenteredLift_transition_of_mem_polytope (Φ : FlagDecomposition p d f)
    {y x : Φ.flag.Node} (h : y ≤ x) (q : IntCoord (Φ.flag.rank y))
    (hq : q.real ∈ (Φ.flag.polytope y).carrier) :
    IsCenteredLift p ((Φ.flag.transition h).integer q) := by
  apply Φ.isCenteredLift_of_mem_polytope x
  rw [← (Φ.flag.transition h).real_integer]
  exact Φ.flag.transition_mem h hq

/-- Transitions of nonzero local lifts stay centered automatically. -/
theorem isCenteredLift_transition_of_localLift (Φ : FlagDecomposition p d f)
    {y x : Φ.flag.Node} (h : y ≤ x) (q : IntCoord (Φ.flag.rank y))
    (hq : Φ.localLift y q ≠ 0) :
    IsCenteredLift p ((Φ.flag.transition h).integer q) :=
  Φ.isCenteredLift_transition_of_mem_polytope h q
    (Φ.mem_polytope_of_localLift_ne_zero y q hq)

end EGZ.FlagDecomposition
