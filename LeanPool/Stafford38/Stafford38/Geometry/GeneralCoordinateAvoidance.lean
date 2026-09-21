/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Nullstellensatz

/-!
# Polynomial inverses from coordinate avoidance

A coordinate that never vanishes on an affine zero locus is invertible modulo
its defining ideal. The ideal need not be prime or radical.
-/

namespace Stafford38.Geometry.GeneralCoordinateAvoidance

noncomputable section

theorem exists_coordinate_inverse_of_avoidance
    {k : Type*} [Field k] [IsAlgClosed k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k)) (i : Fin m)
    (havoid : ∀ y ∈ MvPolynomial.zeroLocus k I, y i ≠ 0) :
    ∃ g : MvPolynomial (Fin m) k, MvPolynomial.X i * g - 1 ∈ I := by
  classical
  let J := I ⊔ Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial (Fin m) k))
  have htop : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨y, hMy⟩ :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hM
    have hy : y ∈ MvPolynomial.zeroLocus k I := by
      intro p hp
      have hpM := hJM (show p ∈ J from Ideal.mem_sup_left hp)
      rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpM
      exact hpM
    have hxM : MvPolynomial.X i ∈ M :=
      hJM (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hxM
    exact havoid y hy (by simpa using hxM)
  have hone : (1 : MvPolynomial (Fin m) k) ∈ J := by simp [htop]
  obtain ⟨b, hb, z, hz, hbz⟩ := Submodule.mem_sup.mp hone
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hz
  refine ⟨g, ?_⟩
  have heq : MvPolynomial.X i * g - 1 = -b := by
    rw [← hg]
    rw [← hbz]
    ring
  rw [heq]
  exact I.neg_mem hb


end
end Stafford38.Geometry.GeneralCoordinateAvoidance
