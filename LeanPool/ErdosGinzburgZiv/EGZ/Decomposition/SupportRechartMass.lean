/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass

/-!
# Recharting supported fibre masses without a representation

Exact centered-mass transport uses only a support-generated lattice chart,
modular injectivity, and containment of the supported centered lifts in the
old support. The original finite-field affine map need not be surjective.
-/

open scoped BigOperators
open Classical

namespace EGZ

namespace FlagDecompositionRaw

variable {p d n : ℕ} [NeZero p]

theorem centeredFibreMass_ne_zero_iff (w : FpCoord p d → ℕ)
    (φ : FpCoord p d → FpCoord p n) (q : IntCoord n) :
    centeredFibreMass w φ q ≠ 0 ↔ IsCenteredLift p q ∧
      ∃ v, φ v = q.mod p ∧ w v ≠ 0 := by
  unfold centeredFibreMass
  by_cases hc : IsCenteredLift p q
  · rw [ite_eq_left hc]
    constructor
    · intro hmass
      obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmass
      by_cases heq : φ v = q.mod p
      · exact ⟨hc, v, heq, by simpa only [ite_eq_left heq] using hv⟩
      · exact (hv (ite_eq_right heq)).elim
    · rintro ⟨_, v, heq, hv⟩
      have hle : w v ≤ affineFibreMass w φ (q.mod p) := by
        simpa only [affineFibreMass, ite_eq_left heq] using Finset.single_le_sum
          (f := fun u ↦ if φ u = q.mod p then w u else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
      exact ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le hle)
  · rw [ite_eq_right hc]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h ↦ (hc h).elim

theorem centeredLift_mem_of_support_spec (hp : Odd p)
    (w : FpCoord p d → ℕ) (φ : FpCoord p d → FpCoord p n)
    (S : Finset (IntCoord n))
    (hS : ∀ q, q ∈ S ↔ centeredFibreMass w φ q ≠ 0)
    {v : FpCoord p d} (hv : w v ≠ 0) : FpCoord.centeredLift (φ v) ∈ S := by
  apply (hS _).mpr
  exact (centeredFibreMass_ne_zero_iff w φ _).mpr
    ⟨FpCoord.isCenteredLift_centeredLift hp _, v, (FpCoord.mod_centeredLift _).symm, hv⟩

end FlagDecompositionRaw

namespace IntegerLatticeChart

variable {p d n : ℕ} [NeZero p] [Fact p.Prime] {S : Finset (IntCoord n)}
    (C : IntegerLatticeChart S)
    (φ : FpCoord p d →ᵃ[ZMod p] FpCoord p n)
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))

include hmod

omit [NeZero p] in
theorem rechartMap_eq_coordinates_mod_of_mem {v : FpCoord p d}
    (hv : FpCoord.centeredLift (φ v) ∈ S) :
    C.rechartMap φ v = (C.coordinates (FpCoord.centeredLift (φ v))).mod p := by
  have hchart : (IntegralAffineMap.ofIntAffineMap C.map).modp p
      ((C.coordinates (FpCoord.centeredLift (φ v))).mod p) = φ v := by
    rw [IntegralAffineMap.mod_integer]
    exact (congrArg (IntCoord.mod p) (C.map_coordinates_of_mem hv)).trans
      (FpCoord.mod_centeredLift _)
  change affineLeftInverse ((IntegralAffineMap.ofIntAffineMap C.map).modp p) (φ v) = _
  conv_lhs => rw [← hchart]
  exact affineLeftInverse_apply _ hmod _

theorem rechart_centered_fibre_iff (hp : Odd p)
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q)
    {v : FpCoord p d} (hv : FpCoord.centeredLift (φ v) ∈ S) (q : IntCoord C.rank) :
    (IsCenteredLift p q ∧ C.rechartMap φ v = q.mod p) ↔
      (IsCenteredLift p (C.map q) ∧ φ v = (C.map q).mod p) := by
  let z := FpCoord.centeredLift (φ v)
  have hzc : IsCenteredLift p z := FpCoord.isCenteredLift_centeredLift hp _
  have hc : IsCenteredLift p (C.coordinates z) :=
    hcenter _ (C.coordinates_mem_coordinateSupport hv)
  have hmap : C.map (C.coordinates z) = z := C.map_coordinates_of_mem hv
  have hnew : C.rechartMap φ v = (C.coordinates z).mod p :=
    C.rechartMap_eq_coordinates_mod_of_mem φ hmod hv
  have hzmod : z.mod p = φ v := FpCoord.mod_centeredLift _
  constructor
  · rintro ⟨hq, hqmod⟩
    have heq : q = C.coordinates z := hq.eq_of_mod_eq hc (hqmod.symm.trans hnew)
    rw [heq, hmap]
    exact ⟨hzc, hzmod.symm⟩
  · rintro ⟨hq, hqmod⟩
    have heq : C.map q = z := hq.eq_of_mod_eq hzc (hqmod.symm.trans hzmod.symm)
    have hqcoord : q = C.coordinates z := C.injective (heq.trans hmap.symm)
    rw [hqcoord]
    exact ⟨hc, hnew⟩

/-- Exact mass transport for arbitrary supported weights and an affine map
which is not required to be surjective. -/
theorem centeredFibreMass_rechart (hp : Odd p)
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q)
    (w : FpCoord p d → ℕ)
    (hwS : ∀ v, w v ≠ 0 → FpCoord.centeredLift (φ v) ∈ S) (q : IntCoord C.rank) :
    FlagDecompositionRaw.centeredFibreMass w (C.rechartMap φ) q =
      FlagDecompositionRaw.centeredFibreMass w φ (C.map q) := by
  rw [FlagDecompositionRaw.centeredFibreMass_eq_sum,
    FlagDecompositionRaw.centeredFibreMass_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : w v = 0
  · simp [hv]
  · have heq := C.rechart_centered_fibre_iff φ hmod hp hcenter (hwS v hv) q
    simp only [heq]

/-- If the old support is exactly the nonzero centered fibre support, its
chart-coordinate support is exactly the new nonzero centered fibre support. -/
theorem coordinateSupport_spec_rechart (hp : Odd p)
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q)
    (w : FpCoord p d → ℕ)
    (hS : ∀ z, z ∈ S ↔ FlagDecompositionRaw.centeredFibreMass w φ z ≠ 0)
    (q : IntCoord C.rank) :
    q ∈ C.coordinateSupport ↔
      FlagDecompositionRaw.centeredFibreMass w (C.rechartMap φ) q ≠ 0 := by
  rw [C.centeredFibreMass_rechart φ hmod hp hcenter w
    (fun _ hv ↦ FlagDecompositionRaw.centeredLift_mem_of_support_spec hp w φ S hS hv),
    C.mem_coordinateSupport]
  exact hS (C.map q)

end IntegerLatticeChart
end EGZ
