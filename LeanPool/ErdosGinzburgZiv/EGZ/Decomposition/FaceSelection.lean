/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Pullback
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass

/-!
# Selecting local atoms over a face

The face refinement splits every local summand below its anchor using the
same predicate on ambient points. Compatibility of centered lifts identifies
the selected cumulative support with the inverse image of the target face.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

open Classical in
/-- Ambient atoms whose centered coordinate at the anchor lies on its face. -/
def faceSelector (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (v : FpCoord p d) : Prop :=
  (FpCoord.centeredLift (Φ.representation.map x v)).real ∈ Γ.carrier

open Classical in
/-- On supported atoms, taking centered representatives commutes with every
transition of the old decomposition. -/
theorem transition_centeredLift (hp : Odd p) {y x : Φ.flag.Node} (h : y ≤ x)
    (v : FpCoord p d) (hv : Φ.cumulativeWeight y v ≠ 0) :
    (Φ.flag.transition h).integer (FpCoord.centeredLift (Φ.representation.map y v)) =
      FpCoord.centeredLift (Φ.representation.map x v) := by
  have hq : Φ.hat y (FpCoord.centeredLift (Φ.representation.map y v)) ≠ 0 := by
    apply (Φ.originalWeights.hat_ne_zero_iff _ _).mpr
    exact ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
      (FpCoord.mod_centeredLift _).symm, hv⟩
  apply (Φ.originalWeights.transition_centered h hq).eq_of_mod_eq
    (FpCoord.isCenteredLift_centeredLift hp _)
  rw [← (Φ.flag.transition h).mod_integer, FpCoord.mod_centeredLift,
    FpCoord.mod_centeredLift]
  exact (Φ.representation.compatible h (Φ.originalWeights.cumulative_supported y v hv)).symm

open Classical in
theorem faceSelector_iff (hp : Odd p) {y x : Φ.flag.Node} (h : y ≤ x)
    (Γ : (Φ.flag.polytope x).Face) (q : IntCoord (Φ.flag.rank y))
    (hc : IsCenteredLift p q) (v : FpCoord p d)
    (hmap : Φ.representation.map y v = q.mod p) (hv : Φ.cumulativeWeight y v ≠ 0) :
    Φ.faceSelector x Γ v ↔ (Φ.flag.transition h).real q.real ∈ Γ.carrier := by
  have hz : FpCoord.centeredLift (Φ.representation.map y v) = q := by
    rw [hmap, FpCoord.centeredLift_mod hc]
  unfold faceSelector
  rw [← Φ.transition_centeredLift hp h v hv, hz, ← (Φ.flag.transition h).real_integer]

open Classical in
/-- Selecting a face does not split any nonzero cumulative fibre below the
anchor: the entire fibre is retained or the entire fibre is removed. -/
theorem centeredFibreMass_faceSelector (hp : Odd p) {y x : Φ.flag.Node} (h : y ≤ x)
    (Γ : (Φ.flag.polytope x).Face) (q : IntCoord (Φ.flag.rank y)) :
    FlagDecompositionRaw.centeredFibreMass
        (fun v ↦ if Φ.faceSelector x Γ v then Φ.cumulativeWeight y v else 0)
        (Φ.representation.map y) q =
      if (Φ.flag.transition h).real q.real ∈ Γ.carrier then Φ.hat y q else 0 := by
  classical
  unfold FlagDecompositionRaw.centeredFibreMass FlagDecomposition.hat FlagDecompositionRaw.hat
  by_cases hc : IsCenteredLift p q
  · rw [ite_eq_left hc, ite_eq_left hc]
    unfold FlagDecompositionRaw.affineFibreMass
    by_cases hface : (Φ.flag.transition h).real q.real ∈ Γ.carrier
    · rw [ite_eq_left hface]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hmap : Φ.representation.map y v = q.mod p
      · rw [ite_eq_left hmap, ite_eq_left hmap]
        change (if Φ.faceSelector x Γ v then Φ.cumulativeWeight y v else 0) =
          Φ.cumulativeWeight y v
        by_cases hv : Φ.cumulativeWeight y v = 0
        · simp only [hv, ite_self]
        · rw [ite_eq_left ((Φ.faceSelector_iff hp h Γ q hc v hmap hv).mpr hface)]
      · rw [ite_eq_right hmap, ite_eq_right hmap]
    · rw [ite_eq_right hface]
      apply Finset.sum_eq_zero
      intro v _
      by_cases hmap : Φ.representation.map y v = q.mod p
      · rw [ite_eq_left hmap]
        change (if Φ.faceSelector x Γ v then Φ.cumulativeWeight y v else 0) = 0
        by_cases hv : Φ.cumulativeWeight y v = 0
        · simp only [hv, ite_self]
        · rw [ite_eq_right (fun hs ↦ hface ((Φ.faceSelector_iff hp h Γ q hc v hmap hv).mp hs))]
      · rw [ite_eq_right hmap]
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp only [ite_self]

open Classical in
/-- The selected support at the anchor is precisely its old support on the
chosen face. -/
theorem centeredFibreMass_faceSelector_self (hp : Odd p)
    (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) (q : IntCoord (Φ.flag.rank x)) :
    FlagDecompositionRaw.centeredFibreMass
        (fun v ↦ if Φ.faceSelector x Γ v then Φ.cumulativeWeight x v else 0)
        (Φ.representation.map x) q =
      if q.real ∈ Γ.carrier then Φ.hat x q else 0 := by
  simpa only [Φ.flag.transition_refl, IntegralAffineMap.id_real, AffineMap.id_apply] using
    Φ.centeredFibreMass_faceSelector hp (le_refl x) Γ q

end EGZ.FlagDecomposition
