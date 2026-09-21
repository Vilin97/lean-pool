/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-!
# Centered coordinate lifts

For odd moduli, reduction identifies the centered integer box with the whole
finite coordinate space.  The finite boxes also supply explicit support sets
for the lifted weights used in flag decompositions.
-/

open scoped BigOperators

namespace EGZ

@[simp]
theorem latticeSupNorm_le_iff {n K : ℕ} {z : IntCoord n} :
    latticeSupNorm z ≤ K ↔ ∀ i, (z i).natAbs ≤ K := by
  simp [latticeSupNorm, Finset.sup_le_iff]

@[simp]
theorem isCenteredLift_iff {p n : ℕ} {z : IntCoord n} :
    IsCenteredLift p z ↔ ∀ i, (z i).natAbs ≤ (p - 1) / 2 :=
  latticeSupNorm_le_iff

/-- Integer coordinate vectors in the closed box of radius `K`. -/
noncomputable def latticeBox (n K : ℕ) : Finset (IntCoord n) :=
  Fintype.piFinset fun _ : Fin n ↦ Finset.Icc (-(K : ℤ)) (K : ℤ)

@[simp]
theorem mem_latticeBox {n K : ℕ} {z : IntCoord n} :
    z ∈ latticeBox n K ↔ latticeSupNorm z ≤ K := by
  simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc,
    latticeSupNorm_le_iff]
  congr! 1
  omega

@[simp]
theorem card_latticeBox (n K : ℕ) :
    (latticeBox n K).card = (2 * K + 1) ^ n := by
  simp [latticeBox, Fintype.card_piFinset, Int.card_Icc]
  congr 1
  omega

theorem card_le_of_latticeSupNorm_le {n K : ℕ} (S : Finset (IntCoord n))
    (hS : ∀ z ∈ S, latticeSupNorm z ≤ K) :
    S.card ≤ (2 * K + 1) ^ n := by
  rw [← card_latticeBox]
  exact Finset.card_le_card (fun z hz ↦ mem_latticeBox.mpr (hS z hz))

namespace FpCoord

/-- Coordinatewise integer representatives with least absolute value. -/
def centeredLift {p n : ℕ} (c : FpCoord p n) : IntCoord n :=
  fun i ↦ (c i).valMinAbs

@[simp]
theorem centeredLift_apply {p n : ℕ} (c : FpCoord p n) (i : Fin n) :
    centeredLift c i = (c i).valMinAbs := rfl

@[simp]
theorem mod_centeredLift {p n : ℕ} (c : FpCoord p n) :
    (centeredLift c).mod p = c := by
  funext i
  exact ZMod.coe_valMinAbs (c i)

theorem isCenteredLift_centeredLift {p n : ℕ} [NeZero p]
    (hp : Odd p) (c : FpCoord p n) : IsCenteredLift p (centeredLift c) := by
  rw [isCenteredLift_iff]
  intro i
  have hpdiv : p / 2 = (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := hp
    omega
  simpa only [centeredLift_apply, ← hpdiv] using (c i).natAbs_valMinAbs_le

theorem centeredLift_mod {p n : ℕ} [NeZero p]
    {z : IntCoord n} (hz : IsCenteredLift p z) : centeredLift (z.mod p) = z := by
  funext i
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · have hi := isCenteredLift_iff.mp hz i
    have hp := NeZero.pos p
    omega
  · have hi := isCenteredLift_iff.mp hz i
    omega

end FpCoord

/-- Reduction is injective on the centered box, even for an even modulus. -/
theorem IsCenteredLift.eq_of_mod_eq {p n : ℕ} [NeZero p]
    {z w : IntCoord n} (hz : IsCenteredLift p z) (hw : IsCenteredLift p w)
    (h : z.mod p = w.mod p) : z = w := by
  rw [← FpCoord.centeredLift_mod hz, h, FpCoord.centeredLift_mod hw]

/-- For odd moduli each finite-field vector has exactly one centered lift. -/
theorem existsUnique_isCenteredLift {p n : ℕ} [NeZero p] (hp : Odd p)
    (c : FpCoord p n) : ∃! z : IntCoord n, IsCenteredLift p z ∧ z.mod p = c := by
  refine ⟨FpCoord.centeredLift c,
    ⟨FpCoord.isCenteredLift_centeredLift hp c, FpCoord.mod_centeredLift c⟩, ?_⟩
  intro z hz
  rw [← hz.2, FpCoord.centeredLift_mod hz.1]

/-- Summing over centered integer coordinates is the same as summing over
the finite coordinate space. -/
theorem sum_latticeBox_mod {p n : ℕ} [NeZero p] (hp : Odd p)
    (g : FpCoord p n → ℕ) :
    ∑ z ∈ latticeBox n ((p - 1) / 2), g (z.mod p) = ∑ c, g c := by
  classical
  apply Finset.sum_bij (fun z _ ↦ z.mod p)
  · intro z hz
    exact Finset.mem_univ _
  · intro z hz w hw hzw
    exact IsCenteredLift.eq_of_mod_eq (mem_latticeBox.mp hz)
      (mem_latticeBox.mp hw) hzw
  · intro c _
    refine ⟨FpCoord.centeredLift c, ?_, FpCoord.mod_centeredLift c⟩
    exact mem_latticeBox.mpr (FpCoord.isCenteredLift_centeredLift hp c)
  · intro z hz
    rfl

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- The support of the cumulative centered lift, constructed from a finite
box instead of stored as extra data. -/
noncomputable def hatSupport (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node) :
    Finset (IntCoord (F.rank x)) := by
  classical
  exact (latticeBox (F.rank x) ((p - 1) / 2)).filter
    fun z ↦ hat R pieces x z ≠ 0

@[simp]
theorem mem_hatSupport (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (z : IntCoord (F.rank x)) :
    z ∈ hatSupport R pieces x ↔ hat R pieces x z ≠ 0 := by
  classical
  simp only [hatSupport, Finset.mem_filter, mem_latticeBox]
  constructor
  · exact And.right
  · intro hz
    refine ⟨?_, hz⟩
    by_contra hcentered
    exact hz (by simp [hat, IsCenteredLift, hcentered])

theorem sum_affineFibreMass {n : ℕ} (w : FpCoord p d → ℕ)
    (φ : FpCoord p d → FpCoord p n) :
    ∑ c, affineFibreMass w φ c = natMass w := by
  classical
  unfold affineFibreMass natMass
  rw [Finset.sum_comm]
  simp

/-- Cumulative lifted mass is exactly cumulative finite-field mass. -/
theorem sum_hatSupport (hp : Odd p) (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node) :
    ∑ z ∈ hatSupport R pieces x, hat R pieces x z =
      natMass (cumulativeWeight pieces x) := by
  classical
  calc
    ∑ z ∈ hatSupport R pieces x, hat R pieces x z =
        ∑ z ∈ latticeBox (F.rank x) ((p - 1) / 2), hat R pieces x z := by
          rw [hatSupport, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs with hz
          · rfl
          · exact (not_ne_iff.mp hz).symm
    _ = ∑ z ∈ latticeBox (F.rank x) ((p - 1) / 2),
        affineFibreMass (cumulativeWeight pieces x) (R.map x) (z.mod p) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact ite_eq_left (mem_latticeBox.mp hz : IsCenteredLift p z)
    _ = ∑ c, affineFibreMass (cumulativeWeight pieces x) (R.map x) c :=
      sum_latticeBox_mod hp _
    _ = natMass (cumulativeWeight pieces x) := sum_affineFibreMass _ _

end FlagDecompositionRaw

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

theorem liftedSupport_eq_hatSupport (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    Φ.liftedSupport x =
      FlagDecompositionRaw.hatSupport Φ.representation Φ.localWeight x := by
  ext z
  rw [Φ.liftedSupport_spec, FlagDecompositionRaw.mem_hatSupport]

/-- The stored support does not change the total cumulative mass. -/
theorem sum_liftedSupport (hp : Odd p) (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    ∑ z ∈ Φ.liftedSupport x, Φ.hat x z = natMass (Φ.cumulativeWeight x) := by
  rw [Φ.liftedSupport_eq_hatSupport]
  exact FlagDecompositionRaw.sum_hatSupport hp Φ.representation Φ.localWeight x

end FlagDecomposition

namespace FpRepresentation

/-- The rank of a represented node cannot exceed the ambient dimension. -/
theorem rank_le {p d : ℕ} [Fact p.Prime] {F : ConvexFlag}
    (R : FpRepresentation p d F) (x : F.Node) : F.rank x ≤ d := by
  have hsurj : Function.Surjective (R.map x) := by
    intro c
    obtain ⟨v, _hv, hvc⟩ := R.map_surjective x (Set.mem_univ c)
    exact ⟨v, hvc⟩
  have hlinear := (R.map x).linear_surjective_iff.mpr hsurj
  simpa using LinearMap.finrank_le_finrank_of_surjective hlinear

end FpRepresentation

end EGZ
