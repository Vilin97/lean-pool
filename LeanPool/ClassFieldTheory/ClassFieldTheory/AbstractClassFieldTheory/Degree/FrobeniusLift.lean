/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius

/-! # Frobenius Lift -/
namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: lifting finite Galois automorphisms

This file defines the Frobenius semigroup in `G(\widetilde L|K)` and proves
the lifting statement of the finite degree-quotient decomposition.  Positivity is explicit, so the
convention `0 ∉ ℕ` is not lost in Lean's natural numbers.
-/

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- In a finite cyclic quotient of `ℤ̂`, every class is represented by a
strictly positive natural multiple of `1`. -/
theorem exists_positive_nsmul_one_sub_mem_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) (z : ZHat) :
    ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H := by
  let m := H.index
  have hm : 0 < m := Nat.pos_of_ne_zero hH
  let r : ZMod m := zHatReduction m hm z
  let n : ℕ := r.val + m
  refine ⟨n, Nat.add_pos_right r.val hm, ?_⟩
  rw [zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH,
    zHatMulNat_range_eq_ker_reduction m hm]
  change zHatReduction m hm (z - n • (1 : ZHat)) = 0
  rw [map_sub, map_nsmul]
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  rw [hredOne]
  change zHatReduction m hm z - n • (1 : ZMod m) = 0
  rw [nsmul_eq_mul, mul_one]
  change r - (n : ZMod m) = 0
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hn : (n : ZMod m) = r := by
    change ((r.val + m : ℕ) : ZMod m) = r
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  rw [hn, sub_self]

namespace DegreeData

/-- `I_L`, viewed inside `G_K`; this is `G_{\widetilde L}`. -/
def extensionInertiaWithin (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : Subgroup K.toSubgroup :=
  extensionSubgroup K L hLK ⊓ D.fieldInertiaWithin K

/--
The relative inertia subgroup is normal whenever the full extension subgroup is normal.
-/
instance extensionInertiaWithin_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (D.extensionInertiaWithin K L hLK).Normal := by
  rw [extensionInertiaWithin]
  infer_instance

private theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker := by
  intro x hx
  rw [D.normalizedDegree_ker K]
  exact hx.2

/-- The factorized map `d_K : G(\widetilde L|K) → ℤ̂`. -/
def extensionNormalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →* ZHatMul :=
  QuotientGroup.lift (D.extensionInertiaWithin K.field L hLK)
    (D.normalizedDegree K).toMonoidHom
    (D.extensionInertiaWithin_le_normalizedDegree_ker K L hLK)

/--
Establishes the identity `D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
D.normalizedDegree K k`.
-/
@[simp]
theorem extensionNormalizedDegree_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) :
    D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
      D.normalizedDegree K k :=
  rfl

/-- Restriction from `G(\widetilde L|K)` to `G(L|K)`. -/
def extensionRestriction (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) →*
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  QuotientGroup.map (D.extensionInertiaWithin K L hLK)
    (extensionSubgroup K L hLK) (MonoidHom.id K.toSubgroup) inf_le_left

/--
Establishes the identity `D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk
k`.
-/
@[simp]
theorem extensionRestriction_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    D.extensionRestriction K L hLK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- The semigroup `Frob(\widetilde L|K)`: elements whose normalized
degree is a strictly positive natural. -/
def FrobeniusElements (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] : Type u :=
  {σ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK //
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree K L hLK σ =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n}

/-- The restriction map occurring in the finite degree-quotient decomposition. -/
def frobeniusRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
  fun σ => D.extensionRestriction K.field L hLK σ.1

private def normalizedExtensionImageAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup'
    ((extensionSubgroup K.field L hLK).map
      (D.normalizedDegree K).toMonoidHom)

private theorem normalizedExtensionImageAdd_index_ne_zero
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    (D.normalizedExtensionImageAdd K L hLK).index ≠ 0 := by
  let E := extensionSubgroup K.field L hLK
  let dK := (D.normalizedDegree K).toMonoidHom
  let H := E.map dK
  have hE : E ≤ H.comap dK := Subgroup.le_comap_map dK E
  have hdvd : (H.comap dK).index ∣ E.index :=
    Subgroup.index_dvd_of_le hE
  have hcomap : (H.comap dK).index = H.index :=
    Subgroup.index_comap_of_surjective H (D.normalizedDegree_surjective K)
  have hHdvd : H.index ∣ E.index := hcomap ▸ hdvd
  have hE0 : E.index ≠ 0 := E.index_ne_zero_of_finite
  have hH0 : H.index ≠ 0 := by
    intro hzero
    rw [hzero] at hHdvd
    exact hE0 (zero_dvd_iff.mp hHdvd)
  exact hH0

/-- **the finite degree-quotient decomposition.** For a finite Galois extension `L | K`, restriction
maps the Frobenius semigroup onto `G(L|K)`. -/
theorem frobeniusRestriction_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Function.Surjective (D.frobeniusRestriction K L hLK) := by
  intro σ
  refine Quotient.inductionOn' σ ?_
  intro s
  let H := D.normalizedExtensionImageAdd K L hLK
  have hH0 : H.index ≠ 0 :=
    D.normalizedExtensionImageAdd_index_ne_zero K L hLK
  obtain ⟨n, hn, hmem⟩ :=
    exists_positive_nsmul_one_sub_mem_of_index_ne_zero H hH0
      (D.normalizedDegree K s).toAdd
  have hneg : n • (1 : ZHat) - (D.normalizedDegree K s).toAdd ∈ H := by
    simpa [sub_eq_add_neg, add_comm] using H.neg_mem hmem
  change Multiplicative.ofAdd
      (n • (1 : ZHat) - (D.normalizedDegree K s).toAdd) ∈
    (extensionSubgroup K.field L hLK).map
      (D.normalizedDegree K).toMonoidHom at hneg
  obtain ⟨l, hlE, hdl⟩ := hneg
  let t : K.field.toSubgroup := s * l
  let q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.mk t
  have hdq : D.extensionNormalizedDegree K L hLK q =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    apply Multiplicative.ext
    change (D.normalizedDegree K (s * l)).toAdd =
      n • (1 : ZHat)
    rw [map_mul]
    change (D.normalizedDegree K s).toAdd +
        (D.normalizedDegree K l).toAdd = n • (1 : ZHat)
    have hdl' := congrArg Multiplicative.toAdd hdl
    change (D.normalizedDegree K l).toAdd =
      n • (1 : ZHat) - (D.normalizedDegree K s).toAdd at hdl'
    rw [hdl']
    abel
  let qF : D.FrobeniusElements K L hLK := ⟨q, n, hn, hdq⟩
  refine ⟨qF, ?_⟩
  change QuotientGroup.mk (s * l) = QuotientGroup.mk s
  apply QuotientGroup.eq.mpr
  change (s * l)⁻¹ * s ∈ extensionSubgroup K.field L hLK
  simpa [mul_inv_rev, mul_assoc] using
    (extensionSubgroup K.field L hLK).inv_mem hlE

end DegreeData

end
end ClassFormation
