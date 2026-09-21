/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.Valuation.Basic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.OrderedGroupConvex

/-!
# Valuation Coarsening by Convex Subgroups

Given a valuation `v : Valuation R Γ₀` and a convex subgroup `H` of `Γ`, the
**coarsened valuation** `v.coarsen H` is the composition of `v` with the
projection `Γ₀ → (Γ ⧸ H)₀`, following §7.1 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `WithZero.mapMonoidWithZeroHom` : Lift a `MonoidHom` to a `MonoidWithZeroHom` on `WithZero`.
* `Valuation.coarsen` : Coarsening of a valuation by a convex subgroup.

## Main results

* `Valuation.coarsen_supp` : Coarsening preserves the support ideal.
* `Valuation.coarsen_le_one_of_le_one` : If `v(a) ≤ 1` then `(v.coarsen H)(a) ≤ 1`.
* `Valuation.coarsen_lt_one_of_not_mem` : If `v(a) < 1` and `v(a) ∉ H`, then
  `(v.coarsen H)(a) < 1`.
* `Valuation.coarsen_pow_cofinal` : In an archimedean quotient, powers of elements
  with coarsened value `< 1` are cofinal for `0`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.1
-/

/-! ### Lifting `MonoidHom` to `MonoidWithZeroHom` on `WithZero` -/

namespace WithZero

variable {α β : Type*} [CommGroup α] [CommGroup β]

/-- Lift a `MonoidHom α β` to a `MonoidWithZeroHom (WithZero α) (WithZero β)`. -/
noncomputable def mapMonoidWithZeroHom (f : α →* β) : WithZero α →*₀ WithZero β where
  toFun := WithZero.map f
  map_zero' := WithZero.map_bot f
  map_one' := by
    change WithZero.map f (↑(1 : α)) = ↑(1 : β)
    rw [WithZero.map_coe, map_one]
  map_mul' x y := by
    cases x with
    | zero => simp [WithZero.map_bot, zero_mul]
    | coe a =>
      cases y with
      | zero => simp [WithZero.map_bot, mul_zero]
      | coe b =>
        change WithZero.map f (↑a * ↑b) = WithZero.map f ↑a * WithZero.map f ↑b
        rw [← WithZero.coe_mul, WithZero.map_coe, WithZero.map_coe, WithZero.map_coe,
            ← WithZero.coe_mul, map_mul]

@[simp]
theorem mapMonoidWithZeroHom_apply_coe (f : α →* β) (a : α) :
    mapMonoidWithZeroHom f (↑a) = ↑(f a) :=
  WithZero.map_coe f a

@[simp]
theorem mapMonoidWithZeroHom_apply_zero (f : α →* β) :
    mapMonoidWithZeroHom f 0 = 0 :=
  WithZero.map_bot f

theorem mapMonoidWithZeroHom_monotone [LinearOrder α]
    [LinearOrder β] (f : α →* β) (hf : Monotone f) :
    Monotone (mapMonoidWithZeroHom f) := by
  intro x y hxy
  cases x with
  | zero => exact bot_le
  | coe a =>
    cases y with
    | zero => exact absurd hxy (not_le.mpr (WithZero.zero_lt_coe a))
    | coe b =>
      change WithZero.map f ↑a ≤ WithZero.map f ↑b
      rw [WithZero.map_coe, WithZero.map_coe]
      exact WithZero.coe_le_coe.mpr (hf (WithZero.coe_le_coe.mp hxy))

end WithZero

/-! ### Quotient projection is monotone -/

namespace ConvexSubgroup

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- The quotient map `Γ → Γ ⧸ H.toSubgroup` is monotone. -/
theorem quotientMk_monotone (H : ConvexSubgroup Γ) :
    Monotone (QuotientGroup.mk' H.toSubgroup) := by
  intro a b hab
  change b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup
  left
  rwa [inv_mul_le_iff_le_mul, mul_one]

/-- The quotient map sends elements `≤ 1` to elements `≤ 1`. -/
theorem quotientMk_le_one (H : ConvexSubgroup Γ) {a : Γ} (ha : a ≤ 1) :
    (QuotientGroup.mk' H.toSubgroup a : Γ ⧸ H.toSubgroup) ≤ 1 := by
  have : (1 : Γ ⧸ H.toSubgroup) = QuotientGroup.mk' H.toSubgroup 1 := by simp
  rw [this]
  exact H.quotientMk_monotone ha

/-- If `a < 1` and `a ∉ H`, then `[a] < 1` in the quotient. -/
theorem quotientMk_lt_one_of_not_mem (H : ConvexSubgroup Γ) {a : Γ}
    (ha : a < 1) (haH : a ∉ H) :
    (QuotientGroup.mk' H.toSubgroup a : Γ ⧸ H.toSubgroup) < 1 := by
  refine lt_of_le_of_ne (H.quotientMk_le_one ha.le) ?_
  intro heq
  have hmem : a⁻¹ * 1 ∈ H.toSubgroup := QuotientGroup.eq.mp (by
    change QuotientGroup.mk' H.toSubgroup a = QuotientGroup.mk' H.toSubgroup 1
    exact heq ▸ by simp)
  rw [mul_one] at hmem
  exact haH (inv_inv a ▸ inv_mem hmem)

end ConvexSubgroup

/-! ### Valuation coarsening -/

namespace Valuation

variable {R : Type*} [CommRing R]
variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- **Coarsening** of a valuation by a convex subgroup `H` of its value group.
The coarsened valuation is the composition `R →ᵥ Γ₀ →π (Γ/H)₀` where `π` is the
quotient projection (§7.1 of Wedhorn). -/
noncomputable def coarsen (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ) :
    Valuation R (WithZero (Γ ⧸ H.toSubgroup)) :=
  v.map (WithZero.mapMonoidWithZeroHom (QuotientGroup.mk' H.toSubgroup))
    (WithZero.mapMonoidWithZeroHom_monotone _ H.quotientMk_monotone)

@[simp]
theorem coarsen_apply (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ) (r : R) :
    v.coarsen H r = WithZero.mapMonoidWithZeroHom (QuotientGroup.mk' H.toSubgroup) (v r) :=
  Valuation.map_apply _ _ _ _

/-- Coarsening preserves the support: `supp(v.coarsen H) = supp(v)`. -/
theorem coarsen_supp (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ) :
    (v.coarsen H).supp = v.supp := by
  ext r
  simp only [Valuation.mem_supp_iff, coarsen_apply]
  constructor
  · intro h
    cases hr : v r with
    | zero => exact rfl
    | coe g =>
      simp [hr, WithZero.mapMonoidWithZeroHom_apply_coe] at h
  · intro h
    simp [h]

/-- If `v(a) ≤ 1` then `(v.coarsen H)(a) ≤ 1`. -/
theorem coarsen_le_one_of_le_one (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ)
    {a : R} (ha : v a ≤ 1) : v.coarsen H a ≤ 1 := by
  simp only [coarsen_apply]
  cases hr : v a with
  | zero => simp [WithZero.mapMonoidWithZeroHom_apply_zero]
  | coe g =>
    rw [WithZero.mapMonoidWithZeroHom_apply_coe]
    rw [hr] at ha
    have hg : g ≤ 1 := by rwa [WithZero.coe_le_one] at ha
    exact WithZero.coe_le_one.mpr (H.quotientMk_le_one hg)

/-- If `v(a) < 1` and the underlying value is not in `H`, then `(v.coarsen H)(a) < 1`. -/
theorem coarsen_lt_one_of_not_mem (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ)
    {a : R} {g : Γ} (hva : v a = ↑g) (hg1 : g < 1) (hgH : g ∉ H) :
    v.coarsen H a < 1 := by
  simp only [coarsen_apply, hva, WithZero.mapMonoidWithZeroHom_apply_coe]
  exact WithZero.coe_lt_one.mpr (H.quotientMk_lt_one_of_not_mem hg1 hgH)

/-! ### Cofinal property for archimedean coarsenings -/

/-- In a `MulArchimedean` quotient, elements `< 1` have powers cofinal for `0`. -/
theorem WithZero.pow_eventually_le_of_lt_one {Q : Type*} [CommGroup Q] [LinearOrder Q]
    [IsOrderedMonoid Q] [MulArchimedean Q]
    {g : Q} (hg : g < 1) (δ : WithZero Q) (hδ : 0 < δ) :
    ∃ n : ℕ, (↑(g ^ n) : WithZero Q) ≤ δ := by
  obtain ⟨d, rfl⟩ := WithZero.ne_zero_iff_exists.mp (ne_of_gt hδ)
  obtain ⟨n, hn⟩ := MulArchimedean.arch d⁻¹ (one_lt_inv_of_inv hg)
  exact ⟨n, WithZero.coe_le_coe.mpr (by rwa [inv_pow, inv_le_inv_iff] at hn)⟩

/-- Powers of elements with coarsened value `< 1` are cofinal for `0`. -/
theorem coarsen_pow_cofinal
    (v : Valuation R (WithZero Γ)) (H : ConvexSubgroup Γ)
    [MulArchimedean (Γ ⧸ H.toSubgroup)]
    {a : R} (ha_ne : v a ≠ 0) (ha_lt : v.coarsen H a < 1)
    (δ : WithZero (Γ ⧸ H.toSubgroup)) (hδ : 0 < δ) :
    ∃ n : ℕ, v.coarsen H (a ^ n) ≤ δ := by
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.mp ha_ne
  have hca : v.coarsen H a = ↑(QuotientGroup.mk' H.toSubgroup γ) := by
    simp only [coarsen_apply, ← hγ, WithZero.mapMonoidWithZeroHom_apply_coe]
  have hq_lt : QuotientGroup.mk' H.toSubgroup γ < 1 := by
    rwa [hca, WithZero.coe_lt_one] at ha_lt
  obtain ⟨d, rfl⟩ := WithZero.ne_zero_iff_exists.mp (ne_of_gt hδ)
  obtain ⟨n, hn⟩ := MulArchimedean.arch d⁻¹ (one_lt_inv_of_inv hq_lt)
  refine ⟨n, ?_⟩
  rw [map_pow, hca, ← WithZero.coe_pow]
  exact WithZero.coe_le_coe.mpr (by rwa [inv_pow, inv_le_inv_iff] at hn)

end Valuation
