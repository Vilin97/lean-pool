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
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Convex Subgroups of Linearly Ordered Commutative Groups

We define convex subgroups of linearly ordered commutative groups and prove
basic properties, following §7.1 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `ConvexSubgroup Γ` : A subgroup of `Γ` that is order-convex.
* `ConvexSubgroup.quotientLinearOrder` : `LinearOrder` on `Γ ⧸ H.toSubgroup`.
* `ConvexSubgroup.quotientIsOrderedMonoid` : `IsOrderedMonoid` on `Γ ⧸ H.toSubgroup`.
* `ConvexSubgroup.mulArchimedean_iff_convex_trivial` : `MulArchimedean Γ ↔ only ⊥ and ⊤`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.1
-/

variable (Γ : Type*) [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- A **convex subgroup** of a linearly ordered commutative group `Γ` is a subgroup
that is order-convex: if `a ≤ x ≤ b` and `a, b ∈ H`, then `x ∈ H`. -/
structure ConvexSubgroup extends Subgroup Γ where
  convex' : ∀ {a b x : Γ},
    a ∈ carrier → b ∈ carrier → a ≤ x → x ≤ b → x ∈ carrier

namespace ConvexSubgroup

variable {Γ}

instance : SetLike (ConvexSubgroup Γ) Γ where
  coe H := H.carrier
  coe_injective := by
    intro ⟨H₁, _⟩ ⟨H₂, _⟩ h
    congr 1
    exact Subgroup.ext (Set.ext_iff.mp h)

instance : SubgroupClass (ConvexSubgroup Γ) Γ where
  mul_mem {H} := H.toSubgroup.mul_mem'
  one_mem {H} := H.toSubgroup.one_mem'
  inv_mem {H} := H.toSubgroup.inv_mem'

omit [IsOrderedMonoid Γ] in
/-- Extensionality for convex subgroups. -/
@[ext]
theorem ext {H₁ H₂ : ConvexSubgroup Γ} (h : ∀ x, x ∈ H₁ ↔ x ∈ H₂) : H₁ = H₂ :=
  SetLike.ext h

omit [IsOrderedMonoid Γ] in
/-- Convexity: if `a, b ∈ H` and `a ≤ x ≤ b`, then `x ∈ H`. -/
theorem convex (H : ConvexSubgroup Γ) {a b x : Γ} (ha : a ∈ H) (hb : b ∈ H)
    (h₁ : a ≤ x) (h₂ : x ≤ b) : x ∈ H :=
  H.convex' ha hb h₁ h₂

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between `1` and any of its members ≥ 1. -/
theorem mem_of_one_le_le {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (h1 : 1 ≤ x) (hx : x ≤ h) : x ∈ H :=
  H.convex (one_mem H) hh h1 hx

omit [IsOrderedMonoid Γ] in
/-- A convex subgroup contains every element between any of its members ≤ 1 and `1`. -/
theorem mem_of_le_le_one {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (hx : h ≤ x) (h1 : x ≤ 1) : x ∈ H :=
  H.convex hh (one_mem H) hx h1

/-- The trivial convex subgroup `{1}`. -/
instance : Bot (ConvexSubgroup Γ) where
  bot := {
    toSubgroup := ⊥
    convex' := by
      intro a b x ha hb h₁ h₂
      change x ∈ (⊥ : Subgroup Γ)
      rw [Subgroup.mem_bot]
      have ha' : a = 1 := Subgroup.mem_bot.mp ha
      have hb' : b = 1 := Subgroup.mem_bot.mp hb
      exact le_antisymm (h₂.trans hb'.le) (ha'.ge.trans h₁)
  }

/-- The full group as a convex subgroup. -/
instance : Top (ConvexSubgroup Γ) where
  top := {
    toSubgroup := ⊤
    convex' := fun _ _ _ _ ↦ trivial
  }

omit [IsOrderedMonoid Γ] in
/-- Membership in `⊥` is equivalent to being `1`. -/
@[simp] theorem mem_bot {x : Γ} : x ∈ (⊥ : ConvexSubgroup Γ) ↔ x = 1 :=
  Subgroup.mem_bot

omit [IsOrderedMonoid Γ] in
/-- Every element belongs to `⊤`. -/
@[simp] theorem mem_top {x : Γ} : x ∈ (⊤ : ConvexSubgroup Γ) :=
  trivial

/-- Convex subgroups are normal (automatic for commutative groups). -/
instance normal (H : ConvexSubgroup Γ) : H.toSubgroup.Normal :=
  Subgroup.normal_of_isMulCommutative H.toSubgroup

omit [IsOrderedMonoid Γ] in
/-- An element `γ` with `1 ≤ γ` is in `H` iff `γ⁻¹` is. -/
theorem inv_mem_iff_mem {H : ConvexSubgroup Γ} {γ : Γ} :
    γ⁻¹ ∈ H ↔ γ ∈ H :=
  ⟨fun h ↦ inv_inv γ ▸ inv_mem h, inv_mem⟩

/-- Partial order on convex subgroups by inclusion. -/
instance : PartialOrder (ConvexSubgroup Γ) :=
  { le := fun H₁ H₂ ↦ ∀ x, x ∈ H₁ → x ∈ H₂
    le_refl := fun _ _ hx ↦ hx
    le_trans := fun _ _ _ h₁₂ h₂₃ x hx ↦ h₂₃ x (h₁₂ x hx)
    le_antisymm := fun _ _ h₁₂ h₂₁ ↦ ext fun _ ↦ ⟨h₁₂ _, h₂₁ _⟩ }

instance : OrderBot (ConvexSubgroup Γ) where
  bot_le := fun H _ hx ↦ mem_bot.mp hx ▸ one_mem H

instance : OrderTop (ConvexSubgroup Γ) where
  le_top := fun _ _ _ ↦ mem_top

/-! ### Elements outside a convex subgroup -/

omit [IsOrderedMonoid Γ] in
/-- If `γ ∉ H` and `γ < 1`, then `γ < h` for every `h ∈ H`. -/
theorem lt_of_not_mem_of_lt_one (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1)
    {h : Γ} (hh : h ∈ H) : γ < h := by
  by_contra hle; push Not at hle; exact hγ (H.convex' hh (one_mem H) hle hγ1.le)

omit [IsOrderedMonoid Γ] in
/-- If `γ ∉ H` and `1 < γ`, then `h < γ` for every `h ∈ H`. -/
theorem lt_of_not_mem_of_one_lt (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ)
    {h : Γ} (hh : h ∈ H) : h < γ := by
  by_contra hle; push Not at hle; exact hγ (H.convex' (one_mem H) hh hγ1.le hle)

/-! ### Quotient linear order on `Γ ⧸ H.toSubgroup` -/

/-- `c ≤ 1 ∨ c ∈ H` is invariant under right-multiplication by `H`-elements. -/
private theorem quotientLE_aux (H : ConvexSubgroup Γ) (c k : Γ) (hk : k ∈ H.toSubgroup) :
    (c ≤ 1 ∨ c ∈ H.toSubgroup) ↔ (c * k ≤ 1 ∨ c * k ∈ H.toSubgroup) := by
  by_cases hc : (c : Γ) ∈ H
  · exact ⟨fun _ ↦ .inr (H.toSubgroup.mul_mem hc hk), fun _ ↦ .inr hc⟩
  · have hck : c * k ∉ H := by
      intro hmem; have := H.toSubgroup.mul_mem hmem (H.toSubgroup.inv_mem hk)
      simp only [mul_inv_cancel_right] at this; exact hc this
    simp only [show ¬(c ∈ H.toSubgroup) from hc,
      show ¬(c * k ∈ H.toSubgroup) from hck, or_false]
    exact ⟨fun h1 ↦ le_of_lt (lt_inv_iff_mul_lt_one.mp (H.lt_of_not_mem_of_lt_one hc
        (lt_of_le_of_ne h1 (fun h ↦ hc (h ▸ H.toSubgroup.one_mem))) (inv_mem hk))),
      fun h1 ↦ by by_contra hc1; push Not at hc1; exact absurd h1 (not_le.mpr
        (inv_lt_iff_one_lt_mul.mp (H.lt_of_not_mem_of_one_lt hc hc1 (inv_mem hk))))⟩

/-- `[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or `b⁻¹ * a ∈ H`. -/
instance quotientLE (H : ConvexSubgroup Γ) : LE (Γ ⧸ H.toSubgroup) where
  le x y := Quotient.liftOn₂' x y
    (fun a b ↦ b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup)
    (fun a₁ b₁ a₂ b₂ ha hb ↦ by
      rw [QuotientGroup.leftRel_apply] at ha hb
      have hk : (b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂) ∈ H.toSubgroup :=
        H.toSubgroup.mul_mem (H.toSubgroup.inv_mem hb) ha
      have : b₂⁻¹ * a₂ =
          (b₁⁻¹ * a₁) * ((b₁⁻¹ * b₂)⁻¹ * (a₁⁻¹ * a₂)) := by
        simp only [mul_inv_rev, inv_inv, ← mul_assoc]; simp [mul_comm, mul_left_comm, mul_assoc]
      rw [this]; exact propext (quotientLE_aux H _ _ hk))

/-- Unfolding of `≤` on the quotient `Γ ⧸ H.toSubgroup`. -/
theorem quotient_le_iff (H : ConvexSubgroup Γ) (a b : Γ) :
    ((a : Γ ⧸ H.toSubgroup) ≤ (b : Γ ⧸ H.toSubgroup)) ↔
    (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) :=
  Iff.rfl

private theorem quotient_le_total' (H : ConvexSubgroup Γ) (a b : Γ) :
    (a : Γ ⧸ H.toSubgroup) ≤ b ∨ (b : Γ ⧸ H.toSubgroup) ≤ a := by
  change (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) ∨
         (a⁻¹ * b ≤ 1 ∨ a⁻¹ * b ∈ H.toSubgroup)
  by_cases hm : b⁻¹ * a ∈ H.toSubgroup
  · exact .inl (.inr hm)
  · have hne : b⁻¹ * a ≠ 1 := fun h ↦ hm (h ▸ H.toSubgroup.one_mem)
    rcases lt_or_gt_of_ne hne with h | h
    · exact .inl (.inl h.le)
    · exact .inr (.inl (le_of_lt (by
        rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
        exact inv_lt_one_of_one_lt h)))

/-- The quotient `Γ ⧸ H.toSubgroup` by a convex subgroup `H` carries a linear order:
`[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or `b⁻¹ * a ∈ H`. -/
noncomputable instance quotientLinearOrder (H : ConvexSubgroup Γ) :
    LinearOrder (Γ ⧸ H.toSubgroup) where
  le_refl x := by
    induction x using Quotient.inductionOn with
    | _ a => exact .inl (inv_mul_cancel a).le
  le_trans x y z hxy hyz := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    induction z using Quotient.inductionOn with | _ c =>
    change c⁻¹ * a ≤ 1 ∨ _
    change b⁻¹ * a ≤ 1 ∨ _ at hxy
    change c⁻¹ * b ≤ 1 ∨ _ at hyz
    have : c⁻¹ * a = (c⁻¹ * b) * (b⁻¹ * a) := by simp [mul_assoc, mul_inv_cancel_left]
    rw [this]
    rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
    · left; exact mul_le_one' hyz hxy
    · rw [mul_comm]; exact (quotientLE_aux H _ _ hyz).mp (.inl hxy)
    · exact (quotientLE_aux H _ _ hxy).mp (.inl hyz)
    · right; exact H.toSubgroup.mul_mem hyz hxy
  le_antisymm x y hxy hyx := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    change b⁻¹ * a ≤ 1 ∨ _ at hxy; change a⁻¹ * b ≤ 1 ∨ _ at hyx
    apply QuotientGroup.eq.mpr
    rcases hxy with hxy | hxy
    · rcases hyx with hyx | hyx
      · have h1 : 1 ≤ b⁻¹ * a := by
          rw [show b⁻¹ * a = (a⁻¹ * b)⁻¹ from by simp [mul_inv_rev, inv_inv]]
          exact one_le_inv_of_le_one hyx
        have : a⁻¹ * b = 1 := by
          rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
          exact inv_eq_one.mpr (le_antisymm hxy h1)
        rw [this]; exact H.toSubgroup.one_mem
      · exact hyx
    · rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by simp [mul_inv_rev, inv_inv]]
      exact H.toSubgroup.inv_mem hxy
  le_total x y := by
    induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
    exact quotient_le_total' H a b
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

/-- The quotient order is compatible with the group operation. -/
instance quotientIsOrderedMonoid (H : ConvexSubgroup Γ) :
    IsOrderedMonoid (Γ ⧸ H.toSubgroup) where
  mul_le_mul_left a b hab c := by
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    induction c using Quotient.inductionOn with | _ c =>
    change (b * c)⁻¹ * (a * c) ≤ 1 ∨ _
    change b⁻¹ * a ≤ 1 ∨ _ at hab
    have : (b * c)⁻¹ * (a * c) = b⁻¹ * a := by simp [mul_inv_rev, mul_comm, mul_assoc]
    rw [this]; exact hab

/-! ### Total ordering of convex subgroups -/

/-- Convex subgroups of a linearly ordered commutative group are totally ordered. -/
theorem le_total_of_convex (H₁ H₂ : ConvexSubgroup Γ) : H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  by_contra h
  push Not at h
  obtain ⟨hne₁, hne₂⟩ := h
  obtain ⟨a, haH₁, haH₂⟩ := Set.not_subset.mp (show ¬(H₁ : Set Γ) ⊆ H₂ from hne₁)
  have ha1 : a ≠ 1 := fun h ↦ haH₂ (h ▸ one_mem H₂)
  have hle : ∀ b, b ∈ H₂ → b ∈ H₁ := by
    intro b hb
    rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
    · have hab : a < b := H₂.lt_of_not_mem_of_lt_one haH₂ ha_lt hb
      have : a⁻¹ ∉ H₂ := inv_mem_iff_mem.not.mpr haH₂
      have hba : b < a⁻¹ := H₂.lt_of_not_mem_of_one_lt this (one_lt_inv_of_inv ha_lt) hb
      exact H₁.convex haH₁ (inv_mem haH₁) hab.le hba.le
    · have hba : b < a := H₂.lt_of_not_mem_of_one_lt haH₂ ha_gt hb
      have : a⁻¹ ∉ H₂ := inv_mem_iff_mem.not.mpr haH₂
      have hab : a⁻¹ < b := H₂.lt_of_not_mem_of_lt_one this (inv_lt_one_of_one_lt ha_gt) hb
      exact H₁.convex (inv_mem haH₁) haH₁ hab.le hba.le
  exact hne₂ hle

noncomputable instance : LinearOrder (ConvexSubgroup Γ) :=
  { (inferInstance : PartialOrder (ConvexSubgroup Γ)) with
    le_total := le_total_of_convex
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _
    toDecidableLT := Classical.decRel _ }

/-! ### Smallest convex subgroup containing a set -/

/-- **Convex subgroup generated by a set.** The smallest convex subgroup of `Γ`
containing every element of `S`. Defined as the intersection of all convex
subgroups containing `S`.

This is the universal "containing" construction dual to `maxAvoid` (which is
the largest convex subgroup *avoiding* a single element). For our use, this
underwrites `cΓ_v(I)` from Wedhorn 7.3: the smallest convex subgroup
generated by `{v(a) : v(a) ≥ 1, a ∈ A} ∪ {v(b)⁻¹ : b ∈ I, v(b) > 0}`. -/
def minContain (S : Set Γ) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := { x | ∀ (H : ConvexSubgroup Γ), S ⊆ H → x ∈ H }
      one_mem' := fun H _ ↦ one_mem H
      mul_mem' := fun ha hb H hS ↦ mul_mem (ha H hS) (hb H hS)
      inv_mem' := fun ha H hS ↦ inv_mem (ha H hS) }
  convex' := fun ha hb h₁ h₂ H hS ↦
    H.convex (ha H hS) (hb H hS) h₁ h₂

omit [IsOrderedMonoid Γ] in
/-- `S ⊆ minContain S` — the generating set is contained in its convex closure. -/
theorem subset_minContain (S : Set Γ) : S ⊆ minContain S :=
  fun _ hx _ hS ↦ hS hx

omit [IsOrderedMonoid Γ] in
/-- Universal property: `minContain S` is contained in every convex subgroup
containing `S`. -/
theorem minContain_le {S : Set Γ} {H : ConvexSubgroup Γ} (hS : S ⊆ H) :
    minContain S ≤ H :=
  fun _ hx ↦ hx H hS

/-! ### Largest convex subgroup avoiding an element -/

/-- The largest convex subgroup of `Γ` not containing `γ`. -/
noncomputable def maxAvoid {γ : Γ} (hγ : γ ≠ 1) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := { x | ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H }
      mul_mem' := fun {a b} ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ ↦ by
        rcases le_total H₁ H₂ with h | h
        · exact ⟨H₂, hγ₂, H₂.toSubgroup.mul_mem' (h _ ha) hb⟩
        · exact ⟨H₁, hγ₁, H₁.toSubgroup.mul_mem' ha (h _ hb)⟩
      one_mem' := ⟨⊥, mem_bot.not.mpr hγ, one_mem ⊥⟩
      inv_mem' := fun {a} ⟨H, hγH, ha⟩ ↦ ⟨H, hγH, H.toSubgroup.inv_mem' ha⟩ }
  convex' := by
    intro a b x ⟨H₁, hγ₁, ha⟩ ⟨H₂, hγ₂, hb⟩ h₁ h₂
    rcases le_total H₁ H₂ with h | h
    · exact ⟨H₂, hγ₂, H₂.convex (h _ ha) hb h₁ h₂⟩
    · exact ⟨H₁, hγ₁, H₁.convex ha (h _ hb) h₁ h₂⟩

/-- Membership in `maxAvoid hγ`: `x ∈ maxAvoid hγ` iff some convex subgroup excludes `γ`
but contains `x`. -/
theorem mem_maxAvoid_iff {γ : Γ} {hγ : γ ≠ 1} {x : Γ} :
    x ∈ maxAvoid hγ ↔ ∃ H : ConvexSubgroup Γ, γ ∉ H ∧ x ∈ H := Iff.rfl

/-- The element `γ` is not in `maxAvoid hγ`. -/
theorem not_mem_maxAvoid {γ : Γ} (hγ : γ ≠ 1) : γ ∉ maxAvoid hγ :=
  fun ⟨_, hγH, hγH'⟩ ↦ hγH hγH'

/-- Any convex subgroup not containing `γ` is `≤ maxAvoid hγ`. -/
theorem le_maxAvoid_of_not_mem {γ : Γ} {hγ : γ ≠ 1} {H : ConvexSubgroup Γ} (h : γ ∉ H) :
    H ≤ maxAvoid hγ :=
  fun _ hx ↦ ⟨H, h, hx⟩

omit [IsOrderedMonoid Γ] in
/-- If `γ ∉ H`, `1 < γ`, and `γ ≤ x`, then `x ∉ H`.

Any element above an excluded element (above `1`) is also excluded, by
convexity: if `x ∈ H` then `γ` would lie between `1 ∈ H` and `x ∈ H`,
hence `γ ∈ H`. -/
theorem not_mem_of_not_mem_of_one_lt_le (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ) {x : Γ} (hγx : γ ≤ x) : x ∉ H :=
  fun hx ↦ hγ (H.convex (one_mem H) hx hγ1.le hγx)

omit [IsOrderedMonoid Γ] in
/-- Elements `≤` an excluded element below `1` are also excluded. -/
theorem not_mem_of_not_mem_of_le_lt_one (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1) {x : Γ} (hxγ : x ≤ γ) : x ∉ H :=
  fun hx ↦ hγ (H.convex hx (one_mem H) hxγ hγ1.le)

/-- If `γ ∉ maxAvoid hδ` and `1 < γ` and `γ ≤ x`, then `x ∉ maxAvoid hδ`. -/
theorem not_mem_maxAvoid_of_le {δ : Γ} {hδ : δ ≠ 1} {γ : Γ}
    (hγ : γ ∉ maxAvoid hδ) (hγ1 : 1 < γ) {x : Γ} (hγx : γ ≤ x) :
    x ∉ maxAvoid hδ :=
  (maxAvoid hδ).not_mem_of_not_mem_of_one_lt_le hγ hγ1 hγx

/-! ### Properties of `maxAvoid` -/

/-- Every nontrivial convex subgroup of `Γ ⧸ (maxAvoid hγ)` contains `[γ]`. -/
theorem maxAvoid_mem_of_nontrivial {γ : Γ} (hγ : γ ≠ 1)
    (K : ConvexSubgroup (Γ ⧸ (maxAvoid hγ).toSubgroup))
    (hK : K ≠ ⊥) :
    (QuotientGroup.mk' (maxAvoid hγ).toSubgroup γ : Γ ⧸ _) ∈ K := by
  by_contra hγK
  have hπ_mono : Monotone (QuotientGroup.mk' (maxAvoid hγ).toSubgroup) := by
    intro a b hab; left; rwa [inv_mul_le_iff_le_mul, mul_one]
  let C : ConvexSubgroup Γ :=
    { toSubgroup := K.toSubgroup.comap (QuotientGroup.mk' (maxAvoid hγ).toSubgroup)
      convex' := fun ha hb h₁ h₂ ↦ K.convex ha hb (hπ_mono h₁) (hπ_mono h₂) }
  have hle : maxAvoid hγ ≤ C := fun x hx ↦ by
    change (x : Γ ⧸ (maxAvoid hγ).toSubgroup) ∈ K
    rw [(QuotientGroup.eq_one_iff x).mpr hx]; exact one_mem K
  have hγC : γ ∉ C := hγK
  have hle' : C ≤ maxAvoid hγ := le_maxAvoid_of_not_mem hγC
  apply hK; ext ⟨x⟩; constructor
  · exact fun hx ↦ (QuotientGroup.eq_one_iff x).mpr (hle' _ hx)
  · intro hx; rw [hx]; exact one_mem K

/-! ### Archimedean characterization -/

/-- In a `MulArchimedean` linearly ordered group, every convex subgroup is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_mulArchimedean [MulArchimedean Γ]
    (H : ConvexSubgroup Γ) : H = ⊥ ∨ H = ⊤ := by
  by_contra hH; push Not at hH; obtain ⟨hbot, htop⟩ := hH
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ H, 1 < y := by
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ H, y ≠ 1 := by
      by_contra h; push Not at h; exact hbot (ext fun x ↦
        ⟨fun hx ↦ mem_bot.mpr (h x hx), fun hx ↦ mem_bot.mp hx ▸ one_mem H⟩)
    rcases lt_or_gt_of_ne hy1 with h | h
    · exact ⟨y⁻¹, inv_mem hy, one_lt_inv_of_inv h⟩
    · exact ⟨y, hy, h⟩
  obtain ⟨x, hx, hx1⟩ : ∃ x, x ∉ H ∧ 1 < x := by
    obtain ⟨x, hxH⟩ : ∃ x, x ∉ H := by
      by_contra h; push Not at h; exact htop (ext fun x ↦
        ⟨fun _ ↦ mem_top, fun _ ↦ h x⟩)
    rcases lt_or_gt_of_ne (show x ≠ 1 from fun h ↦ hxH (h ▸ one_mem H)) with h | h
    · exact ⟨x⁻¹, inv_mem_iff_mem.not.mpr hxH, one_lt_inv_of_inv h⟩
    · exact ⟨x, hxH, h⟩
  obtain ⟨n, hn⟩ := MulArchimedean.arch x hy1
  exact hx (H.convex (one_mem H) (H.toSubgroup.pow_mem hy n) hx1.le hn)

/-- The convex subgroup generated by `y > 1`: all elements bounded by powers of `y`.

`convexGenerated hy` is the **smallest** convex subgroup of `Γ` containing `y`.
Its carrier is `{h | ∃ n : ℕ, (y ^ n)⁻¹ ≤ h ∧ h ≤ y ^ n}`.

This is used in the retraction construction of Wedhorn (7.1.2) and in the
proof that the quotient by `maxAvoid` need not be MulArchimedean while the
generated subgroup itself always is (see `mulArchimedean_convexGenerated`). -/
noncomputable def convexGenerated {y : Γ} (hy : 1 < y) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := {h | ∃ n : ℕ, (y ^ n)⁻¹ ≤ h ∧ h ≤ y ^ n}
      mul_mem' := by
        rintro a b ⟨n₁, ha_lo, ha_hi⟩ ⟨n₂, hb_lo, hb_hi⟩
        refine ⟨n₁ + n₂, ?_, ?_⟩
        · rw [pow_add, mul_inv_rev, mul_comm]; exact mul_le_mul' ha_lo hb_lo
        · exact (mul_le_mul' ha_hi hb_hi).trans (pow_add y n₁ n₂ ▸ le_refl _)
      one_mem' := ⟨0, by simp only [pow_zero, inv_one, le_refl],
        le_of_eq (by simp only [pow_zero])⟩
      inv_mem' := by
        rintro a ⟨n, ha_lo, ha_hi⟩
        exact ⟨n, inv_le_inv' ha_hi, inv_inv (y ^ n) ▸ inv_le_inv' ha_lo⟩ }
  convex' := by
    rintro a b x ⟨n₁, ha_lo, -⟩ ⟨n₂, -, hb_hi⟩ hax hxb
    exact ⟨max n₁ n₂,
      (inv_le_inv' (pow_le_pow_right' hy.le (le_max_left _ _))).trans (ha_lo.trans hax),
      hxb.trans (hb_hi.trans (pow_le_pow_right' hy.le (le_max_right _ _)))⟩

/-- Membership in `convexGenerated hy`: bounded between inverse powers and powers of `y`. -/
theorem mem_convexGenerated_iff {y : Γ} {hy : 1 < y} {h : Γ} :
    h ∈ convexGenerated hy ↔ ∃ n : ℕ, (y ^ n)⁻¹ ≤ h ∧ h ≤ y ^ n :=
  Iff.rfl

/-- The generator `y` belongs to `convexGenerated hy`. -/
theorem self_mem_convexGenerated {y : Γ} (hy : 1 < y) :
    y ∈ convexGenerated hy := by
  refine ⟨1, ?_, by simp only [pow_one, le_refl]⟩
  simp only [pow_one]
  exact (inv_le_one_of_one_le hy.le).trans hy.le

/-- An element `h ≤ y` with `y⁻¹ ≤ h` belongs to `convexGenerated hy`. -/
theorem mem_convexGenerated_of_between {y : Γ} {hy : 1 < y} {h : Γ}
    (h_lo : y⁻¹ ≤ h) (h_hi : h ≤ y) :
    h ∈ convexGenerated hy :=
  ⟨1, by simpa using h_lo, by simpa using h_hi⟩

/-- `convexGenerated hy` is the smallest convex subgroup containing `y`. -/
theorem convexGenerated_le {y : Γ} {hy : 1 < y} {H : ConvexSubgroup Γ}
    (hH : y ∈ H) : convexGenerated hy ≤ H := by
  intro x ⟨n, hlo, hhi⟩
  exact H.convex (inv_mem (H.toSubgroup.pow_mem hH n))
    (H.toSubgroup.pow_mem hH n) hlo hhi

/-- In `convexGenerated hy`, every element `> 1` eventually exceeds any given element
under repeated powering by the generator. More precisely, for `x ∈ convexGenerated hy`,
there exists `n` with `x ≤ y ^ n`.

This is the key cofinal/archimedean property of the generated convex subgroup. -/
theorem le_pow_of_mem_convexGenerated {y : Γ} {hy : 1 < y} {x : Γ}
    (hx : x ∈ convexGenerated hy) : ∃ n : ℕ, x ≤ y ^ n :=
  let ⟨n, _, hhi⟩ := hx; ⟨n, hhi⟩

/-- Powers of `y⁻¹` are cofinal below any element of `convexGenerated hy`:
for any `x ∈ convexGenerated hy`, there exists `n` with `(y⁻¹)^n ≤ x`,
equivalently `(y^n)⁻¹ ≤ x`. -/
theorem inv_pow_le_of_mem_convexGenerated {y : Γ} {hy : 1 < y} {x : Γ}
    (hx : x ∈ convexGenerated hy) : ∃ n : ℕ, (y ^ n)⁻¹ ≤ x :=
  let ⟨n, hlo, _⟩ := hx; ⟨n, hlo⟩

/-- **Strict cofinal property.** For any `h ∈ convexGenerated hy`, there exists `n`
with `(y ^ (n+1))⁻¹ < h`. Since `y > 1`, `(y^{n+1})⁻¹ < (y^n)⁻¹ ≤ h`. -/
theorem inv_pow_succ_lt_of_mem_convexGenerated {y : Γ} (hy : 1 < y) {h : Γ}
    (hh : h ∈ convexGenerated hy) :
    ∃ n : ℕ, (y ^ (n + 1))⁻¹ < h := by
  obtain ⟨m, hm_lo, _⟩ := hh
  refine ⟨m, lt_of_lt_of_le ?_ hm_lo⟩
  exact inv_lt_inv' (pow_lt_pow_right' hy m.lt_succ_self)

/-- **The key cofinal property for Wedhorn's retraction (7.1.2).**
For `y > 1` and any `h ∈ convexGenerated hy`, there exists `n` with `y⁻¹ ^ n < h`. -/
theorem exists_inv_pow_lt_of_mem_convexGenerated {y : Γ} (hy : 1 < y) {h : Γ}
    (hh : h ∈ convexGenerated hy) :
    ∃ n : ℕ, y⁻¹ ^ n < h := by
  obtain ⟨m, hm⟩ := inv_pow_succ_lt_of_mem_convexGenerated hy hh
  exact ⟨m + 1, by rwa [inv_pow]⟩

/-- **Wedhorn Definition 1.16.** `γ` is *cofinal* for the subgroup `H` if every element of
`H` eventually dominates a power of `γ` (`∀ h ∈ H, ∃ n, γ^n < h`). -/
def IsCofinalElt (H : ConvexSubgroup Γ) (γ : Γ) : Prop :=
  ∀ h ∈ H, ∃ n : ℕ, γ ^ n < h

/-- **Wedhorn Proposition 1.20** (`wedhorn.txt:348`). If `γ` is cofinal for the convex
subgroup `Γ'` and `Δ ⊊ Γ'` is a proper convex subgroup, then `δ * γ` is cofinal for `Γ'`
for every `δ ∈ Δ`. -/
theorem isCofinalElt_mul_of_mem_of_lt {Γ' Δ : ConvexSubgroup Γ}
    (hlt : Δ < Γ') {γ : Γ} (hγ : IsCofinalElt Γ' γ) {δ : Γ} (hδ : δ ∈ Δ) :
    IsCofinalElt Γ' (δ * γ) := by
  intro h hh
  obtain ⟨x, hxQ, hxD⟩ := SetLike.exists_of_lt hlt
  -- WLOG the witness `z ∈ Γ' \ Δ` has `1 < z`.
  obtain ⟨z, hzQ, hzD, hz_gt⟩ : ∃ z, z ∈ Γ' ∧ z ∉ Δ ∧ 1 < z := by
    rcases lt_trichotomy x 1 with hl | he | hg
    · exact ⟨x⁻¹, inv_mem hxQ, fun e => hxD (by simpa using inv_mem e), one_lt_inv'.mpr hl⟩
    · exact absurd (he ▸ one_mem Δ) hxD
    · exact ⟨x, hxQ, hxD, hg⟩
  obtain ⟨n, hn⟩ := hγ z⁻¹ (inv_mem hzQ)
  have hzi_lt : z⁻¹ < 1 := inv_lt_one'.mpr hz_gt
  have hγ_lt : γ < 1 := by
    by_contra hge; rw [not_lt] at hge
    exact absurd (lt_of_lt_of_le hn (le_trans hzi_lt.le (one_le_pow_of_one_le' hge n)))
      (lt_irrefl _)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp only [pow_zero] at hn; exact absurd (hn.trans hzi_lt) (lt_irrefl _)
    · exact hp
  -- `z` dominates all of `Δ` (convexity: `z ∉ Δ`, `z > 1`, `1 ∈ Δ`).
  have hz_gt_D : ∀ d ∈ Δ, d < z := fun d hd => by
    by_contra hge; rw [not_lt] at hge
    exact hzD (Δ.convex (one_mem Δ) hd hz_gt.le hge)
  -- Key inequality `(δγ)^(2n) < γ^n` (Wedhorn 1.20 proof).
  have hzγn : z * γ ^ n < 1 := by
    have h2 : γ ^ n * z < z⁻¹ * z := mul_lt_mul_left hn z
    rw [inv_mul_cancel] at h2; rwa [mul_comm] at h2
  have hkey : (δ * γ) ^ (2 * n) < γ ^ n := by
    have hδ2n : δ ^ (2 * n) < z := hz_gt_D _ (Δ.toSubgroup.pow_mem hδ (2 * n))
    calc (δ * γ) ^ (2 * n) = δ ^ (2 * n) * γ ^ (2 * n) := mul_pow δ γ (2 * n)
      _ < z * γ ^ (2 * n) := mul_lt_mul_left hδ2n _
      _ = (z * γ ^ n) * γ ^ n := by rw [two_mul, pow_add, ← mul_assoc]
      _ < 1 * γ ^ n := mul_lt_mul_left hzγn _
      _ = γ ^ n := one_mul _
  -- Cofinality: pick `m ≥ 1` with `γ^m < h`, then `(δγ)^(2nm) < γ^(nm) ≤ γ^m < h`.
  obtain ⟨m, hm1, hm⟩ : ∃ m, 1 ≤ m ∧ γ ^ m < h := by
    obtain ⟨m0, hm0⟩ := hγ h hh
    rcases Nat.eq_zero_or_pos m0 with rfl | hp
    · exact ⟨1, le_refl _, by rw [pow_one]; rw [pow_zero] at hm0; exact lt_trans hγ_lt hm0⟩
    · exact ⟨m0, hp, hm0⟩
  refine ⟨2 * n * m, ?_⟩
  calc (δ * γ) ^ (2 * n * m) = ((δ * γ) ^ (2 * n)) ^ m := by rw [← pow_mul]
    _ < (γ ^ n) ^ m := pow_lt_pow_left' (Nat.one_le_iff_ne_zero.mp hm1) hkey
    _ = γ ^ (n * m) := by rw [← pow_mul]
    _ ≤ γ ^ m := pow_le_pow_right_of_le_one' hγ_lt.le (Nat.le_mul_of_pos_left m hn1)
    _ < h := hm

/-- If every convex subgroup is `⊥` or `⊤`, the group is `MulArchimedean`. -/
theorem mulArchimedean_of_no_proper_nontrivial
    (h : ∀ H : ConvexSubgroup Γ, H = ⊥ ∨ H = ⊤) : MulArchimedean Γ where
  arch x {y} hy := by
    by_contra hna; push Not at hna
    let G := convexGenerated hy
    have hy_mem : y ∈ G := self_mem_convexGenerated hy
    have hx_nmem : x ∉ G := fun ⟨n, _, hle⟩ ↦ not_le.mpr (hna n) hle
    rcases h G with heq | heq
    · exact ne_of_gt hy (mem_bot.mp (heq ▸ hy_mem))
    · exact hx_nmem (heq ▸ mem_top)

/-- **Archimedean characterization.** A linearly ordered commutative group is
`MulArchimedean` if and only if its only convex subgroups are `⊥` and `⊤`. -/
theorem mulArchimedean_iff_convex_trivial :
    MulArchimedean Γ ↔ (∀ H : ConvexSubgroup Γ, H = ⊥ ∨ H = ⊤) :=
  ⟨fun _ ↦ eq_bot_or_eq_top_of_mulArchimedean,
   mulArchimedean_of_no_proper_nontrivial⟩

/-! ### Preimage of convex subgroups -/

/-- Preimage of a convex subgroup under a monotone group homomorphism is convex.

If `f : Γ →* Δ` is monotone and `K` is a convex subgroup of `Δ`, then
`f⁻¹(K)` is a convex subgroup of `Γ`. This is used to lift convex subgroups
from quotient value groups back to the original value group. -/
def comap {Δ : Type*} [CommGroup Δ] [LinearOrder Δ] [IsOrderedMonoid Δ]
    (K : ConvexSubgroup Δ) (f : Γ →* Δ) (hf : Monotone f) :
    ConvexSubgroup Γ where
  toSubgroup := K.toSubgroup.comap f
  convex' := fun ha hb hax hxb ↦ K.convex ha hb (hf hax) (hf hxb)

omit [IsOrderedMonoid Γ] in
@[simp]
theorem mem_comap {Δ : Type*} [CommGroup Δ] [LinearOrder Δ] [IsOrderedMonoid Δ]
    {K : ConvexSubgroup Δ} {f : Γ →* Δ} {hf : Monotone f} {x : Γ} :
    x ∈ K.comap f hf ↔ f x ∈ K :=
  Iff.rfl

end ConvexSubgroup
