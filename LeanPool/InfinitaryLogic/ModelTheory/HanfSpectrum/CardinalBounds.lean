/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Cardinal lemmas for the beth ladder

The consumer-shaped cardinal arithmetic of the Hanf beth-ladder upper-bound induction and its
supremum endpoint (`docs/hanf-ladder-audit.md` §3, §5) — no syntax, no models:

* `mk_sigma_le_of_countable` / `mk_iUnion_le_of_countable` — countable families of `≤ κ`-sized
  pieces stay `≤ κ` (for infinite `κ`): the limit-level case;
* `sum_le_of_countable_lift` / `lift_mk_iUnion_le_of_countable` — the same, for a bound that does
  not live in the ambient universe. A bound assembled from both language data and structure data
  is in neither, so the same-universe forms cannot state it;
* `mk_le_two_power_of_injective_set` — an injection into a powerset bounds by `2 ^ ·`:
  the successor-level case (with Mathlib's `Cardinal.beth_succ` for orientation);
* `iSup_beth_add_one_omega1` — the successor-cofinal supremum at `ω₁`:
  `⨆_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁}` — the endpoint that turns the per-stage witnesses into
  `ℶ_{ω₁} ≤ Hanf(L_{ω₁ω})`.

Marker's recursion `ℶ_α = sup_{β<α} 2^{ℶ_β}` agrees with Mathlib's `beth` for `α ≠ 0` (at `0`
the right side is the empty supremum), so Mathlib's `beth_zero`/`beth_succ`/`beth_limit` are
used directly as the formal interface; no second recursive beth is introduced.
-/

namespace FirstOrder

namespace HanfLadder

open Cardinal

universe u

/-- The countable-sum core: a countable sum of cardinals each `≤ κ` is `≤ κ`, for infinite
`κ`. -/
private theorem sum_le_of_countable {ι : Type u} [Countable ι]
    {f : ι → Cardinal.{u}} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hf : ∀ i, f i ≤ κ) : Cardinal.sum f ≤ κ := by
  calc Cardinal.sum f ≤ Cardinal.sum (fun _ : ι => κ) := Cardinal.sum_le_sum _ _ hf
    _ = Cardinal.mk ι * κ := Cardinal.sum_const' _ _
    _ ≤ Cardinal.aleph0 * κ :=
        mul_le_mul_left Cardinal.mk_le_aleph0 κ
    _ = κ := Cardinal.aleph0_mul_eq hκ

universe v

/-- `sum_le_of_countable` with the bound in a larger universe than the index type.

A bound assembled from both language data and structure data does not live in the structure's
universe, so the same-universe form cannot state it. The index type still has to be countable
in its own universe; only the summands move. -/
private theorem sum_le_of_countable_lift {ι : Type u} [Countable ι] {f : ι → Cardinal.{v}}
    {κ : Cardinal.{max u v}} (hκ : Cardinal.aleph0 ≤ κ)
    (hf : ∀ i, Cardinal.lift.{u} (f i) ≤ κ) : Cardinal.sum f ≤ κ := by
  have hι : Cardinal.lift.{max u v} (Cardinal.mk ι) ≤ Cardinal.aleph0 := by
    simp [Cardinal.mk_le_aleph0]
  calc Cardinal.sum f
      = Cardinal.sum (fun i => Cardinal.lift.{u} (f i)) :=
        (Cardinal.lift_id' _).symm.trans (Cardinal.lift_sum f)
    _ ≤ Cardinal.sum (fun _ : ι => κ) := Cardinal.sum_le_sum _ _ hf
    _ = Cardinal.lift.{max u v} (Cardinal.mk ι) * Cardinal.lift.{u} κ := Cardinal.sum_const _ _
    _ = Cardinal.lift.{max u v} (Cardinal.mk ι) * κ := by rw [Cardinal.lift_id' κ]
    _ ≤ Cardinal.aleph0 * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.aleph0_mul_eq hκ

universe w

/-- The lifted form of `mk_iUnion_le_of_countable`, for a bound outside the ambient universe.

The index type gets its own universe: an index fixed independently of the ambient type (a stage
count, say) would otherwise drag that type down to the index's universe. -/
theorem lift_mk_iUnion_le_of_countable {M : Type u} {ι : Type w} [Countable ι] {X : ι → Set M}
    {κ : Cardinal.{max u v w}} (hκ : Cardinal.aleph0 ≤ κ)
    (hX : ∀ i, Cardinal.lift.{max v w} (Cardinal.mk (X i)) ≤ κ) :
    Cardinal.lift.{max v w} (Cardinal.mk (⋃ i, X i)) ≤ κ := by
  have h := Cardinal.lift_le.{v}.mpr (Cardinal.mk_iUnion_le_sum_mk_lift (α := M) (f := X))
  rw [Cardinal.lift_lift, Cardinal.lift_sum] at h
  refine le_trans h (sum_le_of_countable_lift hκ fun i => ?_)
  rw [Cardinal.lift_lift]
  exact hX i

/-- A countable dependent sum of types each of size `≤ κ` has size `≤ κ`, for infinite `κ`. -/
theorem mk_sigma_le_of_countable {ι : Type u} [Countable ι] {X : ι → Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hX : ∀ i, Cardinal.mk (X i) ≤ κ) :
    Cardinal.mk (Σ i, X i) ≤ κ := by
  rw [Cardinal.mk_sigma]
  exact sum_le_of_countable hκ hX

/-- A countable union of sets each of size `≤ κ` has size `≤ κ`, for infinite `κ` — the
limit-level case of the ladder induction. -/
theorem mk_iUnion_le_of_countable {M : Type u} {ι : Type u} [Countable ι] {X : ι → Set M}
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) (hX : ∀ i, Cardinal.mk (X i) ≤ κ) :
    Cardinal.mk (⋃ i, X i) ≤ κ :=
  le_trans (Cardinal.mk_iUnion_le_sum_mk) (sum_le_of_countable hκ hX)

/-- An injection into a powerset bounds by `2 ^ ·` — the successor-level case of the ladder
induction. -/
theorem mk_le_two_power_of_injective_set {X Y : Type u} {f : X → Set Y}
    (hf : Function.Injective f) : Cardinal.mk X ≤ 2 ^ Cardinal.mk Y :=
  (Cardinal.mk_le_of_injective hf).trans_eq (Cardinal.mk_set)

/-- The successor-cofinal supremum at `ω₁`: `⨆_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁}` — the ladder's
endpoint. -/
theorem iSup_beth_add_one_omega1 :
    ⨆ α : Set.Iio (Ordinal.omega 1), Cardinal.beth (α.1 + 1) = Cardinal.beth (Ordinal.omega 1) := by
  have hlim : Order.IsSuccLimit (Ordinal.omega 1) := Cardinal.isSuccLimit_omega 1
  apply le_antisymm
  · refine ciSup_le' fun α => ?_
    exact Cardinal.beth_le_beth.mpr (Order.succ_eq_add_one α.1 ▸ (hlim.succ_lt α.2).le)
  · rw [Cardinal.beth_limit hlim]
    refine ciSup_le' fun β => ?_
    refine le_trans (Cardinal.beth_le_beth.mpr
      (le_of_lt ((Order.lt_succ β.1).trans_eq (Order.succ_eq_add_one β.1)))) ?_
    exact le_ciSup (f := fun α : Set.Iio (Ordinal.omega 1) => Cardinal.beth (α.1 + 1))
      Cardinal.bddAbove_of_small ⟨β.1, β.2⟩

end HanfLadder

end FirstOrder
