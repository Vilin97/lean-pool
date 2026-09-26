/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the conflict-overlap count at two distinct vertices

Pure `Finset` combinatorics, no probability.  The variance estimate for the safe degree needs the
following triple count: summing, over the edges `f` through `u` and the edges `g` through a
DIFFERENT
vertex `u'`, the number of edges conflicting with both, one gets a bound carrying a factor of the
CODEGREE `κ`:

  `∑_{f ∋ u} ∑_{g ∋ u'} |conflicts f ∩ conflicts g| ≤ 4 r² κ Δ²`.

(The corresponding statement at `u = u'` is false — there the sum is of order `Δ³` — which is
exactly
why the residual degree of a vertex does not concentrate while its SAFE degree does.)

Proof.  Writing `S = ∑_{h ∈ H} a(h)·b(h)` with `a(h) = #{f ∋ u : h ∈ conflicts f}` and
`b(h) = #{g ∋ u' : h ∈ conflicts g}` (`conflictCountAt`), split on whether `u' ∈ h`:

* `∑_{h ∈ H} a(h) = ∑_{f ∋ u} |conflicts f| ≤ Δ·rΔ`;
* for `u' ∉ h`, every `g ∋ u'` meeting `h` does so at a vertex `w ≠ u'`, so `b(h) ≤ r·κ`;
* for `u' ∈ h` and `u ∈ h` there are at most `codeg(u,u') ≤ κ` such `h`, and `a(h), b(h) ≤ Δ`;
* for `u' ∈ h` and `u ∉ h` there are at most `deg(u') ≤ Δ` such `h`, `a(h) ≤ rκ` and `b(h) ≤ Δ`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-- The number of edges through `x` that conflict with a given edge `h`. -/
def conflictCountAt (H : Finset (Finset V)) (x : V) (h : Finset V) : ℕ :=
  ((H.filter (fun f => x ∈ f)).filter (fun f => h ∈ conflicts H f)).card

/-- `conflictCountAt` is bounded by the degree of `x`. -/
theorem conflictCountAt_le_degree (H : Finset (Finset V)) (x : V) (h : Finset V) :
    conflictCountAt H x h ≤ degree H x :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- If `x ∉ h`, then every edge through `x` conflicting with `h` meets `h` at a vertex `≠ x`, so
`conflictCountAt` is bounded by a sum of codegrees. -/
theorem conflictCountAt_le_sum_codegree (H : Finset (Finset V)) {x : V} {h : Finset V} :
    conflictCountAt H x h ≤ ∑ w ∈ h, codegree H x w := by
  classical
  have hsub : ((H.filter (fun f => x ∈ f)).filter (fun f => h ∈ conflicts H f))
      ⊆ h.biUnion (fun w => H.filter (fun f => x ∈ f ∧ w ∈ f)) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨hfH, hxf⟩, hconf⟩ := hf
    obtain ⟨_, _, w, hw⟩ := Finset.mem_filter.mp hconf
    rw [Finset.mem_inter] at hw
    exact Finset.mem_biUnion.mpr ⟨w, hw.2, Finset.mem_filter.mpr ⟨hfH, hxf, hw.1⟩⟩
  calc conflictCountAt H x h ≤ (h.biUnion (fun w => H.filter (fun f => x ∈ f ∧ w ∈ f))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ h, (H.filter (fun f => x ∈ f ∧ w ∈ f)).card := Finset.card_biUnion_le
    _ = ∑ w ∈ h, codegree H x w := rfl

/-- With uniformity and a codegree bound: if `x ∉ h`, then `conflictCountAt H x h ≤ r·κ`. -/
theorem conflictCountAt_le_of_notMem {H : Finset (Finset V)} {r κ : ℕ} (hr : IsUniform H r)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) {x : V} {h : Finset V} (hh : h ∈ H)
    (hxh : x ∉ h) : conflictCountAt H x h ≤ r * κ := by
  calc conflictCountAt H x h ≤ ∑ w ∈ h, codegree H x w := conflictCountAt_le_sum_codegree H
    _ ≤ ∑ _w ∈ h, κ := Finset.sum_le_sum (fun w hw => hκ x w (fun hxw => hxh (hxw ▸ hw)))
    _ = r * κ := by rw [Finset.sum_const, smul_eq_mul, hr h hh]

/-- Double counting: summing `conflictCountAt H x ·` over all edges gives the total conflict count
of the edges through `x`. -/
theorem sum_conflictCountAt (H : Finset (Finset V)) (x : V) :
    ∑ h ∈ H, conflictCountAt H x h
      = ∑ f ∈ H.filter (fun f => x ∈ f), (conflicts H f).card := by
  classical
  simp only [conflictCountAt, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  ext h
  simp only [Finset.mem_filter]
  exact ⟨fun hh => hh.2, fun hh => ⟨(Finset.mem_filter.mp hh).1, hh⟩⟩

/-- The total conflict count of the edges through `x` is at most `Δ·rΔ`. -/
theorem sum_conflictCountAt_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y, degree H y ≤ Δ) (x : V) :
    ∑ h ∈ H, conflictCountAt H x h ≤ Δ * (r * Δ) := by
  classical
  rw [sum_conflictCountAt]
  calc ∑ f ∈ H.filter (fun f => x ∈ f), (conflicts H f).card
      ≤ ∑ _f ∈ H.filter (fun f => x ∈ f), r * Δ :=
        Finset.sum_le_sum (fun f hf =>
          conflicts_card_le_of_uniform hr hΔ (Finset.mem_filter.mp hf).1)
    _ = degree H x * (r * Δ) := by rw [Finset.sum_const, smul_eq_mul, degree]
    _ ≤ Δ * (r * Δ) := Nat.mul_le_mul_right _ (hΔ x)

/-- The double sum of conflict overlaps, written as a single sum over edges. -/
theorem sum_sum_conflicts_inter_eq (H : Finset (Finset V)) (u u' : V) :
    ∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        (conflicts H f ∩ conflicts H g).card
      = ∑ h ∈ H, conflictCountAt H u h * conflictCountAt H u' h := by
  classical
  set A := H.filter (fun f => u ∈ f) with hA
  set B := H.filter (fun g => u' ∈ g) with hB
  have key : ∀ f g : Finset V, (conflicts H f ∩ conflicts H g).card
      = ∑ h ∈ H, (if h ∈ conflicts H f then 1 else 0) * (if h ∈ conflicts H g then 1 else 0) := by
    intro f g
    have hset : conflicts H f ∩ conflicts H g
        = H.filter (fun h => h ∈ conflicts H f ∧ h ∈ conflicts H g) := by
      ext h
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun hh => ⟨(Finset.mem_filter.mp hh.1).1, hh.1, hh.2⟩, fun hh => ⟨hh.2.1, hh.2.2⟩⟩
    rw [hset, Finset.card_filter]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases h1 : h ∈ conflicts H f <;> by_cases h2 : h ∈ conflicts H g <;> simp [h1, h2]
  simp only [key]
  rw [Finset.sum_congr rfl (fun f (_ : f ∈ A) => Finset.sum_comm
    (s := B) (t := H)
    (f := fun g h => (if h ∈ conflicts H f then 1 else 0) *
      (if h ∈ conflicts H g then 1 else 0))), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [conflictCountAt, conflictCountAt, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_mul_sum]

/-- **The conflict-overlap count at two DISTINCT vertices.** `∑_{f ∋ u} ∑_{g ∋ u'} |conf f ∩ conf g|
≤ 4 r² κ Δ²`, where `Δ` bounds the degrees and `κ` the codegrees of distinct pairs. -/
theorem sum_conflicts_inter_card_le {H : Finset (Finset V)} {r Δ κ : ℕ}
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hΔ : ∀ x, degree H x ≤ Δ)
    (hκ : ∀ x y : V, x ≠ y → codegree H x y ≤ κ)
    {u u' : V} (huu' : u ≠ u') :
    ∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        (conflicts H f ∩ conflicts H g).card ≤ 4 * r ^ 2 * κ * Δ ^ 2 := by
  classical
  rw [sum_sum_conflicts_inter_eq]
  set a : Finset V → ℕ := fun h => conflictCountAt H u h with ha
  set b : Finset V → ℕ := fun h => conflictCountAt H u' h with hb
  -- split on whether `u' ∈ h`
  rw [← Finset.sum_filter_add_sum_filter_not H (fun h => u' ∈ h)]
  have hfar : ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h ≤ r ^ 2 * κ * Δ ^ 2 := by
    calc ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h
        ≤ ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * (r * κ) :=
          Finset.sum_le_sum (fun h hh => Nat.mul_le_mul_left _
            (conflictCountAt_le_of_notMem hr hκ (Finset.mem_filter.mp hh).1
              (Finset.mem_filter.mp hh).2))
      _ = (∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h) * (r * κ) := by rw [Finset.sum_mul]
      _ ≤ (∑ h ∈ H, a h) * (r * κ) := Nat.mul_le_mul_right _
          (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ ≤ (Δ * (r * Δ)) * (r * κ) := Nat.mul_le_mul_right _ (sum_conflictCountAt_le hr hΔ u)
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  have hnear : ∑ h ∈ H.filter (fun h => u' ∈ h), a h * b h ≤ κ * Δ ^ 2 + r * κ * Δ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (H.filter (fun h => u' ∈ h)) (fun h => u ∈ h)]
    have h1 : ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), a h * b h
        ≤ κ * Δ ^ 2 := by
      calc ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), a h * b h
          ≤ ∑ _h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), Δ * Δ :=
            Finset.sum_le_sum (fun h _ => Nat.mul_le_mul
              (conflictCountAt_le_degree H u h |>.trans (hΔ u))
              (conflictCountAt_le_degree H u' h |>.trans (hΔ u')))
        _ = ((H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h)).card * (Δ * Δ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ κ * (Δ * Δ) := by
            refine Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (hκ u u' huu'))
            rw [codegree]
            congr 1
            ext h
            simp only [Finset.mem_filter]
            tauto
        _ = κ * Δ ^ 2 := by ring
    have h2 : ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), a h * b h
        ≤ r * κ * Δ ^ 2 := by
      calc ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), a h * b h
          ≤ ∑ _h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), (r * κ) * Δ :=
            Finset.sum_le_sum (fun h hh => Nat.mul_le_mul
              (conflictCountAt_le_of_notMem hr hκ
                (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
                (Finset.mem_filter.mp hh).2)
              (conflictCountAt_le_degree H u' h |>.trans (hΔ u')))
        _ = ((H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h)).card * ((r * κ) * Δ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Δ * ((r * κ) * Δ) := by
            refine Nat.mul_le_mul_right _ ?_
            exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (hΔ u')
        _ = r * κ * Δ ^ 2 := by ring
    exact Nat.add_le_add h1 h2
  have h1 : κ * Δ ^ 2 ≤ r ^ 2 * κ * Δ ^ 2 := by
    have hp : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr1
    calc κ * Δ ^ 2 = 1 * (κ * Δ ^ 2) := by ring
      _ ≤ r ^ 2 * (κ * Δ ^ 2) := Nat.mul_le_mul_right _ hp
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  have h2 : r * κ * Δ ^ 2 ≤ r ^ 2 * κ * Δ ^ 2 := by
    have hp : r ≤ r ^ 2 := by nlinarith only []
    calc r * κ * Δ ^ 2 = r * (κ * Δ ^ 2) := by ring
      _ ≤ r ^ 2 * (κ * Δ ^ 2) := Nat.mul_le_mul_right _ hp
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  calc ∑ h ∈ H.filter (fun h => u' ∈ h), a h * b h
        + ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h
      ≤ (κ * Δ ^ 2 + r * κ * Δ ^ 2) + r ^ 2 * κ * Δ ^ 2 := Nat.add_le_add hnear hfar
    _ ≤ (r ^ 2 * κ * Δ ^ 2 + r ^ 2 * κ * Δ ^ 2) + r ^ 2 * κ * Δ ^ 2 :=
        Nat.add_le_add_right (Nat.add_le_add h1 h2) _
    _ = 3 * (r ^ 2 * κ * Δ ^ 2) := by ring
    _ ≤ 4 * (r ^ 2 * κ * Δ ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * r ^ 2 * κ * Δ ^ 2 := by ring

end LeanPool.AsymptoticTrianglePacking.Internal
