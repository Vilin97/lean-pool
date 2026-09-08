/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.IntegerDivergence
import LeanPool.RareDistanceFields.RationalPlane

/-!
# Both rare-distance assertions for rational-coordinate planar sets

See the project entry module for the exact coordinate restrictions and source roles.
Clearing denominators preserves every distance class and its unordered count.
For n rational-coordinate planar points and r occurring positive Euclidean
lengths of multiplicity at most n, the theorem below proves n <= 2^r.
No reduction of arbitrary real planar configurations is claimed.
-/

namespace LeanPool.RareDistanceFields.RationalDivergence

open RationalPlane
noncomputable section

variable {V : Type*} [Fintype V]

open Classical in
/-- Occurring rational squared distances with multiplicity at most the label count. -/
def rareSquared (x : V → Point) : Finset ℚ :=
  (OrderedColors.palette (fun a b => sqDist (x a) (x b))).filter
    fun r => (graph x r).edgeFinset.card ≤ Fintype.card V

open Classical in
/-- Occurring Euclidean distances with unordered multiplicity at most the label count. -/
def rareDistances (x : V → Point) : Finset ℝ :=
  (OrderedColors.palette (fun a b => dist (complexPoint (x a)) (complexPoint (x b)))).filter
    fun r => (distanceGraph x r).edgeFinset.card ≤ Fintype.card V

open Classical in
theorem exists_pair_of_mem_rareSquared (x : V → Point) {r : ℚ} (hr : r ∈ rareSquared x) :
    ∃ a b, a ≠ b ∧ sqDist (x a) (x b) = r := by
  obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
  exact ⟨a, b, (Finset.mem_offDiag.mp hab).2.2, he⟩

open Classical in
theorem rareSquared_positive (x : V → Point) (hx : Function.Injective x)
    {r : ℚ} (hr : r ∈ rareSquared x) : 0 < r := by
  obtain ⟨a, b, hab, rfl⟩ := exists_pair_of_mem_rareSquared x hr
  exact sqDist_pos _ _ (hx.ne hab)

open Classical in
theorem card_le_pow_rareSquared (x : V → Point) (hx : Function.Injective x) :
    Fintype.card V ≤ 2 ^ (rareSquared x).card := by
  classical
  obtain ⟨B, hB, y, hy⟩ := clear_denominators x
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hB2 : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hB'
  have hscale (p q : V) : (IntegerPlane.sqDist (y p) (y q) : ℚ) =
      (B : ℚ) ^ 2 * sqDist (x p) (x q) := by
    dsimp [IntegerPlane.sqDist, DyadicNorm.normSq, sqDist]
    push_cast
    rw [(hy p).1, (hy p).2, (hy q).1, (hy q).2]
    ring
  have hyinj : Function.Injective y := by
    intro p q he
    apply hx
    apply Prod.ext
    · apply mul_left_cancel₀ hB'
      rw [← (hy p).1, ← (hy q).1, he]
    · apply mul_left_cancel₀ hB'
      rw [← (hy p).2, ← (hy q).2, he]
  let f : ℤ → ℚ := fun r => (r : ℚ) / (B : ℚ) ^ 2
  have hf : Function.Injective f := by
    intro r s he
    apply Int.cast_injective (α := ℚ)
    have hh := congrArg (fun q : ℚ => q * (B : ℚ) ^ 2) he
    simpa [f, hB2] using hh
  have heq (p q : V) (r : ℤ) : IntegerPlane.sqDist (y p) (y q) = r ↔
      sqDist (x p) (x q) = f r := by
    constructor
    · intro h
      apply (eq_div_iff hB2).mpr
      rw [mul_comm, ← hscale, h]
    · intro h
      apply Int.cast_injective (α := ℚ)
      rw [hscale, h]
      dsimp [f]
      field_simp
  have hg (r : ℤ) : IntegerPlane.graph y r = graph x (f r) := by
    ext p q
    simp only [IntegerPlane.graph, graph, OrderedColors.colorGraph, heq]
  have hsub : (IntegerDivergence.rareSquared y).image f ⊆ rareSquared x := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    have hs' := Finset.mem_filter.mp hs
    obtain ⟨a, b, hab, he⟩ := IntegerDivergence.exists_pair_of_mem_palette y hs'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], (heq a b s).mp he⟩, ?_⟩
    exact hg s ▸ hs'.2
  have hc : (IntegerDivergence.rareSquared y).card ≤ (rareSquared x).card := by
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hf] at hh
  exact (IntegerDivergence.card_le_pow_rare y hyinj).trans
    (Nat.pow_le_pow_right (by decide) hc)

open Classical in
theorem sqrt_sqDist (p q : Point) :
    Real.sqrt (sqDist p q : ℝ) = dist (complexPoint p) (complexPoint q) := by
  rw [← complex_dist_sq]
  exact Real.sqrt_sq (dist_nonneg)

open Classical in
theorem rareSquared_card_le_rareDistances (x : V → Point) (hx : Function.Injective x) :
    (rareSquared x).card ≤ (rareDistances x).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun r : ℚ => Real.sqrt (r : ℝ))
  · intro r hr
    obtain ⟨a, b, hab, he⟩ := exists_pair_of_mem_rareSquared x hr
    have hs : Real.sqrt (r : ℝ) = dist (complexPoint (x a)) (complexPoint (x b)) := by
      rw [← he, sqrt_sqDist]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], hs.symm⟩, ?_⟩
    have hm := (Finset.mem_filter.mp hr).2
    rw [← he, graph_eq_distanceGraph] at hm
    change (distanceGraph x (Real.sqrt (r : ℝ))).edgeFinset.card ≤ Fintype.card V
    rwa [hs]
  · intro r hr s hs he
    have hrp : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (rareSquared_positive x hx hr).le
    have hsp : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (rareSquared_positive x hx hs).le
    have hh := congrArg (fun a : ℝ => a ^ 2) he
    rw [Real.sq_sqrt hrp, Real.sq_sqrt hsp] at hh
    exact_mod_cast hh

open Classical in
/-- A quantitative bound using actual positive Euclidean distance classes. -/
theorem card_le_pow_rareDistances (x : V → Point) (hx : Function.Injective x) :
    Fintype.card V ≤ 2 ^ (rareDistances x).card :=
  (card_le_pow_rareSquared x hx).trans
    (Nat.pow_le_pow_right (by decide) (rareSquared_card_le_rareDistances x hx))

open Classical in
theorem rareDistances_spec (x : V → Point) (hx : Function.Injective x)
    {d : ℝ} (hd : d ∈ rareDistances x) : 0 < d ∧
    (∃ a b, dist (complexPoint (x a)) (complexPoint (x b)) = d) ∧
    (distanceGraph x d).edgeFinset.card ≤ Fintype.card V := by
  have hd' := Finset.mem_filter.mp hd
  obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hd'.1
  dsimp only at he
  refine ⟨?_, ⟨a, b, he⟩, hd'.2⟩
  have hp := sqDist_pos (x a) (x b) (hx.ne (Finset.mem_offDiag.mp hab).2.2)
  have hp' : (0 : ℝ) < (sqDist (x a) (x b) : ℝ) := by exact_mod_cast hp
  rw [← complex_dist_sq, he] at hp'
  have hn : 0 ≤ d := he ▸ dist_nonneg
  nlinarith

open Classical in
/-- Uniform divergence for rational-coordinate planar sets; N=2^k suffices. -/
theorem uniform_divergence (k : ℕ) : ∃ N : ℕ, ∀ {V : Type*} [Fintype V]
    (x : V → Point), Function.Injective x → N ≤ Fintype.card V →
      k ≤ (rareDistances x).card := by
  refine ⟨2 ^ k, ?_⟩
  intro V inst x hx hn
  have hh := card_le_pow_rareDistances x hx
  by_contra h
  have hp : 2 ^ (rareDistances x).card < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end
end LeanPool.RareDistanceFields.RationalDivergence
