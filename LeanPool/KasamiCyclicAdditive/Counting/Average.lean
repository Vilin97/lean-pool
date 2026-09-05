/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Counting.Definitions
import LeanPool.KasamiCyclicAdditive.Assembly.ElementaryInputs

/-!
# The Walsh and average formulas from half-size alone

The Walsh triple-count formula and the slope-average formula are elementary
consequences of the derivative-image half-size equation `2|Δ| = Q` alone, for
an arbitrary finite subset of a characteristic-two field: no Kasami-specific
fact beyond half-size is used.

The arguments are additive-character orthogonality for the Walsh formula, and
direct double-counting — including the diagonal `x = y = z` contribution — for
the average.  Both are proved for an arbitrary `Δ : Finset K` and then
specialized to `derivativeImage k K`.
-/

open Finset

namespace KasamiCyclicAdditive

namespace CountAverage

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Normalized triple count for an arbitrary finite subset. -/
def slopeTripleCount (Delta : Finset K) (ρ : K) : ℕ :=
  ((Delta ×ˢ Delta ×ˢ Delta).filter
    (fun p => p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0)).card

/-- Walsh coefficient of a finite subset: `∑_{x ∈ Δ} ψ(a x)`. -/
noncomputable def walshCoefficient (Delta : Finset K) (psi : AddChar K ℂ) (a : K) : ℂ :=
  ∑ x ∈ Delta, psi (a * x)

/-! ### Auxiliary lemmas -/

/-- Orthogonality: the sum of `psi (a * t)` over all `a` is `|K|` if `t = 0`, else `0`. -/
lemma sum_char_mul (psi : AddChar K ℂ) (hpsi : psi.IsPrimitive) (t : K) :
    ∑ a : K, psi (a * t) = if t = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht, Finset.card_univ]
  · simp only [ht, ite_false]
    have h : ∀ a : K, psi (a * t) = (AddChar.mulShift psi t) a := by
      intro a; simp [AddChar.mulShift_apply, mul_comm]
    simp_rw [h]
    exact AddChar.sum_eq_zero_of_ne_one (hpsi ht)

/-- Sum over the units of `K` equals the sum over the nonzero elements. -/
lemma sum_units_eq (f : K → ℂ) :
    ∑ u : Kˣ, f (u : K) = ∑ a ∈ Finset.univ.erase (0 : K), f a := by
  rw [Finset.sum_subtype (p := fun a : K => a ≠ 0) (Finset.univ.erase (0 : K))
      (by intro x; simp) (fun a => f a)]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)

omit [Fintype K] [DecidableEq K] in
/-- The Walsh coefficient at `0` is `|Δ|`. -/
lemma walshCoefficient_zero (Delta : Finset K) (psi : AddChar K ℂ) :
    walshCoefficient Delta psi 0 = (Delta.card : ℂ) := by
  simp [walshCoefficient]

omit [Field K] [Fintype K] [DecidableEq K] in
/-- A sum over `Δ³` of a product of three one-variable functions factors into
the product of the three sums. -/
lemma sum_triple_prod (Delta : Finset K) (f g h : K → ℂ) :
    ∑ p ∈ Delta ×ˢ Delta ×ˢ Delta, f p.1 * g p.2.1 * h p.2.2
      = (∑ x ∈ Delta, f x) * (∑ y ∈ Delta, g y) * (∑ z ∈ Delta, h z) := by
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

omit [Fintype K] [DecidableEq K] in
/-- The additive character of the slope form factors over the triple product
into the three Walsh coefficients. -/
private lemma sum_char_slope_form (Delta : Finset K) (psi : AddChar K ℂ) (ρ a : K) :
    ∑ p ∈ Delta ×ˢ Delta ×ˢ Delta,
        psi (a * (p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2))
      = walshCoefficient Delta psi a * walshCoefficient Delta psi (ρ * a)
          * walshCoefficient Delta psi ((1 + ρ) * a) := by
  rw [show (walshCoefficient Delta psi a * walshCoefficient Delta psi (ρ * a)
      * walshCoefficient Delta psi ((1 + ρ) * a))
      = ∑ p ∈ Delta ×ˢ Delta ×ˢ Delta,
          psi (a * p.1) * psi ((ρ * a) * p.2.1) * psi (((1 + ρ) * a) * p.2.2) from
    (sum_triple_prod Delta (fun x => psi (a * x)) (fun y => psi ((ρ * a) * y))
      (fun z => psi (((1 + ρ) * a) * z))).trans rfl |>.symm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hx : a * (p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2)
      = a * p.1 + (ρ * a) * p.2.1 + ((1 + ρ) * a) * p.2.2 := by ring
  rw [hx, psi.map_add_eq_mul, psi.map_add_eq_mul]

/-- Summing over all shifts `a`: the `a = 0` term contributes `|Δ|³`, and the
nonzero shifts contribute exactly the phase triple sum. -/
private lemma sum_walsh_triple_eq_card_pow_add_phase
    (Delta : Finset K) (psi : AddChar K ℂ) (ρ : K) :
    ∑ a : K, walshCoefficient Delta psi a * walshCoefficient Delta psi (ρ * a)
        * walshCoefficient Delta psi ((1 + ρ) * a)
      = (Delta.card : ℂ) ^ 3 + Phase.phaseTripleSum (walshCoefficient Delta psi) ρ (1 + ρ) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
  congr 1
  · simp [walshCoefficient_zero]
    ring
  · simp only [Phase.phaseTripleSum]
    exact (sum_units_eq (fun a => walshCoefficient Delta psi a * walshCoefficient Delta psi (ρ * a)
      * walshCoefficient Delta psi ((1 + ρ) * a))).symm

/-- The count as a complex identity: `(|Δ|³ + Z(ρ)) / |K|`. -/
lemma slopeTripleCount_complex (Delta : Finset K) (psi : AddChar K ℂ) (hpsi : psi.IsPrimitive)
    (ρ : K) :
    (slopeTripleCount Delta ρ : ℂ)
      = ((Delta.card : ℂ) ^ 3 + Phase.phaseTripleSum (walshCoefficient Delta psi) ρ (1 + ρ))
        / (Fintype.card K : ℂ) := by
  have hQ : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 Fintype.card_ne_zero
  have step1 : (slopeTripleCount Delta ρ : ℂ)
      = ∑ p ∈ Delta ×ˢ Delta ×ˢ Delta,
          (if p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0 then (1 : ℂ) else 0) := by
    rw [slopeTripleCount, Finset.card_filter]
    push_cast
    rfl
  have step2 : ∀ p : K × K × K,
      (if p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0 then (1 : ℂ) else 0)
        = (∑ a : K, psi (a * (p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2)))
            / (Fintype.card K : ℂ) := by
    intro p
    rw [sum_char_mul psi hpsi]
    split <;> simp [hQ]
  rw [step1]
  simp_rw [step2]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  simp_rw [sum_char_slope_form Delta psi ρ]
  exact sum_walsh_triple_eq_card_pow_add_phase Delta psi ρ

/-! ### Combinatorial lemmas for the average -/

/-- `slopes K` is `K` with `0` and `1` removed, hence has `|K| - 2` elements. -/
lemma slopes_card (hK : 2 < Fintype.card K) : (slopes K).card = Fintype.card K - 2 := by
  have hset : slopes K = (Finset.univ.erase (0 : K)).erase 1 := by
    ext r
    simp only [slopes, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      true_and]
    tauto
  rw [hset, Finset.card_erase_of_mem (by simp [Finset.mem_erase, one_ne_zero]),
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ]
  omega

/-- Membership in `slopes K` is being neither `0` nor `1`. -/
lemma mem_slopes_iff (r : K) : r ∈ slopes K ↔ r ≠ 0 ∧ r ≠ 1 := by
  simp [slopes]

omit [Fintype K] [DecidableEq K] in
/-- If `y = z`, the slope equation is independent of `ρ`: it holds exactly
when `x = y`. -/
private lemma slope_eq_zero_iff_of_eq [CharP K 2] (x y ρ : K) :
    x + ρ * y + (1 + ρ) * y = 0 ↔ x = y := by
  have key : x + ρ * y + (1 + ρ) * y = x + y := by
    have h2 : ρ * y + ρ * y = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2
  rw [key, CharTwo.add_eq_zero]

omit [Fintype K] [DecidableEq K] in
/-- If `y ≠ z`, the slope equation is linear in `ρ`, with the unique solution
`(x + z) / (y + z)`. -/
private lemma slope_eq_zero_iff_of_ne [CharP K 2] {x y z : K} (hyz : y ≠ z) (ρ : K) :
    x + ρ * y + (1 + ρ) * z = 0 ↔ ρ = (x + z) / (y + z) := by
  have hyzne : y + z ≠ 0 := fun h => hyz (CharTwo.add_eq_zero.mp h)
  have hE : x + ρ * y + (1 + ρ) * z = ρ * (y + z) - (x + z) := by
    have h2 : x + x = 0 := CharTwo.add_self_eq_zero x
    have h3 : z + z = 0 := CharTwo.add_self_eq_zero z
    linear_combination h2 + h3
  rw [hE, sub_eq_zero, eq_div_iff hyzne]

/-- For `y ≠ z`, the unique slope `(x + z)/(y + z)` is admissible exactly
when `x`, `y`, and `z` are pairwise distinct. -/
private lemma div_mem_slopes_iff [CharP K 2] {x y z : K} (hyz : y ≠ z) :
    (x + z) / (y + z) ∈ slopes K ↔ (x ≠ y ∧ x ≠ z ∧ y ≠ z) := by
  have hyzne : y + z ≠ 0 := fun h => hyz (CharTwo.add_eq_zero.mp h)
  rw [mem_slopes_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun hxy => h1 ?_, fun hxz => h0 ?_, hyz⟩
    · rw [div_eq_one_iff_eq hyzne, hxy]
    · rw [div_eq_zero_iff]
      exact Or.inl (CharTwo.add_eq_zero.mpr hxz)
  · rintro ⟨hxy, hxz, -⟩
    refine ⟨div_ne_zero (fun h => hxz (CharTwo.add_eq_zero.mp h)) hyzne, ?_⟩
    intro h
    rw [div_eq_one_iff_eq hyzne] at h
    exact hxy (add_right_cancel h)

/-- For a fixed triple, the number of admissible slopes solving the equation:
`|K| - 2` on the diagonal `x = y = z`, one for a pairwise-distinct triple, and
none otherwise. -/
lemma slope_filter_card [CharP K 2] (hK : 2 < Fintype.card K) (x y z : K) :
    ((slopes K).filter (fun ρ => x + ρ * y + (1 + ρ) * z = 0)).card
      = (Fintype.card K - 2) * (if x = y ∧ y = z then 1 else 0)
        + (if x ≠ y ∧ x ≠ z ∧ y ≠ z then 1 else 0) := by
  by_cases hyz : y = z
  · subst z
    by_cases hxy : x = y
    · have hf : ((slopes K).filter (fun ρ => x + ρ * y + (1 + ρ) * y = 0)) = slopes K :=
        Finset.filter_true_of_mem (fun ρ _ => (slope_eq_zero_iff_of_eq x y ρ).mpr hxy)
      rw [hf, slopes_card hK, ite_eq_left ⟨hxy, rfl⟩, ite_eq_right (by simp [hxy])]
      ring
    · have hf : ((slopes K).filter (fun ρ => x + ρ * y + (1 + ρ) * y = 0)) = ∅ :=
        Finset.filter_false_of_mem (fun ρ _ h => hxy ((slope_eq_zero_iff_of_eq x y ρ).mp h))
      rw [hf]
      simp [hxy]
  · have hfilter : ((slopes K).filter (fun ρ => x + ρ * y + (1 + ρ) * z = 0))
        = (slopes K).filter (fun ρ => ρ = (x + z) / (y + z)) := by
      apply Finset.filter_congr
      intro ρ _
      simp [slope_eq_zero_iff_of_ne hyz ρ]
    rw [hfilter, Finset.filter_eq' (slopes K) ((x + z) / (y + z))]
    have hmem := div_mem_slopes_iff (K := K) (x := x) hyz
    have hdiag : ¬ (x = y ∧ y = z) := by rintro ⟨-, rfl⟩; exact hyz rfl
    rw [ite_eq_right hdiag]
    by_cases hd : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [ite_eq_left (hmem.mpr hd), ite_eq_left hd]
      simp
    · rw [ite_eq_right (fun h => hd (hmem.mp h)), ite_eq_right hd]
      simp

omit [Field K] [Fintype K] in
/-- The diagonal `x = y = z` of `Δ³` has `|Δ|` points. -/
lemma diag_card (Delta : Finset K) :
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.1 = p.2.1 ∧ p.2.1 = p.2.2)).card
      = Delta.card := by
  refine Finset.card_nbij' (fun p => p.1) (fun x => (x, x, x)) ?_ ?_ ?_ ?_ <;>
    simp +contextual [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Prod.ext_iff]

omit [Field K] [Fintype K] in
/-- Removing one specified element from a finite set lowers its cardinality by one. -/
private lemma card_filter_ne_one (Delta : Finset K) {x : K} (hx : x ∈ Delta) :
    (Delta.filter (fun y => x ≠ y)).card = Delta.card - 1 := by
  have hset : Delta.filter (fun y => x ≠ y) = Delta.erase x := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
    exact ⟨fun h => ⟨fun hw => h.2 hw.symm, h.1⟩, fun h => ⟨h.2, fun hw => h.1 hw.symm⟩⟩
  rw [hset, Finset.card_erase_of_mem hx]

omit [Field K] [Fintype K] in
/-- Removing two specified distinct elements of a finite set lowers its
cardinality by two. -/
lemma card_filter_ne_two (Delta : Finset K) {x y : K} (hx : x ∈ Delta) (hy : y ∈ Delta)
    (hxy : x ≠ y) : (Delta.filter (fun z => x ≠ z ∧ y ≠ z)).card = Delta.card - 2 := by
  have hset : Delta.filter (fun z => x ≠ z ∧ y ≠ z) = (Delta.erase x).erase y := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
    constructor
    · rintro ⟨hw, h1, h2⟩; exact ⟨fun h => h2 h.symm, fun h => h1 h.symm, hw⟩
    · rintro ⟨h1, h2, hw⟩; exact ⟨hw, fun h => h2 h.symm, fun h => h1 h.symm⟩
  rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨fun h => hxy h.symm, hy⟩),
    Finset.card_erase_of_mem hx]
  omega

omit [Field K] [Fintype K] in
/-- `Δ³` has `|Δ| * (|Δ| - 1) * (|Δ| - 2)` pairwise-distinct triples. -/
lemma distinct_card (Delta : Finset K) :
    ((Delta ×ˢ Delta ×ˢ Delta).filter
        (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)).card
      = Delta.card * (Delta.card - 1) * (Delta.card - 2) := by
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ x ∈ Delta,
      (∑ q ∈ Delta ×ˢ Delta, if x ≠ q.1 ∧ x ≠ q.2 ∧ q.1 ≠ q.2 then 1 else 0)
        = (Delta.card - 1) * (Delta.card - 2) := by
    intro x hx
    rw [Finset.sum_product]
    have middle : ∀ y ∈ Delta,
        (∑ z ∈ Delta, if x ≠ y ∧ x ≠ z ∧ y ≠ z then 1 else 0)
          = if x ≠ y then Delta.card - 2 else 0 := by
      intro y hy
      by_cases hxy : x = y
      · simp [hxy]
      · rw [ite_eq_left hxy]
        rw [← Finset.card_filter]
        rw [← card_filter_ne_two Delta hx hy hxy]
        congr 1
        apply Finset.filter_congr
        intro z _
        simp [hxy]
    rw [Finset.sum_congr rfl middle]
    have : ∀ y ∈ Delta, (if x ≠ y then Delta.card - 2 else 0)
        = (Delta.card - 2) * (if x ≠ y then 1 else 0) := by
      intro y _; by_cases hxy : x = y <;> simp [hxy]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Finset.card_filter,
      card_filter_ne_one Delta hx, Nat.mul_comm]
  rw [Finset.sum_congr rfl inner, Finset.sum_const, smul_eq_mul, Nat.mul_assoc]

/-- Double-counting over the admissible slopes: a diagonal triple is counted by
all `|K| - 2` slopes, a pairwise-distinct triple by exactly one, and no other
triple contributes. -/
lemma sum_tripleCount [CharP K 2] (Delta : Finset K) (hK : 2 < Fintype.card K) :
    ∑ ρ ∈ slopes K, slopeTripleCount Delta ρ
      = (Fintype.card K - 2) * Delta.card
        + Delta.card * (Delta.card - 1) * (Delta.card - 2) := by
  have h1 : ∀ ρ : K, slopeTripleCount Delta ρ
      = ∑ p ∈ Delta ×ˢ Delta ×ˢ Delta,
          (if p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0 then 1 else 0) := by
    intro ρ; rw [slopeTripleCount, Finset.card_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ p : K × K × K,
      (∑ ρ ∈ slopes K, if p.1 + ρ * p.2.1 + (1 + ρ) * p.2.2 = 0 then 1 else 0)
        = (Fintype.card K - 2) * (if p.1 = p.2.1 ∧ p.2.1 = p.2.2 then 1 else 0)
          + (if p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 then 1 else 0) := by
    intro p
    rw [← Finset.card_filter]
    exact slope_filter_card hK p.1 p.2.1 p.2.2
  simp_rw [h2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter,
    diag_card, distinct_card]

/-! ### The two generic targets -/

/-- The count formula under half-size: additive-character orthogonality turns
`2|Δ| = |K|` into `|K|²/8` plus the real part of the phase correction, at every
slope `ρ`. -/
theorem count_formula_of_half_size
    (Delta : Finset K) (psi : AddChar K ℂ) (hpsi : psi.IsPrimitive)
    (hhalf : 2 * Delta.card = Fintype.card K) :
    ∀ ρ : K,
      (slopeTripleCount Delta ρ : ℝ)
        = (Fintype.card K : ℝ) ^ 2 / 8
          + (Phase.phaseTripleSum (walshCoefficient Delta psi) ρ (1 + ρ)).re /
            (Fintype.card K : ℝ) := by
  intro ρ
  have hMpos : 0 < Delta.card := by
    have hK : 0 < Fintype.card K := Fintype.card_pos
    omega
  have hQC : (Fintype.card K : ℂ) = 2 * (Delta.card : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) hhalf.symm
  have hMne : (Delta.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcube : ((Delta.card : ℂ) ^ 3) / (Fintype.card K : ℂ)
      = (((Fintype.card K : ℝ) ^ 2 / 8 : ℝ) : ℂ) := by
    have : (((Fintype.card K : ℝ) ^ 2 / 8 : ℝ) : ℂ) = (Fintype.card K : ℂ) ^ 2 / 8 := by
      push_cast; ring
    rw [this, hQC]
    field_simp
    ring
  have h2 : (slopeTripleCount Delta ρ : ℂ)
      = (((Fintype.card K : ℝ) ^ 2 / 8 : ℝ) : ℂ)
        + Phase.phaseTripleSum (walshCoefficient Delta psi) ρ (1 + ρ) / (Fintype.card K : ℂ) := by
    rw [slopeTripleCount_complex Delta psi hpsi ρ, add_div, hcube]
  have h3 := congrArg Complex.re h2
  rw [Complex.add_re, Complex.ofReal_re, Complex.div_natCast_re, Complex.natCast_re] at h3
  exact h3

/-- Under half-size the admissible-slope average of the triple count is exactly
`|K|²/8`, by double-counting `(ρ,x,y,z)`.  The assumption `2 < |K|` only makes
the average's denominator nonzero; in the final Kasami theorem `|K| = 2^n` with
`n ≥ 2`. -/
theorem average_of_half_size [CharP K 2]
    (Delta : Finset K) (hhalf : 2 * Delta.card = Fintype.card K)
    (hK : 2 < Fintype.card K) :
    (∑ ρ ∈ slopes K, (slopeTripleCount Delta ρ : ℝ)) / ((slopes K).card : ℝ)
      = (Fintype.card K : ℝ) ^ 2 / 8 := by
  have hM2 : 2 ≤ Delta.card := by omega
  have hQ2 : 2 ≤ Fintype.card K := by omega
  have hsum : (∑ ρ ∈ slopes K, (slopeTripleCount Delta ρ : ℝ))
      = ((Fintype.card K : ℝ) - 2) * (Delta.card : ℝ)
        + (Delta.card : ℝ) * ((Delta.card : ℝ) - 1) * ((Delta.card : ℝ) - 2) := by
    have := sum_tripleCount Delta hK
    have hcast : ((∑ ρ ∈ slopes K, slopeTripleCount Delta ρ : ℕ) : ℝ)
        = ∑ ρ ∈ slopes K, (slopeTripleCount Delta ρ : ℝ) := by push_cast; ring
    rw [← hcast, this]
    push_cast [Nat.cast_sub hQ2, Nat.cast_sub hM2, Nat.cast_sub (le_trans one_le_two hM2)]
    ring
  rw [hsum, slopes_card hK]
  have hMR : (Fintype.card K : ℝ) = 2 * (Delta.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hhalf.symm
  have hden : ((Fintype.card K - 2 : ℕ) : ℝ) = (Fintype.card K : ℝ) - 2 :=
    Nat.cast_sub hQ2
  rw [hden, hMR]
  have hM1 : (Delta.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Delta.card : ℝ) := by exact_mod_cast hM2
    intro h; nlinarith
  field_simp
  ring

end CountAverage

/-! ### Specialization to `derivativeImage k K` -/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The Walsh triple-count formula follows from the derivative-image half-size
equation alone.  `AdmissibleSlope` is retained here because this theorem is the
downstream slope-interface, although the generic identity holds for every `ρ`. -/
theorem walshTripleCountFormula_of_half_size {k : ℕ}
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) :
    ∀ ρ : K, AdmissibleSlope ρ →
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8
        + (Phase.phaseTripleSum (walshCoefficient k (primitiveAddChar K)) ρ (1 + ρ)).re /
            (Fintype.card K : ℝ) := by
  intro ρ _
  exact CountAverage.count_formula_of_half_size (derivativeImage k K) (primitiveAddChar K)
    primitiveAddChar_isPrimitive hhalf ρ

/-- The slope-average formula follows from the derivative-image half-size
equation (and `|K| > 2`) alone. -/
theorem slopeAverageFormula_of_half_size [CharP K 2] {k : ℕ}
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) (hK : 2 < Fintype.card K) :
    (∑ ρ ∈ slopes K, (slopeTripleCount k ρ : ℝ)) / ((slopes K).card : ℝ)
      = (Fintype.card K : ℝ) ^ 2 / 8 :=
  CountAverage.average_of_half_size (derivativeImage k K) hhalf hK

end KasamiCyclicAdditive
