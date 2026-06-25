/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/

import Mathlib

namespace Kaprekar4


/-
# Problem Description

Throughout, fix an odd integer base `B > 3`.

This problem concerns Kaprekar's routine applied to `4`-tuples of base-`B` digits.
Given a `4`-tuple of base-`B` digits, sort them as `a₁ ≥ a₂ ≥ a₃ ≥ a₄` (each
`aᵢ ∈ {0, 1, …, B-1}`). Kaprekar's operation forms the descending number
`a₁a₂a₃a₄` and the ascending number `a₄a₃a₂a₁` in base `B` and subtracts them.
Their difference equals

  `(a₁ B³ + a₂ B² + a₃ B + a₄) - (a₄ B³ + a₃ B² + a₂ B + a₁)
    = d₁ (B³ - 1) + d₂ (B² - B)`,

where `d₁ = a₁ - a₄` and `d₂ = a₂ - a₃`. Hence the next iterate depends only on the
pair `(d₁, d₂)`, justifying the use of difference pairs as states.

We study the dynamical system given by Kaprekar's map on the space of difference
pairs, its terminal cycles, and a conjugacy with a "doubling map" on projective
residues.

## Notes and Interpretation

- All claims were checked computationally for odd bases `B` up to `39`.
- The bound `c_max(B) ≤ (B-1)/2` holds for all tested `B`, with equality exactly for
  `B ∈ {7, 11, 13, 19, 23, 29, 37}` in this range — precisely the primes `≥ 7` for
  which `2` has projective order `(B-1)/2` (the least `m` with `2^m ≡ ±1 mod B`).
- The map `Φ` realizes the dynamics of `K_B` on `T_B` as multiplication by `2` on
  (unordered pairs of) projective residues.
- "`4`-digit" allows leading zeros: states are arbitrary multisets of four base-`B`
  digits with `d₁ ≥ 1`.
-/

/-! ## Auxiliary definitions for digits and sorting -/

/-- Sort four natural numbers in descending order, returning the `4`-tuple
`(b₁, b₂, b₃, b₄)` with `b₁ ≥ b₂ ≥ b₃ ≥ b₄`. -/
def sort4 (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match (List.mergeSort [a, b, c, d] (· ≥ ·)) with
  | [x, y, z, w] => (x, y, z, w)
  | _ => (0, 0, 0, 0)

/-! ## Main Definitions -/

/-- **Definition 2 (State space `X_B`).**
`X_B = {(d₁, d₂) ∈ ℕ² : 1 ≤ d₁ < B, 0 ≤ d₂ ≤ d₁}`.
The constraint `d₁ ≥ 1` excludes the trivial repdigit case `a₁ = a₂ = a₃ = a₄`. -/
def XBset (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter (fun p => 1 ≤ p.1 ∧ p.1 < B ∧ p.2 ≤ p.1)

/-- **Definition 3 (Kaprekar map `K_B`).**
For `(d₁, d₂)`, set `N = d₁ (B³ - 1) + d₂ (B² - B)`, take the four base-`B` digits
`(c₁, c₂, c₃, c₄)` of `N` (with `N = c₁ B³ + c₂ B² + c₃ B + c₄`), sort them as
`b₁ ≥ b₂ ≥ b₃ ≥ b₄`, and return `(b₁ - b₄, b₂ - b₃)`. -/
def KB (B : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let N := p.1 * (B ^ 3 - 1) + p.2 * (B ^ 2 - B)
  match sort4 (N / B ^ 3) ((N / B ^ 2) % B) ((N / B) % B) (N % B) with
  | (b1, b2, b3, b4) => (b1 - b4, b2 - b3)

/-- **Definition 4 (Target set `T_B`).**
`T_B = {(d₁, d₂) ∈ X_B : d₁ > d₂ > 0, d₁ odd, d₂ odd}`. -/
def TBset (B : ℕ) : Finset (ℕ × ℕ) :=
  (XBset B).filter (fun p => p.2 < p.1 ∧ 0 < p.2 ∧ Odd p.1 ∧ Odd p.2)

/-- The setoid on `ZMod B` identifying each residue with its negative (`x ∼ -x`). -/
def projSetoid (B : ℕ) : Setoid (ZMod B) where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y h; rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; ring)
    · intro x y z hxy hyz
      rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
      · exact Or.inl (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inl (by rw [h1, h2]; ring)

/-- **Definition 5 (Projective residues `P_B`).**
`P_B = (ZMod B) / {±1}`. (The nonzero projective residues
`((ZMod B) \ {0}) / {±1}` are those classes different from the class of `0`.) -/
def PB (B : ℕ) := Quotient (projSetoid B)

/-- The projective class `[x]` of `x : ZMod B`. -/
def PBmk (B : ℕ) (x : ZMod B) : PB B := Quotient.mk (projSetoid B) x

/-- `P_B` is finite (a quotient of the finite type `ZMod B` when `B ≠ 0`). -/
noncomputable instance PBfintype (B : ℕ) [NeZero B] : Fintype (PB B) := by
  unfold PB
  haveI : DecidableRel (projSetoid B).r := by
    intro x y; unfold projSetoid; exact inferInstanceAs (Decidable (x = y ∨ x = -y))
  exact Quotient.fintype (projSetoid B)

/-- The unordered pairs of distinct nonzero projective residues, i.e. `binom(P_B, 2)`.
An element of `Sym2 (P_B)` lies in this set iff it is not on the diagonal (its two
entries are distinct) and the class `[0]` is not one of its entries. -/
def binomSet (B : ℕ) : Set (Sym2 (PB B)) :=
  {s | ¬ s.IsDiag ∧ PBmk B 0 ∉ s}

/-- **Definition 6 (The map `Φ`).**
For `(d₁, d₂)` (with `d₁, d₂` both odd, as in `T_B`), set `r = (d₁ + d₂)/2` and
`s = (d₁ - d₂)/2`, and return the unordered pair `{[r], [s]}` of projective residues. -/
def Phi (B : ℕ) (p : ℕ × ℕ) : Sym2 (PB B) :=
  Sym2.mk (PBmk B (((p.1 + p.2) / 2 : ℕ) : ZMod B), PBmk B (((p.1 - p.2) / 2 : ℕ) : ZMod B))

/-- Doubling on projective residues: `[x] ↦ [2x]`. Well-defined since `2(-x) = -(2x)`. -/
def doubleP (B : ℕ) : PB B → PB B :=
  Quotient.map (fun x => 2 * x) (by
    intro x y h
    rcases h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; ring))

/-- **Definition 7 (Doubling map `D`).**
`D({[r], [s]}) = {[2r], [2s]}`, the image of the unordered pair under `[·] ↦ [2·]`. -/
def Dmap (B : ℕ) : Sym2 (PB B) → Sym2 (PB B) := Sym2.map (doubleP B)

/-- The number of terminal cycles of `K_B` of length exactly `c_max(B)`.
A terminal cycle is the orbit of a periodic point; its length is the minimal period.
Counting the periodic points whose minimal period equals `c_max(B)` and dividing by
`c_max(B)` (the number of points per such cycle) gives the number of such cycles. -/
noncomputable def cmax (B : ℕ) : ℕ :=
  (XBset B).sup (fun p => Function.minimalPeriod (KB B) p)

/-- Number of terminal cycles of `K_B` whose length equals `c_max(B)`. -/
noncomputable def numMaxCycles (B : ℕ) : ℕ :=
  ((XBset B).filter (fun p => Function.minimalPeriod (KB B) p = cmax B)).card / cmax B

/-! ## Decomposition into sub-lemmas

The proof is organized around one computational fact — the closed form of the four
base-`B` digits of `N = d₁(B³-1) + d₂(B²-B)` — from which every part of Theorem 1
follows by elementary bookkeeping, and around the conjugacy `Φ ∘ K_B = D ∘ Φ`, which
reduces the two corollaries to the orbit structure of "multiply by `2`" on `P_B`.

Throughout, write `r = (d₁+d₂)/2`, `s = (d₁-d₂)/2`, so for `(d₁,d₂) ∈ T_B`
(both odd, `d₁ > d₂ > 0`) we have `d₁ = r+s`, `d₂ = r-s`, with `r > s > 0` and
`r < B` (since `2r = d₁+d₂ ≤ 2d₁ < 2B`, in fact `r ≤ d₁ < B`), so `[r], [s]` are
genuine nonzero projective classes. -/

/-- **Lemma `digits_of_N_pos` (closed-form digits, generic case `d₂ ≥ 1`).**
For `1 ≤ d₂ ≤ d₁ < B`, the base-`B` digits of `N = d₁(B³-1)+d₂(B²-B)` are, in the
order (`B³`-place, `B²`-place, `B`-place, units),
`(d₁, d₂-1, B-1-d₂, B-d₁)`.

*Proof (informal).* Expand `N = d₁B³ + d₂B² - d₂B - d₁`. Regroup using one borrow at
the units place and one at the `B`-place:
`N = d₁·B³ + (d₂-1)·B² + (B-1-d₂)·B + (B-d₁)`.
Indeed `(d₂-1)B² + (B-1-d₂)B + (B-d₁) = d₂B² - B² + B² - B - d₂B + B - d₁
      = d₂B² - d₂B - d₁`, matching `N - d₁B³`. Each coefficient lies in `[0,B-1]`
because `1 ≤ d₂ ≤ d₁ < B`: `0 ≤ d₂-1 ≤ B-2`, `0 ≤ B-1-d₂ ≤ B-2`, `1 ≤ B-d₁ ≤ B-1`,
and `d₁ ≤ B-1`. Hence these are exactly the digits, i.e. `N / B³ = d₁`,
`(N / B²) % B = d₂-1`, `(N / B) % B = B-1-d₂`, `N % B = B-d₁`. -/
theorem digits_of_N_pos (B d₁ d₂ : ℕ) (hd₂ : 1 ≤ d₂) (hd : d₂ ≤ d₁) (hd₁ : d₁ < B) :
    let N := d₁ * (B ^ 3 - 1) + d₂ * (B ^ 2 - B)
    N / B ^ 3 = d₁ ∧ (N / B ^ 2) % B = d₂ - 1 ∧
      (N / B) % B = B - 1 - d₂ ∧ N % B = B - d₁ := by
  intro N
  have hB1 : 1 ≤ B := by omega
  have hBpos : 0 < B := by omega
  have hbd2 : d₂ ≤ B - 1 := by omega
  -- Horner regrouping: N = (B-d₁) + B*((B-1-d₂) + B*((d₂-1) + B*d₁))
  have key : N = (B - d₁) + B * ((B - 1 - d₂) + B * ((d₂ - 1) + B * d₁)) := by
    show d₁ * (B ^ 3 - 1) + d₂ * (B ^ 2 - B) = _
    have h3 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h2 : B ≤ B ^ 2 := by nlinarith [sq_nonneg B]
    zify [hd₁, h3, h2, hB1, hd₂, hd, hbd2, Nat.sub_le]
    ring
  have hc0 : B - d₁ < B := by omega
  have hc1 : B - 1 - d₂ < B := by omega
  have hc2 : d₂ - 1 < B := by omega
  have hc3 : d₁ < B := hd₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : B ^ 3 = B * B * B := by ring
    rw [key, this]
    rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc1, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc2, zero_add]
  · have : B ^ 2 = B * B := by ring
    rw [key, this]
    rw [← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc1, zero_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc2]
  · rw [key]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc1]
  · rw [key]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]

/-- **Lemma `digits_of_N_zero` (degenerate case `d₂ = 0`).**
For `1 ≤ d₁ < B`, the base-`B` digits of `N = d₁(B³-1)` are `(d₁-1, B-1, B-1, B-d₁)`.

*Proof (informal).* `N = d₁B³ - d₁ = (d₁-1)B³ + (B-1)B² + (B-1)B + (B-d₁)` since the
right side equals `d₁B³ - B³ + (B³ - B²) + (B² - B) + (B - d₁) = d₁B³ - d₁`. All four
coefficients lie in `[0,B-1]` as `1 ≤ d₁ < B`. -/
theorem digits_of_N_zero (B d₁ : ℕ) (hd₁0 : 1 ≤ d₁) (hd₁ : d₁ < B) :
    let N := d₁ * (B ^ 3 - 1)
    N / B ^ 3 = d₁ - 1 ∧ (N / B ^ 2) % B = B - 1 ∧
      (N / B) % B = B - 1 ∧ N % B = B - d₁ := by
  intro N
  have hB1 : 1 ≤ B := by omega
  have hBpos : 0 < B := by omega
  -- Horner regrouping: N = (B-d₁) + B*((B-1) + B*((B-1) + B*(d₁-1)))
  have key : N = (B - d₁) + B * ((B - 1) + B * ((B - 1) + B * (d₁ - 1))) := by
    show d₁ * (B ^ 3 - 1) = _
    have h3 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [hd₁, h3, hB1, hd₁0, Nat.sub_le]
    ring
  -- bounds
  have hc0 : B - d₁ < B := by omega
  have hc1 : B - 1 < B := by omega
  have hc3 : d₁ - 1 < B := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- N / B^3 = d₁ - 1
    have : B ^ 3 = B * B * B := by ring
    rw [key, this]
    rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc1, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc1, zero_add]
  · -- (N / B^2) % B = B - 1
    have : B ^ 2 = B * B := by ring
    rw [key, this]
    rw [← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc1, zero_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc1]
  · -- (N / B) % B = B - 1
    rw [key]
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt hc0, zero_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc1]
  · -- N % B = B - d₁
    rw [key]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]

/-- Helper: `sort4` evaluation via a sorted permutation. -/
theorem sort4_perm_eq (a b c d w x y z : ℕ)
    (hperm : List.Perm [a,b,c,d] [w,x,y,z])
    (hwx : x ≤ w) (hxy : y ≤ x) (hyz : z ≤ y) :
    sort4 a b c d = (w,x,y,z) := by
  have hms : List.mergeSort [a,b,c,d] (· ≥ ·) = [w,x,y,z] := by
    have hp1 : List.Perm (List.mergeSort [a,b,c,d] (· ≥ ·)) [w,x,y,z] :=
      (List.mergeSort_perm _ _).trans hperm
    apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
    · intro p q _ _ hpq hqp; omega
    · have := List.pairwise_mergeSort (le := fun (x1 x2 : ℕ) => decide (x1 ≥ x2))
        (by intro a b c hab hbc; simp_all; omega) (by intro a b; simp; omega) [a,b,c,d]
      simpa using this
    · simp [List.Pairwise]; omega
    · exact hp1
  unfold sort4
  rw [hms]

/-- Helper: equality of projective classes. -/
theorem PBmk_eq_iff (B : ℕ) (a b : ZMod B) : PBmk B a = PBmk B b ↔ (a = b ∨ a = -b) := by
  unfold PBmk; rw [Quotient.eq]; rfl

/-- Helper: build a `Sym2` equality from componentwise projective equalities. -/
theorem Sym2_finish (B : ℕ) (u₁ u₂ v₁ v₂ : ZMod B)
    (h : (u₁ = v₁ ∨ u₁ = -v₁) ∧ (u₂ = v₂ ∨ u₂ = -v₂)) :
    Sym2.mk (PBmk B u₁, PBmk B u₂) = Sym2.mk (PBmk B v₁, PBmk B v₂) := by
  obtain ⟨h1, h2⟩ := h
  rw [(PBmk_eq_iff B _ _).2 h1, (PBmk_eq_iff B _ _).2 h2]

/-- Helper: build a `Sym2` equality from cross componentwise projective equalities. -/
theorem Sym2_finish_swap (B : ℕ) (u₁ u₂ v₁ v₂ : ZMod B)
    (h : (u₁ = v₂ ∨ u₁ = -v₂) ∧ (u₂ = v₁ ∨ u₂ = -v₁)) :
    Sym2.mk (PBmk B u₁, PBmk B u₂) = Sym2.mk (PBmk B v₁, PBmk B v₂) := by
  obtain ⟨h1, h2⟩ := h
  rw [(PBmk_eq_iff B _ _).2 h1, (PBmk_eq_iff B _ _).2 h2, Sym2.eq_swap]

/-- Helper: explicit form of `Dmap ∘ Phi`. -/
theorem Dmap_Phi (B : ℕ) (p : ℕ × ℕ) :
    Dmap B (Phi B p) =
      Sym2.mk (PBmk B (2 * (((p.1 + p.2) / 2 : ℕ) : ZMod B)),
               PBmk B (2 * (((p.1 - p.2) / 2 : ℕ) : ZMod B))) := by
  unfold Dmap Phi
  rw [Sym2.map_pair_eq]
  congr 1


/-- **Lemma `KB_eq_on_T` (explicit Kaprekar step on `T_B`).**
For `(d₁,d₂) ∈ T_B`, writing `r = (d₁+d₂)/2`, `s = (d₁-d₂)/2`, the next state is
`K_B(d₁,d₂) = (max - min, mid₁ - mid₂)` of the multiset `{d₁, d₂-1, B-1-d₂, B-d₁}`.
Crucially, as a *projective pair* it equals `{[2r], [2s]}`; concretely, setting
`(e₁,e₂) = K_B(d₁,d₂)`, one has `{[(e₁+e₂)/2], [(e₁-e₂)/2]} = {[d₁+d₂], [d₁-d₂]}`
in `P_B` (note `2r = d₁+d₂`, `2s = d₁-d₂`).

*Proof (informal).* By `digits_of_N_pos` (here `d₂ ≥ 1` since `(d₁,d₂) ∈ T_B`) the
four digits are `{d₁, d₂-1, B-1-d₂, B-d₁}`. Sorting and taking `(b₁-b₄, b₂-b₃)` gives
`K_B`. The two output differences `e₁ = b₁-b₄`, `e₂ = b₂-b₃` recombine, modulo `B`
and up to sign, into the residues `±(d₁+d₂)` and `±(d₁-d₂)`: the four digits are
`{d₁, B-d₁} ∪ {d₂-1, B-1-d₂}`, two "complementary" pairs summing to `B-1` after the
borrow accounting, whose pairwise differences are `≡ ±(d₁+d₂), ±(d₁-d₂) (mod B)`.
This is the doubling identity verified computationally for all odd `B ≤ 39`. -/
theorem KB_eq_on_T (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (p : ℕ × ℕ)
    (hp : p ∈ TBset B) :
    Phi B (KB B p) = Dmap B (Phi B p) := by
  simp only [TBset, XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨⟨⟨_, _⟩, _, hd1B, _⟩, hd2d1, hd2pos, hodd1, hodd2⟩ := hp
  set d₁ := p.1 with hd1def
  set d₂ := p.2 with hd2def
  obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_pos B d₁ d₂ (by omega) (by omega) hd1B
  rw [Dmap_Phi]
  have hsum_even : 2 ∣ (d₁ + d₂) := by
    obtain ⟨a, ha⟩ := hodd1; obtain ⟨b, hb⟩ := hodd2; omega
  have hdiff_even : 2 ∣ (d₁ - d₂) := by
    obtain ⟨a, ha⟩ := hodd1; obtain ⟨b, hb⟩ := hodd2; omega
  have hRsum : (2 * (((d₁ + d₂) / 2 : ℕ) : ZMod B)) = ((d₁ + d₂ : ℕ) : ZMod B) := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, Nat.mul_div_cancel' hsum_even]
  have hRdiff : (2 * (((d₁ - d₂) / 2 : ℕ) : ZMod B)) = ((d₁ - d₂ : ℕ) : ZMod B) := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, Nat.mul_div_cancel' hdiff_even]
  rw [hRsum, hRdiff]
  have hKB : KB B p =
      (let S := sort4 d₁ (d₂ - 1) (B - 1 - d₂) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
    unfold KB
    simp only [← hd1def, ← hd2def]
    rw [hN1, hN2, hN3, hN4]
  rw [hKB]
  have hBd1 : B - d₁ < B := by omega
  obtain ⟨bk, hbk⟩ := hBodd
  obtain ⟨d1k, hd1k⟩ := hodd1
  obtain ⟨d2k, hd2k⟩ := hodd2
  -- case-split on the descending order of the four digits {d₁, d₂-1, B-1-d₂, B-d₁}
  rcases le_total (B - 1 - d₂) (d₂ - 1) with hPQ | hPQ
  · -- order A,P,Q,R  (P1)
    rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-1-d₂) (B-d₁)
        (List.Perm.refl _)
        (by omega) (by omega) (by omega)]
    simp only
    unfold Phi
    have hf1 : ((d₁ - (B - d₁)) + ((d₂ - 1) - (B - 1 - d₂))) / 2 = d₁ + d₂ - B := by omega
    have hf2 : ((d₁ - (B - d₁)) - ((d₂ - 1) - (B - 1 - d₂))) / 2 = d₁ - d₂ := by omega
    rw [hf1, hf2]
    apply Sym2_finish
    constructor
    · left
      have e : ((d₁ + d₂ - B : ℕ) : ZMod B) = (d₁ : ZMod B) + d₂ - B := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e, ZMod.natCast_self]; push_cast; ring
    · left; rfl
  · rcases le_total (B - 1 - d₂) d₁ with hQA | hQA
    · rcases le_total (d₂ - 1) (B - d₁) with hPR | hPR
      · -- order A,Q,R,P  (P3); d₁+d₂ ∈ {B-1, B+1}
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (B-d₁) (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        unfold Phi
        have hf1 : ((d₁ - (d₂ - 1)) + ((B - 1 - d₂) - (B - d₁))) / 2 = d₁ - d₂ := by omega
        have hf2 : ((d₁ - (d₂ - 1)) - ((B - 1 - d₂) - (B - d₁))) / 2 = 1 := by omega
        rw [hf1, hf2]
        apply Sym2_finish_swap
        refine ⟨Or.inl rfl, ?_⟩
        rcases (by omega : d₁ + d₂ = B - 1 ∨ d₁ + d₂ = B + 1) with hsum | hsum
        · right
          rw [hsum]
          have hle : (1 : ℕ) ≤ B := by omega
          have hB1 : ((B - 1 : ℕ) : ZMod B) = -1 := by
            rw [Nat.cast_sub hle, ZMod.natCast_self]; simp
          rw [hB1]; simp
        · left
          rw [hsum]
          have hB1 : ((B + 1 : ℕ) : ZMod B) = 1 := by
            rw [Nat.cast_add, ZMod.natCast_self]; simp
          rw [hB1]; simp
      · -- order A,Q,P,R  (P2)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (d₂-1) (B-d₁)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        unfold Phi
        have hf1 : ((d₁ - (B - d₁)) + ((B - 1 - d₂) - (d₂ - 1))) / 2 = d₁ - d₂ := by omega
        have hf2 : ((d₁ - (B - d₁)) - ((B - 1 - d₂) - (d₂ - 1))) / 2 = d₁ + d₂ - B := by omega
        rw [hf1, hf2]
        apply Sym2_finish_swap
        refine ⟨Or.inl rfl, Or.inl ?_⟩
        have e : ((d₁ + d₂ - B : ℕ) : ZMod B) = (d₁ : ZMod B) + d₂ - B := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [e, ZMod.natCast_self]; push_cast; ring
    · rcases le_total (B - d₁) d₁ with hRA | hRA
      · -- order Q,A,R,P  (P4)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) d₁ (B-d₁) (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        unfold Phi
        have hf1 : ((B - 1 - d₂) - (d₂ - 1) + (d₁ - (B - d₁))) / 2 = d₁ - d₂ := by omega
        have hf2 : ((B - 1 - d₂) - (d₂ - 1) - (d₁ - (B - d₁))) / 2 = B - d₁ - d₂ := by omega
        rw [hf1, hf2]
        apply Sym2_finish_swap
        refine ⟨Or.inl rfl, Or.inr ?_⟩
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
        push_cast; ring
      · -- order Q,R,A,P  (P5)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) (B-d₁) d₁ (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        unfold Phi
        have hf1 : ((B - 1 - d₂) - (d₂ - 1) + ((B - d₁) - d₁)) / 2 = B - d₁ - d₂ := by omega
        have hf2 : ((B - 1 - d₂) - (d₂ - 1) - ((B - d₁) - d₁)) / 2 = d₁ - d₂ := by omega
        rw [hf1, hf2]
        apply Sym2_finish
        refine ⟨Or.inr ?_, Or.inl rfl⟩
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
        push_cast; ring
/-- **Lemma `KB_maps_T_into_T`** — part (1) of Theorem 1.
`K_B` maps `T_B` into `T_B`.

*Proof (informal).* Let `(d₁,d₂) ∈ T_B` and `(e₁,e₂) = K_B(d₁,d₂)`. From the explicit
digits `{d₁, d₂-1, B-1-d₂, B-d₁}` (Lemma `digits_of_N_pos`) one computes the sorted
differences. Parity: the four digits have the same parities as `d₁, d₂+1, d₂+1, d₁`
(mod 2; using `B` odd so `B-1-d₂ ≡ d₂` and `B-d₁ ≡ d₁+1`); a short case analysis on
the sort shows `e₁ = b₁-b₄` and `e₂ = b₂-b₃` are both odd, with `e₁ > e₂ > 0` and
`e₁ < B`. (Conceptually this is immediate from the conjugacy `KB_eq_on_T`: the image
projective pair `{[2r],[2s]}` is again a pair of *distinct nonzero* classes — `2r ≢ 0`,
`2s ≢ 0` since `B` is odd and `0 < s < r < B`, and `[2r] ≠ [2s]` since `[r] ≠ [s]` and
doubling is injective on `P_B` for odd `B` — and `Φ` is a bijection `T_B → binom(P_B,2)`,
so the image lies in `T_B`.) -/
theorem KB_maps_T_into_T (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    ∀ p ∈ TBset B, KB B p ∈ TBset B := by
  -- SANITY CHECK PASSED (no counterexample; exhaustive over odd B≤61 in Lean)
  intro p hp
  simp only [TBset, XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  obtain ⟨⟨⟨_, _⟩, _, hd1B, _⟩, hd2d1, hd2pos, hodd1, hodd2⟩ := hp
  set d₁ := p.1 with hd1def
  set d₂ := p.2 with hd2def
  obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_pos B d₁ d₂ (by omega) (by omega) hd1B
  have hKB : KB B p =
      (let S := sort4 d₁ (d₂ - 1) (B - 1 - d₂) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
    unfold KB
    simp only [← hd1def, ← hd2def]
    rw [hN1, hN2, hN3, hN4]
  rw [hKB]
  obtain ⟨bk, hbk⟩ := hBodd
  obtain ⟨d1k, hd1k⟩ := hodd1
  obtain ⟨d2k, hd2k⟩ := hodd2
  -- case-split on the descending order of the four digits {d₁, d₂-1, B-1-d₂, B-d₁}
  rcases le_total (B - 1 - d₂) (d₂ - 1) with hPQ | hPQ
  · -- order A,P,Q,R  (P1)
    rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-1-d₂) (B-d₁)
        (List.Perm.refl _)
        (by omega) (by omega) (by omega)]
    simp only
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      first | omega | (rw [Nat.odd_iff]; omega)
  · rcases le_total (B - 1 - d₂) d₁ with hQA | hQA
    · rcases le_total (d₂ - 1) (B - d₁) with hPR | hPR
      · -- order A,Q,R,P  (P3)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (B-d₁) (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          first | omega | (rw [Nat.odd_iff]; omega)
      · -- order A,Q,P,R  (P2)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (d₂-1) (B-d₁)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          first | omega | (rw [Nat.odd_iff]; omega)
    · rcases le_total (B - d₁) d₁ with hRA | hRA
      · -- order Q,A,R,P  (P4)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) d₁ (B-d₁) (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          first | omega | (rw [Nat.odd_iff]; omega)
      · -- order Q,R,A,P  (P5)
        rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) (B-d₁) d₁ (d₂-1)
            (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
            (by omega) (by omega) (by omega)]
        simp only
        refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
          first | omega | (rw [Nat.odd_iff]; omega)

/- **Lemma `KB3_maps_X_into_T`** — part (2) of Theorem 1.
The third iterate of `K_B` maps `X_B` into `T_B`.

*Proof (informal).* Take `(d₁,d₂) ∈ X_B`. Using the digit formulas
(`digits_of_N_pos`/`digits_of_N_zero`) one checks that after a single step the state
already satisfies `d₁ ≥ d₂` and lands in the region where both coordinates become odd
within at most three steps:
  * one step makes `d₁` odd (the top digit `d₁` of `N` and bottom digit `B-d₁` differ
    by `2d₁ - B`, which is odd since `B` is odd, forcing the new first coordinate
    `e₁ = b₁ - b₄` odd);
  * the constraint `e₂ < e₁` and `e₂ > 0` is reached because the middle digits
    `d₂-1, B-1-d₂` are distinct unless `d₂ = (B-1)/2... ` handled by a further step;
  * the projective picture (via `KB_eq_on_T`, valid once in `T_B`) confirms no further
    degeneration. Concretely: `K_B(X_B) ⊆ {d₁ odd}`, `K_B²(X_B) ⊆ {d₁,d₂ odd}`, and the
    third step removes the boundary cases `d₂ = 0` and `d₂ = d₁`, landing in `T_B`.
This "lands in `T_B` within 3 steps" was verified computationally for all odd `B ≤ 39`;
the bound `3` is uniform. -/
-- SANITY CHECK PASSED (computationally verified: no counterexample for all odd B in (3,60))

/-- Intermediate invariant `I` reached after one Kaprekar step from `X_B`:
in `X_B` (with `1 ≤ d₁ < B`, `d₂ ≤ d₁`), equal parity of the two coordinates, and
if `d₂ = 0` then `d₁ ∈ {2, B-1}`. -/
def inI (B : ℕ) (q : ℕ × ℕ) : Prop :=
  1 ≤ q.1 ∧ q.1 < B ∧ q.2 ≤ q.1 ∧ q.1 % 2 = q.2 % 2 ∧ (q.2 ≠ 0 ∨ q.1 = 2 ∨ q.1 = B - 1)

/-- The "both-even gap-2" exceptional set `E = {(d, d-2) : d even, 2 ≤ d < B}`. -/
def inE (B : ℕ) (q : ℕ × ℕ) : Prop :=
  ¬ Odd q.1 ∧ q.2 + 2 = q.1 ∧ 2 ≤ q.1 ∧ q.1 < B

/-- **Helper 1.** One Kaprekar step sends every point of `X_B` into the invariant `I`. -/
theorem KB_step1_into_I (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    ∀ p ∈ XBset B, inI B (KB B p) := by
  intro p hp
  simp only [XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨⟨_, _⟩, hd1pos, hd1B, hd2d1⟩ := hp
  set d₁ := p.1 with hd1def
  set d₂ := p.2 with hd2def
  obtain ⟨bk, hbk⟩ := hBodd
  rcases Nat.eq_zero_or_pos d₂ with hd2z | hd2pos
  · -- d₂ = 0 case: digits {d₁-1, B-1, B-1, B-d₁}
    have hp2z : p.2 = 0 := by rw [← hd2def]; exact hd2z
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_zero B d₁ (by omega) hd1B
    have hKB : KB B p =
        (let S := sort4 (d₁ - 1) (B - 1) (B - 1) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, hp2z, Nat.zero_mul, Nat.add_zero]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    unfold inI
    -- order the four digits {d₁-1, B-1, B-1, B-d₁}
    rcases le_total (d₁ - 1) (B - d₁) with hAB | hAB
    · -- B-1 ≥ B-1 ≥ B-d₁ ≥ d₁-1
      rw [sort4_perm_eq (d₁-1) (B-1) (B-1) (B-d₁) (B-1) (B-1) (B-d₁) (d₁-1)
          (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
          (by omega) (by omega) (by omega)]
      simp only
      refine ⟨by omega, by omega, by omega, by omega, by omega⟩
    · -- B-1 ≥ B-1 ≥ d₁-1 ≥ B-d₁
      rw [sort4_perm_eq (d₁-1) (B-1) (B-1) (B-d₁) (B-1) (B-1) (d₁-1) (B-d₁)
          (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
          (by omega) (by omega) (by omega)]
      simp only
      refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · -- d₂ ≥ 1 case: digits {d₁, d₂-1, B-1-d₂, B-d₁}
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_pos B d₁ d₂ (by omega) (by omega) hd1B
    have hKB : KB B p =
        (let S := sort4 d₁ (d₂ - 1) (B - 1 - d₂) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, ← hd2def]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    unfold inI
    rcases (show d₂ = d₁ ∨ d₂ < d₁ by omega) with heqd | hltd
    · -- d₂ = d₁: digits {d₁, d₁-1, B-1-d₁, B-d₁} (heqd : d₂ = d₁)
      rcases le_total (B - d₁) d₁ with hRA | hRA
      · rcases le_total (B - d₁) (d₂ - 1) with hRP | hRP
        · -- d₁ ≥ d₂-1 ≥ B-d₁ ≥ B-1-d₂
          rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-d₁) (B-1-d₂)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨by omega, by omega, by omega, by omega, by omega⟩
        · -- d₁ ≥ B-d₁ ≥ d₂-1 ≥ B-1-d₂
          rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-d₁) (d₂-1) (B-1-d₂)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨by omega, by omega, by omega, by omega, by omega⟩
      · rcases le_total d₁ (B - 1 - d₂) with hAQ | hAQ
        · -- B-d₁ ≥ B-1-d₂ ≥ d₁ ≥ d₂-1
          rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-d₁) (B-1-d₂) d₁ (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨by omega, by omega, by omega, by omega, by omega⟩
        · -- B-d₁ ≥ d₁ ≥ B-1-d₂ ≥ d₂-1
          rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-d₁) d₁ (B-1-d₂) (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨by omega, by omega, by omega, by omega, by omega⟩
    · rcases le_total (B - 1 - d₂) (d₂ - 1) with hPQ | hPQ
      · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-1-d₂) (B-d₁)
            (List.Perm.refl _) (by omega) (by omega) (by omega)]
        simp only
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩
      · rcases le_total (B - 1 - d₂) d₁ with hQA | hQA
        · rcases le_total (d₂ - 1) (B - d₁) with hPR | hPR
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (B-d₁) (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (d₂-1) (B-d₁)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩
        · rcases le_total (B - d₁) d₁ with hRA | hRA
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) d₁ (B-d₁) (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) (B-d₁) d₁ (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Helper 2.** From the invariant `I`, one Kaprekar step lands in `T_B` or in `E`. -/
theorem KB_stepI (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (q : ℕ × ℕ) (hq : inI B q) :
    KB B q ∈ TBset B ∨ inE B (KB B q) := by
  obtain ⟨hd1pos, hd1B, hd2d1, hpar, hcond⟩ := hq
  simp only [TBset, XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  set d₁ := q.1 with hd1def
  set d₂ := q.2 with hd2def
  obtain ⟨bk, hbk⟩ := hBodd
  rcases Nat.eq_zero_or_pos d₂ with hd2z | hd2pos
  · -- d₂ = 0, so by hcond d₁ = 2 or d₁ = B-1; both even (B odd ⇒ B-1 even)
    have hq2z : q.2 = 0 := by rw [← hd2def]; exact hd2z
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_zero B d₁ (by omega) hd1B
    have hKB : KB B q =
        (let S := sort4 (d₁ - 1) (B - 1) (B - 1) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, hq2z, Nat.zero_mul, Nat.add_zero]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    rcases le_total (d₁ - 1) (B - d₁) with hAB | hAB
    · rw [sort4_perm_eq (d₁-1) (B-1) (B-1) (B-d₁) (B-1) (B-1) (B-d₁) (d₁-1)
          (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
          (by omega) (by omega) (by omega)]
      simp only
      unfold inE
      -- d₁ ∈ {2, B-1}; the output is (d₁-1)-difference; decide T_B vs E by parity
      simp only [Nat.odd_iff, Nat.not_odd_iff]
      omega
    · rw [sort4_perm_eq (d₁-1) (B-1) (B-1) (B-d₁) (B-1) (B-1) (d₁-1) (B-d₁)
          (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
          (by omega) (by omega) (by omega)]
      simp only
      unfold inE
      simp only [Nat.odd_iff, Nat.not_odd_iff]
      omega
  · -- d₂ ≥ 1: digits {d₁, d₂-1, B-1-d₂, B-d₁}, with d₁ ≡ d₂ (mod 2)
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_pos B d₁ d₂ (by omega) (by omega) hd1B
    have hKB : KB B q =
        (let S := sort4 d₁ (d₂ - 1) (B - 1 - d₂) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, ← hd2def]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    unfold inE
    rcases (show d₂ = d₁ ∨ d₂ < d₁ by omega) with heqd | hltd
    · -- d₂ = d₁: digits {d₁, d₁-1, B-1-d₁, B-d₁} (heqd : d₂ = d₁)
      rcases le_total (B - d₁) d₁ with hRA | hRA
      · rcases le_total (B - d₁) (d₂ - 1) with hRP | hRP
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-d₁) (B-1-d₂)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          simp only [Nat.odd_iff, Nat.not_odd_iff]
          omega
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-d₁) (d₂-1) (B-1-d₂)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          simp only [Nat.odd_iff, Nat.not_odd_iff]
          omega
      · rcases le_total d₁ (B - 1 - d₂) with hAQ | hAQ
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-d₁) (B-1-d₂) d₁ (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          simp only [Nat.odd_iff, Nat.not_odd_iff]
          omega
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-d₁) d₁ (B-1-d₂) (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          simp only [Nat.odd_iff, Nat.not_odd_iff]
          omega
    · rcases le_total (B - 1 - d₂) (d₂ - 1) with hPQ | hPQ
      · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-1-d₂) (B-d₁)
            (List.Perm.refl _) (by omega) (by omega) (by omega)]
        simp only
        simp only [Nat.odd_iff, Nat.not_odd_iff]
        omega
      · rcases le_total (B - 1 - d₂) d₁ with hQA | hQA
        · rcases le_total (d₂ - 1) (B - d₁) with hPR | hPR
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (B-d₁) (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            simp only [Nat.odd_iff, Nat.not_odd_iff]
            omega
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (d₂-1) (B-d₁)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            simp only [Nat.odd_iff, Nat.not_odd_iff]
            omega
        · rcases le_total (B - d₁) d₁ with hRA | hRA
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) d₁ (B-d₁) (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            simp only [Nat.odd_iff, Nat.not_odd_iff]
            omega
          · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) (B-d₁) d₁ (d₂-1)
                (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
                (by omega) (by omega) (by omega)]
            simp only
            simp only [Nat.odd_iff, Nat.not_odd_iff]
            omega

/-- **Helper 3.** From the exceptional set `E = {(d,d-2): d even}`, one step lands in `T_B`. -/
theorem KB_stepE (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (q : ℕ × ℕ) (hq : inE B q) :
    KB B q ∈ TBset B := by
  obtain ⟨hd1even, hgap, hd1ge, hd1B⟩ := hq
  simp only [TBset, XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  set d₁ := q.1 with hd1def
  set d₂ := q.2 with hd2def
  obtain ⟨bk, hbk⟩ := hBodd
  have hd1par : d₁ % 2 = 0 := by rw [Nat.not_odd_iff] at hd1even; exact hd1even
  rcases Nat.eq_zero_or_pos d₂ with hd2z | hd2pos
  · -- d₂ = 0, d₁ = 2: digits {1, B-1, B-1, B-2}
    have hq2z : q.2 = 0 := by rw [← hd2def]; exact hd2z
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_zero B d₁ (by omega) hd1B
    have hKB : KB B q =
        (let S := sort4 (d₁ - 1) (B - 1) (B - 1) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, hq2z, Nat.zero_mul, Nat.add_zero]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    rw [sort4_perm_eq (d₁-1) (B-1) (B-1) (B-d₁) (B-1) (B-1) (B-d₁) (d₁-1)
        (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
        (by omega) (by omega) (by omega)]
    simp only
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      first | omega | (rw [Nat.odd_iff]; omega)
  · -- d₂ ≥ 1: digits {d₁, d₂-1, B-1-d₂, B-d₁}, d₂ = d₁ - 2 even
    obtain ⟨hN1, hN2, hN3, hN4⟩ := digits_of_N_pos B d₁ d₂ (by omega) (by omega) hd1B
    have hKB : KB B q =
        (let S := sort4 d₁ (d₂ - 1) (B - 1 - d₂) (B - d₁); (S.1 - S.2.2.2, S.2.1 - S.2.2.1)) := by
      unfold KB
      simp only [← hd1def, ← hd2def]
      rw [hN1, hN2, hN3, hN4]
    rw [hKB]
    rcases le_total (B - 1 - d₂) (d₂ - 1) with hPQ | hPQ
    · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (d₂-1) (B-1-d₂) (B-d₁)
          (List.Perm.refl _) (by omega) (by omega) (by omega)]
      simp only
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
        first | omega | (rw [Nat.odd_iff]; omega)
    · rcases le_total (B - 1 - d₂) d₁ with hQA | hQA
      · rcases le_total (d₂ - 1) (B - d₁) with hPR | hPR
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (B-d₁) (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
            first | omega | (rw [Nat.odd_iff]; omega)
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) d₁ (B-1-d₂) (d₂-1) (B-d₁)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
            first | omega | (rw [Nat.odd_iff]; omega)
      · rcases le_total (B - d₁) d₁ with hRA | hRA
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) d₁ (B-d₁) (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
            first | omega | (rw [Nat.odd_iff]; omega)
        · rw [sort4_perm_eq d₁ (d₂-1) (B-1-d₂) (B-d₁) (B-1-d₂) (B-d₁) d₁ (d₂-1)
              (by apply (List.perm_iff_count).2; intro x; simp only [List.count_cons, List.count_nil]; ring)
              (by omega) (by omega) (by omega)]
          simp only
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
            first | omega | (rw [Nat.odd_iff]; omega)

theorem KB3_maps_X_into_T (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    ∀ p ∈ XBset B, (KB B)^[3] p ∈ TBset B := by
  intro p hp
  have hiter : (KB B)^[3] p = KB B (KB B (KB B p)) := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [hiter]
  have h1 : inI B (KB B p) := KB_step1_into_I B hB3 hBodd p hp
  have h2 : KB B (KB B p) ∈ TBset B ∨ inE B (KB B (KB B p)) := KB_stepI B hB3 hBodd _ h1
  rcases h2 with hT | hE
  · exact KB_maps_T_into_T B hB3 hBodd _ hT
  · exact KB_stepE B hB3 hBodd _ hE

/- **Lemma `Phi_bijOn`** — part (3) of Theorem 1.
`Φ` is a bijection from `T_B` onto `binom(P_B, 2)`.

*Proof (informal).* Three steps.
  (a) *Maps into `binom(P_B,2)`.* For `(d₁,d₂) ∈ T_B`, `r = (d₁+d₂)/2`,
      `s = (d₁-d₂)/2` satisfy `0 < s < r < B`, so `[r], [s]` are nonzero, and
      `[r] ≠ [s]` because `r ≢ ±s (mod B)`: `r-s = d₂ ∈ (0,B)` and
      `r+s = d₁ ∈ (0,B)` are both nonzero mod `B`. Hence `Φ(d₁,d₂)` is an
      off-diagonal pair avoiding `[0]`.
  (b) *Injective.* From `{[r],[s]}` one recovers the unordered pair of *absolute*
      representatives `{r,s} ⊆ {1,…,(B-1)/2}` (each class has a unique representative
      in `1..(B-1)/2`), then `d₁ = r+s`, `d₂ = r-s` (with `r > s`). So `Φ` is injective
      on `T_B`.
  (c) *Surjective / cardinality.* `|P_B| = (B-1)/2`, so
      `|binom(P_B,2)| = C((B-1)/2, 2)`. Also `|T_B| = C((B-1)/2, 2)` (pairs of distinct
      odd numbers `d₂ < d₁` in `[1,B)` biject with pairs `s < r` in `[1,(B-1)/2]`).
      An injection between finite sets of equal cardinality is a bijection; combined
      with (a),(b) this gives `Set.BijOn`. -/
/-- **Helper `Phi_mapsTo`** — part (a) of `Phi_bijOn`.
`Φ` sends every `(d₁,d₂) ∈ T_B` to an off-diagonal pair avoiding `[0]`.

*Proof route.* For `(d₁,d₂) ∈ T_B`, set `r = (d₁+d₂)/2`, `s = (d₁-d₂)/2`; then
`0 < s < r < B`, `r+s = d₁`, `r-s = d₂`. Unfold `Phi`, `binomSet`, `Sym2.IsDiag`
(use `Sym2.isDiag_iff_proj_eq` / `Sym2.mk_isDiag_iff`) and `Sym2` membership
(`Sym2.mem_iff`). Reduce to three facts via `PBmk_eq_iff`:
  * `[r] ≠ [s]`: would need `r = ±s (mod B)`; `r-s = d₂` and `r+s = d₁` are both in
    `(0,B)`, hence nonzero mod `B`, contradiction.
  * `[0] ≠ [r]`: `r ∈ (0,B)`, so `(r : ZMod B) ≠ 0` (use `ZMod.natCast_zmod_eq_zero_iff_dvd`
    / `CharP.cast_eq_zero_iff`, with `r < B`, `0 < r`); and `0 = -r` impossible likewise.
  * `[0] ≠ [s]`: same with `s ∈ (0,B)`. -/
-- SANITY CHECK PASSED (no counterexample; exhaustive over odd B≤39, sub-part of Phi_bijOn)
theorem Phi_mapsTo (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    Set.MapsTo (Phi B) (↑(TBset B)) (binomSet B) := by
  haveI : NeZero B := ⟨by omega⟩
  intro p hp
  simp only [Finset.mem_coe, TBset, XBset, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hp
  obtain ⟨⟨⟨_, hd1lt⟩, hd2le⟩, hd2lt, hd2pos, hd1odd, hd2odd⟩ := hp
  set r := (p.1 + p.2) / 2 with hr
  set s := (p.1 - p.2) / 2 with hs
  -- arithmetic facts about r, s
  obtain ⟨k1, hk1⟩ := hd1odd
  obtain ⟨k2, hk2⟩ := hd2odd
  have hrs_add : r + s = p.1 := by omega
  have hrs_sub : r - s = p.2 := by omega
  have hslt_r : s < r := by omega
  have hrpos : 0 < r := by omega
  have hrlt : r < B := by omega
  have hspos : 0 < s := by omega
  have hslt : s < B := by omega
  -- the cast-nonzero helper
  have cast_ne_zero : ∀ m : ℕ, 0 < m → m < B → (m : ZMod B) ≠ 0 := by
    intro m hm0 hmB
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hm0 hdvd
    omega
  -- the cast-eq helper (mod B comparison)
  have cast_eq_iff : ∀ a b : ℕ, ((a : ZMod B) = (b : ZMod B)) ↔ a ≡ b [MOD B] := by
    intro a b; exact (ZMod.natCast_eq_natCast_iff a b B)
  refine ⟨?_, ?_⟩
  · -- ¬ IsDiag : [r] ≠ [s]
    rw [Phi, Sym2.mk_isDiag_iff]
    intro hdiag
    rw [PBmk_eq_iff] at hdiag
    rcases hdiag with h | h
    · -- (r:ZMod B) = (s:ZMod B) → r ≡ s, but r-s = p.2 ∈ (0,B)
      rw [cast_eq_iff] at h
      have hmod : r % B = s % B := h
      rw [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hslt] at hmod
      omega
    · -- (r:ZMod B) = -(s:ZMod B) → (r+s) = 0, but r+s = p.1 ∈ (0,B)
      have hsum : ((r + s : ℕ) : ZMod B) = 0 := by push_cast; rw [h]; ring
      exact cast_ne_zero (r + s) (by omega) (by omega) hsum
  · -- PBmk B 0 ∉ {[r],[s]}
    rw [Phi, Sym2.mem_iff]
    rw [← hr, ← hs]
    push_neg
    constructor
    · intro h
      rw [eq_comm, PBmk_eq_iff] at h
      rcases h with h | h
      · exact cast_ne_zero r hrpos hrlt h
      · have : (r : ZMod B) = 0 := by rw [h]; simp
        exact cast_ne_zero r hrpos hrlt this
    · intro h
      rw [eq_comm, PBmk_eq_iff] at h
      rcases h with h | h
      · exact cast_ne_zero s hspos hslt h
      · have : (s : ZMod B) = 0 := by rw [h]; simp
        exact cast_ne_zero s hspos hslt this

/-- **Helper `Phi_injOn`** — part (b) of `Phi_bijOn`.
`Φ` is injective on `T_B`.

*Proof route.* Suppose `Phi B p = Phi B q` for `p,q ∈ T_B`. With
`rₚ=(p.1+p.2)/2, sₚ=(p.1-p.2)/2` (similarly `q`), all four lie in `1..(B-1)/2`
(since `0 < sₚ < rₚ` and `rₚ ≤ p.1 < B`, but more precisely the canonical
representative of each class is in `1..(B-1)/2`). From the `Sym2` equality use
`Sym2.eq_iff` to get matched or swapped cases; `PBmk_eq_iff` turns each into
`x = ±y (mod B)`. Because all of `rₚ,sₚ,rₚ,sₚ ∈ (0, B/2)` (use `r,s ≤ (B-1)/2`,
which holds as `r = (d₁+d₂)/2 ≤ (2·((B-1)/2)+...)` — CAUTION: r can be up to `d₁ ≤ B-1`,
so `r` is NOT always `≤ (B-1)/2`; the correct uniqueness uses the projective
representative `min(x, B-x)`). Establish: for `0<x<B, 0<y<B`, `(x:ZMod B)=±(y:ZMod B)`
⟹ `x=y ∨ x+y=B`. Then with `rₚ+sₚ=p.1<B`, `rₚ-sₚ=p.2`, and the same for `q`, an `omega`
case-split recovers `p.1=q.1 ∧ p.2=q.2`. (See the closer's analysis in CONTEXT.md: the
key bound to add is `r+s < B`, which rules out the bad `r+r'=B ∧ s+s'=B` combination.)
Finish with `Prod.ext`. -/
-- SANITY CHECK PASSED (no counterexample; sub-part of the sanity-checked Phi_bijOn, B=5,7,9,11 Lean / B≤39 Python)
theorem Phi_injOn (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    Set.InjOn (Phi B) (↑(TBset B)) := by
  haveI : NeZero B := ⟨by omega⟩
  -- cast helpers
  have cast_ne_zero : ∀ m : ℕ, 0 < m → m < B → (m : ZMod B) ≠ 0 := by
    intro m hm0 hmB
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hm0 hdvd
    omega
  -- bridge: 0<x<B, 0<y<B, (x:ZMod B) = ±(y:ZMod B) → x=y ∨ x+y=B
  have bridge : ∀ x y : ℕ, 0 < x → x < B → 0 < y → y < B →
      ((x : ZMod B) = (y : ZMod B) ∨ (x : ZMod B) = -(y : ZMod B)) → x = y ∨ x + y = B := by
    intro x y hx0 hxB hy0 hyB h
    rcases h with h | h
    · -- x ≡ y mod B
      have hmod : x % B = y % B := (ZMod.natCast_eq_natCast_iff x y B).1 h
      rw [Nat.mod_eq_of_lt hxB, Nat.mod_eq_of_lt hyB] at hmod
      exact Or.inl hmod
    · -- x ≡ -y, i.e. x + y ≡ 0
      right
      have hsum : ((x + y : ℕ) : ZMod B) = 0 := by push_cast; rw [h]; ring
      rw [ZMod.natCast_eq_zero_iff] at hsum
      obtain ⟨c, hc⟩ := hsum
      -- x + y = B * c, with 0 < x+y < 2B ⟹ c = 1
      have hclt : c < 2 := by nlinarith
      interval_cases c <;> omega
  intro p hp q hq heq
  obtain ⟨kB, hkB⟩ := hBodd
  simp only [Finset.mem_coe, TBset, XBset, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hp hq
  obtain ⟨⟨⟨_, hpd1lt⟩, hpd2le⟩, hpd2lt, hpd2pos, hpd1odd, hpd2odd⟩ := hp
  obtain ⟨⟨⟨_, hqd1lt⟩, hqd2le⟩, hqd2lt, hqd2pos, hqd1odd, hqd2odd⟩ := hq
  set rp := (p.1 + p.2) / 2 with hrp
  set sp := (p.1 - p.2) / 2 with hsp
  set rq := (q.1 + q.2) / 2 with hrq
  set sq := (q.1 - q.2) / 2 with hsq
  obtain ⟨kp1, hkp1⟩ := hpd1odd
  obtain ⟨kp2, hkp2⟩ := hpd2odd
  obtain ⟨kq1, hkq1⟩ := hqd1odd
  obtain ⟨kq2, hkq2⟩ := hqd2odd
  have hrp_add : rp + sp = p.1 := by omega
  have hrp_sub : rp - sp = p.2 := by omega
  have hsp_lt_rp : sp < rp := by omega
  have hrp_pos : 0 < rp := by omega
  have hrp_lt : rp < B := by omega
  have hsp_pos : 0 < sp := by omega
  have hsp_lt : sp < B := by omega
  have hrq_add : rq + sq = q.1 := by omega
  have hrq_sub : rq - sq = q.2 := by omega
  have hsq_lt_rq : sq < rq := by omega
  have hrq_pos : 0 < rq := by omega
  have hrq_lt : rq < B := by omega
  have hsq_pos : 0 < sq := by omega
  have hsq_lt : sq < B := by omega
  -- unfold Phi-equality into Sym2 equality, then matched ∨ swapped
  rw [Phi, Phi, ← hrp, ← hsp, ← hrq, ← hsq, Sym2.eq_iff] at heq
  -- explicit linear facts for omega (sums of half-coordinates stay below B)
  have hpsum : rp + sp < B := by omega
  have hqsum : rq + sq < B := by omega
  -- recover the projective-class equalities and turn each into ℕ disjunctions
  have key : (p.1 = q.1 ∧ p.2 = q.2) := by
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- [rp]=[rq] ∧ [sp]=[sq]
      rw [PBmk_eq_iff] at h1 h2
      have e1 := bridge rp rq hrp_pos hrp_lt hrq_pos hrq_lt h1
      have e2 := bridge sp sq hsp_pos hsp_lt hsq_pos hsq_lt h2
      constructor <;> omega
    · -- [rp]=[sq] ∧ [sp]=[rq]
      rw [PBmk_eq_iff] at h1 h2
      have e1 := bridge rp sq hrp_pos hrp_lt hsq_pos hsq_lt h1
      have e2 := bridge sp rq hsp_pos hsp_lt hrq_pos hrq_lt h2
      constructor <;> omega
  exact Prod.ext key.1 key.2

/- **Helper `binomSet_ncard_le_TBset`** — the cardinality input to surjectivity.
`|binom(P_B,2)| ≤ |T_B|`. (In fact equality, but `≤` suffices given injectivity.)

*Proof route.* Both equal `C((B-1)/2, 2)`.
  * `|T_B|`: `T_B` is in bijection with pairs `s < r` in `1..(B-1)/2` via
    `(d₁,d₂) ↦ ((d₁+d₂)/2,(d₁-d₂)/2)`; counting the odd pairs `d₂ < d₁` in `[1,B)`
    gives `C((B-1)/2, 2)`.
  * `|binomSet B|`: `|P_B| = (B-1)/2` (each nonzero class `{x,-x}` has two
    representatives; there are `B-1` nonzero residues, plus the class of `0`, but the
    binomSet excludes `[0]`, so it counts 2-subsets of the `(B-1)/2` nonzero classes,
    i.e. `C((B-1)/2, 2)`). Use `Sym2` / `Fintype.card` and
    `Nat.card_eq_fintype_card`; relate `|P_B|` to `ZMod B` via the quotient cardinality
    (`ZMod.card`, `Fintype.card_quotient` / orbit-size 2 for `x ≠ 0`, fixed `0`).
This is the hardest counting step; it may be split further if needed. -/
-- SANITY CHECK PASSED (no counterexample; equal to |T_B|=C((B-1)/2,2), B≤199 exhaustive)
/-- The "odd representative" of `x : ZMod B`: the odd one of `x.val` and `B - x.val`. -/
def oddVal (B : ℕ) (x : ZMod B) : ℕ := if Odd x.val then x.val else B - x.val

theorem oddVal_lt (B : ℕ) [NeZero B] {x : ZMod B} (hx : x ≠ 0) : oddVal B x < B := by
  have hvpos : 0 < x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd ((ZMod.val_eq_zero x).1 h) hx
    · exact h
  have hvlt : x.val < B := ZMod.val_lt x
  unfold oddVal; split <;> omega

theorem oddVal_pos (B : ℕ) [NeZero B] {x : ZMod B} (hx : x ≠ 0) : 0 < oddVal B x := by
  have hvpos : 0 < x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd ((ZMod.val_eq_zero x).1 h) hx
    · exact h
  have hvlt : x.val < B := ZMod.val_lt x
  unfold oddVal; split <;> omega

theorem oddVal_odd (B : ℕ) (hBodd : Odd B) {x : ZMod B} (hx : x ≠ 0) : Odd (oddVal B x) := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  have hvpos : 0 < x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd ((ZMod.val_eq_zero x).1 h) hx
    · exact h
  have hvlt : x.val < B := ZMod.val_lt x
  unfold oddVal
  by_cases ho : Odd x.val
  · rw [if_pos ho]; exact ho
  · rw [if_neg ho]; rw [Nat.odd_iff] at ho ⊢; rcases hBodd with ⟨k,hk⟩; simp at ho; omega

theorem oddVal_cast (B : ℕ) [NeZero B] (x : ZMod B) :
    ((oddVal B x : ℕ) : ZMod B) = x ∨ ((oddVal B x : ℕ) : ZMod B) = -x := by
  have hvlt : x.val ≤ B := le_of_lt (ZMod.val_lt x)
  unfold oddVal
  by_cases ho : Odd x.val
  · rw [if_pos ho]; left; exact ZMod.natCast_zmod_val x
  · rw [if_neg ho]; right
    rw [Nat.cast_sub hvlt, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring

theorem oddVal_inj (B : ℕ) [NeZero B] {x y : ZMod B}
    (h : oddVal B x = oddVal B y) : x = y ∨ x = -y := by
  have hx := oddVal_cast B x
  have hy := oddVal_cast B y
  rw [h] at hx
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [← hx, hy]
  · right; rw [← hx, hy]
  · right; have e : -x = y := by rw [← hx, hy]
    rw [← e]; ring
  · left; have e : -x = -y := by rw [← hx, hy]
    exact neg_injective e

theorem oddVal_neg (B : ℕ) (hBodd : Odd B) (x : ZMod B) : oddVal B (-x) = oddVal B x := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  unfold oddVal
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · have hvlt : x.val < B := ZMod.val_lt x
    have hvpos : 0 < x.val := by
      rcases Nat.eq_zero_or_pos x.val with h | h
      · exact absurd ((ZMod.val_eq_zero x).1 h) hx
      · exact h
    have hval : (-x).val = B - x.val := by
      rw [ZMod.neg_val' x]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [hval]
    rcases hBodd with ⟨k, hk⟩
    by_cases ho : Odd x.val
    · have hno : ¬ Odd (B - x.val) := by rw [Nat.odd_iff] at ho ⊢; omega
      rw [if_pos ho, if_neg hno]
      have : B - (B - x.val) = x.val := by omega
      rw [this]
    · have ho2 : Odd (B - x.val) := by rw [Nat.odd_iff] at ho ⊢; simp at ho; omega
      rw [if_neg ho, if_pos ho2]

/-- The odd representative lifted to projective classes. -/
def oddRep (B : ℕ) (hBodd : Odd B) : PB B → ℕ :=
  Quotient.lift (oddVal B) (by
    intro x y h
    rcases h with h | h
    · rw [h]
    · rw [h, oddVal_neg B hBodd])

theorem oddRep_mk (B : ℕ) (hBodd : Odd B) (x : ZMod B) :
    oddRep B hBodd (PBmk B x) = oddVal B x := rfl

theorem PBmk_ne_zero_iff (B : ℕ) [NeZero B] (x : ZMod B) :
    PBmk B x ≠ PBmk B 0 ↔ x ≠ 0 := by
  simp only [Ne, PBmk_eq_iff, neg_zero, or_self]

theorem oddRep_pos (B : ℕ) (hBodd : Odd B) {c : PB B} (hc : c ≠ PBmk B 0) :
    0 < oddRep B hBodd c := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  induction c using Quotient.ind with
  | _ x =>
    have hx : x ≠ 0 := (PBmk_ne_zero_iff B x).1 hc
    exact oddVal_pos B hx

theorem oddRep_lt (B : ℕ) (hBodd : Odd B) {c : PB B} (hc : c ≠ PBmk B 0) :
    oddRep B hBodd c < B := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  induction c using Quotient.ind with
  | _ x =>
    have hx : x ≠ 0 := (PBmk_ne_zero_iff B x).1 hc
    exact oddVal_lt B hx

theorem oddRep_odd (B : ℕ) (hBodd : Odd B) {c : PB B} (hc : c ≠ PBmk B 0) :
    Odd (oddRep B hBodd c) := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  induction c using Quotient.ind with
  | _ x =>
    have hx : x ≠ 0 := (PBmk_ne_zero_iff B x).1 hc
    exact oddVal_odd B hBodd hx

theorem oddRep_inj (B : ℕ) (hBodd : Odd B) {c d : PB B}
    (h : oddRep B hBodd c = oddRep B hBodd d) : c = d := by
  haveI : NeZero B := ⟨by rcases hBodd with ⟨k, hk⟩; omega⟩
  induction c using Quotient.ind with
  | _ x =>
    induction d using Quotient.ind with
    | _ y =>
      have := oddVal_inj B (x := x) (y := y) h
      exact (PBmk_eq_iff B x y).2 this

/-- The injection `binom(P_B,2) → ℕ × ℕ` sending `{[x],[y]}` to the ordered pair of
odd representatives `(max, min)`. -/
def gmap (B : ℕ) (hBodd : Odd B) : Sym2 (PB B) → ℕ × ℕ :=
  Sym2.lift ⟨fun c d => (max (oddRep B hBodd c) (oddRep B hBodd d),
                          min (oddRep B hBodd c) (oddRep B hBodd d)),
            by intro a b; simp [max_comm, min_comm]⟩

theorem gmap_mk (B : ℕ) (hBodd : Odd B) (c d : PB B) :
    gmap B hBodd (Sym2.mk (c, d)) =
      (max (oddRep B hBodd c) (oddRep B hBodd d), min (oddRep B hBodd c) (oddRep B hBodd d)) := rfl

theorem binomSet_ncard_le_TBset (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    (binomSet B).ncard ≤ (TBset B).card := by
  haveI : NeZero B := ⟨by omega⟩
  rw [← Set.ncard_coe_finset (TBset B)]
  apply Set.ncard_le_ncard_of_injOn (gmap B hBodd)
  · -- MapsTo: the image of an off-diagonal nonzero-avoiding pair lands in `T_B`.
    intro s hs
    induction s using Sym2.ind with
    | _ c d =>
      obtain ⟨hdiag, hmem⟩ := hs
      rw [Sym2.mk_isDiag_iff] at hdiag
      rw [Sym2.mem_iff] at hmem
      push_neg at hmem
      obtain ⟨hc0, hd0⟩ := hmem
      have hcne : c ≠ PBmk B 0 := fun h => hc0 h.symm
      have hdne : d ≠ PBmk B 0 := fun h => hd0 h.symm
      have hcd : oddRep B hBodd c ≠ oddRep B hBodd d := by
        intro h; exact hdiag (oddRep_inj B hBodd h)
      have hcpos := oddRep_pos B hBodd hcne
      have hdpos := oddRep_pos B hBodd hdne
      have hclt := oddRep_lt B hBodd hcne
      have hdlt := oddRep_lt B hBodd hdne
      have hcodd := oddRep_odd B hBodd hcne
      have hdodd := oddRep_odd B hBodd hdne
      rw [Finset.mem_coe, gmap_mk]
      simp only [TBset, XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      set a := oddRep B hBodd c
      set b := oddRep B hBodd d
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rcases max_choice a b with hm | hm <;> rw [hm] <;> assumption
      · rcases min_choice a b with hm | hm <;> rw [hm] <;> assumption
  · -- InjOn: distinct pairs give distinct (max, min) of odd representatives.
    intro s hs t ht hst
    induction s using Sym2.ind with
    | _ c d =>
      induction t using Sym2.ind with
      | _ e f =>
        rw [gmap_mk, gmap_mk] at hst
        rw [Prod.ext_iff] at hst
        obtain ⟨hmax, hmin⟩ := hst
        set a := oddRep B hBodd c
        set b := oddRep B hBodd d
        set u := oddRep B hBodd e
        set v := oddRep B hBodd f
        have hpair : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
          rcases le_total a b with hab | hab <;> rcases le_total u v with huv | huv <;>
            simp_all
        rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hce : c = e := oddRep_inj B hBodd h1
          have hdf : d = f := oddRep_inj B hBodd h2
          rw [hce, hdf]
        · have hcf : c = f := oddRep_inj B hBodd h1
          have hde : d = e := oddRep_inj B hBodd h2
          rw [hcf, hde, Sym2.eq_swap]

-- SANITY CHECK PASSED (no counterexample; verified B=5,7,9,11 in Lean, B≤39 in Python)
/-- Assembles parts (a),(b),(c): MapsTo + InjOn + (image = binomSet by cardinality). -/
theorem Phi_bijOn (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    Set.BijOn (Phi B) (↑(TBset B)) (binomSet B) := by
  haveI : NeZero B := ⟨by omega⟩
  have hmaps := Phi_mapsTo B hB3 hBodd
  have hinj := Phi_injOn B hB3 hBodd
  refine ⟨hmaps, hinj, ?_⟩
  -- SurjOn via cardinality: the (injective) image equals the finite target binomSet.
  have hfin : (binomSet B).Finite := Set.toFinite _
  have himg_sub : Phi B '' (↑(TBset B)) ⊆ binomSet B := hmaps.image_subset
  have himg_card : (Phi B '' (↑(TBset B))).ncard = (TBset B).card := by
    rw [Set.InjOn.ncard_image hinj, Set.ncard_coe_finset]
  have hle : (binomSet B).ncard ≤ (Phi B '' (↑(TBset B))).ncard := by
    rw [himg_card]; exact binomSet_ncard_le_TBset B hB3 hBodd
  have heq : Phi B '' (↑(TBset B)) = binomSet B :=
    Set.eq_of_subset_of_ncard_le himg_sub hle hfin
  rw [Set.SurjOn, heq]

/-! ## Main Statements -/

/-- **Statement 1 (Theorem 1, structural).**
Let `B > 3` be odd. Then:
1. `K_B(T_B) ⊆ T_B`;
2. `K_B³(X_B) ⊆ T_B`;
3. `Φ : T_B → binom(P_B, 2)` is a bijection;
4. the restriction `K_B : T_B → T_B` is conjugate, under `Φ`, to the doubling map `D`,
   i.e. `Φ(K_B(d₁, d₂)) = D(Φ(d₁, d₂))` for all `(d₁, d₂) ∈ T_B`. -/
theorem thm_structural (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    -- (1) `K_B` maps `T_B` into `T_B`
    (∀ p ∈ TBset B, KB B p ∈ TBset B) ∧
    -- (2) the third iterate of `K_B` maps `X_B` into `T_B`
    (∀ p ∈ XBset B, (KB B)^[3] p ∈ TBset B) ∧
    -- (3) `Φ` is a bijection from `T_B` onto `binom(P_B, 2)`
    (Set.BijOn (Phi B) (↑(TBset B)) (binomSet B)) ∧
    -- (4) conjugacy with the doubling map
    (∀ p ∈ TBset B, Phi B (KB B p) = Dmap B (Phi B p)) :=
  ⟨KB_maps_T_into_T B hB3 hBodd,
   KB3_maps_X_into_T B hB3 hBodd,
   Phi_bijOn B hB3 hBodd,
   fun p hp => KB_eq_on_T B hB3 hBodd p hp⟩

/-- **Lemma `cmax_le`** — the bound half of Corollary 1.
`c_max(B) ≤ (B-1)/2`.

*Proof (informal).* By Theorem 1, every terminal cycle of `K_B` lies in `T_B`
(part 2: `K_B³(X_B) ⊆ T_B`, and periodic points lie in the eventual image), and on
`T_B` the map `K_B` is conjugate via `Φ` to the doubling map `D` on `binom(P_B,2)`
(parts 3,4). Hence the length of any terminal cycle equals the period of the
corresponding `D`-orbit on an unordered pair `{[r],[s]}`. Doubling acts as
multiplication by `2` on `P_B ≅ (ℤ/B)^× / {±1}` (restricted to the nonzero classes
appearing); the order of `2` in this quotient is the least `m` with `2^m ≡ ±1 (mod B)`,
which divides `|(ℤ/B)^×/{±1}| = φ(B)/2 ≤ (B-1)/2`. The period of a *pair* divides the
period of its larger entry, so every cycle length divides this order and is `≤ (B-1)/2`.
Taking the sup over `X_B` gives `c_max(B) ≤ (B-1)/2`.

Formal route: transport `minimalPeriod (KB B)` along the conjugacy to
`minimalPeriod (Dmap B)`, bound the latter by the projective order of `2`, and bound
that by `(B-1)/2` via `ZMod.card_units_le`/`orderOf_dvd_card` and `φ(B) ≤ B-1`. -/
-- SANITY CHECK PASSED (no counterexample; cmax B ≤ (B-1)/2 holds for all odd B in (3,40),
-- equality at {7,11,13,19,23,29,37}, verified computationally in Lean)
theorem cmax_le (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    cmax B ≤ (B - 1) / 2 := by
  haveI : NeZero B := ⟨by omega⟩
  haveI : Fact (1 < B) := ⟨by omega⟩
  classical
  -- abbreviations
  set σ : PB B → PB B := doubleP B with hσ
  -- (D1) doubling on representatives
  have hdbl : ∀ (x : ZMod B), σ (PBmk B x) = PBmk B (2 * x) := by
    intro x; rfl
  -- (D2) iterated doubling on representatives
  have hdblIt : ∀ (k : ℕ) (x : ZMod B), σ^[k] (PBmk B x) = PBmk B (2 ^ k * x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ', Function.comp_apply, ih, hdbl]
        rw [show (2 : ZMod B) ^ (n + 1) * x = 2 * (2 ^ n * x) by ring]
  -- (D3) PBmk equality criterion
  have hmk_eq : ∀ (a b : ZMod B), PBmk B a = PBmk B b ↔ (a = b ∨ a = -b) := by
    intro a b
    constructor
    · intro h; exact Quotient.exact h
    · intro h; exact Quotient.sound h
  -- The projective order of 2 : least m>0 with 2^m = ±1
  set m₀ : ℕ := Function.minimalPeriod σ (PBmk B 1) with hm0def
  -- 2 is a unit in ZMod B (B odd ⟹ coprime to 2)
  have h2unit : IsUnit (2 : ZMod B) := by
    have h2dvd : ¬ (2 ∣ B) := by
      rcases hBodd with ⟨t, ht⟩; omega
    have hco : Nat.Coprime 2 B := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2dvd
    have : IsUnit ((2 : ℕ) : ZMod B) := (ZMod.isUnit_iff_coprime 2 B).mpr hco
    simpa using this
  -- (P1) PBmk B 1 is a periodic point: 2 has finite order
  have hr : (2 : ZMod B) ^ (orderOf (2 : ZMod B)) = 1 := pow_orderOf_eq_one 2
  have h2fin : IsOfFinOrder (2 : ZMod B) := isOfFinOrder_iff_isUnit.mpr h2unit
  have hrpos : 0 < orderOf (2 : ZMod B) := h2fin.orderOf_pos
  have hperiodic1 : PBmk B 1 ∈ Function.periodicPts σ := by
    refine ⟨orderOf (2 : ZMod B), hrpos, ?_⟩
    show σ^[orderOf (2 : ZMod B)] (PBmk B 1) = PBmk B 1
    rw [hdblIt]
    rw [mul_one, hr]
  -- (P2) 0 < m₀
  have hm0pos : 0 < m₀ := Function.minimalPeriod_pos_of_mem_periodicPts hperiodic1
  -- (P3) σ^[m₀] (PBmk B 1) = PBmk B 1, hence 2^m₀ = ±1
  have hfix1 : σ^[m₀] (PBmk B 1) = PBmk B 1 := Function.iterate_minimalPeriod
  have hpm1 : (2 : ZMod B) ^ m₀ = 1 ∨ (2 : ZMod B) ^ m₀ = -1 := by
    have := hfix1
    rw [hdblIt] at this
    simp only [mul_one] at this
    have := (hmk_eq _ _).mp this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- (P4) hence σ^[m₀] = id on all of PB B
  have hσid : ∀ (c : PB B), σ^[m₀] c = c := by
    intro c
    induction c using Quotient.inductionOn with
    | _ x =>
      show σ^[m₀] (PBmk B x) = PBmk B x
      rw [hdblIt]
      rcases hpm1 with h | h
      · rw [h, one_mul]
      · apply (hmk_eq _ _).mpr; right; rw [h, neg_one_mul]
  -- (P5) m₀ ≤ (B-1)/2 : the orbit of [1] injects into the nonzero classes
  have hcardPB : Fintype.card (PB B) = (B - 1) / 2 + 1 := by
    have hne : ∀ x : ZMod B, x ≠ 0 → x ≠ -x := by
      intro x hx h
      apply hx
      have hz : (2 : ZMod B) * x = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
      exact (h2unit.mul_right_eq_zero).mp hz
    have hfib : ∀ c : PB B,
        (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card
          = if c = PBmk B 0 then 1 else 2 := by
      intro c
      induction c using Quotient.inductionOn with
      | _ a =>
        show (Finset.univ.filter (fun x : ZMod B => PBmk B x = PBmk B a)).card = _
        have hset : (Finset.univ.filter (fun x : ZMod B => PBmk B x = PBmk B a)) = {a, -a} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          rw [hmk_eq]
        rw [hset]
        by_cases ha : a = 0
        · subst ha
          rw [show (Quotient.mk (projSetoid B) (0 : ZMod B)) = PBmk B 0 from rfl, if_pos rfl]
          simp
        · have hane : a ≠ -a := hne a ha
          rw [Finset.card_insert_of_notMem (by simp [hane]), Finset.card_singleton]
          rw [if_neg]
          intro hc
          have hc' := (hmk_eq a 0).mp hc
          rcases hc' with h | h
          · exact ha h
          · rw [neg_zero] at h; exact ha h
    have hsum : Fintype.card (ZMod B)
        = ∑ c : PB B, (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card := by
      rw [Fintype.card]
      exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    rw [ZMod.card] at hsum
    have hsum2 : ∑ c : PB B, (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card
        = ∑ c : PB B, (if c = PBmk B 0 then 1 else 2) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hfib c
    rw [hsum2] at hsum
    have hone : ∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ (PBmk B 0) (fun _ => (1:ℕ))]
      simp
    have hcombine : (∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 2))
        + (∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 0))
        = 2 * Fintype.card (PB B) := by
      rw [← Finset.sum_add_distrib]
      have hpt : ∀ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 2)
          + (if c = PBmk B 0 then (1:ℕ) else 0) = 2 := by
        intro c; by_cases h : c = PBmk B 0 <;> simp [h]
      rw [Finset.sum_congr rfl (fun c _ => hpt c)]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [hone] at hcombine
    obtain ⟨t, ht⟩ := hBodd
    omega
  have hm0_le : m₀ ≤ (B - 1) / 2 := by
    -- each orbit point is nonzero
    have hne0 : ∀ i, σ^[i] (PBmk B 1) ≠ PBmk B 0 := by
      intro i hcontra
      rw [hdblIt, mul_one] at hcontra
      have hc := (hmk_eq _ _).mp hcontra
      have h2i : (2 : ZMod B) ^ i ≠ 0 := (h2unit.pow i).ne_zero
      rcases hc with h | h
      · exact h2i h
      · rw [neg_zero] at h; exact h2i h
    -- the image finset of the orbit on range m₀
    set S : Finset (PB B) := (Finset.range m₀).image (fun i => σ^[i] (PBmk B 1)) with hS
    have hSinj : Set.InjOn (fun i => σ^[i] (PBmk B 1)) (Finset.range m₀) := by
      intro a ha b hb hab
      exact Function.iterate_injOn_Iio_minimalPeriod
        (Set.mem_Iio.mpr (Finset.mem_range.mp ha))
        (Set.mem_Iio.mpr (Finset.mem_range.mp hb)) hab
    have hScard : S.card = m₀ := by
      rw [hS, Finset.card_image_of_injOn hSinj, Finset.card_range]
    have h0notin : PBmk B 0 ∉ S := by
      rw [hS, Finset.mem_image]
      rintro ⟨i, _, hi⟩
      exact hne0 i hi
    -- insert PBmk B 0 to get card m₀ + 1 ≤ card (PB B)
    have hins : (insert (PBmk B 0) S).card = m₀ + 1 := by
      rw [Finset.card_insert_of_notMem h0notin, hScard]
    have hle : (insert (PBmk B 0) S).card ≤ Fintype.card (PB B) :=
      Finset.card_le_univ _
    rw [hins, hcardPB] at hle
    omega
  -- ===== Main reduction =====
  rw [cmax]
  apply Finset.sup_le
  intro p hp
  -- n := minimalPeriod (KB B) p
  set n := Function.minimalPeriod (KB B) p with hndef
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0]; exact Nat.zero_le _
  · -- p is periodic
    have hpPer : p ∈ Function.periodicPts (KB B) :=
      Function.minimalPeriod_pos_iff_mem_periodicPts.mp hnpos
    -- q := (KB B)^[3] p ∈ TBset, with same minimal period
    set q := (KB B)^[3] p with hqdef
    have hqT : q ∈ TBset B := KB3_maps_X_into_T B hB3 hBodd p hp
    have hnq : Function.minimalPeriod (KB B) q = n := by
      rw [hqdef, hndef]; exact Function.minimalPeriod_apply_iterate hpPer 3
    -- orbit of q stays in TBset
    have horbT : ∀ k, (KB B)^[k] q ∈ TBset B := by
      intro k
      induction k with
      | zero => simpa using hqT
      | succ j ih =>
          rw [Function.iterate_succ', Function.comp_apply]
          exact KB_maps_T_into_T B hB3 hBodd _ ih
    -- conjugacy on iterates: Phi ((KB)^[k] q) = (Dmap)^[k] (Phi q)
    have hconj : ∀ k, Phi B ((KB B)^[k] q) = (Dmap B)^[k] (Phi B q) := by
      intro k
      induction k with
      | zero => simp
      | succ j ih =>
          rw [Function.iterate_succ', Function.comp_apply,
              Function.iterate_succ', Function.comp_apply, ← ih]
          exact KB_eq_on_T B hB3 hBodd _ (horbT j)
    -- (Dmap B)^[m₀] (Phi B q) = Phi B q
    have hDmapfix : (Dmap B)^[m₀] (Phi B q) = Phi B q := by
      have hiter : ∀ k (s : Sym2 (PB B)), (Dmap B)^[k] s = Sym2.map (σ^[k]) s := by
        intro k
        induction k with
        | zero => intro s; simp
        | succ j ih =>
            intro s
            rw [Function.iterate_succ', Function.comp_apply, ih]
            rw [Dmap, Sym2.map_map]
            rw [Function.iterate_succ']
      rw [hiter]
      have : σ^[m₀] = id := funext hσid
      rw [this, Sym2.map_id, id_eq]
    -- transport back: (KB B)^[m₀] q = q
    have hKBfix : (KB B)^[m₀] q = q := by
      have h1 : Phi B ((KB B)^[m₀] q) = Phi B q := by
        rw [hconj]; exact hDmapfix
      -- Phi injective on TBset
      have hinj : Set.InjOn (Phi B) (↑(TBset B)) := (Phi_bijOn B hB3 hBodd).injOn
      exact hinj (horbT m₀) hqT h1
    -- conclude
    show n ≤ (B - 1) / 2
    have hfin : Function.minimalPeriod (KB B) q ≤ m₀ :=
      Function.IsPeriodicPt.minimalPeriod_le hm0pos hKBfix
    rw [hnq] at hfin
    exact le_trans hfin hm0_le

/-- For `B = 5`, the Kaprekar map fixes the unique terminal state `(3, 1)`. -/
theorem KB5_fix : KB 5 (3, 1) = (3, 1) := by simp [KB, sort4, List.mergeSort]

/-- For `B = 5`, every state in `X_5` reaches the fixed point `(3, 1)` after `3` steps. -/
theorem KB5_reaches : ∀ p ∈ XBset 5, (KB 5)^[3] p = (3, 1) := by
  intro p hp
  fin_cases hp <;>
    (simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq];
     simp [KB, sort4, List.mergeSort])

/-- `c_max(5) ≤ 1`: every `K_5`-orbit on `X_5` reaches the fixed point `(3, 1)` in `3`
steps, so every periodic point equals `(3, 1)` (minimal period `1`) and every other
point is transient (minimal period `0`). -/
theorem cmax_five_le : cmax 5 ≤ 1 := by
  rw [cmax]
  apply Finset.sup_le
  intro p hp
  by_cases hper : p ∈ Function.periodicPts (KB 5)
  · -- p is periodic; show p = (3,1)
    have hnpos : 0 < Function.minimalPeriod (KB 5) p :=
      Function.minimalPeriod_pos_of_mem_periodicPts hper
    have hfix : Function.IsPeriodicPt (KB 5) (Function.minimalPeriod (KB 5) p) p :=
      Function.iterate_minimalPeriod
    set n := Function.minimalPeriod (KB 5) p with hn
    have hpern3 : Function.IsPeriodicPt (KB 5) (n * 3) p := hfix.mul_const 3
    have hfixiter : ∀ k, (KB 5)^[k] (3, 1) = (3, 1) := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply, KB5_fix, ih]
    have h31 : (KB 5)^[n * 3] p = (3, 1) := by
      have h3 : (KB 5)^[3] p = (3, 1) := KB5_reaches p hp
      have hsplit : n * 3 = (n * 3 - 3) + 3 := by omega
      rw [hsplit, Function.iterate_add_apply, h3, hfixiter]
    have hp31 : p = (3, 1) := by
      have hh := hpern3
      unfold Function.IsPeriodicPt Function.IsFixedPt at hh
      rw [h31] at hh
      exact hh.symm
    have : n = 1 := by
      rw [hn, hp31]
      exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr KB5_fix
    omega
  · -- transient: minimal period 0
    simp only [Function.minimalPeriod, dif_neg hper]
    omega

/-- **Lemma `cmax_eq_iff`** — the equality characterization of Corollary 1.
`c_max(B) = (B-1)/2` iff `B ≥ 7`, `B` prime, and the least `m` with `2^m ≡ ±1 (mod B)`
equals `(B-1)/2`.

*Proof (informal).* By the conjugacy, `c_max(B)` is the largest `D`-orbit length on
`binom(P_B,2)`, which (for the maximal orbits) equals the projective order
`ord = ` least `m` with `2^m ≡ ±1 (mod B)`, *provided* the action of `⟨2⟩` on `P_B` is
free with full-length orbits — this requires `B` prime (so `(ℤ/B)^×` is the cyclic group
of order `B-1` and `P_B` is a single `⟨2⟩`-orbit-friendly torsor) and the projective
order of `2` to be exactly `(B-1)/2` (i.e. `2` generates `(ℤ/B)^×/{±1}`). Equality
`c_max(B) = (B-1)/2` then holds. Conversely, if `B` is composite or the projective order
of `2` is a proper divisor of `(B-1)/2`, the orbits of `2` on `P_B` are shorter than
`(B-1)/2`, and the maximal pair-orbit is strictly smaller, so `c_max(B) < (B-1)/2`.
The threshold `B ≥ 7` excludes `B = 5` (where `|T_B| = 1`, `c_max = 1 < 2`). This is the
characterization verified computationally for all odd `B ≤ 39`. -/
theorem cmax_eq_iff (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    cmax B = (B - 1) / 2 ↔
      (7 ≤ B ∧ B.Prime ∧
        IsLeast {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)}
          ((B - 1) / 2)) := by
  -- SANITY CHECK PASSED (no counterexample; LHS⟺RHS for all odd B in 5..41;
  -- equality holds exactly for B∈{7,11,13,19,23,29,37}≤39)
  haveI : NeZero B := ⟨by omega⟩
  haveI : Fact (1 < B) := ⟨by omega⟩
  classical
  set σ : PB B → PB B := doubleP B with hσ
  -- doubling on representatives
  have hdbl : ∀ (x : ZMod B), σ (PBmk B x) = PBmk B (2 * x) := fun x => rfl
  have hdblIt : ∀ (k : ℕ) (x : ZMod B), σ^[k] (PBmk B x) = PBmk B (2 ^ k * x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ', Function.comp_apply, ih, hdbl]
        rw [show (2 : ZMod B) ^ (n + 1) * x = 2 * (2 ^ n * x) by ring]
  have hmk_eq : ∀ (a b : ZMod B), PBmk B a = PBmk B b ↔ (a = b ∨ a = -b) :=
    fun a b => PBmk_eq_iff B a b
  -- projective order of 2
  set m₀ : ℕ := Function.minimalPeriod σ (PBmk B 1) with hm0def
  have h2unit : IsUnit (2 : ZMod B) := by
    have h2dvd : ¬ (2 ∣ B) := by rcases hBodd with ⟨t, ht⟩; omega
    have hco : Nat.Coprime 2 B := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2dvd
    have : IsUnit ((2 : ℕ) : ZMod B) := (ZMod.isUnit_iff_coprime 2 B).mpr hco
    simpa using this
  have hr : (2 : ZMod B) ^ (orderOf (2 : ZMod B)) = 1 := pow_orderOf_eq_one 2
  have h2fin : IsOfFinOrder (2 : ZMod B) := isOfFinOrder_iff_isUnit.mpr h2unit
  have hrpos : 0 < orderOf (2 : ZMod B) := h2fin.orderOf_pos
  have hperiodic1 : PBmk B 1 ∈ Function.periodicPts σ := by
    refine ⟨orderOf (2 : ZMod B), hrpos, ?_⟩
    show σ^[orderOf (2 : ZMod B)] (PBmk B 1) = PBmk B 1
    rw [hdblIt, mul_one, hr]
  have hm0pos : 0 < m₀ := Function.minimalPeriod_pos_of_mem_periodicPts hperiodic1
  have hfix1 : σ^[m₀] (PBmk B 1) = PBmk B 1 := Function.iterate_minimalPeriod
  have hpm1 : (2 : ZMod B) ^ m₀ = 1 ∨ (2 : ZMod B) ^ m₀ = -1 := by
    have h := hfix1
    rw [hdblIt, mul_one] at h
    rcases (hmk_eq _ _).mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the IsLeast set S
  set S : Set ℕ := {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)} with hSdef
  -- m₀ ∈ S
  have hm0mem : m₀ ∈ S := ⟨hm0pos, hpm1⟩
  -- m₀ is a lower bound of S : any m ∈ S has σ^[m] (PBmk B 1) = PBmk B 1, so m₀ ∣ m, so m₀ ≤ m
  have hm0lb : ∀ m ∈ S, m₀ ≤ m := by
    intro m hm
    obtain ⟨hmpos, hpm⟩ := hm
    have hper : Function.IsPeriodicPt σ m (PBmk B 1) := by
      show σ^[m] (PBmk B 1) = PBmk B 1
      rw [hdblIt, mul_one]
      rcases hpm with h | h
      · rw [h]
      · apply (hmk_eq _ _).mpr; right; rw [h]
    exact Function.IsPeriodicPt.minimalPeriod_le hmpos hper
  have hIsLeast_m0 : IsLeast S m₀ := ⟨hm0mem, hm0lb⟩
  -- Claim B : IsLeast S ((B-1)/2) ↔ m₀ = (B-1)/2
  have hIsLeast_iff : IsLeast S ((B - 1) / 2) ↔ m₀ = (B - 1) / 2 := by
    constructor
    · intro h; exact IsLeast.unique hIsLeast_m0 h
    · intro h; rw [← h]; exact hIsLeast_m0
  -- the always-true bound
  have hcmax_le : cmax B ≤ (B - 1) / 2 := cmax_le B hB3 hBodd
  -- σ^[m₀] = id on all of PB B (since 2^m₀ = ±1)
  have hσid : ∀ (c : PB B), σ^[m₀] c = c := by
    intro c
    induction c using Quotient.inductionOn with
    | _ x =>
      show σ^[m₀] (PBmk B x) = PBmk B x
      rw [hdblIt]
      rcases hpm1 with h | h
      · rw [h, one_mul]
      · apply (hmk_eq _ _).mpr; right; rw [h, neg_one_mul]
  -- (H1) every KB-minimalPeriod over XBset divides m₀, hence cmax B ∣ m₀
  have hcmax_dvd : cmax B ∣ m₀ := by
    -- For p ∈ XBset, q := (KB B)^[3] p ∈ TBset and is a periodic point of period dividing m₀.
    have hKBfix : ∀ p ∈ XBset B, (KB B)^[m₀] ((KB B)^[3] p) = (KB B)^[3] p := by
      intro p hp
      set q := (KB B)^[3] p with hqdef
      have hqT : q ∈ TBset B := KB3_maps_X_into_T B hB3 hBodd p hp
      have horbT : ∀ k, (KB B)^[k] q ∈ TBset B := by
        intro k
        induction k with
        | zero => simpa using hqT
        | succ j ih => rw [Function.iterate_succ', Function.comp_apply]; exact KB_maps_T_into_T B hB3 hBodd _ ih
      have hconj : ∀ k, Phi B ((KB B)^[k] q) = (Dmap B)^[k] (Phi B q) := by
        intro k
        induction k with
        | zero => simp
        | succ j ih =>
            rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ', Function.comp_apply, ← ih]
            exact KB_eq_on_T B hB3 hBodd _ (horbT j)
      have hDmapfix : (Dmap B)^[m₀] (Phi B q) = Phi B q := by
        have hiter : ∀ k (s : Sym2 (PB B)), (Dmap B)^[k] s = Sym2.map (σ^[k]) s := by
          intro k
          induction k with
          | zero => intro s; simp
          | succ j ih => intro s; rw [Function.iterate_succ', Function.comp_apply, ih, Dmap, Sym2.map_map, Function.iterate_succ']
        rw [hiter]
        have : σ^[m₀] = id := funext hσid
        rw [this, Sym2.map_id, id_eq]
      have h1 : Phi B ((KB B)^[m₀] q) = Phi B q := by rw [hconj]; exact hDmapfix
      have hinj : Set.InjOn (Phi B) (↑(TBset B)) := (Phi_bijOn B hB3 hBodd).injOn
      exact hinj (horbT m₀) hqT h1
    -- For each p ∈ XBset, minimalPeriod (KB B) p divides m₀ or is 0.
    have hdvd_or_zero : ∀ p ∈ XBset B,
        Function.minimalPeriod (KB B) p ∣ m₀ ∨ Function.minimalPeriod (KB B) p = 0 := by
      intro p hp
      set q := (KB B)^[3] p with hqdef
      have hqper : Function.IsPeriodicPt (KB B) m₀ q := hKBfix p hp
      have hqdvd : Function.minimalPeriod (KB B) q ∣ m₀ := hqper.minimalPeriod_dvd
      by_cases hpper : p ∈ Function.periodicPts (KB B)
      · left
        have : Function.minimalPeriod (KB B) q = Function.minimalPeriod (KB B) p := by
          rw [hqdef]; exact Function.minimalPeriod_apply_iterate hpper 3
        rwa [this] at hqdvd
      · right
        simp only [Function.minimalPeriod, dif_neg hpper]
    -- There is a periodic point in XBset with positive minimal period, so cmax B ≠ 0.
    have hne : XBset B = ∅ → False := by
      intro hEmpty
      have : ((1, 0) : ℕ × ℕ) ∈ XBset B := by
        simp only [XBset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      rw [hEmpty] at this; simp at this
    have hXne : (XBset B).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hne h)
    obtain ⟨p₀, hp₀mem, hp₀eq⟩ :=
      Finset.exists_mem_eq_sup (XBset B) hXne (fun p => Function.minimalPeriod (KB B) p)
    -- cmax B is achieved at p₀.
    have hcmax_eq : cmax B = Function.minimalPeriod (KB B) p₀ := by rw [cmax]; exact hp₀eq
    -- cmax B > 0 : take any element, its image under KB^[3] is periodic.
    have hpos : 0 < cmax B := by
      obtain ⟨p, hp⟩ := hXne
      set q := (KB B)^[3] p with hqdef
      have hqper : Function.IsPeriodicPt (KB B) m₀ q := hKBfix p hp
      have hqmem : q ∈ Function.periodicPts (KB B) := ⟨m₀, hm0pos, hqper⟩
      have hqpos : 0 < Function.minimalPeriod (KB B) q :=
        Function.minimalPeriod_pos_of_mem_periodicPts hqmem
      have hqX : q ∈ XBset B := by
        have := KB3_maps_X_into_T B hB3 hBodd p hp
        rw [TBset] at this
        exact (Finset.mem_filter.mp this).1
      have hle : Function.minimalPeriod (KB B) q ≤ cmax B := by
        rw [cmax]; exact Finset.le_sup hqX
      omega
    rcases hdvd_or_zero p₀ hp₀mem with hd | hz
    · rwa [hcmax_eq]
    · exfalso; rw [hcmax_eq] at hpos; omega
  have hm0_le : m₀ ≤ (B - 1) / 2 := by
    -- cardinality of the projective space: (B-1)/2 nonzero classes + the zero class
    have hcardPB : Fintype.card (PB B) = (B - 1) / 2 + 1 := by
      have hne : ∀ x : ZMod B, x ≠ 0 → x ≠ -x := by
        intro x hx h
        apply hx
        have hz : (2 : ZMod B) * x = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
        exact (h2unit.mul_right_eq_zero).mp hz
      have hfib : ∀ c : PB B,
          (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card
            = if c = PBmk B 0 then 1 else 2 := by
        intro c
        induction c using Quotient.inductionOn with
        | _ a =>
          show (Finset.univ.filter (fun x : ZMod B => PBmk B x = PBmk B a)).card = _
          have hset : (Finset.univ.filter (fun x : ZMod B => PBmk B x = PBmk B a)) = {a, -a} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            rw [hmk_eq]
          rw [hset]
          by_cases ha : a = 0
          · subst ha
            rw [show (Quotient.mk (projSetoid B) (0 : ZMod B)) = PBmk B 0 from rfl, if_pos rfl]
            simp
          · have hane : a ≠ -a := hne a ha
            rw [Finset.card_insert_of_notMem (by simp [hane]), Finset.card_singleton]
            rw [if_neg]
            intro hc
            have hc' := (hmk_eq a 0).mp hc
            rcases hc' with h | h
            · exact ha h
            · rw [neg_zero] at h; exact ha h
      have hsum : Fintype.card (ZMod B)
          = ∑ c : PB B, (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card := by
        rw [Fintype.card]
        exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
      rw [ZMod.card] at hsum
      have hsum2 : ∑ c : PB B, (Finset.univ.filter (fun x : ZMod B => PBmk B x = c)).card
          = ∑ c : PB B, (if c = PBmk B 0 then 1 else 2) := by
        apply Finset.sum_congr rfl
        intro c _
        exact hfib c
      rw [hsum2] at hsum
      have hone : ∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ (PBmk B 0) (fun _ => (1:ℕ))]
        simp
      have hcombine : (∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 2))
          + (∑ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 0))
          = 2 * Fintype.card (PB B) := by
        rw [← Finset.sum_add_distrib]
        have hpt : ∀ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 2)
            + (if c = PBmk B 0 then (1:ℕ) else 0) = 2 := by
          intro c; by_cases h : c = PBmk B 0 <;> simp [h]
        rw [Finset.sum_congr rfl (fun c _ => hpt c)]
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      rw [hone] at hcombine
      obtain ⟨t, ht⟩ := hBodd
      omega
    -- each orbit point is nonzero
    have hne0 : ∀ i, σ^[i] (PBmk B 1) ≠ PBmk B 0 := by
      intro i hcontra
      rw [hdblIt, mul_one] at hcontra
      have hc := (hmk_eq _ _).mp hcontra
      have h2i : (2 : ZMod B) ^ i ≠ 0 := (h2unit.pow i).ne_zero
      rcases hc with h | h
      · exact h2i h
      · rw [neg_zero] at h; exact h2i h
    -- the image finset of the orbit on range m₀
    set Sorb : Finset (PB B) := (Finset.range m₀).image (fun i => σ^[i] (PBmk B 1)) with hSorb
    have hSinj : Set.InjOn (fun i => σ^[i] (PBmk B 1)) (Finset.range m₀) := by
      intro a ha b hb hab
      exact Function.iterate_injOn_Iio_minimalPeriod
        (Set.mem_Iio.mpr (Finset.mem_range.mp ha))
        (Set.mem_Iio.mpr (Finset.mem_range.mp hb)) hab
    have hScard : Sorb.card = m₀ := by
      rw [hSorb, Finset.card_image_of_injOn hSinj, Finset.card_range]
    have h0notin : PBmk B 0 ∉ Sorb := by
      rw [hSorb, Finset.mem_image]
      rintro ⟨i, _, hi⟩
      exact hne0 i hi
    -- insert PBmk B 0 to get card m₀ + 1 ≤ card (PB B)
    have hins : (insert (PBmk B 0) Sorb).card = m₀ + 1 := by
      rw [Finset.card_insert_of_notMem h0notin, hScard]
    have hle : (insert (PBmk B 0) Sorb).card ≤ Fintype.card (PB B) :=
      Finset.card_le_univ _
    rw [hins, hcardPB] at hle
    omega
  -- (H2) when m₀ ≥ 3, the pair {[1],[2]} realises an orbit of length m₀, giving cmax B ≥ m₀
  have hwitness : 3 ≤ m₀ → m₀ ≤ cmax B := by
    intro hm3
    set w : Sym2 (PB B) := s(PBmk B 1, PBmk B 2) with hwdef
    have hiter : ∀ k (s : Sym2 (PB B)), (Dmap B)^[k] s = Sym2.map (σ^[k]) s := by
      intro k
      induction k with
      | zero => intro s; simp
      | succ j ih => intro s; rw [Function.iterate_succ', Function.comp_apply, ih, Dmap, Sym2.map_map, Function.iterate_succ']
    have hDw : ∀ k, (Dmap B)^[k] w = s(PBmk B (2 ^ k * 1), PBmk B (2 ^ k * 2)) := by
      intro k
      rw [hiter, hwdef, Sym2.map_pair_eq, hdblIt, hdblIt]
    -- w ∈ binomSet B
    have hwmem : w ∈ binomSet B := by
      refine ⟨?_, ?_⟩
      · rw [hwdef, Sym2.isDiag_iff_proj_eq]
        intro heq
        rcases (hmk_eq _ _).mp heq with h | h
        · have h2 : (2 : ZMod B) ^ 1 = 1 := by rw [pow_one]; linear_combination -h
          have : m₀ ≤ 1 := hm0lb 1 ⟨one_pos, Or.inl h2⟩
          omega
        · have h2 : (2 : ZMod B) ^ 1 = -1 := by rw [pow_one]; linear_combination h
          have : m₀ ≤ 1 := hm0lb 1 ⟨one_pos, Or.inr h2⟩
          omega
      · rw [hwdef, Sym2.mem_iff]
        push_neg
        refine ⟨?_, ?_⟩
        · intro hc
          rcases (hmk_eq _ _).mp hc with h | h
          · exact one_ne_zero (α := ZMod B) h.symm
          · exact one_ne_zero (α := ZMod B) (by linear_combination h)
        · intro hc
          rcases (hmk_eq _ _).mp hc with h | h
          · exact h2unit.ne_zero h.symm
          · exact h2unit.ne_zero (by linear_combination h)
    -- get p₀
    obtain ⟨p₀, hp₀T, hp₀eq⟩ := (Phi_bijOn B hB3 hBodd).surjOn hwmem
    have horbT : ∀ k, (KB B)^[k] p₀ ∈ TBset B := by
      intro k
      induction k with
      | zero => simpa using Finset.mem_coe.mp hp₀T
      | succ j ih => rw [Function.iterate_succ', Function.comp_apply]; exact KB_maps_T_into_T B hB3 hBodd _ ih
    have hconj : ∀ k, Phi B ((KB B)^[k] p₀) = (Dmap B)^[k] (Phi B p₀) := by
      intro k
      induction k with
      | zero => simp
      | succ j ih =>
          rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ', Function.comp_apply, ← ih]
          exact KB_eq_on_T B hB3 hBodd _ (horbT j)
    have hinj : Set.InjOn (Phi B) (↑(TBset B)) := (Phi_bijOn B hB3 hBodd).injOn
    -- minimalPeriod (KB B) p₀ = minimalPeriod (Dmap B) w
    have hmpeq : Function.minimalPeriod (KB B) p₀ = Function.minimalPeriod (Dmap B) w := by
      rw [Function.minimalPeriod_eq_minimalPeriod_iff]
      intro n
      constructor
      · intro hpp
        have h1 : Phi B ((KB B)^[n] p₀) = Phi B p₀ := by rw [hpp]
        rw [hconj, hp₀eq] at h1
        show (Dmap B)^[n] w = w
        exact h1
      · intro hpp
        have h1 : Phi B ((KB B)^[n] p₀) = Phi B p₀ := by
          rw [hconj, hp₀eq]; exact hpp
        show (KB B)^[n] p₀ = p₀
        exact hinj (Finset.mem_coe.mpr (horbT n)) hp₀T h1
    -- minimalPeriod (Dmap B) w = m₀
    have hwper_m0 : (Dmap B)^[m₀] w = w := by
      rw [hiter]
      have hid : σ^[m₀] = id := funext hσid
      rw [hid, Sym2.map_id, id_eq]
    have hwperPts : w ∈ Function.periodicPts (Dmap B) := ⟨m₀, hm0pos, hwper_m0⟩
    have hdpos : 0 < Function.minimalPeriod (Dmap B) w :=
      Function.minimalPeriod_pos_of_mem_periodicPts hwperPts
    have hddvd : Function.minimalPeriod (Dmap B) w ∣ m₀ :=
      Function.IsPeriodicPt.minimalPeriod_dvd (x := w) (n := m₀) hwper_m0
    set d := Function.minimalPeriod (Dmap B) w with hddef
    have hdfix : (Dmap B)^[d] w = w := Function.iterate_minimalPeriod
    have hdeq : m₀ = d := by
      have hdle : d ≤ m₀ := Nat.le_of_dvd hm0pos hddvd
      have hdw := hDw d
      rw [hdfix, hwdef] at hdw
      have hsym : s(PBmk B (2 ^ d * 1), PBmk B (2 ^ d * 2)) = s(PBmk B 1, PBmk B 2) := hdw.symm
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨h1, _h2⟩ | ⟨_h1, h2⟩
      · rw [mul_one] at h1
        rcases (hmk_eq _ _).mp h1 with hh | hh
        · have : m₀ ≤ d := hm0lb d ⟨hdpos, Or.inl hh⟩
          omega
        · have : m₀ ≤ d := hm0lb d ⟨hdpos, Or.inr hh⟩
          omega
      · have hpow : (2 : ZMod B) ^ d * 2 = (2 : ZMod B) ^ (d + 1) := by ring
        rcases (hmk_eq _ _).mp h2 with hh | hh
        · rw [hpow] at hh
          have hmle : m₀ ≤ d + 1 := hm0lb (d + 1) ⟨Nat.succ_pos d, Or.inl hh⟩
          rcases eq_or_lt_of_le hdle with he | hlt
          · omega
          · have := Nat.eq_of_dvd_of_lt_two_mul hm0pos.ne' hddvd (by omega)
            omega
        · rw [hpow] at hh
          have hmle : m₀ ≤ d + 1 := hm0lb (d + 1) ⟨Nat.succ_pos d, Or.inr hh⟩
          rcases eq_or_lt_of_le hdle with he | hlt
          · omega
          · have := Nat.eq_of_dvd_of_lt_two_mul hm0pos.ne' hddvd (by omega)
            omega
    -- conclude
    have hp₀X : p₀ ∈ XBset B := by
      have hmem : p₀ ∈ TBset B := Finset.mem_coe.mp hp₀T
      rw [TBset] at hmem
      exact (Finset.mem_filter.mp hmem).1
    have hmp_m0 : Function.minimalPeriod (KB B) p₀ = m₀ := by rw [hmpeq]; omega
    calc m₀ = Function.minimalPeriod (KB B) p₀ := hmp_m0.symm
      _ ≤ cmax B := by rw [cmax]; exact Finset.le_sup hp₀X
  -- (H3) B = 5 is excluded : cmax 5 ≠ 2
  -- prime from m₀ = (B-1)/2
  have hprime_of_m0 : m₀ = (B - 1) / 2 → B.Prime := by
    -- SANITY CHECK PASSED (no counterexample: for all odd B in 5..5000, whenever the
    -- projective order of 2 equals (B-1)/2, B is prime)
    intro hm0eq
    -- Setup
    haveI : Fact (2 < B) := ⟨by omega⟩
    set u : (ZMod B)ˣ := h2unit.unit with hu
    have huval : (u : ZMod B) = 2 := h2unit.unit_spec
    -- B - 1 = 2 * m₀
    have hB1 : B - 1 = 2 * m₀ := by
      obtain ⟨t, ht⟩ := hBodd
      omega
    -- d := orderOf u
    set d : ℕ := orderOf u with hd
    have hdord2 : d = orderOf (2 : ZMod B) := by
      rw [hd]; conv_rhs => rw [← huval]; rw [orderOf_units]
    -- 2^d = 1
    have h2d1 : (2 : ZMod B) ^ d = 1 := by
      rw [hdord2]; exact pow_orderOf_eq_one _
    -- d > 0 (finite order)
    have hdpos : 0 < d := by
      rw [hd]; exact orderOf_pos u
    -- d ∈ S, hence m₀ ≤ d
    have hdS : d ∈ S := by
      rw [hSdef]; exact ⟨hdpos, Or.inl h2d1⟩
    have hm0led : m₀ ≤ d := hm0lb d hdS
    -- d ∣ 2 * m₀
    have hd_dvd_2m0 : d ∣ 2 * m₀ := by
      rw [hdord2]
      apply orderOf_dvd_of_pow_eq_one
      rw [mul_comm, pow_mul]
      rcases hpm1 with h | h <;> rw [h] <;> ring
    -- d ∣ totient B
    have hd_dvd_tot : d ∣ B.totient := by
      have : Nat.card (ZMod B)ˣ = B.totient := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      rw [hd, ← this]
      exact orderOf_dvd_natCard u
    -- KEY: 2 * m₀ ∣ totient B
    have key : 2 * m₀ ∣ B.totient := by
      rcases hpm1 with hm0_one | hm0_neg
      · -- Case 2^m₀ = 1: d = m₀, need extra factor 2 via -1 ∉ ⟨u⟩
        have hne : (1 : ZMod B) ≠ -1 := fun h => ZMod.neg_one_ne_one h.symm
        -- d ∣ m₀ since 2^m₀ = 1
        have hd_dvd_m0 : d ∣ m₀ := by
          rw [hdord2]; exact orderOf_dvd_of_pow_eq_one hm0_one
        -- d = m₀
        have hdm0 : d = m₀ := le_antisymm (Nat.le_of_dvd hm0pos hd_dvd_m0) hm0led
        -- orderOf (2 : ZMod B) = m₀
        have hord2m0 : orderOf (2 : ZMod B) = m₀ := by rw [← hdord2]; exact hdm0
        set H : Subgroup (ZMod B)ˣ := Subgroup.zpowers u with hH
        -- card H = m₀
        have hcardH : Nat.card H = m₀ := by
          rw [hH, Nat.card_zpowers, ← hd, hdm0]
        -- -1 ∉ H
        have hneg_notin : (-1 : (ZMod B)ˣ) ∉ H := by
          intro hmem
          rw [hH, ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
          obtain ⟨k, hk⟩ := hmem
          -- cast to ZMod B: 2^k = -1
          have hcast : (2 : ZMod B) ^ k = -1 := by
            have := congrArg (Units.val) hk
            rwa [Units.val_pow_eq_pow_val, huval, Units.val_neg, Units.val_one] at this
          -- reduce mod m₀
          have hred : (2 : ZMod B) ^ (k % m₀) = -1 := by
            rw [← hord2m0, pow_mod_orderOf, hcast]
          -- k % m₀ ≠ 0
          have hkm0_ne : k % m₀ ≠ 0 := by
            intro h0
            rw [h0, pow_zero] at hred
            exact hne hred
          have hkm0_lt : k % m₀ < m₀ := Nat.mod_lt k hm0pos
          have : k % m₀ ∈ S := by
            rw [hSdef]; exact ⟨Nat.pos_of_ne_zero hkm0_ne, Or.inr hred⟩
          have := hm0lb _ this
          omega
        -- 2 ∣ index H
        have h2_dvd_idx : 2 ∣ H.index := by
          have hord : orderOf (QuotientGroup.mk (-1 : (ZMod B)ˣ) : (ZMod B)ˣ ⧸ H) = 2 := by
            apply orderOf_eq_prime
            · -- (mk -1)^2 = 1
              have : ((-1 : (ZMod B)ˣ)) ^ 2 = 1 := by rw [pow_two, neg_one_mul, neg_neg]
              rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
            · -- mk -1 ≠ 1
              rw [Ne, QuotientGroup.eq_one_iff]
              exact hneg_notin
          have : orderOf (QuotientGroup.mk (-1 : (ZMod B)ˣ) : (ZMod B)ˣ ⧸ H) ∣ H.index := by
            rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard _
          rwa [hord] at this
        -- combine: 2 * m₀ ∣ φ(B)
        have htotB : Nat.card (ZMod B)ˣ = B.totient := by
          rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        have hcard_mul : Nat.card H * H.index = B.totient := by
          rw [Subgroup.card_mul_index, htotB]
        obtain ⟨k, hk⟩ := h2_dvd_idx
        rw [hcardH, hk] at hcard_mul
        exact ⟨k, by rw [← hcard_mul]; ring⟩
      · -- Case 2^m₀ = -1: d = 2*m₀ directly
        have hne : (1 : ZMod B) ≠ -1 := fun h => ZMod.neg_one_ne_one h.symm
        -- d ∤ m₀
        have hdnm0 : ¬ (d ∣ m₀) := by
          intro hdvd
          obtain ⟨c, hc⟩ := hdvd
          have h1 : (2 : ZMod B) ^ m₀ = 1 := by
            rw [hc, pow_mul, h2d1, one_pow]
          exact hne (h1.symm.trans hm0_neg)
        -- m₀ < d
        have hlt : m₀ < d := lt_of_le_of_ne hm0led (by
          intro he; exact hdnm0 (he ▸ dvd_refl d))
        -- d = 2 * m₀
        have hdeq : d = 2 * m₀ := by
          have := Nat.eq_of_dvd_of_lt_two_mul (a := 2 * m₀) (b := d)
            (by omega) hd_dvd_2m0 (by omega)
          omega
        rw [← hdeq]; exact hd_dvd_tot
    -- Finish: totient B = B - 1, hence prime
    have htot_lt : B.totient < B := Nat.totient_lt B (by omega)
    have htot_eq : B.totient = B - 1 := by
      have hle : 2 * m₀ ≤ B.totient := Nat.le_of_dvd (by
        rw [Nat.totient_pos]; omega) key
      omega
    exact (Nat.totient_eq_iff_prime (by omega)).mp (by rw [htot_eq])
  constructor
  · -- forward
    intro hcmax
    have hm0eq : m₀ = (B - 1) / 2 := by
      have h1 : cmax B ≤ m₀ := Nat.le_of_dvd hm0pos hcmax_dvd
      omega
    refine ⟨?_, hprime_of_m0 hm0eq, hIsLeast_iff.mpr hm0eq⟩
    -- 7 ≤ B : exclude B = 5
    by_contra hlt
    push_neg at hlt
    -- B odd, 3 < B, B < 7 ⟹ B = 5
    have hB5 : B = 5 := by rcases hBodd with ⟨t, ht⟩; omega
    -- SANITY CHECK PASSED (computational: for B=5, every K_B orbit on X_5 reaches the
    -- fixed point (3,1); all minimal periods are 0 or 1, so cmax 5 = 1 ≠ 2 = (5-1)/2)
    -- cmax 5 ≤ 1 (proven helper `cmax_five_le`), but `hcmax` forces cmax 5 = (5-1)/2 = 2.
    rw [hB5] at hcmax
    have hle := cmax_five_le
    omega
  · -- backward
    rintro ⟨hB7, hBprime, hLeast⟩
    have hm0eq : m₀ = (B - 1) / 2 := hIsLeast_iff.mp hLeast
    have hm03 : 3 ≤ m₀ := by rw [hm0eq]; omega
    have hge : m₀ ≤ cmax B := hwitness hm03
    omega

/-- **Statement 2 (Corollary 1, cycle-length bound).**
Let `B > 3` be odd. Then `c_max(B) ≤ (B-1)/2`. Moreover equality holds if and only if
`B ≥ 7`, `B` is prime, and the least positive integer `m` with `2^m ≡ ±1 (mod B)` is
`m = (B-1)/2`. -/
theorem cor_length (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    cmax B ≤ (B - 1) / 2 ∧
    (cmax B = (B - 1) / 2 ↔
      (7 ≤ B ∧ B.Prime ∧
        IsLeast {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)}
          ((B - 1) / 2))) :=
  ⟨cmax_le B hB3 hBodd, cmax_eq_iff B hB3 hBodd⟩

-- ===== HELPER LEMMAS for numMaxCycles_eq (Corollary 2) =====

/-- Iterating `+1` on `ZMod n`. -/
theorem rot_iterate (n : ℕ) (k : ℕ) (x : ZMod n) :
    (fun y : ZMod n => y + 1)^[k] x = x + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih]; push_cast; ring

/-- Iterating the Sym2 rotation. -/
theorem srot_iterate (n : ℕ) (k : ℕ) (s : Sym2 (ZMod n)) :
    (Sym2.map (fun x : ZMod n => x + 1))^[k] s = Sym2.map (fun x : ZMod n => x + (k : ZMod n)) s := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Sym2.map_map]
      congr 1
      funext x
      simp only [Function.comp_apply]
      push_cast; ring

/-- The full-rotation: `Sym2.map (·+n) = id` on `ZMod n`. -/
theorem srot_pow_n (n : ℕ) [NeZero n] (s : Sym2 (ZMod n)) :
    (Sym2.map (fun x : ZMod n => x + 1))^[n] s = s := by
  rw [srot_iterate]
  have : ((n : ℕ) : ZMod n) = 0 := by exact_mod_cast ZMod.natCast_self n
  rw [this]
  simp

/-- Period characterization for the rotation on a non-diagonal pair. -/
theorem srot_minPeriod_eq (n : ℕ) [NeZero n] (a b : ZMod n) (hab : a ≠ b) :
    Function.minimalPeriod (Sym2.map (fun x : ZMod n => x + 1)) (s(a, b)) = n ↔
      (2 : ZMod n) * (a - b) ≠ 0 := by
  set r : Sym2 (ZMod n) → Sym2 (ZMod n) := Sym2.map (fun x : ZMod n => x + 1) with hr
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- s is periodic with period n
  have hper_n : Function.IsPeriodicPt r n (s(a, b)) := by
    show r^[n] (s(a, b)) = s(a, b)
    exact srot_pow_n n (s(a, b))
  have hmem : (s(a, b)) ∈ Function.periodicPts r := ⟨n, hnpos, hper_n⟩
  have hmpos : 0 < Function.minimalPeriod r (s(a, b)) :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hmdvd : Function.minimalPeriod r (s(a, b)) ∣ n := hper_n.minimalPeriod_dvd
  have hmle : Function.minimalPeriod r (s(a, b)) ≤ n := Nat.le_of_dvd hnpos hmdvd
  -- iterate formula
  have hiterk : ∀ k : ℕ, r^[k] (s(a, b)) = s(a + (k : ZMod n), b + (k : ZMod n)) := by
    intro k; rw [hr, srot_iterate]; rfl
  constructor
  · -- minimalPeriod = n ⟹ 2*(a-b) ≠ 0
    intro hmn h2
    -- 2*(a-b) = 0 produces a smaller period d.val
    set d : ZMod n := a - b with hd
    have hd0 : d ≠ 0 := fun h => hab (by rw [hd] at h; linear_combination h)
    have hswap : r^[d.val] (s(a, b)) = s(a, b) := by
      rw [hiterk]
      have hcast : ((d.val : ℕ) : ZMod n) = d := ZMod.natCast_zmod_val d
      rw [hcast]
      rw [Sym2.eq_iff]
      right
      constructor
      · rw [hd]; linear_combination h2
      · rw [hd]; ring
    have hdval_pos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd ((ZMod.val_eq_zero d).mp h) hd0
      · exact h
    have hdval_lt : d.val < n := ZMod.val_lt d
    have hper_d : Function.IsPeriodicPt r d.val (s(a, b)) := hswap
    have := hper_d.minimalPeriod_le hdval_pos
    rw [hmn] at this
    omega
  · -- 2*(a-b) ≠ 0 ⟹ minimalPeriod = n
    intro h2
    -- minimalPeriod is a period; analyze
    set m := Function.minimalPeriod r (s(a, b)) with hmdef
    have hmfix : r^[m] (s(a, b)) = s(a, b) := Function.iterate_minimalPeriod
    rw [hiterk] at hmfix
    rw [Sym2.eq_iff] at hmfix
    rcases hmfix with ⟨h1, _⟩ | ⟨h1, h2'⟩
    · -- a + m = a ⟹ (m : ZMod n) = 0 ⟹ n ∣ m
      have hm0 : ((m : ℕ) : ZMod n) = 0 := by linear_combination h1
      have hndvd : (n : ℕ) ∣ m := by
        rwa [ZMod.natCast_eq_zero_iff] at hm0
      exact Nat.dvd_antisymm hmdvd hndvd
    · -- a + m = b and b + m = a ⟹ 2*(a-b) = 0, contradiction
      exfalso
      apply h2
      have hma : (m : ZMod n) = b - a := by linear_combination h1
      have hb : (m : ZMod n) = a - b := by linear_combination h2'
      have hsym : (a - b) = (b - a) := by rw [← hb, hma]
      linear_combination hsym

/-- Symmetric decidable predicate `2*(a-b) ≠ 0` lifted to `Sym2 (ZMod n)`. -/
noncomputable def Qsym (n : ℕ) : Sym2 (ZMod n) → Prop :=
  Sym2.lift ⟨fun a b => (2 : ZMod n) * (a - b) ≠ 0, by
    intro a b
    simp only [eq_iff_iff]
    constructor <;> intro h hc <;> apply h <;> linear_combination -hc⟩

/-- Count of solutions to `2*c = 0` in `ZMod n` for odd `n`: just `c = 0`. -/
theorem rot_count_kernel_odd (n : ℕ) [NeZero n] (hodd : Odd n) :
    (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0)).card = 1 := by
  classical
  have hunit : IsUnit (2 : ZMod n) := by
    have h2 : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
    rw [← h2, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr hodd
  have hset : (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0)) = {0} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact (hunit.mul_right_eq_zero).mp h
    · intro h; rw [h, mul_zero]
  rw [hset, Finset.card_singleton]

/-- Count of solutions to `2*c = 0` in `ZMod n` for even `n = 2m`: `{0, m}`. -/
theorem rot_count_kernel_even (n : ℕ) [NeZero n] (m : ℕ) (hm : n = 2 * m) (hmpos : 0 < m) :
    (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0)).card = 2 := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have key : ∀ c : ZMod n, (2:ZMod n) * c = 0 ↔ (c = 0 ∨ c = (m : ZMod n)) := by
    intro c
    have h2 : (2:ZMod n) * c = ((2 * c.val : ℕ) : ZMod n) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    rw [h2, ZMod.natCast_eq_zero_iff]
    constructor
    · intro hdvd
      have hmdvd : m ∣ c.val := by
        rcases hdvd with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have : 2 * c.val = 2 * (m * k) := by rw [hk, hm]; ring
        omega
      have hlt : c.val < 2 * m := by rw [← hm]; exact ZMod.val_lt c
      obtain ⟨j, hj⟩ := hmdvd
      have hjlt : j < 2 := by
        by_contra h
        push_neg at h
        have : 2 * m ≤ m * j := by nlinarith
        omega
      interval_cases j
      · left; rw [← ZMod.natCast_zmod_val c, hj]; simp
      · right; rw [← ZMod.natCast_zmod_val c, hj]; simp
    · intro hc
      rcases hc with hc | hc
      · rw [hc]; simp
      · rw [hc, ZMod.val_natCast]
        have hmod : m % n = m := Nat.mod_eq_of_lt (by omega)
        rw [hmod, hm]
  have hset : (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0)) = {0, (m : ZMod n)} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact key c
  rw [hset]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro hcontra
  have hval : ((m:ℕ) : ZMod n).val = m := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  rw [← hcontra] at hval
  simp at hval
  omega

/-- **Combinatorial core (REMAINING SORRY #1).** Number of full-period non-diagonal
pairs for the rotation `+1` on `ZMod n` equals `n * ((n-1)/2)`.

Pure finite combinatorics, no Kaprekar content. Using `srot_minPeriod_eq`, for a
non-diagonal pair `s(a,b)` (so `a ≠ b`), `minimalPeriod (rotation) s(a,b) = n ↔
2*(a-b) ≠ 0`. Hence this filtered set equals `{ s(a,b) | a ≠ b ∧ 2*(a-b) ≠ 0 }`. Count:
total non-diagonal pairs `= C(n,2) = n(n-1)/2`; "bad" non-diagonal pairs have `2*(a-b)=0`,
`a ≠ b`, i.e. `0` (n odd) or `n/2` (n even) of them (`{a, a+n/2}`); subtracting gives
`n*(n-1)/2 - (if Even n then n/2 else 0) = n * ((n-1)/2)` by a parity case split + `omega`. -/
theorem rot_period_count (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (Finset.univ.filter
      (fun s : Sym2 (ZMod n) => ¬ s.IsDiag ∧
        Function.minimalPeriod (Sym2.map (fun x : ZMod n => x + 1)) s = n)).card
      = n * ((n - 1) / 2) := by
  classical
  -- Step 1: replace the minimalPeriod predicate by the symmetric algebraic condition.
  have step1 : (Finset.univ.filter
      (fun s : Sym2 (ZMod n) => ¬ s.IsDiag ∧
        Function.minimalPeriod (Sym2.map (fun x : ZMod n => x + 1)) s = n))
      = (Finset.univ.filter (fun s : Sym2 (ZMod n) => ¬ s.IsDiag ∧ Qsym n s)) := by
    apply Finset.filter_congr
    intro s _
    induction s using Sym2.inductionOn with
    | hf a b =>
      simp only [Sym2.mk_isDiag_iff]
      by_cases hab : a = b
      · simp [hab]
      · rw [srot_minPeriod_eq n a b hab]
        unfold Qsym
        rw [Sym2.lift_mk]
  rw [step1]
  set S := (Finset.univ.filter (fun s : Sym2 (ZMod n) => ¬ s.IsDiag ∧ Qsym n s)) with hS
  set O := (Finset.univ.filter
      (fun p : ZMod n × ZMod n => p.1 ≠ p.2 ∧ (2:ZMod n)*(p.1 - p.2) ≠ 0)) with hO
  set K := (Finset.univ.filter (fun c : ZMod n => c ≠ 0 ∧ (2:ZMod n)*c ≠ 0)).card with hK
  -- Step 2: O.card = 2 * S.card  (Sym2.mk is 2-to-1 off the diagonal).
  have hOS : O.card = 2 * S.card := by
    have hmaps : Set.MapsTo (fun p : ZMod n × ZMod n => Sym2.mk p) (↑O) (↑S) := by
      intro p hp
      simp only [hO, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      obtain ⟨a, b⟩ := p
      refine ⟨?_, ?_⟩
      · rw [Sym2.mk_isDiag_iff]; exact hp.1
      · unfold Qsym; rw [Sym2.lift_mk]; exact hp.2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ x ∈ S, (Finset.filter (fun p => Sym2.mk p = x) O).card = 2 := by
      intro x hx
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      induction x using Sym2.inductionOn with
      | hf a b =>
        have hab : a ≠ b := by
          intro h; apply hx.1; rw [h, Sym2.mk_isDiag_iff]
        have hQ : (2:ZMod n) * (a - b) ≠ 0 := by
          have := hx.2; unfold Qsym at this; rw [Sym2.lift_mk] at this; exact this
        rw [Finset.card_eq_two]
        refine ⟨(a,b), (b,a), ?_, ?_⟩
        · simp only [ne_eq, Prod.mk.injEq, not_and]
          intro h; exact absurd h hab
        · ext p
          simp only [Finset.mem_filter, hO, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          obtain ⟨c, d⟩ := p
          constructor
          · rintro ⟨_, heq⟩
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
            · left; rw [h1, h2]
            · right; rw [h1, h2]
          · rintro (h | h) <;> (rw [Prod.mk.injEq] at h; obtain ⟨h1,h2⟩ := h; subst h1; subst h2)
            · exact ⟨⟨hab, hQ⟩, rfl⟩
            · refine ⟨⟨fun hh => hab hh.symm, ?_⟩, Sym2.eq_swap⟩
              intro hc; apply hQ; linear_combination -hc
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Step 3: O.card = n * K  (translation makes each fiber over `a` a copy of K).
  have hOK : O.card = n * K := by
    rw [hK]
    rw [Finset.card_eq_sum_card_fiberwise (s := O) (t := (Finset.univ : Finset (ZMod n)))
        (f := Prod.fst) (by intro p _; exact Finset.mem_univ _)]
    have hfib : ∀ a ∈ (Finset.univ : Finset (ZMod n)),
        (Finset.filter (fun p => p.1 = a) O).card
          = (Finset.univ.filter (fun c : ZMod n => c ≠ 0 ∧ (2:ZMod n)*c ≠ 0)).card := by
      intro a _
      apply Finset.card_bij (fun p _ => a - p.2)
      · intro p hp
        simp only [Finset.mem_filter, hO, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨hne, h2⟩, hfst⟩ := hp
        subst hfst
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hc => hne (by linear_combination hc), h2⟩
      · intro p hp q hq heq
        simp only [Finset.mem_filter, hO, Finset.mem_univ, true_and] at hp hq
        obtain ⟨c,d⟩ := p; obtain ⟨e,f⟩ := q
        simp only at hp hq heq
        obtain ⟨_, hc⟩ := hp; obtain ⟨_, he⟩ := hq
        subst hc; subst he
        have : d = f := by linear_combination -heq
        rw [this]
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        refine ⟨(a, a - c), ?_, ?_⟩
        · simp only [Finset.mem_filter, hO, Finset.mem_univ, true_and, and_true]
          refine ⟨fun h => hc.1 (by linear_combination h), ?_⟩
          · have h2 : a - (a - c) = c := by ring
            rw [h2]; exact hc.2
        · simp only
          ring
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_univ, ZMod.card,
      smul_eq_mul]
  -- Step 4: K = 2 * ((n-1)/2), via complement and the kernel count.
  have hKcompl : K = n - (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0)).card := by
    rw [hK]
    have heq : (Finset.univ.filter (fun c : ZMod n => c ≠ 0 ∧ (2:ZMod n)*c ≠ 0))
        = (Finset.univ.filter (fun c : ZMod n => (2:ZMod n)*c = 0))ᶜ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2
        exact ⟨fun hc => h2 (by rw [hc, mul_zero]), h2⟩
    rw [heq, Finset.card_compl, ZMod.card]
  have hKval : K = 2 * ((n - 1) / 2) := by
    rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨m, hm⟩ := hev
      have hm' : n = 2 * m := by omega
      have hmpos : 0 < m := by omega
      rw [hKcompl, rot_count_kernel_even n m hm' hmpos]
      omega
    · rw [hKcompl, rot_count_kernel_odd n hodd]
      obtain ⟨k, hk⟩ := hodd
      omega
  -- Combine: 2 * S.card = O.card = n * K = n * (2 * ((n-1)/2)) = 2 * (n * ((n-1)/2)).
  have : 2 * S.card = 2 * (n * ((n - 1) / 2)) := by
    rw [← hOS, hOK, hKval]; ring
  omega

/-- On `T_B`, `Φ` conjugates `K_B` to `D`, so minimal periods agree. -/
theorem minPeriod_Phi (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (p : ℕ × ℕ)
    (hp : p ∈ TBset B) :
    Function.minimalPeriod (KB B) p = Function.minimalPeriod (Dmap B) (Phi B p) := by
  have horbT : ∀ k, (KB B)^[k] p ∈ TBset B := by
    intro k
    induction k with
    | zero => simpa using hp
    | succ j ih => rw [Function.iterate_succ', Function.comp_apply]; exact KB_maps_T_into_T B hB3 hBodd _ ih
  have hconj : ∀ k, Phi B ((KB B)^[k] p) = (Dmap B)^[k] (Phi B p) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ', Function.comp_apply, ← ih]
        exact KB_eq_on_T B hB3 hBodd _ (horbT j)
  have hinj : Set.InjOn (Phi B) (↑(TBset B)) := (Phi_bijOn B hB3 hBodd).injOn
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro k
  constructor
  · intro hpp
    show (Dmap B)^[k] (Phi B p) = Phi B p
    rw [← hconj k]
    have : (KB B)^[k] p = p := hpp
    rw [this]
  · intro hpp
    show (KB B)^[k] p = p
    apply hinj (Finset.mem_coe.mpr (horbT k)) (Finset.mem_coe.mpr hp)
    rw [hconj k]; exact hpp

/-- A point of `X_B` that is periodic for `K_B` (positive minimal period) lies in `T_B`. -/
theorem periodic_mem_T (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (p : ℕ × ℕ)
    (hp : p ∈ XBset B) (hpos : 0 < Function.minimalPeriod (KB B) p) :
    p ∈ TBset B := by
  set m := Function.minimalPeriod (KB B) p with hm
  have hpPer : p ∈ Function.periodicPts (KB B) :=
    Function.minimalPeriod_pos_iff_mem_periodicPts.mp hpos
  have hqT : (KB B)^[3] p ∈ TBset B := KB3_maps_X_into_T B hB3 hBodd p hp
  have horbT : ∀ k, (KB B)^[k] ((KB B)^[3] p) ∈ TBset B := by
    intro k
    induction k with
    | zero => simpa using hqT
    | succ j ih => rw [Function.iterate_succ', Function.comp_apply]; exact KB_maps_T_into_T B hB3 hBodd _ ih
  have hfix : Function.IsPeriodicPt (KB B) m p := Function.iterate_minimalPeriod
  have hfixk : ∀ k, (KB B)^[k * m] p = p := by
    intro k
    have := (hfix.const_mul k)
    simpa [Function.IsPeriodicPt, Function.IsFixedPt] using this
  have hk : (KB B)^[3 * m] p = p := hfixk 3
  have h3m : 3 ≤ 3 * m := by omega
  have hsplit : 3 * m = (3 * m - 3) + 3 := by omega
  have : p = (KB B)^[3 * m - 3] ((KB B)^[3] p) := by
    conv_lhs => rw [← hk, hsplit, Function.iterate_add_apply]
  rw [this]; exact horbT _

-- ===== HELPER LEMMAS for the (B) count in numMaxCycles_eq (self-contained) =====

/-- For odd `B`, `x = -x` only at `x = 0`. -/
theorem neg_eq_self_iff (B : ℕ) [NeZero B] (hBodd : Odd B) (x : ZMod B) : x = -x ↔ x = 0 := by
  constructor
  · intro h
    have h2 : (2 : ZMod B) * x = 0 := by linear_combination h
    have hunit : IsUnit (2 : ZMod B) := by
      have he : ((2 : ℕ) : ZMod B) = (2 : ZMod B) := by push_cast; ring
      rw [← he, ZMod.isUnit_iff_coprime]
      exact Nat.coprime_two_left.mpr hBodd
    exact (hunit.mul_right_eq_zero).mp h2
  · intro h; rw [h]; ring

/-- `|P_B| = (B-1)/2 + 1` for odd `B`. -/
theorem PB_card (B : ℕ) [NeZero B] (hBodd : Odd B) :
    Fintype.card (PB B) = (B-1)/2 + 1 := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (ZMod B)), PBmk B x ∈ (Finset.univ : Finset (PB B)) :=
    fun x _ => Finset.mem_univ _
  have hsum : (Finset.univ : Finset (ZMod B)).card
      = ∑ c ∈ (Finset.univ : Finset (PB B)), (Finset.univ.filter (fun x => PBmk B x = c)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ c : PB B, (Finset.univ.filter (fun x => PBmk B x = c)).card
      = if c = PBmk B 0 then 1 else 2 := by
    intro c
    induction c using Quotient.inductionOn with
    | h a =>
      show (Finset.univ.filter (fun x => PBmk B x = PBmk B a)).card = if PBmk B a = PBmk B 0 then 1 else 2
      have hset : (Finset.univ.filter (fun x => PBmk B x = PBmk B a)) = {a, -a} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        rw [PBmk_eq_iff]
      rw [hset]
      by_cases hc : PBmk B a = PBmk B 0
      · rw [if_pos hc]
        rw [PBmk_eq_iff] at hc
        have ha0 : a = 0 := by
          rcases hc with h | h
          · exact h
          · rw [neg_zero] at h; exact h
        simp [ha0]
      · rw [if_neg hc]
        have ha0 : a ≠ 0 := by
          intro h; apply hc; rw [h]
        have hane : a ≠ -a := by
          intro hh; rw [neg_eq_self_iff B hBodd] at hh; exact ha0 hh
        rw [Finset.card_pair hane]
  simp only [hfib] at hsum
  rw [Finset.card_univ, ZMod.card] at hsum
  have hrw : ∀ c : PB B, (if c = PBmk B 0 then (1:ℕ) else 2)
      = 1 + (if c = PBmk B 0 then 0 else 1) := by
    intro c; by_cases h : c = PBmk B 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun c _ => hrw c), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hcompl : ∑ c : PB B, (if c = PBmk B 0 then (0:ℕ) else 1)
      = Fintype.card (PB B) - 1 := by
    have : ∑ c : PB B, (if c = PBmk B 0 then (0:ℕ) else 1)
        = ∑ c ∈ (Finset.univ.filter (fun c => c ≠ PBmk B 0)), 1 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c = PBmk B 0 <;> simp [h]
    rw [this, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [hcompl] at hsum
  haveI : Nonempty (PB B) := ⟨PBmk B 0⟩
  have hpos : 0 < Fintype.card (PB B) := Fintype.card_pos
  omega

/-- `(doubleP B)^[i] [1] = [2^i]`. -/
theorem doubleP_iterate (B : ℕ) (i : ℕ) : (doubleP B)^[i] (PBmk B 1) = PBmk B (2^i) := by
  induction i with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      show doubleP B (PBmk B (2^j)) = PBmk B (2^(j+1))
      rw [show doubleP B (PBmk B (2^j)) = PBmk B (2 * 2^j) from rfl]
      congr 1; ring

/-- `minimalPeriod (doubleP B) [1]` equals the projective order `n`. -/
theorem minPeriod_doubleP (B : ℕ) [NeZero B] (n : ℕ)
    (hleast : IsLeast {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)} n) :
    Function.minimalPeriod (doubleP B) (PBmk B 1) = n := by
  have hper : ∀ m : ℕ, Function.IsPeriodicPt (doubleP B) m (PBmk B 1)
      ↔ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1) := by
    intro m
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [doubleP_iterate]
    rw [PBmk_eq_iff]
  obtain ⟨⟨hnpos, hn2⟩, hlb⟩ := hleast
  have hnper : Function.IsPeriodicPt (doubleP B) n (PBmk B 1) := (hper n).mpr hn2
  have hmem : (PBmk B 1) ∈ Function.periodicPts (doubleP B) := ⟨n, hnpos, hnper⟩
  have hle : Function.minimalPeriod (doubleP B) (PBmk B 1) ≤ n := hnper.minimalPeriod_le hnpos
  have hmpos : 0 < Function.minimalPeriod (doubleP B) (PBmk B 1) :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hmper : Function.IsPeriodicPt (doubleP B) (Function.minimalPeriod (doubleP B) (PBmk B 1)) (PBmk B 1) :=
    Function.iterate_minimalPeriod
  have hmin_in : Function.minimalPeriod (doubleP B) (PBmk B 1) ∈
      {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)} :=
    ⟨hmpos, (hper _).mp hmper⟩
  have hge : n ≤ Function.minimalPeriod (doubleP B) (PBmk B 1) := hlb hmin_in
  omega

/-- The orbit map `i ↦ [2^i]` re-indexed by `ZMod n`. -/
noncomputable def gZ (B : ℕ) (n : ℕ) (z : ZMod n) : PB B := (doubleP B)^[z.val] (PBmk B 1)

/-- Conjugacy: `doubleP (gZ z) = gZ (z+1)`. -/
theorem gZ_conj (B : ℕ) [NeZero B] (n : ℕ) [NeZero n]
    (hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n) (z : ZMod n) :
    doubleP B (gZ B n z) = gZ B n (z + 1) := by
  unfold gZ
  rw [← Function.iterate_succ_apply' (doubleP B) z.val]
  have hper : Function.IsPeriodicPt (doubleP B) n (PBmk B 1) := by
    rw [← hmp]; exact Function.iterate_minimalPeriod
  have key : ∀ k : ℕ, (doubleP B)^[k] (PBmk B 1) = (doubleP B)^[k % n] (PBmk B 1) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k n]
    rw [Function.iterate_add_apply]
    congr 1
    have hpc : Function.IsPeriodicPt (doubleP B) (n * (k / n)) (PBmk B 1) := by
      rw [Nat.mul_comm]; exact hper.const_mul (k / n)
    exact hpc
  rw [key (z.val + 1), key (z+1).val]
  congr 1
  have h1 : ((z.val + 1 : ℕ) : ZMod n) = (((z+1).val : ℕ) : ZMod n) := by
    have ha : ((z.val + 1 : ℕ) : ZMod n) = z + 1 := by
      push_cast; rw [ZMod.natCast_zmod_val]
    have hb : (((z+1).val : ℕ) : ZMod n) = z + 1 := ZMod.natCast_zmod_val _
    rw [ha, hb]
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  exact h1

/-- `gZ` is injective (orbit of length = minimal period is injective on `Iio n`). -/
theorem gZ_inj (B : ℕ) [NeZero B] (n : ℕ) [NeZero n]
    (hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n) :
    Function.Injective (gZ B n) := by
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := doubleP B) (x := PBmk B 1)
  rw [hmp] at hinj
  intro z w hzw
  unfold gZ at hzw
  have hz : z.val ∈ Set.Iio n := ZMod.val_lt z
  have hw : w.val ∈ Set.Iio n := ZMod.val_lt w
  have := hinj hz hw hzw
  have hcast : ((z.val : ℕ) : ZMod n) = ((w.val : ℕ) : ZMod n) := by rw [this]
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast

/-- Each `gZ z` is a nonzero class (`B` prime so `2^k ≠ 0`). -/
theorem gZ_ne_zero (B : ℕ) [NeZero B] (hBprime : B.Prime) (hB3 : 3 < B) (n : ℕ) (z : ZMod n) :
    gZ B n z ≠ PBmk B 0 := by
  haveI : Fact B.Prime := ⟨hBprime⟩
  unfold gZ
  rw [doubleP_iterate]
  rw [Ne, PBmk_eq_iff]
  push_neg
  have h2ne : (2 : ZMod B) ≠ 0 := by
    have : ((2 : ℕ) : ZMod B) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    simpa using this
  have hpow : (2 : ZMod B) ^ z.val ≠ 0 := pow_ne_zero _ h2ne
  refine ⟨hpow, ?_⟩
  rw [neg_zero]; exact hpow

/-- `gZ` surjects onto the nonzero classes (injective + equal cardinality `n`). -/
theorem gZ_surj (B : ℕ) [NeZero B] (hBodd : Odd B) (hBprime : B.Prime) (hB3 : 3 < B)
    (n : ℕ) [NeZero n] (hndef : n = (B-1)/2)
    (hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n)
    (c : PB B) (hc : c ≠ PBmk B 0) :
    ∃ z : ZMod n, gZ B n z = c := by
  classical
  let F : ZMod n → {d : PB B // d ≠ PBmk B 0} := fun z => ⟨gZ B n z, gZ_ne_zero B hBprime hB3 n z⟩
  have hFinj : Function.Injective F := by
    intro z w hzw
    apply gZ_inj B n hmp
    exact Subtype.ext_iff.mp hzw
  have hcardsub : Fintype.card {d : PB B // d ≠ PBmk B 0} = n := by
    rw [Fintype.card_subtype_compl]
    rw [PB_card B hBodd]
    simp [hndef]
  have hcardZ : Fintype.card (ZMod n) = n := ZMod.card n
  have hFsurj : Function.Surjective F := by
    have hbij : Function.Bijective F := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hFinj, by rw [hcardZ, hcardsub]⟩
    exact hbij.surjective
  obtain ⟨z, hz⟩ := hFsurj ⟨c, hc⟩
  exact ⟨z, congrArg Subtype.val hz⟩

/-- Sym2-level conjugacy of `Dmap` with the rotation through `Sym2.map gZ`. -/
theorem Dmap_conj (B : ℕ) [NeZero B] (n : ℕ) [NeZero n]
    (hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n) (s : Sym2 (ZMod n)) :
    Dmap B (Sym2.map (gZ B n) s) = Sym2.map (gZ B n) (Sym2.map (fun x : ZMod n => x + 1) s) := by
  unfold Dmap
  rw [Sym2.map_map, Sym2.map_map]
  congr 1
  funext z
  simp only [Function.comp_apply]
  exact gZ_conj B n hmp z

/-- Minimal periods are conjugacy-invariant through `Sym2.map gZ`. -/
theorem minPeriod_map_eq (B : ℕ) [NeZero B] (n : ℕ) [NeZero n]
    (hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n) (s : Sym2 (ZMod n)) :
    Function.minimalPeriod (Dmap B) (Sym2.map (gZ B n) s)
      = Function.minimalPeriod (Sym2.map (fun x : ZMod n => x + 1)) s := by
  have hmapinj : Function.Injective (Sym2.map (gZ B n)) := Sym2.map.injective (gZ_inj B n hmp)
  have hconj : ∀ k, (Dmap B)^[k] (Sym2.map (gZ B n) s)
      = Sym2.map (gZ B n) ((Sym2.map (fun x : ZMod n => x + 1))^[k] s) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ', Function.comp_apply, ih,
            Function.iterate_succ', Function.comp_apply]
        exact Dmap_conj B n hmp _
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro k
  constructor
  · intro hpp
    show (Sym2.map (fun x : ZMod n => x + 1))^[k] s = s
    apply hmapinj
    rw [← hconj k]
    exact hpp
  · intro hpp
    show (Dmap B)^[k] (Sym2.map (gZ B n) s) = Sym2.map (gZ B n) s
    rw [hconj k]
    have : (Sym2.map (fun x : ZMod n => x + 1))^[k] s = s := hpp
    rw [this]

/-- **Lemma `numMaxCycles_eq`** — Corollary 2.
Under the equality hypothesis of Corollary 1 (with `B` prime), the number of terminal
cycles of length `c_max(B) = (B-1)/2` equals `⌊(c_max(B) - 1)/2⌋`.

*Proof (informal).* By the conjugacy, terminal cycles of length `n := (B-1)/2`
correspond to `D`-orbits of size `n` on `binom(P_B,2)`. Since `2` has full projective
order `n` (equality hypothesis, `B` prime), `⟨2⟩` acts on `P_B` (a set of size `n`) as a
single transitive cyclic action — `P_B` is one `⟨2⟩`-orbit of size `n`. The induced
action on unordered pairs `binom(P_B,2)` (size `C(n,2) = n(n-1)/2`) decomposes into
orbits. A pair `{x, 2^k x}` has `D`-orbit length `n / gcd(...)`; the number of *full*
orbits (length exactly `n`) is `C(n,2)/n` minus the short orbits. Counting: the number
of pairs is `n(n-1)/2`, the points of `K_B` with minimal period exactly `n` number
`n · (#full cycles)`, and dividing the pair-count by the orbit sizes yields
`#full cycles = ⌊(n-1)/2⌋`. (The short orbits arise only from the unique pair fixed
by the half-rotation `2^{n/2}` when `n` is even, which is why the floor appears.)
This count matches `⌊(c_max(p)-1)/2⌋` computationally for `p ∈ {7,11,13,19,23,29,37}`. -/
theorem numMaxCycles_eq (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (hBprime : B.Prime)
    (hEq : cmax B = (B - 1) / 2) :
    numMaxCycles B = (cmax B - 1) / 2 := by
  -- SANITY CHECK PASSED (exhaustive over primes B<40 in scope {7,11,13,19,23,29,37}; no counterexample)
  haveI : NeZero B := ⟨by omega⟩
  haveI : Fact (1 < B) := ⟨by omega⟩
  classical
  set n : ℕ := (B - 1) / 2 with hndef
  have hn3 : 3 ≤ n := by
    have := (cmax_eq_iff B hB3 hBodd).mp hEq
    obtain ⟨hB7, _, _⟩ := this
    omega
  -- (A) numMaxCycles reduces to a Dmap-orbit point count divided by n
  have hA : numMaxCycles B =
      (Finset.univ.filter
        (fun w : Sym2 (PB B) => w ∈ binomSet B ∧
          Function.minimalPeriod (Dmap B) w = n)).card / n := by
    rw [numMaxCycles, hEq]
    congr 1
    set L : Finset (ℕ × ℕ) := (XBset B).filter (fun p => Function.minimalPeriod (KB B) p = n) with hL
    set R : Finset (Sym2 (PB B)) := Finset.univ.filter
      (fun w : Sym2 (PB B) => w ∈ binomSet B ∧ Function.minimalPeriod (Dmap B) w = n) with hR
    have hmemT : ∀ p ∈ L, p ∈ TBset B := by
      intro p hp
      rw [hL, Finset.mem_filter] at hp
      exact periodic_mem_T B hB3 hBodd p hp.1 (by rw [hp.2]; omega)
    apply Finset.card_bij (fun p _ => Phi B p)
    · intro p hp
      have hpT : p ∈ TBset B := hmemT p hp
      rw [hL, Finset.mem_filter] at hp
      rw [hR, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Phi_bijOn B hB3 hBodd).mapsTo (Finset.mem_coe.mpr hpT)
      · rw [← minPeriod_Phi B hB3 hBodd p hpT]; exact hp.2
    · intro p1 hp1 p2 hp2 heq
      have hinj : Set.InjOn (Phi B) (↑(TBset B)) := (Phi_bijOn B hB3 hBodd).injOn
      exact hinj (Finset.mem_coe.mpr (hmemT p1 hp1)) (Finset.mem_coe.mpr (hmemT p2 hp2)) heq
    · intro w hw
      rw [hR, Finset.mem_filter] at hw
      obtain ⟨_, hwbinom, hwper⟩ := hw
      obtain ⟨p, hpT, hpeq⟩ := (Phi_bijOn B hB3 hBodd).surjOn hwbinom
      have hpTm : p ∈ TBset B := Finset.mem_coe.mp hpT
      have hpX : p ∈ XBset B := (Finset.mem_filter.mp hpTm).1
      refine ⟨p, ?_, hpeq⟩
      rw [hL, Finset.mem_filter]
      refine ⟨hpX, ?_⟩
      rw [minPeriod_Phi B hB3 hBodd p hpTm, hpeq]; exact hwper
  -- (B) the Dmap-orbit point count equals n * ((n-1)/2)
  -- REMAINING SORRY (#2). Transport the count from `binomSet B`/`Dmap` to
  -- `Sym2 (ZMod n)`/rotation, then invoke `rot_period_count n hn3`.
  -- Since `B` is prime and `2` has projective order exactly `n`
  -- (`(cmax_eq_iff B hB3 hBodd).mp hEq` gives `IsLeast {m | 0<m ∧ 2^m=±1} n`), the orbit
  -- `i ↦ PBmk B (2^i)` is injective on `{0,…,n-1}` and surjects onto the `n` nonzero
  -- classes `P_B \ {[0]}` (via `|P_B| = n+1`, proven by the fiberwise count in `cmax_le`).
  -- This gives a bijection `e` from `ZMod n` onto the nonzero classes with
  -- `doubleP B (e i) = e (i+1)` (conjugating `+1` to `doubleP`); lifting through `Sym2.map`
  -- yields `binomSet B ≃ {s : Sym2 (ZMod n) // ¬ s.IsDiag}` conjugating `Dmap B` to the
  -- rotation `Sym2.map (·+1)`. Minimal periods are conjugacy-invariant, so the LHS card
  -- equals the card counted by `rot_period_count n hn3`, namely `n * ((n-1)/2)`.
  have hB : (Finset.univ.filter
        (fun w : Sym2 (PB B) => w ∈ binomSet B ∧
          Function.minimalPeriod (Dmap B) w = n)).card = n * ((n - 1) / 2) := by
    haveI : NeZero n := ⟨by omega⟩
    have hleast : IsLeast {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)} n := by
      have := (cmax_eq_iff B hB3 hBodd).mp hEq
      rw [← hndef] at this
      exact this.2.2
    have hmp : Function.minimalPeriod (doubleP B) (PBmk B 1) = n := minPeriod_doubleP B n hleast
    rw [← rot_period_count n hn3]
    symm
    apply Finset.card_bij (fun s _ => Sym2.map (gZ B n) s)
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨hdiag, hper⟩ := hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · induction s using Sym2.inductionOn with
        | hf a b =>
          simp only [Sym2.map_pair_eq, Sym2.mk_isDiag_iff] at hdiag ⊢
          intro hgab
          exact hdiag (gZ_inj B n hmp hgab)
      · induction s using Sym2.inductionOn with
        | hf a b =>
          simp only [Sym2.map_pair_eq, Sym2.mem_iff]
          push_neg
          exact ⟨fun h => gZ_ne_zero B hBprime hB3 n a h.symm,
                 fun h => gZ_ne_zero B hBprime hB3 n b h.symm⟩
      · rw [minPeriod_map_eq B n hmp]; exact hper
    · intro s1 _ s2 _ heq
      exact Sym2.map.injective (gZ_inj B n hmp) heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨⟨hdiag, hmem⟩, hper⟩ := hw
      induction w using Sym2.inductionOn with
      | hf c d =>
        simp only [Sym2.mk_isDiag_iff] at hdiag
        simp only [Sym2.mem_iff, not_or] at hmem
        obtain ⟨hc0, hd0⟩ := hmem
        obtain ⟨a, ha⟩ := gZ_surj B hBodd hBprime hB3 n hndef hmp c (fun h => hc0 h.symm)
        obtain ⟨b, hb⟩ := gZ_surj B hBodd hBprime hB3 n hndef hmp d (fun h => hd0 h.symm)
        refine ⟨s(a, b), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · simp only [Sym2.mk_isDiag_iff]
            intro hab
            apply hdiag
            rw [← ha, ← hb, hab]
          · have hmapeq : Sym2.map (gZ B n) s(a, b) = s(c, d) := by
              simp only [Sym2.map_pair_eq, ha, hb]
            rw [← minPeriod_map_eq B n hmp s(a, b), hmapeq]
            exact hper
        · simp only [Sym2.map_pair_eq, ha, hb]
  rw [hA, hB, hEq, Nat.mul_div_cancel_left _ (by omega : 0 < n)]

/-- **Statement 3 (Corollary 2, count of maximal cycles).**
Suppose `B` is a prime `p` for which equality holds in Statement 2
(so `c_max(p) = (p-1)/2`). Then the number of terminal cycles of `K_p` of length
exactly `c_max(p)` equals `⌊(c_max(p) - 1)/2⌋`. -/
theorem cor_prime (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (hBprime : B.Prime)
    (hEq : cmax B = (B - 1) / 2) :
    numMaxCycles B = (cmax B - 1) / 2 :=
  numMaxCycles_eq B hB3 hBodd hBprime hEq

end Kaprekar4
