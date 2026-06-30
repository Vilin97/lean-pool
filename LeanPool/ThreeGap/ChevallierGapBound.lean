/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# The combinatorial core of the higher-dimensional three-distance bound (Shutov / Chevallier)

A 2024 result of A. V. Shutov (*Best Diophantine Approximations and Multidimensional Three Distance
Theorem*, arXiv:2410.04257) gives an **elementary, dynamics-free** proof of the higher-dimensional
three-distance *upper bound* — `g_∞ ≤ 2^d + 1` in all dimensions, and the sharp `g_2 ≤ 5` for the
Euclidean metric on `𝕋²` (the Haynes–Marklof bound) — via best *simultaneous* Diophantine
approximation, bypassing homogeneous dynamics **and** the sphere-covering / kissing-number library.

The mechanism has two geometric/Diophantine inputs and one combinatorial core:

* **Chevallier's Lemma (1996).** With the best-simultaneous-approximation denominators `qₙ`, if
  `qₙ ≤ N < qₙ₊₁` and `2qₘ ≤ N < 2qₘ₊₁`, then the number of distinct nearest-neighbour distances is
  `g_dist(α,N) = n − m` or `n − m + 1`.
* **The growth inequality.** `qₙ₊ₖ ≥ qₙ₊₁ + qₙ` for all `n`. Via Lagarias's Theorem 2 one may take
  `K` = the **contact (kissing) number** of the unit ball (`K = 6` for the Euclidean plane); sharper
  norm-specific growth constants are known (Romanov's `K = 4` for `L²`, `d = 2`; Shutov's `2^d` for
  `L^∞`). This is where the geometry of numbers enters — and *only* as this one inequality.
* **The core (this file).** Purely from the above, `g_dist ≤ K + 1`. The denominators more than
  double every `K` steps (`qₙ₊ₖ ≥ qₙ₊₁ + qₙ > 2qₙ`), so the indices `n` and `m` (where `qₙ ≈ N` and
  `qₘ ≈ N/2`) differ by at most `K`.

This is the same best-approximation-denominator arithmetic as the 1-D continued-fraction theory
in `EuclideanCF.lean`, now driving the higher-dimensional bound. The two inputs (Chevallier's Lemma
and the growth inequality) are the substantial geometric pieces still to formalize.

Axiom-clean; elementary.
-/

namespace ThreeGap.Chevallier

/-! ## The best-simultaneous-approximation denominators (Shutov, Sequence 2)

The denominators `qₙ` are the **record minima** of the cost `r q = dist(0, qα mod ℤᵈ)` (the torus
distance of `qα` to the origin): `q₁ = 1`, and `qₙ₊₁ = min{ q > qₙ : r q < r qₙ }`. This is the
higher-dimensional analogue of the continued-fraction convergent denominators (the 1-D record
minima of `‖qα‖`, `EuclideanCF.lean`). We formalize the sequence abstractly from a cost function
`r : ℕ → ℝ` together with the hypothesis that records never stop (Dirichlet / irrationality), and
prove the structural facts the rest of the route consumes: the denominators are **strictly
increasing** and the costs **strictly decreasing**. -/

variable (r : ℕ → ℝ)

/-- Records never stop: every **positive** denominator is beaten by a larger one (Dirichlet's
theorem for the relevant `α` — the best approximations improve without bound). The restriction to
`q ≥ 1` is essential: the cost `r 0 = δ_0 = 0` is the global minimum (the zero denominator has zero
defect), so no `q'` can beat it — a `∀ q` version would be vacuously unsatisfiable. Denominators are
`≥ 1` throughout (`bestDenom` starts at `1`), so this is exactly the right hypothesis. -/
def RecordsContinue : Prop := ∀ q : ℕ, 1 ≤ q → ∃ q' > q, r q' < r q

open Classical in
/-- **The best-approximation denominators** `qₙ`, with the positivity proof carried alongside (so
the
`q ≥ 1` hypothesis of `RecordsContinue` can be discharged at each recursive step). `q₀ = 1`; `qₙ₊₁`
is the smallest `q > qₙ` with `r q < r qₙ`. -/
noncomputable def bestDenomAux (hr : RecordsContinue r) : ℕ → {q : ℕ // 1 ≤ q}
  | 0 => ⟨1, le_refl 1⟩
  | (n + 1) =>
    ⟨Nat.find (hr (bestDenomAux hr n).1 (bestDenomAux hr n).2), by
      have h := (Nat.find_spec (hr (bestDenomAux hr n).1 (bestDenomAux hr n).2)).1
      have := (bestDenomAux hr n).2
      omega⟩

/-- **The best-approximation denominators** `qₙ` (Shutov's Sequence 2): the record minima of the
cost `r`. `q₀ = 1`; `qₙ₊₁` is the *smallest* `q > qₙ` with `r q < r qₙ`. -/
noncomputable def bestDenom (hr : RecordsContinue r) (n : ℕ) : ℕ := (bestDenomAux r hr n).1

/-- Every best-approximation denominator is `≥ 1` (carried by the subtype). -/
theorem bestDenom_pos (hr : RecordsContinue r) (n : ℕ) : 1 ≤ bestDenom r hr n :=
  (bestDenomAux r hr n).2

/-- The defining unfolding of `bestDenom` at a successor (with the positivity proof discharged). -/
theorem bestDenom_succ (hr : RecordsContinue r) (n : ℕ) :
    bestDenom r hr (n + 1) = Nat.find (hr (bestDenom r hr n) (bestDenom_pos r hr n)) := rfl

/-- Each best-approximation denominator is strictly larger than the previous. -/
theorem bestDenom_lt (hr : RecordsContinue r) (n : ℕ) :
    bestDenom r hr n < bestDenom r hr (n + 1) := by
  rw [bestDenom_succ]
  exact (Nat.find_spec (hr (bestDenom r hr n) (bestDenom_pos r hr n))).1

/-- The best-approximation denominators are **strictly increasing**. -/
theorem bestDenom_strictMono (hr : RecordsContinue r) : StrictMono (bestDenom r hr) :=
  strictMono_nat_of_lt_succ (bestDenom_lt r hr)

/-- The costs `r qₙ` are **strictly decreasing** (each new denominator approximates strictly
better). -/
theorem bestDenom_cost_lt (hr : RecordsContinue r) (n : ℕ) :
    r (bestDenom r hr (n + 1)) < r (bestDenom r hr n) := by
  rw [bestDenom_succ]
  exact (Nat.find_spec (hr (bestDenom r hr n) (bestDenom_pos r hr n))).2

/-- **Minimality (the record property).** No denominator strictly between `qₙ` and `qₙ₊₁`
approximates better than `qₙ`: for `qₙ < q < qₙ₊₁`, `r qₙ ≤ r q`. This is exactly what makes the
`qₙ` *best* approximations. -/
theorem bestDenom_record (hr : RecordsContinue r) (n : ℕ) {q : ℕ}
    (hlo : bestDenom r hr n < q) (hhi : q < bestDenom r hr (n + 1)) :
    r (bestDenom r hr n) ≤ r q := by
  by_contra hcon
  rw [not_le] at hcon
  rw [bestDenom_succ] at hhi
  have hmin : Nat.find (hr (bestDenom r hr n) (bestDenom_pos r hr n)) ≤ q :=
    Nat.find_min' (hr (bestDenom r hr n) (bestDenom_pos r hr n)) ⟨hlo, hcon⟩
  omega

/-- The best-approximation denominators, as a strictly-increasing **integer** sequence — the input
to `index_bound` / `gap_count_le`. -/
theorem bestDenom_int_strictMono (hr : RecordsContinue r) :
    StrictMono (fun n => (bestDenom r hr n : ℤ)) := by
  intro a b h
  change (bestDenom r hr a : ℤ) < (bestDenom r hr b : ℤ)
  exact_mod_cast bestDenom_strictMono r hr h

/-- **General bracketing.** A strictly-increasing `ℕ`-sequence `f` brackets every `N ≥ f 0`:
`∃ m, f m ≤ N < f (m+1)`. -/
theorem strictMono_bracket (f : ℕ → ℕ) (hf : StrictMono f) {N : ℕ} (hN : f 0 ≤ N) :
    ∃ m, f m ≤ N ∧ N < f (m + 1) := by
  classical
  have hex : ∃ k, N < f k := by
    refine ⟨N + 1, ?_⟩
    have : N + 1 ≤ f (N + 1) := hf.le_apply
    omega
  have hspec : N < f (Nat.find hex) := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hspec; omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨m, ?_, hm ▸ hspec⟩
  by_contra hc
  rw [not_le] at hc
  have : Nat.find hex ≤ m := Nat.find_min' hex hc
  omega

/-- **Bracketing (the `n`-index).** For any `N ≥ 1` there is `n` with `qₙ ≤ N < qₙ₊₁` — the index
Chevallier's Lemma reads off `N`. -/
theorem bestDenom_bracket (hr : RecordsContinue r) {N : ℕ} (hN : 1 ≤ N) :
    ∃ n, bestDenom r hr n ≤ N ∧ N < bestDenom r hr (n + 1) :=
  strictMono_bracket _ (bestDenom_strictMono r hr)
    (by rw [show bestDenom r hr 0 = 1 from rfl]; omega)

/-- **Bracketing (the `m`-index).** For any `N ≥ 2` there is `m` with `2qₘ ≤ N < 2qₘ₊₁` — the second
index of Chevallier's Lemma (bracketing `N/2`). -/
theorem bestDenom_bracket2 (hr : RecordsContinue r) {N : ℕ} (hN : 2 ≤ N) :
    ∃ m, 2 * bestDenom r hr m ≤ N ∧ N < 2 * bestDenom r hr (m + 1) :=
  strictMono_bracket (fun k => 2 * bestDenom r hr k)
    (fun a b h => by
      change 2 * bestDenom r hr a < 2 * bestDenom r hr b
      have := bestDenom_strictMono r hr h; omega)
    (by show 2 * bestDenom r hr 0 ≤ N; rw [show bestDenom r hr 0 = 1 from rfl]; omega)

/-- **The index bound.** For a strictly increasing positive sequence `q` (the best-approximation
denominators) obeying the growth inequality `qₙ₊₁ + qₙ ≤ qₙ₊ₖ`, the index `n` (with `qₙ ≤ N`) and
the index `m` (with `N < 2qₘ₊₁`) satisfy `n ≤ m + K`. Proof: if `n ≥ m+1+K`, then
`qₙ ≥ qₘ₊₁₊ₖ ≥ qₘ₊₂ + qₘ₊₁ > 2qₘ₊₁ > N ≥ qₙ`, a contradiction. -/
theorem index_bound (q : ℕ → ℤ) (hmono : StrictMono q) (K : ℕ)
    (hgrowth : ∀ n, q (n + 1) + q n ≤ q (n + K))
    {N : ℤ} {m n : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1)) :
    n ≤ m + K := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : m + 1 + K ≤ n := by omega
  have h2 : q (m + 1 + K) ≤ q n := hmono.monotone hle
  have h3 : q (m + 2) + q (m + 1) ≤ q (m + 1 + K) := hgrowth (m + 1)
  have h4 : q (m + 1) < q (m + 2) := hmono (by omega)
  linarith [hnN, hNm, h2, h3, h4]

/-- **Index bound, doubling form.** Same conclusion `n ≤ m + K` from the *weaker* growth hypothesis
`2qₙ ≤ qₙ₊ₖ` (the denominators at least double every `K` steps). This is the elementary form proved
for the sup norm by the orthant pigeonhole (`q_{n+2^d} ≥ 2q_n`, Chevallier survey §2.4.1 /
Lagarias),
and it already suffices: with `N < 2qₘ₊₁ ≤ qₘ₊₁₊ₖ ≤ qₙ ≤ N` we get a contradiction. -/
theorem index_bound_doubling (q : ℕ → ℤ) (hmono : StrictMono q) (K : ℕ)
    (hgrowth : ∀ n, 2 * q n ≤ q (n + K))
    {N : ℤ} {m n : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1)) :
    n ≤ m + K := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : m + 1 + K ≤ n := by omega
  have h2 : q (m + 1 + K) ≤ q n := hmono.monotone hle
  have h3 : 2 * q (m + 1) ≤ q (m + 1 + K) := hgrowth (m + 1)
  linarith [hnN, hNm, h2, h3]

/-- **The gap-count bound, doubling form.** `g ≤ K + 1` from Chevallier's Lemma conclusion and the
doubling growth inequality `2qₙ ≤ qₙ₊ₖ`. For the sup norm with `K = 2^d` (orthant pigeonhole) this
gives the unconditional (modulo Chevallier's Lemma) bound `g_∞ ≤ 2^d + 1`. -/
theorem gap_count_doubling (q : ℕ → ℤ) (hmono : StrictMono q) (K : ℕ)
    (hgrowth : ∀ n, 2 * q n ≤ q (n + K))
    {N : ℤ} {m n g : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1))
    (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ K + 1 := by
  have hnm : n ≤ m + K := index_bound_doubling q hmono K hgrowth hnN hNm
  rcases hg with h | h <;> omega

/-- **The gap-count bound (Shutov's reduction).** Given Chevallier's Lemma conclusion
(`g = n − m` or `n − m + 1`) and the growth inequality with constant `K`, the number of distinct
nearest-neighbour distances is `g ≤ K + 1`. The constant `K` is the growth constant of the
best-approximation denominators (`q_{k+K} ≥ q_{k+1} + q_k`); via Lagarias's Theorem 2 one may take
`K` = the contact (kissing) number of the unit ball, and sharper norm-specific values are known
(see `gap_count_five`). -/
theorem gap_count_le (q : ℕ → ℤ) (hmono : StrictMono q) (K : ℕ)
    (hgrowth : ∀ n, q (n + 1) + q n ≤ q (n + K))
    {N : ℤ} {m n g : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1))
    (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ K + 1 := by
  have hnm : n ≤ m + K := index_bound q hmono K hgrowth hnN hNm
  rcases hg with h | h <;> omega

/-- **`g_∞ ≤ 2^d + 1`** (Shutov's `L^∞` higher-dimensional three-distance bound), as the `K = 2^d`
instance of the reduction — conditional on Chevallier's Lemma and the `L^∞` growth inequality
`qₙ₊₂^d ≥ qₙ₊₁ + qₙ` (Shutov 2024, where `2^d` is the claimed growth constant for the sup norm).
NB: this is the *growth constant*, which need not equal the sup-norm contact number; the theorem
below is exactly the `K = 2^d` instance of `gap_count_le`, valid whenever that growth holds. -/
theorem gap_count_Linfty (d : ℕ) (q : ℕ → ℤ) (hmono : StrictMono q)
    (hgrowth : ∀ n, q (n + 1) + q n ≤ q (n + 2 ^ d))
    {N : ℤ} {m n g : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1))
    (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ 2 ^ d + 1 :=
  gap_count_le q hmono (2 ^ d) hgrowth hnN hNm hg

/-- **`g_2 ≤ 5`** (the sharp Euclidean five-distance bound on `𝕋²`, Haynes–Marklof), as the `K = 4`
instance — conditional on Chevallier's Lemma and the Euclidean growth inequality
`qₙ₊₄ ≥ qₙ₊₁ + qₙ`. **Verified attribution** (Ermakov, arXiv:1002.2713): the `K = 4` here is
*Romanov's improvement* (Moscow Univ. Math. Bull. 61 (2006)), **not** the contact number. The
contact-number route (Lagarias Thm 2) gives only `K = 6` for the Euclidean plane (the kissing number
of circles), hence `g ≤ 7`; Romanov sharpened the growth constant to `4`, yielding `g ≤ 5`. -/
theorem gap_count_five (q : ℕ → ℤ) (hmono : StrictMono q)
    (hgrowth : ∀ n, q (n + 1) + q n ≤ q (n + 4))
    {N : ℤ} {m n g : ℕ} (hnN : q n ≤ N) (hNm : N < 2 * q (m + 1))
    (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ 5 :=
  gap_count_le q hmono 4 hgrowth hnN hNm hg

/-- **The assembled chain over the real best-approximation denominators.** For the record-minima
denominators `qₙ = bestDenom r hr n` (Shutov's Sequence 2), given the growth inequality (constant
`K`) and Chevallier's index structure, the gap count is `g ≤ K + 1`. This ties the *definition* of
best approximation to the bound; the two remaining inputs — Chevallier's Lemma (the hypothesis
`hg`) and the growth inequality (`hgrowth`, where the kissing number enters) — are the geometric
pieces (Chevallier 1996, Lagarias 1980), now sitting on a fully formalized denominator framework. -/
theorem gap_count_bestDenom (hr : RecordsContinue r) (K : ℕ)
    (hgrowth : ∀ n, (bestDenom r hr (n + 1) : ℤ) + bestDenom r hr n ≤ bestDenom r hr (n + K))
    {N : ℤ} {m n g : ℕ} (hnN : (bestDenom r hr n : ℤ) ≤ N)
    (hNm : N < 2 * (bestDenom r hr (m + 1) : ℤ)) (hg : g = n - m ∨ g = n - m + 1) :
    g ≤ K + 1 :=
  gap_count_le (fun k => (bestDenom r hr k : ℤ)) (bestDenom_int_strictMono r hr) K
    hgrowth hnN hNm hg

/-- **Fully assembled: from `N` to the bound.** For every `N ≥ 2`, given only the growth inequality
(constant `K`) and Chevallier's Lemma (supplied as the hypothesis `hChev` relating the gap count to
the two bracketing indices), the number of distinct nearest-neighbour distances is `g ≤ K + 1`. The
bracketing indices `n` (`qₙ ≤ N < qₙ₊₁`) and `m` (`2qₘ ≤ N < 2qₘ₊₁`) are produced internally from
the
denominator framework. So the entire combinatorial machine — definition of best approximation →
bracketing → index bound → gap bound — is closed; the *only* remaining inputs are the two
elementary, dynamics-free geometric results (Chevallier's Lemma and the growth inequality). -/
theorem gap_count_complete (hr : RecordsContinue r) (K : ℕ)
    (hgrowth : ∀ n, (bestDenom r hr (n + 1) : ℤ) + bestDenom r hr n ≤ bestDenom r hr (n + K))
    {N : ℕ} (hN : 2 ≤ N) {g : ℕ}
    (hChev : ∀ n m : ℕ, bestDenom r hr n ≤ N → N < bestDenom r hr (n + 1) →
        2 * bestDenom r hr m ≤ N → N < 2 * bestDenom r hr (m + 1) →
        g = n - m ∨ g = n - m + 1) :
    g ≤ K + 1 := by
  obtain ⟨n, hn1, hn2⟩ := bestDenom_bracket r hr (N := N) (by omega)
  obtain ⟨m, hm1, hm2⟩ := bestDenom_bracket2 r hr (N := N) hN
  exact gap_count_bestDenom r hr K hgrowth (N := (N : ℤ)) (by exact_mod_cast hn1)
    (by exact_mod_cast hm2) (hChev n m hn1 hn2 hm1 hm2)

end ThreeGap.Chevallier
