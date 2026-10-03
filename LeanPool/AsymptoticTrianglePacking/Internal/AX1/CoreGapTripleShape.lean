/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the sub-block grid inside **one** cluster triple

This file carries out the first of the two missing ingredients recorded in
`Nibble.CoreGapGridResidual`: inside a single triple `(U, W, X)` of pairwise `ε₁`-uniform clusters
of densities at least `δ`, it *constructs* the rectangular diagonal family of sub-triples and proves
every clause of `Nibble.AX1.IsSubTripleDesign` that concerns the triple alone.

* `Nibble.AX1.IsSubTripleShape` — the "local" clauses of a design: pairwise disjointness,
  `ε₂`-uniformity and density at least `2ε₂` of the three pairs of each sub-triple, the six
  scale-equalisation inequalities, and edge-disjointness of the family.
* `Nibble.AX1.isSubTripleDesign_of_shape` — a shape plus the "global" clauses (the scale being at
  least `d₀`, the slack, the edge counts and the covering bound) is a design.
* `Nibble.AX1.subTripleShape_grid` — **the construction**: the blocks
  `Nibble.AX1.blockOf` of sizes `sA ≈ τ·d(W,X)`, `sB ≈ τ·d(U,X)`, `sC ≈ τ·d(U,W)` — proportional to
  the *opposite* densities — arranged on the rectangular diagonal grid of
  `Nibble.AX1.rectDesign_pairwise_edgeDisjoint`, form a shape with common triangle-degree scale
  `d = τ·d(U,W)·d(U,X)·d(W,X)`.

Uniformity passes to the blocks by `Nibble.AX1.isUniform_subblock`, their densities are within `ε₁`
of the cluster densities by `Nibble.AX1.edgeDensity_sub_lt_of_isUniform`, and the three
triangle-degree scales are equalised by `Nibble.AX1.scale_window`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BlockSplit
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Positivity
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridDesign


/-! # GridDesignRect -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The general principle -/

omit [Fintype V] [DecidableEq V] in
/-- **A family of sub-triples with pairwise jointly injective index functions is edge-disjoint.**

`IA i`, `IB i`, `IC i` are the indices of the three blocks of the `i`-th sub-triple.  A common edge
of two members determines which *pair* of clusters carries it, and — the blocks of a cluster being
pairwise disjoint and blocks of different clusters being disjoint — the two indices of that pair;
joint injectivity of that pair of index functions then forces the two members to coincide. -/
theorem tripleFamily_pairwise_edgeDisjoint (G : SimpleGraph V) {nA nB nC k : ℕ}
    (Ub Wb Xb : ℕ → Finset V) (IA IB IC : ℕ → ℕ)
    (hIA : ∀ i < k, IA i < nA) (hIB : ∀ i < k, IB i < nB) (hIC : ∀ i < k, IC i < nC)
    (hUU : ∀ a < nA, ∀ b < nA, a ≠ b → Disjoint (Ub a) (Ub b))
    (hWW : ∀ a < nB, ∀ b < nB, a ≠ b → Disjoint (Wb a) (Wb b))
    (hXX : ∀ a < nC, ∀ b < nC, a ≠ b → Disjoint (Xb a) (Xb b))
    (hUW : ∀ a < nA, ∀ b < nB, Disjoint (Ub a) (Wb b))
    (hUX : ∀ a < nA, ∀ b < nC, Disjoint (Ub a) (Xb b))
    (hWX : ∀ a < nB, ∀ b < nC, Disjoint (Wb a) (Xb b))
    (hABinj : ∀ i < k, ∀ i' < k, IA i = IA i' → IB i = IB i' → i = i')
    (hACinj : ∀ i < k, ∀ i' < k, IA i = IA i' → IC i = IC i' → i = i')
    (hBCinj : ∀ i < k, ∀ i' < k, IB i = IB i' → IC i = IC i' → i = i')
    {i : ℕ} (hi : i < k) {i' : ℕ} (hi' : i' < k) (hne : i ≠ i') (x y : V)
    (h : (tripleGraph G (Ub (IA i)) (Wb (IB i)) (Xb (IC i))).Adj x y) :
    ¬ (tripleGraph G (Ub (IA i')) (Wb (IB i')) (Xb (IC i'))).Adj x y := by
  intro h'
  set a := IA i with ha
  set b := IB i with hb
  set c := IC i with hc
  set a' := IA i' with ha'
  set b' := IB i' with hb'
  set c' := IC i' with hc'
  have hai : a < nA := hIA i hi
  have hbi : b < nB := hIB i hi
  have hci : c < nC := hIC i hi
  have hai' : a' < nA := hIA i' hi'
  have hbi' : b' < nB := hIB i' hi'
  have hci' : c' < nC := hIC i' hi'
  have hcross : pairIn (Ub a) (Wb b) x y ∨ pairIn (Ub a) (Xb c) x y ∨ pairIn (Wb b) (Xb c) x y :=
    crossAdj_iff_pairIn.mp h.2
  have hcross' : pairIn (Ub a') (Wb b') x y ∨ pairIn (Ub a') (Xb c') x y
      ∨ pairIn (Wb b') (Xb c') x y := crossAdj_iff_pairIn.mp h'.2
  have hUeq : ∀ p q, p < nA → q < nA → ¬ Disjoint (Ub p) (Ub q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hUU p hp q hq hpq)
  have hWeq : ∀ p q, p < nB → q < nB → ¬ Disjoint (Wb p) (Wb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hWW p hp q hq hpq)
  have hXeq : ∀ p q, p < nC → q < nC → ¬ Disjoint (Xb p) (Xb q) → p = q := by
    intro p q hp hq hd; by_contra hpq; exact hd (hXX p hp q hq hpq)
  refine hne ?_
  rcases hcross with hUW1 | hUX1 | hWX1
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · obtain ⟨h1, h2⟩ := pairIn_match hUW1 hUW2 (hUW a hai b' hbi')
        (Disjoint.symm (hUW a' hai' b hbi))
      exact hABinj i hi i' hi' (hUeq a a' hai hai' h1) (hWeq b b' hbi hbi' h2)
    · exact absurd (pairIn_absurd (pairIn_symm hUW1) hUX2
        (Disjoint.symm (hUW a' hai' b hbi)) (hWX b hbi c' hci')) not_false
    · exact absurd (pairIn_absurd hUW1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hUX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hUX1 hUX2 (hUX a hai c' hci')
        (Disjoint.symm (hUX a' hai' c hci))
      exact hACinj i hi i' hi' (hUeq a a' hai hai' h1) (hXeq c c' hci hci' h2)
    · exact absurd (pairIn_absurd hUX1 hWX2 (hUW a hai b' hbi') (hUX a hai c' hci')) not_false
  · rcases hcross' with hUW2 | hUX2 | hWX2
    · exact absurd (pairIn_absurd (pairIn_symm hWX1) hUW2
        (Disjoint.symm (hUX a' hai' c hci)) (Disjoint.symm (hWX b' hbi' c hci))) not_false
    · exact absurd (pairIn_absurd hUX2 hWX1 (hUW a' hai' b hbi) (hUX a' hai' c hci)) not_false
    · obtain ⟨h1, h2⟩ := pairIn_match hWX1 hWX2 (hWX b hbi c' hci')
        (Disjoint.symm (hWX b' hbi' c hci))
      exact hBCinj i hi i' hi' (hWeq b b' hbi hbi' h1) (hXeq c c' hci hci' h2)

/-! ### The rectangular diagonal indices -/

/-- The `U`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxA (nA nC i : ℕ) : ℕ := (i / nC + i % nC) % nA

/-- The `W`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxB (nC i : ℕ) : ℕ := i / nC

/-- The `X`-block index of the `i`-th member of the rectangular diagonal design. -/
def rectIdxC (nC i : ℕ) : ℕ := i % nC

theorem rectIdxA_lt {nA nC : ℕ} (hnA : 0 < nA) (i : ℕ) : rectIdxA nA nC i < nA :=
  Nat.mod_lt _ hnA

theorem rectIdxB_lt {nB nC i : ℕ} (hi : i < nB * nC) : rectIdxB nC i < nB := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)

theorem rectIdxC_lt {nC : ℕ} (hnC : 0 < nC) (i : ℕ) : rectIdxC nC i < nC :=
  Nat.mod_lt _ hnC

/-- **The `U`–`W` block pair is used at most once** — provided there are at least as many `U`-blocks
as `X`-blocks. -/
theorem rectIdx_AB_inj {nA nB nC i i' : ℕ} (hCA : nC ≤ nA) (hi : i < nB * nC) (hi' : i' < nB * nC)
    (hA : rectIdxA nA nC i = rectIdxA nA nC i') (hB : rectIdxB nC i = rectIdxB nC i') : i = i' := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
  refine eq_of_div_mod_eq hB ?_
  simp only [rectIdxA, rectIdxB] at hA hB
  rw [hB] at hA
  have h1 : (i' / nC + i % nC) % nA = (i' / nC + i' % nC) % nA := hA
  have hr : i % nC < nA := lt_of_lt_of_le (Nat.mod_lt _ hnC) hCA
  have hr' : i' % nC < nA := lt_of_lt_of_le (Nat.mod_lt _ hnC) hCA
  have h2 : (i % nC) % nA = (i' % nC) % nA :=
    Nat.ModEq.add_left_cancel' (i' / nC) (by simpa [Nat.ModEq] using h1)
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h2

/-- **The `U`–`X` block pair is used at most once** — provided there are at least as many `U`-blocks
as `W`-blocks. -/
theorem rectIdx_AC_inj {nA nB nC i i' : ℕ} (hBA : nB ≤ nA) (hi : i < nB * nC) (hi' : i' < nB * nC)
    (hA : rectIdxA nA nC i = rectIdxA nA nC i') (hC : rectIdxC nC i = rectIdxC nC i') : i = i' := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnB : 0 < nB := by
    rcases Nat.eq_zero_or_pos nB with rfl | h
    · simp at hi
    · exact h
  have hnA : 0 < nA := lt_of_lt_of_le hnB hBA
  refine eq_of_div_mod_eq ?_ hC
  simp only [rectIdxA, rectIdxC] at hA hC
  rw [hC] at hA
  have h1 : (i' % nC + i / nC) % nA = (i' % nC + i' / nC) % nA := by
    rw [Nat.add_comm (i' % nC) (i / nC), Nat.add_comm (i' % nC) (i' / nC)]; exact hA
  have h2 : (i / nC) % nA = (i' / nC) % nA :=
    Nat.ModEq.add_left_cancel' (i' % nC) (by simpa [Nat.ModEq] using h1)
  have hdi : i / nC < nA := lt_of_lt_of_le (rectIdxB_lt hi) hBA
  have hdi' : i' / nC < nA := lt_of_lt_of_le (rectIdxB_lt hi') hBA
  rwa [Nat.mod_eq_of_lt hdi, Nat.mod_eq_of_lt hdi'] at h2

/-- **The `W`–`X` block pair is used at most once.** -/
theorem rectIdx_BC_inj {nC i i' : ℕ}
    (hB : rectIdxB nC i = rectIdxB nC i') (hC : rectIdxC nC i = rectIdxC nC i') : i = i' :=
  eq_of_div_mod_eq hB hC

/-! ### The rectangular design -/

omit [Fintype V] [DecidableEq V] in
/-- **The rectangular diagonal design is edge-disjoint.**  The clusters `U`, `W`, `X` are split into
`nA`, `nB`, `nC` pairwise disjoint blocks with `nB, nC ≤ nA`, and the `nB · nC` sub-triples
`(U_{(j+k) mod nA}, W_j, X_k)` have pairwise no common edge. -/
theorem rectDesign_pairwise_edgeDisjoint (G : SimpleGraph V) {nA nB nC : ℕ}
    (Ub Wb Xb : ℕ → Finset V) (hBA : nB ≤ nA) (hCA : nC ≤ nA)
    (hUU : ∀ a < nA, ∀ b < nA, a ≠ b → Disjoint (Ub a) (Ub b))
    (hWW : ∀ a < nB, ∀ b < nB, a ≠ b → Disjoint (Wb a) (Wb b))
    (hXX : ∀ a < nC, ∀ b < nC, a ≠ b → Disjoint (Xb a) (Xb b))
    (hUW : ∀ a < nA, ∀ b < nB, Disjoint (Ub a) (Wb b))
    (hUX : ∀ a < nA, ∀ b < nC, Disjoint (Ub a) (Xb b))
    (hWX : ∀ a < nB, ∀ b < nC, Disjoint (Wb a) (Xb b))
    {i : ℕ} (hi : i < nB * nC) {i' : ℕ} (hi' : i' < nB * nC) (hne : i ≠ i') (x y : V)
    (h : (tripleGraph G (Ub (rectIdxA nA nC i)) (Wb (rectIdxB nC i))
      (Xb (rectIdxC nC i))).Adj x y) :
    ¬ (tripleGraph G (Ub (rectIdxA nA nC i')) (Wb (rectIdxB nC i'))
        (Xb (rectIdxC nC i'))).Adj x y := by
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with rfl | hpos
    · simp at hi
    · exact hpos
  have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
  refine tripleFamily_pairwise_edgeDisjoint (nA := nA) (nB := nB) (nC := nC) (k := nB * nC)
    G Ub Wb Xb _ _ _ (fun j _ => rectIdxA_lt hnA j) (fun j hj => rectIdxB_lt hj)
    (fun j _ => rectIdxC_lt hnC j) hUU hWW hXX hUW hUX hWX
    (fun p hp p' hp' h1 h2 => rectIdx_AB_inj hCA hp hp' h1 h2)
    (fun p hp p' hp' h1 h2 => rectIdx_AC_inj hBA hp hp' h1 h2)
    (fun p _ p' _ h1 h2 => rectIdx_BC_inj h1 h2) hi hi' hne x y h

end Nibble.AX1

end



/-! # GridScale -/

public section

namespace Nibble.AX1

/-- Elementary two-variable bound: shrinking both factors by `E` costs at most `2E`. -/
private theorem shrink_lower {x y E : ℝ} (hE : 0 ≤ E) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    x * y - 2 * E ≤ (x - E) * (y - E) := by
  linarith only [mul_nonneg hE (by linarith : (0:ℝ) ≤ 2 - x - y), sq_nonneg E]

/-- Elementary two-variable bound: growing both factors by `E ≤ 1` costs at most `3E`. -/
private theorem grow_upper {x y E : ℝ} (hE : 0 ≤ E) (hE1 : E ≤ 1) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (x + E) * (y + E) ≤ x * y + 3 * E := by
  nlinarith [mul_nonneg hE (by linarith : (0:ℝ) ≤ 1 - E)]

/-- The purely multiplicative heart of the scale window: with `τ` large enough compared with the
error `e + 2ε`, the products `(xy ∓ cE)(τz ± 1)` are within a factor `1 ± μ` of `τxyz`. -/
private theorem scale_core {x y z τ μ δ ε e : ℝ}
    (hz1 : z ≤ 1) (hE0 : 0 < e + 2 * ε) (hEone : e + 2 * ε ≤ 1 / 12)
    (hxy1 : x * y ≤ 1) (hT2 : 2 ≤ μ * τ * δ ^ 3) (hmul : μ * τ * δ ^ 3 ≤ μ * (τ * (x * y * z)))
    (hEτ : (e + 2 * ε) * τ ≤ μ * τ * δ ^ 3 / 12) (hτpos : 0 < τ) :
    ((1 - μ) * (τ * (x * y * z)) ≤ (x * y - 2 * (e + 2 * ε)) * (τ * z - 1))
      ∧ ((x * y + 3 * (e + 2 * ε)) * (τ * z + 1) ≤ (1 + μ) * (τ * (x * y * z))) := by
  have h1 : (e + 2 * ε) * τ * z ≤ (e + 2 * ε) * τ := by
    have : 0 ≤ (e + 2 * ε) * τ := by positivity
    nlinarith only [hz1, this]
  exact ⟨by linarith, by linarith⟩

/-- Lower half of the window, from the multiplicative core. -/
private theorem window_lower {x y z x' y' s τ μ ε e : ℝ}
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hE0 : 0 < e + 2 * ε) (hε : 0 < ε)
    (hxE : 0 < x - (e + 2 * ε)) (hyE : 0 < y - (e + 2 * ε))
    (hx'lo : x - e ≤ x') (hy'lo : y - e ≤ y')
    (hslo : τ * z - 1 ≤ s) (hτz : 2 ≤ τ * z)
    (hcore : (1 - μ) * (τ * (x * y * z)) ≤ (x * y - 2 * (e + 2 * ε)) * (τ * z - 1)) :
    (1 - μ) * (τ * (x * y * z)) ≤ (x' - ε) * (y' - 2 * ε) * s := by
  have step1 : x * y - 2 * (e + 2 * ε) ≤ (x - (e + 2 * ε)) * (y - (e + 2 * ε)) :=
    shrink_lower hE0.le hx1 hy1
  have step1' : (x - (e + 2 * ε)) * (y - (e + 2 * ε)) ≤ (x' - ε) * (y' - 2 * ε) :=
    mul_le_mul (by linarith) (by linarith) hyE.le (by linarith)
  have hp : 0 ≤ (x' - ε) * (y' - 2 * ε) := mul_nonneg (by linarith) (by linarith)
  have h1 : (x * y - 2 * (e + 2 * ε)) * (τ * z - 1) ≤ (x' - ε) * (y' - 2 * ε) * (τ * z - 1) :=
    mul_le_mul_of_nonneg_right (le_trans step1 step1') (by linarith)
  have h2 : (x' - ε) * (y' - 2 * ε) * (τ * z - 1) ≤ (x' - ε) * (y' - 2 * ε) * s :=
    mul_le_mul_of_nonneg_left hslo hp
  linarith only [hcore, h1, h2]

/-- Upper half of the window, from the multiplicative core. -/
private theorem window_upper {x y z x' y' s τ μ ε e : ℝ}
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hE0 : 0 < e + 2 * ε) (hE1 : e + 2 * ε ≤ 1) (hε : 0 < ε)
    (hx'hi : x' ≤ x + e) (hy'hi : y' ≤ y + e)
    (hx'lo : x - e ≤ x') (hy'lo : y - e ≤ y')
    (hxE : 0 < x - (e + 2 * ε)) (hyE : 0 < y - (e + 2 * ε))
    (hshi : s ≤ τ * z + 1) (hτz : 2 ≤ τ * z)
    (hcore : (x * y + 3 * (e + 2 * ε)) * (τ * z + 1) ≤ (1 + μ) * (τ * (x * y * z))) :
    (x' + ε) * (y' + 2 * ε) * s ≤ (1 + μ) * (τ * (x * y * z)) := by
  have step1 : (x' + ε) * (y' + 2 * ε) ≤ x * y + 3 * (e + 2 * ε) := by
    have h1 : (x' + ε) * (y' + 2 * ε) ≤ (x + (e + 2 * ε)) * (y + (e + 2 * ε)) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : (x + (e + 2 * ε)) * (y + (e + 2 * ε)) ≤ x * y + 3 * (e + 2 * ε) :=
      grow_upper hE0.le hE1 hx1 hy1
    linarith only [h1, h2]
  have hpos : 0 ≤ (x' + ε) * (y' + 2 * ε) := mul_nonneg (by linarith) (by linarith)
  have h1 : (x' + ε) * (y' + 2 * ε) * s ≤ (x' + ε) * (y' + 2 * ε) * (τ * z + 1) :=
    mul_le_mul_of_nonneg_left hshi hpos
  have h2 : (x' + ε) * (y' + 2 * ε) * (τ * z + 1) ≤ (x * y + 3 * (e + 2 * ε)) * (τ * z + 1) :=
    mul_le_mul_of_nonneg_right step1 (by linarith)
  linarith only [hcore, h1, h2]

/-- **Scale equalisation.**  If the three cluster densities `x, y, z` lie in `[δ, 1]`, the measured
sub-block densities `x', y'` are within `e` of `x, y`, the block size `s` is within `1` of `τ·z`,
the total error satisfies `e + 2ε ≤ μδ³/12` and the scale satisfies `τ ≥ 2/(μδ³)`, then the
two-sided codegree count `(x' ∓ ε)(y' ∓ 2ε)·s` lies in the window `(1 ± μ)·d` around the common
scale `d = τ·x·y·z`. -/
theorem scale_window {x y z x' y' s τ d δ μ ε e : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : δ ≤ x) (hx1 : x ≤ 1) (hy : δ ≤ y) (hy1 : y ≤ 1) (hz : δ ≤ z) (hz1 : z ≤ 1)
    (hx' : |x' - x| ≤ e) (hy' : |y' - y| ≤ e)
    (hs : |s - τ * z| ≤ 1)
    (he : 0 ≤ e) (hε : 0 < ε)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hE : e + 2 * ε ≤ μ * δ ^ 3 / 12)
    (hτ : 2 / (μ * δ ^ 3) ≤ τ)
    (hd : d = τ * (x * y * z)) :
    (1 - μ) * d ≤ (x' - ε) * (y' - 2 * ε) * s ∧ (x' + ε) * (y' + 2 * ε) * s ≤ (1 + μ) * d := by
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  have hμδ : (0:ℝ) < μ * δ ^ 3 := by positivity
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hT2 : 2 ≤ μ * τ * δ ^ 3 := by
    rw [div_le_iff₀ hμδ] at hτ; linarith only [hτ]
  have hδcube : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, mul_pos hδ0 hδ0]
  have hE0 : 0 < e + 2 * ε := by linarith only [he, hε]
  have hEone : e + 2 * ε ≤ 1 / 12 := by nlinarith only [hz, hz1, hμ0, hμ1, hE, hδcube]
  have hEδ : e + 2 * ε ≤ δ / 12 := by nlinarith only [hμ0, hμ1, hE, hδcube, hE0]
  have hτ1 : 1 ≤ τ := by nlinarith
  have hz0 : 0 ≤ z := le_trans hδ0.le hz
  have hτz : 2 ≤ τ * z := by nlinarith
  have hxy : δ * δ ≤ x * y := by nlinarith
  have hA : δ ^ 3 ≤ x * y * z := by nlinarith
  have hxy1 : x * y ≤ 1 := by nlinarith
  have hmul : μ * τ * δ ^ 3 ≤ μ * (τ * (x * y * z)) := by
    calc μ * τ * δ ^ 3 = (μ * τ) * δ ^ 3 := by ring
      _ ≤ (μ * τ) * (x * y * z) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = μ * (τ * (x * y * z)) := by ring
  have hEτ : (e + 2 * ε) * τ ≤ μ * τ * δ ^ 3 / 12 := by
    calc (e + 2 * ε) * τ ≤ (μ * δ ^ 3 / 12) * τ := mul_le_mul_of_nonneg_right hE hτpos.le
      _ = μ * τ * δ ^ 3 / 12 := by ring
  have hx'lo : x - e ≤ x' := by have := abs_le.mp hx'; linarith only [this.1]
  have hx'hi : x' ≤ x + e := by have := abs_le.mp hx'; linarith only [this.2]
  have hy'lo : y - e ≤ y' := by have := abs_le.mp hy'; linarith only [this.1]
  have hy'hi : y' ≤ y + e := by have := abs_le.mp hy'; linarith only [this.2]
  have hslo : τ * z - 1 ≤ s := by have := abs_le.mp hs; linarith only [this.1]
  have hshi : s ≤ τ * z + 1 := by have := abs_le.mp hs; linarith only [this.2]
  have hxE : 0 < x - (e + 2 * ε) := by linarith
  have hyE : 0 < y - (e + 2 * ε) := by linarith
  obtain ⟨core1, core2⟩ := scale_core (δ := δ) hz1 hE0 hEone hxy1 hT2 hmul hEτ hτpos
  subst hd
  exact ⟨window_lower hx1 hy1 hE0 hε hxE hyE hx'lo hy'lo hslo hτz core1,
    window_upper hx1 hy1 hE0 (by linarith) hε hx'hi hy'hi hx'lo hy'lo hxE hyE hshi hτz core2⟩

end Nibble.AX1

end



/-! # CoreGapSubblock -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type}

/-- A pair of subsets of relative size at least `α ≥ ε` of an `ε`-uniform pair has density within
`ε` of the density of the pair. -/
theorem edgeDensity_sub_lt_of_isUniform (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A' B' : Finset V} {ε α : ℝ} (hU : G.IsUniform ε A B) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hεα : ε ≤ α) (hcardA : α * (#A : ℝ) ≤ (#A' : ℝ)) (hcardB : α * (#B : ℝ) ≤ (#B' : ℝ)) :
    |(G.edgeDensity A' B' : ℝ) - (G.edgeDensity A B : ℝ)| < ε := by
  refine hU hA' hB' ?_ ?_
  · calc (#A : ℝ) * ε ≤ (#A : ℝ) * α := by
          have : (0 : ℝ) ≤ (#A : ℝ) := Nat.cast_nonneg _
          nlinarith only [hεα]
      _ = α * (#A : ℝ) := by ring
      _ ≤ (#A' : ℝ) := hcardA
  · calc (#B : ℝ) * ε ≤ (#B : ℝ) * α := by
          have : (0 : ℝ) ≤ (#B : ℝ) := Nat.cast_nonneg _
          nlinarith only [hεα]
      _ = α * (#B : ℝ) := by ring
      _ ≤ (#B' : ℝ) := hcardB

/-- **Uniformity passes to large sub-blocks.**  If `(A, B)` is `ε`-uniform and `A' ⊆ A`, `B' ⊆ B`
have relative size at least `α`, with `ε ≤ α ≤ 1/2`, then `(A', B')` is `(ε/α)`-uniform.

The proof is the obvious one: a subset of `A'` of relative size `ε/α` has absolute size at least
`ε|A|`, so uniformity of `(A, B)` applies to it and to `(A', B')` itself, and the two densities are
each within `ε` of `d(A, B)`, hence within `2ε ≤ ε/α` of each other. -/
theorem isUniform_subblock (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A' B' : Finset V} {ε α : ℝ} (hU : G.IsUniform ε A B) (hε : 0 < ε) (hA' : A' ⊆ A)
    (hB' : B' ⊆ B) (hεα : ε ≤ α) (hα : 2 * α ≤ 1)
    (hcardA : α * (#A : ℝ) ≤ (#A' : ℝ)) (hcardB : α * (#B : ℝ) ≤ (#B' : ℝ)) :
    G.IsUniform (ε / α) A' B' := by
  have hα0 : 0 < α := lt_of_lt_of_le hε hεα
  have hbase : |(G.edgeDensity A' B' : ℝ) - (G.edgeDensity A B : ℝ)| < ε :=
    edgeDensity_sub_lt_of_isUniform G hU hA' hB' hεα hcardA hcardB
  intro A'' hA'' B'' hB'' hcA hcB
  -- the sub-sub-blocks are large in `A` and `B`
  have hcA' : (#A : ℝ) * ε ≤ (#A'' : ℝ) := by
    have h1 : (#A : ℝ) * ε = α * (#A : ℝ) * (ε / α) := by field_simp
    have h2 : α * (#A : ℝ) * (ε / α) ≤ (#A' : ℝ) * (ε / α) := by
      have : (0 : ℝ) ≤ ε / α := le_of_lt (div_pos hε hα0)
      nlinarith only [hcardA, this]
    linarith only [hcA, h1.le, h2]
  have hcB' : (#B : ℝ) * ε ≤ (#B'' : ℝ) := by
    have h1 : (#B : ℝ) * ε = α * (#B : ℝ) * (ε / α) := by field_simp
    have h2 : α * (#B : ℝ) * (ε / α) ≤ (#B' : ℝ) * (ε / α) := by
      have : (0 : ℝ) ≤ ε / α := le_of_lt (div_pos hε hα0)
      nlinarith only [hcardB, this]
    linarith only [hcB, h1.le, h2]
  have hsub : |(G.edgeDensity A'' B'' : ℝ) - (G.edgeDensity A B : ℝ)| < ε :=
    hU (hA''.trans hA') (hB''.trans hB') hcA' hcB'
  have hεα' : 2 * ε ≤ ε / α := by
    rw [le_div_iff₀ hα0]
    nlinarith only [hε, hα]
  rw [abs_lt] at hbase hsub ⊢
  constructor <;> linarith only [hbase, hsub, hεα']

end Nibble.AX1

end


/-! # CoreGapTripleShape -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The local clauses of a sub-triple design.**  Everything in
`Nibble.AX1.IsSubTripleDesign` that refers only to the sub-triples themselves: the three parts of
each sub-triple are disjoint, pairwise `ε₂`-uniform and of density at least `2ε₂`, the three
triangle-degree scales of each sub-triple agree with a common `d i` to within `μ₂`, and the
tripartite graphs of the family are pairwise edge-disjoint. -/
@[expose]
def IsSubTripleShape (G : SimpleGraph V) [DecidableRel G.Adj] (ε₂ μ₂ : ℝ) (k : ℕ)
    (A B C : ℕ → Finset V) (d : ℕ → ℝ) : Prop :=
  (∀ i < k, Disjoint (A i) (B i)) ∧
  (∀ i < k, Disjoint (A i) (C i)) ∧
  (∀ i < k, Disjoint (B i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (B i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (B i) (C i)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (B i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (C i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (B i) (C i) : ℝ)) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (C i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(C i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (C i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(C i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(B i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(B i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) - 2 * ε₂) * (#(A i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) + 2 * ε₂) * (#(A i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, ∀ j < k, i ≠ j → ∀ x y,
    (tripleGraph G (A i) (B i) (C i)).Adj x y → ¬ (tripleGraph G (A j) (B j) (C j)).Adj x y)

/-- **A shape together with the global clauses is a design.** -/
theorem isSubTripleDesign_of_shape (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ ε₂ μ₂ t : ℝ} {k : ℕ} {A B C : ℕ → Finset V} {d Elo : ℕ → ℝ}
    (hshape : IsSubTripleShape G ε₂ μ₂ k A B C d)
    (hε₂ : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (ht : 0 < t) (hη : 0 ≤ η) (hμ₂ : μ₂ ≤ μ)
    (hd₀ : ∀ i < k, d₀ ≤ d i) (hdnn : ∀ i < k, 0 ≤ d i)
    (hslack : ∀ i < k, 2 * t ≤ (μ - μ₂) * d i)
    (hElo : ∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ))
    (hexc : ∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * (Fintype.card V : ℝ)
      ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i)))
    (hcover : nu3star G ≤ (∑ i ∈ Finset.range k,
      (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2) :
    IsSubTripleDesign G ε μ η d₀ ε₂ μ₂ t k A B C d Elo := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hshape
  exact ⟨hε₂, hε₂1, ht, hη, hμ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    hd₀, hdnn, hslack, h16, hElo, hexc, hcover⟩

/-! ### The construction inside one cluster triple -/

omit [Fintype V] in
/-- **The sub-block grid of one cluster triple is a shape.**

The clusters `U`, `W`, `X` are pairwise `ε₁`-uniform of densities `x = d(U,W)`, `y = d(U,X)`,
`z = d(W,X)` in `[δ, 1]`.  Split `U` into `nA` blocks of size `sA ≈ τ·z`, `W` into `nB` blocks of
size `sB ≈ τ·y` and `X` into `nC` blocks of size `sC ≈ τ·x` — each block size proportional to the
density of the *opposite* pair, and each block of relative size at least `α` in its cluster — and
take the `nB·nC` diagonal sub-triples of `Nibble.AX1.rectDesign_pairwise_edgeDisjoint`.  Then, at
uniformity scale `ε₂ = ε₁/α`, this family is a shape with the single triangle-degree scale
`d = τ·x·y·z`. -/
theorem subTripleShape_grid (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    {δ μ₂ ε₁ α τ : ℝ} {sA sB sC nA nB nC : ℕ}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X)
    (huUW : G.IsUniform ε₁ U W) (huUX : G.IsUniform ε₁ U X) (huWX : G.IsUniform ε₁ W X)
    (hε₁ : 0 < ε₁) (hαε : ε₁ ≤ α) (hα2 : 2 * α ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hμ0 : 0 < μ₂) (hμ1 : μ₂ ≤ 1)
    (hx : δ ≤ (G.edgeDensity U W : ℝ)) (hy : δ ≤ (G.edgeDensity U X : ℝ))
    (hz : δ ≤ (G.edgeDensity W X : ℝ))
    (hErr : ε₁ + 2 * (ε₁ / α) ≤ μ₂ * δ ^ 3 / 12)
    (hdense : 2 * (ε₁ / α) + ε₁ ≤ δ)
    (hτ : 2 / (μ₂ * δ ^ 3) ≤ τ)
    (hsA : |(sA : ℝ) - τ * (G.edgeDensity W X : ℝ)| ≤ 1)
    (hsB : |(sB : ℝ) - τ * (G.edgeDensity U X : ℝ)| ≤ 1)
    (hsC : |(sC : ℝ) - τ * (G.edgeDensity U W : ℝ)| ≤ 1)
    (hsA0 : 0 < sA) (hsB0 : 0 < sB) (hsC0 : 0 < sC)
    (hfitA : nA * sA ≤ #U) (hfitB : nB * sB ≤ #W) (hfitC : nC * sC ≤ #X)
    (hrelA : α * (#U : ℝ) ≤ (sA : ℝ)) (hrelB : α * (#W : ℝ) ≤ (sB : ℝ))
    (hrelC : α * (#X : ℝ) ≤ (sC : ℝ))
    (hBA : nB ≤ nA) (hCA : nC ≤ nA) :
    IsSubTripleShape G (ε₁ / α) μ₂ (nB * nC)
      (fun i => blockOf U sA (rectIdxA nA nC i))
      (fun i => blockOf W sB (rectIdxB nC i))
      (fun i => blockOf X sC (rectIdxC nC i))
      (fun _ => τ * ((G.edgeDensity U W : ℝ) * (G.edgeDensity U X : ℝ)
        * (G.edgeDensity W X : ℝ))) := by
  classical
  set x : ℝ := (G.edgeDensity U W : ℝ) with hxdef
  set y : ℝ := (G.edgeDensity U X : ℝ) with hydef
  set z : ℝ := (G.edgeDensity W X : ℝ) with hzdef
  have hx1 : x ≤ 1 := by rw [hxdef]; exact_mod_cast G.edgeDensity_le_one U W
  have hy1 : y ≤ 1 := by rw [hydef]; exact_mod_cast G.edgeDensity_le_one U X
  have hz1 : z ≤ 1 := by rw [hzdef]; exact_mod_cast G.edgeDensity_le_one W X
  have hε₂ : 0 < ε₁ / α := div_pos hε₁ (lt_of_lt_of_le hε₁ hαε)
  -- block index bounds
  have hnCpos : ∀ i, i < nB * nC → 0 < nC := by
    intro i hi
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnBpos : ∀ i, i < nB * nC → 0 < nB := by
    intro i hi
    rcases Nat.eq_zero_or_pos nB with rfl | h
    · simp at hi
    · exact h
  -- the blocks and their cardinalities
  have hcardA : ∀ i < nB * nC, #(blockOf U sA (rectIdxA nA nC i)) = sA := by
    intro i hi
    have hnC := hnCpos i hi
    have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
    have ha : rectIdxA nA nC i < nA := rectIdxA_lt hnA i
    refine card_blockOf U hsA0 (le_trans ?_ hfitA)
    exact Nat.mul_le_mul_right _ ha
  have hcardB : ∀ i < nB * nC, #(blockOf W sB (rectIdxB nC i)) = sB := by
    intro i hi
    have hb : rectIdxB nC i < nB := rectIdxB_lt hi
    refine card_blockOf W hsB0 (le_trans ?_ hfitB)
    exact Nat.mul_le_mul_right _ hb
  have hcardC : ∀ i < nB * nC, #(blockOf X sC (rectIdxC nC i)) = sC := by
    intro i hi
    have hc : rectIdxC nC i < nC := rectIdxC_lt (hnCpos i hi) i
    refine card_blockOf X hsC0 (le_trans ?_ hfitC)
    exact Nat.mul_le_mul_right _ hc
  -- uniformity of the block pairs
  have huAB : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf U sA (rectIdxA nA nC i)) (blockOf W sB (rectIdxB nC i)) := by
    intro i hi
    refine isUniform_subblock G huUW hε₁ (blockOf_subset U sA _) (blockOf_subset W sB _)
      hαε hα2 ?_ ?_
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardB i hi]; exact hrelB
  have huAC : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf U sA (rectIdxA nA nC i)) (blockOf X sC (rectIdxC nC i)) := by
    intro i hi
    refine isUniform_subblock G huUX hε₁ (blockOf_subset U sA _) (blockOf_subset X sC _)
      hαε hα2 ?_ ?_
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardC i hi]; exact hrelC
  have huBC : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf W sB (rectIdxB nC i)) (blockOf X sC (rectIdxC nC i)) := by
    intro i hi
    refine isUniform_subblock G huWX hε₁ (blockOf_subset W sB _) (blockOf_subset X sC _)
      hαε hα2 ?_ ?_
    · rw [hcardB i hi]; exact hrelB
    · rw [hcardC i hi]; exact hrelC
  -- the block densities are within `ε₁` of the cluster densities
  have hdAB : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf U sA (rectIdxA nA nC i)) (blockOf W sB (rectIdxB nC i)) : ℝ)
        - x| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huUW (blockOf_subset U sA _)
      (blockOf_subset W sB _) hαε ?_ ?_)
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardB i hi]; exact hrelB
  have hdAC : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf U sA (rectIdxA nA nC i)) (blockOf X sC (rectIdxC nC i)) : ℝ)
        - y| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huUX (blockOf_subset U sA _)
      (blockOf_subset X sC _) hαε ?_ ?_)
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardC i hi]; exact hrelC
  have hdBC : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf W sB (rectIdxB nC i)) (blockOf X sC (rectIdxC nC i)) : ℝ)
        - z| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huWX (blockOf_subset W sB _)
      (blockOf_subset X sC _) hαε ?_ ?_)
    · rw [hcardB i hi]; exact hrelB
    · rw [hcardC i hi]; exact hrelC
  -- densities of the blocks are at least `2ε₂`
  have hlow : ∀ (u v : ℝ), δ ≤ v → |u - v| ≤ ε₁ → 2 * (ε₁ / α) ≤ u := by
    intro u v hv habs
    have := (abs_le.mp habs).1
    linarith
  refine ⟨?_, ?_, ?_, huAB, huAC, huBC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
      (Finset.disjoint_of_subset_right (blockOf_subset W sB _) hUW)
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
      (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hUX)
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset W sB _)
      (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hWX)
  · exact fun i hi => hlow _ _ hx (hdAB i hi)
  · exact fun i hi => hlow _ _ hy (hdAC i hi)
  · exact fun i hi => hlow _ _ hz (hdBC i hi)
  -- the three scale windows
  · intro i hi
    rw [hcardC i hi]
    exact (scale_window (x := y) (y := z) (z := x) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdAC i hi) (hdBC i hi) hsC hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).1
  · intro i hi
    rw [hcardC i hi]
    exact (scale_window (x := y) (y := z) (z := x) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdAC i hi) (hdBC i hi) hsC hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).2
  · intro i hi
    rw [hcardB i hi]
    exact (scale_window (x := x) (y := z) (z := y) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdAB i hi) (hdBC i hi) hsB hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).1
  · intro i hi
    rw [hcardB i hi]
    exact (scale_window (x := x) (y := z) (z := y) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdAB i hi) (hdBC i hi) hsB hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).2
  · intro i hi
    rw [hcardA i hi]
    exact (scale_window (x := x) (y := y) (z := z) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdAB i hi) (hdAC i hi) hsA hε₁.le hε₂ hμ0 hμ1 hErr hτ
      rfl).1
  · intro i hi
    rw [hcardA i hi]
    exact (scale_window (x := x) (y := y) (z := z) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdAB i hi) (hdAC i hi) hsA hε₁.le hε₂ hμ0 hμ1 hErr hτ
      rfl).2
  -- edge-disjointness of the diagonal family
  · intro i hi j hj hij p q hp
    exact rectDesign_pairwise_edgeDisjoint G (blockOf U sA) (blockOf W sB) (blockOf X sC)
      hBA hCA (fun a _ b _ hab => blockOf_disjoint U sA hab)
      (fun a _ b _ hab => blockOf_disjoint W sB hab)
      (fun a _ b _ hab => blockOf_disjoint X sC hab)
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
        (Finset.disjoint_of_subset_right (blockOf_subset W sB _) hUW))
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
        (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hUX))
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset W sB _)
        (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hWX))
      hi hj hij p q hp

end Nibble.AX1
