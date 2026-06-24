/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Scaling
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
  Sundogcert/Looseness.lean — the BASIS-DEPENDENCE / looseness demonstration.

  The column-weight bound `colWeightLb` measures the parity-check matrix `H`, NOT the code.
  Row-reduce `H` to a row-EQUIVALENT dense matrix (multiply on the left by an invertible
  densifier `M`) and the SAME code, the SAME `Safe` predicate, the SAME true min coset weight
  survive — but `colWeightLb` collapses from `m` (TIGHT, sparse projection `H`) to `0`
  (VACUOUS, dense `H`).  The looseness gap is `m`, MAXIMAL.

  Densifier: `lowerTriOnes m` (lower-triangular all-ones, det = 1 over GF(2), INVERTIBLE).
    Inverse `Linv m` = `I + sub-diagonal shift` (bidiagonal).  `lowerTriOnes m * Linv m = 1`
    is proved STRUCTURALLY (a column-by-column parity argument), NOT by `decide`.
  denseH m := lowerTriOnes m * projH m  (= [L | 0], row-equivalent to projH m).

  TIER 3 (floor)  — pure #eval: colBound (projH m) = 1, colWeightLb-value = m (TIGHT) vs
                    colBound (denseH m) = m, colWeightLb-value = 0 (VACUOUS), m ∈ {2,4,8}.
  TIER 2 (anchor) — denseScheme m : Scheme; Safe (denseScheme 4) ↔ Safe (projScheme 4) at the
                    concrete anchor; vCol.run = quarantine (can't reject) vs projScheme reject.
  TIER 1 (stretch)— PARAMETRIC: lowerTriOnes invertibility, general Safe-equivalence
                    `∀ m, Safe (denseScheme m) y ↔ Safe (projScheme m) y`,
                    `colBound (denseH m) = m`, and the LOOSENESS theorem: the same unsafe
                    all-ones body has true min coset
                    weight `m` YET `colWeightLb (denseScheme m) = 0`.  Anti-scaling-law: gap = m.
-/

open Matrix

namespace Sundog.Certificate.Looseness

open Sundog.Certificate
open Sundog.Certificate.Scaling

/-! ### The densifier and its inverse. -/

/-- Lower-triangular all-ones matrix: entry `(i,j) = 1` iff `j ≤ i`.  Det = 1 over GF(2). -/
def lowerTriOnes (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) ≤ (i : ℕ) then 1 else 0

/-- Inverse of `lowerTriOnes`: bidiagonal `I + sub-diagonal shift`.  Entry `(i,j) = 1` iff
    `i = j` (diagonal) or `i = j + 1` (sub-diagonal). -/
def Linv (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- The dense parity-check `lowerTriOnes m * projH m` (= `[L | 0]`, row-equivalent to
    `projH m`). -/
def denseH (m : ℕ) : Matrix (Fin m) (Fin (2 * m)) (ZMod 2) :=
  lowerTriOnes m * projH m

/-! ### TIER 3 — pure computation. The empirical COLLAPSE table.

    Same body (all-ones syndrome), same code, sparse `projH` → colWeightLb = m (TIGHT),
    dense `denseH` → colWeightLb = 0 (VACUOUS). No proofs. -/

/-- colWeightLb value on the all-ones body for a parity-check `H`:
    `hammingNorm (H *ᵥ b) / colBound H`. -/
def lbValue (m : ℕ) (H : Matrix (Fin m) (Fin (2 * m)) (ZMod 2)) : ℕ :=
  hammingNorm (H *ᵥ allOnesSynBody m) / colBound H

/-- One collapse-table row: `(m, colBound projH, lb projH, colBound denseH, lb denseH)`. -/
def collapseRow (m : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m, colBound (projH m), lbValue m (projH m), colBound (denseH m), lbValue m (denseH m))

-- m = 2 : sparse colBound 1, lb 2 (TIGHT); dense colBound 2, lb 0 (VACUOUS).
-- m = 4 : sparse colBound 1, lb 4 (TIGHT); dense colBound 4, lb 0 (VACUOUS).
-- m = 8 : sparse colBound 1, lb 8 (TIGHT); dense colBound 8, lb 0 (VACUOUS).

-- The full collapse table as one #eval over m ∈ {2,4,8}.
-- Each row: (m, colBound_sparse, lb_sparse, colBound_dense, lb_dense).

/-! ### STRUCTURAL invertibility — `lowerTriOnes m * Linv m = 1` (NO `decide`).

    `(L * Linv) i j = ∑_k [k ≤ i] · [k = j ∨ k = j+1]`.  Over GF(2):
      contributions from `k = j` (if `j ≤ i`) and `k = j+1` (if `j+1 ≤ i`).
      i = j  : k=j gives `j ≤ i` true (1), k=j+1 gives `j+1 ≤ i = j` false ⟹ sum = 1.
      i > j  : both true ⟹ 1 + 1 = 0.
      i < j  : both false ⟹ 0.
    So `(L * Linv) i j = if i = j then 1 else 0 = (1 : Matrix) i j`. -/

/-- The structural inverse identity: `lowerTriOnes m * Linv m = 1`.  Proved by a column-by-column
    PARITY argument (the OR-indicator splits into a disjoint sum of two single-row indicators),
    NOT by `decide` — so it holds for ALL `m`, no `2^m`-style enumeration. -/
theorem lowerTriOnes_mul_Linv (m : ℕ) : lowerTriOnes m * Linv m = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [lowerTriOnes, Linv, Matrix.of_apply]
  -- summand at k : [k ≤ i] * [k=j ∨ k=j+1]  =  [k=j ∧ k≤i] + [k=j+1 ∧ k≤i]  (disjoint OR).
  have key : ∀ k : Fin m,
      ((if (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0) *
        if (k:ℕ) = (j:ℕ) ∨ (k:ℕ) = (j:ℕ)+1 then 1 else 0)
      = (if (k:ℕ) = (j:ℕ) ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0)
        + (if (k:ℕ) = (j:ℕ)+1 ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0) := by
    intro k
    by_cases hki : (k:ℕ) ≤ (i:ℕ)
    · rw [if_pos hki]
      by_cases h1 : (k:ℕ) = (j:ℕ)
      · rw [if_pos (Or.inl h1), if_pos ⟨h1, hki⟩, if_neg (by omega), one_mul, add_zero]
      · by_cases h2 : (k:ℕ) = (j:ℕ)+1
        · rw [if_pos (Or.inr h2), if_neg (by tauto), if_pos ⟨h2, hki⟩, one_mul, zero_add]
        · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto), mul_zero, add_zero]
    · rw [if_neg hki, zero_mul, if_neg (by tauto), if_neg (by tauto), add_zero]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib]
  -- Sum A = [j ≤ i] (single term k = j).
  have hA : (∑ k : Fin m, if (k:ℕ) = (j:ℕ) ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0)
      = if (j:ℕ) ≤ (i:ℕ) then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      apply if_neg
      rintro ⟨hkj, _⟩
      exact hk (Fin.ext hkj)
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hA]
  by_cases hij : i = j
  · subst hij
    rw [if_pos (le_refl _)]
    -- Sum B = 0 : (k:ℕ)=i+1 ∧ k ≤ i is impossible.
    have hB : (∑ k : Fin m, if (k:ℕ) = (i:ℕ)+1 ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      apply if_neg
      rintro ⟨h1, h2⟩; omega
    rw [hB, add_zero, if_pos rfl]
  · rw [if_neg hij]
    by_cases hlt : (j:ℕ) < (i:ℕ)
    · -- j < i : [j ≤ i] = 1, and B = 1 (k = j+1 exists, ≤ i), sum 1 + 1 = 0.
      rw [if_pos (le_of_lt hlt)]
      have hj1 : (j:ℕ)+1 < m := by have := i.isLt; omega
      have hB : (∑ k : Fin m, if (k:ℕ) = (j:ℕ)+1 ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0)
          = 1 := by
        rw [Finset.sum_eq_single (⟨(j:ℕ)+1, hj1⟩ : Fin m)]
        · have hval : ((⟨(j:ℕ)+1, hj1⟩ : Fin m) : ℕ) = (j:ℕ)+1 := rfl
          rw [if_pos ⟨hval, by omega⟩]
        · intro k _ hk
          apply if_neg
          rintro ⟨h1, _⟩
          exact hk (Fin.ext (by simpa using h1))
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hB]; decide
    · -- i < j : [j ≤ i] = 0, B = 0.
      have hilt : (i:ℕ) < (j:ℕ) := by
        rcases Nat.lt_trichotomy (i:ℕ) (j:ℕ) with h | h | h
        · exact h
        · exact absurd (Fin.ext h) hij
        · omega
      rw [if_neg (by omega)]
      have hB : (∑ k : Fin m, if (k:ℕ) = (j:ℕ)+1 ∧ (k:ℕ) ≤ (i:ℕ) then (1:ZMod 2) else 0)
          = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        apply if_neg
        rintro ⟨h1, h2⟩; omega
      rw [hB, add_zero]

/-- `lowerTriOnes m` is invertible (with explicit right inverse `Linv m`). -/
instance lowerTriOnesInvertible (m : ℕ) : Invertible (lowerTriOnes m) :=
  invertibleOfRightInverse _ (Linv m) (lowerTriOnes_mul_Linv m)

/-! ### denseH structure: `denseH m *ᵥ v = lowerTriOnes m *ᵥ (projH m *ᵥ v)`. -/

/-- `denseH` factors through `projH`: `denseH m *ᵥ v = lowerTriOnes m *ᵥ (projH m *ᵥ v)`. -/
theorem denseH_mulVec (m : ℕ) (v : Fin (2 * m) → ZMod 2) :
    denseH m *ᵥ v = lowerTriOnes m *ᵥ (projH m *ᵥ v) := by
  rw [denseH, Matrix.mulVec_mulVec]

/-- The dual-pair law for the dense scheme: `denseH m *ᵥ (s ᵥ* projG m) = 0`.
    Via `denseH = L * projH` and `projH m *ᵥ (s ᵥ* projG m) = 0`. -/
theorem hHG_dense (m : ℕ) :
    ∀ s : Fin m → ZMod 2, denseH m *ᵥ (s ᵥ* projG m) = 0 := by
  intro s
  rw [denseH_mulVec, hHG_proj m s, Matrix.mulVec_zero]

/-! ### TIER 2/1 — the dense scheme. -/

/-- The DENSE scheme: same `n,k,m,G,τ` as `projScheme`, but `H := denseH m` (row-equivalent). -/
def denseScheme (m : ℕ) : Scheme (ZMod 2) where
  n := 2 * m
  k := m
  m := m
  G := projG m
  H := denseH m
  τ := m - 1
  hHG := hHG_dense m

/-! ### SAFE-EQUIVALENCE (TIER 1, parametric).

    `denseH m *ᵥ a = denseH m *ᵥ b ↔ projH m *ᵥ a = projH m *ᵥ b`, because `denseH = L · projH`
    and `L` is INVERTIBLE (hence injective on `mulVec`).  Therefore the two schemes have the
    SAME `Safe` predicate — the SAME true min coset weight. -/

/-- Syndrome equivalence: the dense and sparse parity-checks have the SAME kernel relation. -/
theorem dense_syndrome_iff (m : ℕ) (a b : Fin (2 * m) → ZMod 2) :
    denseH m *ᵥ a = denseH m *ᵥ b ↔ projH m *ᵥ a = projH m *ᵥ b := by
  rw [denseH_mulVec, denseH_mulVec]
  constructor
  · intro h
    exact Matrix.mulVec_injective_of_invertible (lowerTriOnes m) h
  · intro h
    rw [h]

/-- **SAFE-EQUIVALENCE (parametric).**  `Safe (denseScheme m) y ↔ Safe (projScheme m) y`.
    SAME code, SAME safety predicate, SAME true min coset weight — only `H` differs. -/
theorem safe_dense_iff_proj (m : ℕ) (y : Fin (2 * m) → ZMod 2) :
    Safe (denseScheme m) y ↔ Safe (projScheme m) y := by
  constructor
  · rintro ⟨e', he, hwt⟩
    exact ⟨e', (dense_syndrome_iff m e' y).mp he, hwt⟩
  · rintro ⟨e', he, hwt⟩
    exact ⟨e', (dense_syndrome_iff m e' y).mpr he, hwt⟩

/-! ### TIER 1 — `colBound (denseH m) = m` (column 0 of `denseH` has weight `m`).

    Column 0 of `denseH m = L * projH m`: `denseH i 0 = ∑_k L i k * projH k 0 = L i 0`
    (only `k = 0` makes `projH k 0 ≠ 0`), and `L i 0 = [0 ≤ i] = 1` for ALL `i`.  So column 0
    is the all-ones vector in `Fin m` — support cardinality `m`.  Every column has support `≤ m`
    trivially (the whole index set), so the sup is exactly `m`. -/

/-- Column 0 of `denseH m` is the all-ones vector: `denseH m i 0 = 1` for every row `i`. -/
theorem denseH_col0 (m : ℕ) (hm : 0 < m) (i : Fin m) :
    denseH m i (⟨0, by omega⟩ : Fin (2 * m)) = 1 := by
  simp only [denseH, Matrix.mul_apply, lowerTriOnes, projH, Matrix.of_apply]
  -- ∑_k [k ≤ i]·[(⟨0,_⟩:ℕ) = k]  — only k = 0 contributes (with value [0 ≤ i] = 1).
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · -- k = 0 : [0 ≤ i] = 1, and the projH guard `(0 : ℕ) = (0 : ℕ)` holds.
    have hcol : ((⟨0, by omega⟩ : Fin (2 * m)) : ℕ) = ((⟨0, hm⟩ : Fin m) : ℕ) := rfl
    rw [if_pos (Nat.zero_le _), if_pos hcol, one_mul]
  · intro k _ hk
    -- k ≠ 0 ⟹ the projH guard `(0 : ℕ) = (k : ℕ)` fails ⟹ second factor 0.
    have hk0 : ((⟨0, by omega⟩ : Fin (2 * m)) : ℕ) ≠ (k : ℕ) :=
      fun h => hk (Fin.ext h.symm)
    rw [if_neg hk0, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Each column of `denseH m` has support cardinality `≤ m` (trivially: at most all `m` rows). -/
theorem colSupp_denseH_le (m : ℕ) (j : Fin (2 * m)) :
    (Finset.univ.filter (fun i : Fin m => denseH m i j ≠ 0)).card ≤ m := by
  calc (Finset.univ.filter (fun i : Fin m => denseH m i j ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- **colBound (denseH m) = m** for `m > 0`: column 0 is all-ones (support `m`), and no column
    exceeds `m`.  The dense `H` has worst-column weight `m` vs `projH`'s `1`. -/
theorem colBound_denseH (m : ℕ) (hm : 0 < m) : colBound (denseH m) = m := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    exact colSupp_denseH_le m j
  · -- column 0 attains m: its support is ALL of Fin m.
    refine le_trans ?_ (Finset.le_sup (f := fun j =>
      (Finset.univ.filter (fun i : Fin m => denseH m i j ≠ 0)).card)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * m))))
    change m ≤ (Finset.univ.filter
        (fun i : Fin m => denseH m i (⟨0, by omega⟩ : Fin (2 * m)) ≠ 0)).card
    have hcol : (Finset.univ.filter
        (fun i : Fin m => denseH m i (⟨0, by omega⟩ : Fin (2 * m)) ≠ 0)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      rw [denseH_col0 m hm i]
      exact one_ne_zero
    rw [hcol, Finset.card_univ, Fintype.card_fin]

/-! ### TIER 1 — the syndrome of the all-ones body under `denseH` collapses the bound.

    `denseH m *ᵥ allOnesSynBody m = L *ᵥ (projH m *ᵥ allOnesSynBody m) = L *ᵥ 1` = row-sums of L
    = `(i + 1 mod 2)_i`.  hammingNorm = ⌈m/2⌉ ≤ m, so `colWeightLb = ⌈m/2⌉ / m = 0` for m ≥ 2. -/

/-- The dense syndrome of the all-ones body:
    `denseH m *ᵥ allOnesSynBody m = lowerTriOnes m *ᵥ 1`. -/
theorem denseH_mulVec_allOnes (m : ℕ) :
    denseH m *ᵥ allOnesSynBody m = lowerTriOnes m *ᵥ (fun _ => 1) := by
  rw [denseH_mulVec, projH_mulVec_allOnes]

/-! ### THE LOOSENESS THEOREM (TIER 1).

    For all `m ≥ 2` the all-ones body has true min coset weight `m` (UNSAFE at τ = m-1, by the
    proven `scaling_law` transferred through `safe_dense_iff_proj`), YET `colWeightLb` on the
    DENSE scheme is `0` — the bound is VACUOUS on the SAME unsafe body.

    `colWeightLb = hammingNorm (denseH *ᵥ b) / colBound (denseH) = (⌈m/2⌉) / m`.  Since the dense
    syndrome has hammingNorm `< m + 1` (at most `m` coordinates) and `colBound (denseH) = m`,
    the floor-division is `0` whenever the numerator `< m`.  We prove numerator `≤ m` always, and
    `< m` for `m ≥ 2` (so the bound is `0` — vacuous, can't reject anything at `τ ≥ 0`). -/

/-- The dense syndrome has hammingNorm `≤ m` (at most all `m` coordinates can be nonzero). -/
theorem hammingNorm_denseSyn_le (m : ℕ) :
    hammingNorm (denseH m *ᵥ allOnesSynBody m) ≤ m := by
  rw [hammingNorm]
  calc (Finset.univ.filter (fun i => (denseH m *ᵥ allOnesSynBody m) i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- The dense syndrome has hammingNorm STRICTLY `< m` for `m ≥ 1`: at least one coordinate is `0`.
    Row 0 of `L *ᵥ 1` is `∑_{k ≤ 0} 1 = 1 ≠ 0`; but row `m-1` is `∑_{k ≤ m-1} 1 = m`, and more
    importantly NOT every row is nonzero — the dense syndrome `(⌈row+1⌉ mod 2)` alternates, so the
    support is at most `⌈m/2⌉ < m` for `m ≥ 2`.  We give the clean fact: row 1 (when m ≥ 2) of
    `L *ᵥ 1` is `1 + 1 = 0`, so coordinate 1 is excluded from the support ⟹ hammingNorm < m. -/
theorem hammingNorm_denseSyn_lt (m : ℕ) (hm : 2 ≤ m) :
    hammingNorm (denseH m *ᵥ allOnesSynBody m) < m := by
  rw [hammingNorm]
  -- Coordinate `⟨1,_⟩` of the dense syndrome is 0 (∑_{k≤1} 1 = card{0,1} = 2 = 0 in GF(2)),
  -- so the support is a STRICT subset of univ.
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have hzero : (denseH m *ᵥ allOnesSynBody m) i1 = 0 := by
    rw [denseH_mulVec_allOnes]
    -- (L *ᵥ 1) i1 = ∑_k L i1 k * 1 = ∑_k [k ≤ 1] = (card {k : (k:ℕ) ≤ 1} : ZMod 2).
    simp only [lowerTriOnes, Matrix.mulVec, Matrix.of_apply, dotProduct, mul_one]
    have hi1v : (i1 : ℕ) = 1 := rfl
    rw [hi1v, Finset.sum_boole]
    -- The filter set {k : (k:ℕ) ≤ 1} = {⟨0,_⟩, ⟨1,_⟩}, card = 2, and (2 : ZMod 2) = 0.
    have hset : (Finset.univ.filter (fun k : Fin m => (k:ℕ) ≤ 1))
        = {(⟨0, by omega⟩ : Fin m), (⟨1, by omega⟩ : Fin m)} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hk
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h | h
        · exact Or.inl (Fin.ext (by simp [h]))
        · exact Or.inr (Fin.ext (by simp [h]))
      · rintro (h | h) <;> (subst h) <;> simp
    rw [hset]
    have hne : (⟨0, by omega⟩ : Fin m) ≠ (⟨1, by omega⟩ : Fin m) := by
      intro h
      exact absurd (congrArg Fin.val h) (by simp)
    rw [Finset.card_pair hne]
    rfl
  have hsub : (Finset.univ.filter (fun i => (denseH m *ᵥ allOnesSynBody m) i ≠ 0))
      ⊂ (Finset.univ : Finset (Fin m)) := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro heq
    have : i1 ∈ (Finset.univ.filter (fun i => (denseH m *ᵥ allOnesSynBody m) i ≠ 0)) := by
      rw [heq]; exact Finset.mem_univ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this hzero
  calc (Finset.univ.filter (fun i => (denseH m *ᵥ allOnesSynBody m) i ≠ 0)).card
      < (Finset.univ : Finset (Fin m)).card := Finset.card_lt_card hsub
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The dense colWeightLb VANISHES**: `colWeightLb (denseScheme m) (denseH *ᵥ allOnes) = 0`
    for `m ≥ 2`.  The numerator (dense syndrome weight) is `< m = colBound (denseH)`, so the
    floor-division is `0`.  The non-degenerate column-weight bound is VACUOUS on the dense `H`. -/
theorem colWeightLb_denseScheme_zero (m : ℕ) (hm : 2 ≤ m) :
    colWeightLb (denseScheme m) ((denseScheme m).H *ᵥ allOnesSynBody m) = 0 := by
  unfold colWeightLb
  -- (denseScheme m).H = denseH m; colBound (denseScheme m).H = colBound (denseH m) = m.
  change hammingNorm (denseH m *ᵥ allOnesSynBody m) / colBound (denseH m) = 0
  rw [colBound_denseH m (by omega)]
  exact Nat.div_eq_of_lt (hammingNorm_denseSyn_lt m hm)

/-- **THE LOOSENESS THEOREM (anti-scaling-law).**  For every `m ≥ 2`:
      (1) the all-ones body is UNSAFE at `τ = m - 1` under `denseScheme` (true min coset weight
          `m`, transferred from the proven `scaling_law` via the SAFE-EQUIVALENCE), and YET
      (2) `colWeightLb (denseScheme m) (...) = 0` — the bound is VACUOUS on the SAME unsafe body.
    The looseness gap = `m - 0 = m`, MAXIMAL.  The bound is BASIS-DEPENDENT: it measures `H`,
    not the code.  The `scaling_law`'s tightness was an artifact of the sparse projection `H`. -/
theorem looseness (m : ℕ) (hm : 2 ≤ m) :
    ¬ Safe (denseScheme m) (allOnesSynBody m) ∧
      colWeightLb (denseScheme m) ((denseScheme m).H *ᵥ allOnesSynBody m) = 0 := by
  refine ⟨?_, colWeightLb_denseScheme_zero m hm⟩
  rw [safe_dense_iff_proj]
  exact scaling_law m (by omega)

/-! ### Anchor verdicts (TIER 2): SAME body, SAME code, OPPOSITE verdict from `H` alone. -/

/-- Forward witness for the dense scheme (identical search to the sparse one). -/
def witnessDenseOpt (m : ℕ) (y : Fin (denseScheme m).n → ZMod 2) :
    Option (Fin (denseScheme m).n → ZMod 2) :=
  if wt y ≤ (denseScheme m).τ then some y else none

theorem witnessDense_sound (m : ℕ) :
    ∀ y e', witnessDenseOpt m y = some e' →
      (denseScheme m).H *ᵥ e' = (denseScheme m).H *ᵥ y ∧ wt e' ≤ (denseScheme m).τ := by
  intro y e' h
  unfold witnessDenseOpt at h
  by_cases hwt : wt y ≤ (denseScheme m).τ
  · simp only [hwt, if_true, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hwt⟩
  · simp only [hwt, if_false] at h
    exact absurd h (by simp)

/-- The DENSE column-weight verifier — same code, same body, but built on `denseH`. -/
def vColDense (m : ℕ) : Verifier (denseScheme m) where
  witnessOpt := witnessDenseOpt m
  lb := colWeightLb (denseScheme m)
  witness_sound := witnessDense_sound m

/-- Verdict line: sparse `projScheme` vCol REJECTS, dense `denseScheme` vCol QUARANTINES —
    SAME all-ones body, SAME code, OPPOSITE verdict purely from the choice of `H`. -/
def looseVerdicts (m : ℕ) : String :=
  let proj := (vCol m).run (projScheme m) (allOnesSynBody m)
  let dense := (vColDense m).run (denseScheme m) (allOnesSynBody m)
  s!"m={m}  projScheme vCol={proj}  denseScheme vCol={dense}"


/-! ### Axiom audit for the key looseness results. -/


end Sundog.Certificate.Looseness
