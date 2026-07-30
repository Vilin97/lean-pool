/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Certificate
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
  Sundogcert/Scaling.lean — the [2m, m] projection-code SCALING family.
  Generalizes the m=2 member in Instance.lean to all m, exhibiting the empirical
  SCALING LAW colWeightLb = m (reject threshold τ = m-1, linear in n = 2m).

  TIER 3 (floor)  — pure #eval of the family at m ∈ {2,4,8,16,32}: colBound = 1,
                    hammingNorm (projH m *ᵥ allOnes) = m, colWeightLb = m.
  TIER 2 (anchors)— actual Scheme instances at m = 4 (τ=3) and m = 8 (τ=7),
                    hHG by the STRUCTURAL route (projH * projGᵀ = 0). vCol REJECTS
                    the all-ones body, vSupp QUARANTINES it (the divergence widens with τ).
  TIER 1 (stretch)— the parametric theorems: colBound (projH m) = 1, hammingNorm = m,
                    general hHG, and the SCALING LAW ¬ Safe (projScheme m) (allOnesSynBody m).

  HONESTY: colBound (projH m) = 1 (uniform projection H) is the FAVORABLE regime — here
  colWeightLb = m is the TRUE min coset weight (TIGHT). On non-uniform H the column-weight
  bound is loose (it divides by the GLOBAL worst column weight; see Certificate.lean). This
  family demonstrates SOUNDNESS and linear-in-n τ reach, NOT general tightness.
-/

open Matrix

namespace Sundog.Certificate.Scaling

/-! ### The parametric family (the [2m, m] projection code). -/

/-- Parity-check `[Iₘ | 0]` : row `i`, col `j` is `1` iff `j = i` (so `j < m`). -/
def projH (m : ℕ) : Matrix (Fin m) (Fin (2 * m)) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) then 1 else 0

/-- Generator `[0 | Iₘ]` : row `i`, col `j` is `1` iff `j = i + m` (so `j ≥ m`).
    Its rows are codewords of `ker (projH m)`. -/
def projG (m : ℕ) : Matrix (Fin m) (Fin (2 * m)) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + m then 1 else 0

/-- The all-ones-syndrome body: the first `m` coordinates are `1`, the rest `0`.
    `projH m *ᵥ (allOnesSynBody m)` is the all-ones vector in `Fin m`. -/
def allOnesSynBody (m : ℕ) : Fin (2 * m) → ZMod 2 :=
  fun j => if (j : ℕ) < m then 1 else 0

/-! ### TIER 3 — pure computation. The empirical scaling law (NO Scheme / hHG needed).

    For each m: colBound (projH m) = 1, hammingNorm (projH m *ᵥ allOnes) = m, and the
    quotient (= colWeightLb value) = m. Reject threshold τ = m - 1 scales linearly in n = 2m. -/

-- m = 2

-- m = 4

-- m = 8

-- m = 16

-- m = 32

-- The scaling table as one #eval: (m, colBound, hammingNorm, colWeightLb = wt/colBound = m).

/-! ### STRUCTURAL hHG — the scalable route (no `decide`, no `2^m` blowup).

    `projH m * (projG m)ᵀ = 0`: entry `(i,k) = ∑_j [j=i]·[j=k+m]`. Since `i < m ≤ k+m`,
    the indices `i` and `k+m` are distinct, so every summand is `0`. Then
    `projH m *ᵥ (s ᵥ* projG m) = (projH m * (projG m)ᵀ) *ᵥ s = 0`. -/

/-- The structural core: `projH m * (projG m)ᵀ = 0`. -/
theorem projH_mul_projG_transpose (m : ℕ) :
    projH m * (projG m)ᵀ = 0 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, projH, projG, Matrix.of_apply,
    Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  -- term is ([j = i]) * ([j = k + m]); the two guards cannot both hold (i < m ≤ k + m)
  by_cases hji : (j : ℕ) = (i : ℕ)
  · -- then j = i < m, so j ≠ k + m
    have hik : (i : ℕ) ≠ (k : ℕ) + m := by
      have : (i : ℕ) < m := i.isLt
      omega
    rw [if_pos hji, if_neg (hji ▸ hik), one_mul]
  · rw [if_neg hji, zero_mul]

/-- The dual-pair law for the family, via the structural core. SCALABLE: kernel cost is
    polynomial in `m` (no `2^m` secret enumeration). -/
theorem hHG_proj (m : ℕ) :
    ∀ s : Fin m → ZMod 2, projH m *ᵥ (s ᵥ* projG m) = 0 := by
  intro s
  -- s ᵥ* projG = (projG)ᵀ *ᵥ s  (mulVec_transpose, read right-to-left)
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, projH_mul_projG_transpose,
    Matrix.zero_mulVec]

/-! ### TIER 2 — concrete anchor Schemes at m = 4 (τ = 3) and m = 8 (τ = 7).

    hHG via `hHG_proj` (structural). Two verifiers each (vSupp, vCol). On the all-ones
    body: vCol REJECTS (colWeightLb = m > τ = m-1), vSupp QUARANTINES (supportLb = 1 ≤ τ).
    The divergence WIDENS with m — the non-degenerate bound's reach grows linearly in τ. -/

/-- The parametric scheme `[2m, m]` at radius `τ = m - 1`. -/
def projScheme (m : ℕ) : Scheme (ZMod 2) where
  n := 2 * m
  k := m
  m := m
  G := projG m
  H := projH m
  τ := m - 1
  hHG := hHG_proj m

/-- Forward witness: a light body is its own same-syndrome witness. -/
def witnessOpt (m : ℕ) (y : Fin (projScheme m).n → ZMod 2) :
    Option (Fin (projScheme m).n → ZMod 2) :=
  if wt y ≤ (projScheme m).τ then some y else none

theorem witness_sound (m : ℕ) :
    ∀ y e', witnessOpt m y = some e' →
      (projScheme m).H *ᵥ e' = (projScheme m).H *ᵥ y ∧ wt e' ≤ (projScheme m).τ := by
  intro y e' h
  unfold witnessOpt at h
  by_cases hwt : wt y ≤ (projScheme m).τ
  · simp only [hwt, if_true, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hwt⟩
  · simp only [hwt, if_false] at h
    exact absurd h (by simp)

/-- Verifier with the degenerate support bound. -/
def vSupp (m : ℕ) : Verifier (projScheme m) where
  witnessOpt := witnessOpt m
  lb := supportLb (projScheme m)
  witness_sound := witness_sound m

/-- Verifier with the non-degenerate column-weight bound. -/
def vCol (m : ℕ) : Verifier (projScheme m) where
  witnessOpt := witnessOpt m
  lb := colWeightLb (projScheme m)
  witness_sound := witness_sound m

/-- Display instance for the three-valued verdict. -/
instance : ToString Verdict where
  toString
    | Verdict.accept => "accept"
    | Verdict.reject => "reject"
    | Verdict.quarantine => "quarantine"

/-! ### Anchor verdicts on the all-ones body: "m  τ  vSupp  vCol". -/

/-- Run both verifiers on the all-ones-syndrome body and format the verdict line. -/
def verdicts (m : ℕ) : String :=
  let s := (vSupp m).run (projScheme m) (allOnesSynBody m)
  let c := (vCol m).run (projScheme m) (allOnesSynBody m)
  s!"m={m}  τ={m - 1}  vSupp={s}  vCol={c}"


/-! ### TIER 1 — the PARAMETRIC SCALING LAW: one proof for the whole family.

    Three parametric facts and the headline theorem:
      colBound_projH        : ∀ m, 0 < m → colBound (projH m) = 1
      projH_mulVec_allOnes  : ∀ m, projH m *ᵥ allOnesSynBody m = 1   (the all-ones vector)
      hammingNorm_projH_allOnes : ∀ m, hammingNorm (projH m *ᵥ allOnesSynBody m) = m
      scaling_law           : ∀ m, 0 < m → ¬ Safe (projScheme m) (allOnesSynBody m). -/

/-- `projH m *ᵥ allOnesSynBody m` is the all-ones vector in `Fin m`: at row `i`, the only
    nonzero term is `j = i` (both guards `j = i` and `j < m` hold since `i < m`). -/
theorem projH_mulVec_allOnes (m : ℕ) :
    projH m *ᵥ allOnesSynBody m = (fun _ => 1) := by
  funext i
  simp only [projH, allOnesSynBody, Matrix.mulVec, Matrix.of_apply, dotProduct]
  rw [Finset.sum_eq_single (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * m))]
  · have hii : ((⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * m)) : ℕ) = (i : ℕ) := rfl
    have hilt : ((⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * m)) : ℕ) < m := i.isLt
    rw [if_pos hii, if_pos hilt, one_mul]
  · intro j _ hj
    -- j ≠ i (as Fin (2*m) with value i), so the first guard fails
    by_cases hjm : (j : ℕ) < m
    · have hji : (j : ℕ) ≠ (i : ℕ) := by
        intro h
        apply hj
        apply Fin.ext
        simp only [h]
      rw [if_neg hji, zero_mul]
    · rw [if_neg hjm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `hammingNorm (projH m *ᵥ allOnesSynBody m) = m`: the all-ones vector over `Fin m`. -/
theorem hammingNorm_projH_allOnes (m : ℕ) :
    hammingNorm (projH m *ᵥ allOnesSynBody m) = m := by
  rw [projH_mulVec_allOnes]
  -- hammingNorm of the constant-1 vector = card of all coordinates = m
  rw [hammingNorm]
  have : (Finset.univ.filter (fun i : Fin m => (1 : ZMod 2) ≠ 0)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact one_ne_zero
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- Each column `j` of `projH m` has support cardinality `≤ 1`: at most the single row `i = j`. -/
theorem colSupp_projH_le_one (m : ℕ) (j : Fin (2 * m)) :
    (Finset.univ.filter (fun i : Fin m => projH m i j ≠ 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' : projH m a j ≠ 0 := (Finset.mem_filter.mp ha).2
  have hb' : projH m b j ≠ 0 := (Finset.mem_filter.mp hb).2
  change (if (j : ℕ) = (a : ℕ) then (1 : ZMod 2) else 0) ≠ 0 at ha'
  change (if (j : ℕ) = (b : ℕ) then (1 : ZMod 2) else 0) ≠ 0 at hb'
  -- projH a j ≠ 0 ⟹ (j = a); likewise (j = b); hence a = b
  have hja : (j : ℕ) = (a : ℕ) := by
    by_contra h
    rw [if_neg h] at ha'
    exact ha' rfl
  have hjb : (j : ℕ) = (b : ℕ) := by
    by_contra h
    rw [if_neg h] at hb'
    exact hb' rfl
  exact Fin.ext (hja ▸ hjb)

/-- **colBound (projH m) = 1** for `m > 0`: every column has ≤ 1 nonzero, and column `0`
    (row `0`) attains it, so the sup is exactly `1`. -/
theorem colBound_projH (m : ℕ) (hm : 0 < m) : colBound (projH m) = 1 := by
  apply le_antisymm
  · -- upper bound: sup over columns of (≤ 1) is ≤ 1
    apply Finset.sup_le
    intro j _
    exact colSupp_projH_le_one m j
  · -- lower bound: column 0 has support cardinality ≥ 1 (row 0 is nonzero)
    have hj0 : (⟨0, by omega⟩ : Fin (2 * m)) ∈ (Finset.univ : Finset (Fin (2 * m))) :=
      Finset.mem_univ _
    refine le_trans ?_ (Finset.le_sup (f := fun j =>
      (Finset.univ.filter (fun i : Fin m => projH m i j ≠ 0)).card) hj0)
    -- the column-0 support contains row 0
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    refine ⟨⟨0, hm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    -- projH ⟨0,hm⟩ ⟨0,_⟩ = if (0 = 0) then 1 else 0 = 1 ≠ 0
    change (if ((⟨0, by omega⟩ : Fin (2 * m)) : ℕ) = ((⟨0, hm⟩ : Fin m) : ℕ)
            then (1 : ZMod 2) else 0) ≠ 0
    rw [if_pos rfl]
    exact one_ne_zero

/-- **THE SCALING LAW.**  For every `m > 0`, the all-ones-syndrome body is UNSAFE at the
    radius `τ = m - 1`: no same-syndrome witness has weight ≤ m - 1, because the syndrome
    `projH m *ᵥ (allOnesSynBody m)` has weight `m`, and (colBound = 1 ⟹) `colWeightLb = m`
    is a SOUND lower bound on every witness weight. One proof, the whole [2m, m] family. -/
theorem scaling_law (m : ℕ) (hm : 0 < m) :
    ¬ Safe (projScheme m) (allOnesSynBody m) := by
  rintro ⟨e', he, hwt⟩
  -- colWeightLb is a sound lower bound: colWeightLb (H *ᵥ y) ≤ wt e'
  have hsound := colWeightLb_sound (projScheme m) (allOnesSynBody m) e' he
  -- colWeightLb (H *ᵥ y) = hammingNorm (H *ᵥ y) / colBound H = m / 1 = m
  have hcw : colWeightLb (projScheme m) ((projScheme m).H *ᵥ allOnesSynBody m) = m := by
    unfold colWeightLb
    change hammingNorm (projH m *ᵥ allOnesSynBody m) / colBound (projH m) = m
    rw [hammingNorm_projH_allOnes, colBound_projH m hm, Nat.div_one]
  rw [hcw] at hsound
  -- but wt e' ≤ τ = m - 1 < m, contradiction
  have hτ : (projScheme m).τ = m - 1 := rfl
  rw [hτ] at hwt
  -- hsound : m ≤ wt e'  ,  hwt : wt e' ≤ m - 1  (same atom `wt e'`)
  omega

/-! ### Axiom audit for the anchor vCol verifiers and the general scaling law. -/


end Sundog.Certificate.Scaling
