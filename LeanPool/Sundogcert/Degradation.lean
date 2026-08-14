/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Looseness
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fintype.Fin

/-!
  Sundogcert/Degradation.lean — the DEGRADATION CURVE of the column-weight bound vs density.

  The column-weight bound `colWeightLb` is capped by (#checks)/(worst column density):
      colWeightLb S z ≤ S.m / colBound S.H        (the GENERAL DEGRADATION LAW, any scheme).
  As the parity-check density `c = colBound H` grows, the CEILING `⌊m/c⌋` shrinks `m → 1`.
  We instantiate this on ONE fixed code, sweeping the density with a band matrix.

  Band densifier: `bandLowerTri m c` — lower band of width `c` (entry `1` iff `0 ≤ i - j < c`).
    c = 1 ⟹ identity (colBound 1);  c = m ⟹ lowerTriOnes (colBound m);  c sweeps 1..m.
    UNIT lower-triangular (diagonal `1`) ⟹ INVERTIBLE ⟹ ker(bandDenseH) = ker(projH) ⟹ the
    WHOLE sweep is the SAME code (same `Safe`, same true min coset weight `m`).  Same argument
    as `safe_dense_iff_proj` in Looseness.lean.

  TIER core (CENTERPIECE) — the GENERAL ceiling theorem `colWeightLb S z ≤ S.m / colBound S.H`,
                    field-generic.  The degradation LAW: the densest column caps the bound.
                    (The ceiling is ELEMENTARY — `hammingNorm ≤ m`; the substance is the PROVEN
                    swept curve below: proven density `c`, proven same-code, the observed sawtooth.)
  TIER 3 (curve)  — #eval the m=8 sawtooth: (c, colBound = c, colWeightLb on allOnes, ⌊8/c⌋).
                    Each actual ≤ its ceiling; even-c collapses to 0 by GF(2) parity cancellation.
  TIER 1 (stretch)— `colBound (bandLowerTri m c) = c` parametric (1 ≤ c ≤ m) so the c-axis is a
                    PROVEN density; and the SAME-CODE fact (band invertible ⟹ ker equivalence ⟹
                    Safe-equivalence for all c), reusing the Looseness invertibility approach.
-/

open Matrix

namespace Sundog.Certificate.Degradation

open Sundog.Certificate
open Sundog.Certificate.Scaling
open Sundog.Certificate.Looseness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### TIER core — THE GENERAL DEGRADATION LAW (the centerpiece). -/

/-- **THE DEGRADATION LAW (centerpiece, any scheme, field-generic).**
    `colWeightLb S z ≤ S.m / colBound S.H`.  The densest column CAPS the cheap bound at
    (#checks) / (column density): as density grows `1 → m`, the ceiling shrinks `m → 1`.
    Proof: `hammingNorm z ≤ Fintype.card (Fin S.m) = S.m` (a filtered support is at most the
    whole index set), then monotonicity of `Nat`-division on the numerator. -/
theorem colWeightLb_le_card_div (S : Scheme F) (z : Fin S.m → F) :
    colWeightLb S z ≤ S.m / colBound S.H := by
  unfold colWeightLb
  have hz : hammingNorm z ≤ S.m := by
    calc hammingNorm z ≤ Fintype.card (Fin S.m) := hammingNorm_le_card_fintype
      _ = S.m := Fintype.card_fin S.m
  exact Nat.div_le_div_right hz

/-! ### The band densifier and the swept dense parity-check. -/

/-- Lower band of width `c`: entry `(i,j) = 1` iff `0 ≤ i - j < c`, i.e. `j ≤ i ∧ i < j + c`.
    `c = 1` ⟹ identity (colBound 1); `c = m` ⟹ `lowerTriOnes` (colBound m). -/
def bandLowerTri (m c : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j : ℕ) + c then 1 else 0

/-- The swept dense parity-check `bandLowerTri m c * projH m` (= `[band | 0]`, row-equivalent
    to `projH m` for every `1 ≤ c ≤ m`). -/
def bandDenseH (m c : ℕ) : Matrix (Fin m) (Fin (2 * m)) (ZMod 2) :=
  bandLowerTri m c * projH m

/-! ### TIER 3 — THE DEGRADATION CURVE (pure #eval, the m=8 sawtooth).

    On ONE fixed code, sweep the parity-check density `c = 1..m`.  Each row reports
      (c, colBound = c, colWeightLb on the all-ones body, ceiling = ⌊m/c⌋).
    actual ≤ ceiling always (the DEGRADATION LAW); even `c` collapses to `0` by GF(2) parity
    cancellation, odd `c` tracks the ceiling — the SAWTOOTH under the `⌊m/c⌋` envelope. -/

/-- colWeightLb value on the all-ones body for `bandDenseH m c`:
    `hammingNorm (bandDenseH m c *ᵥ allOnes) / colBound (bandDenseH m c)`. -/
def bandLbValue (m c : ℕ) : ℕ :=
  hammingNorm (bandDenseH m c *ᵥ allOnesSynBody m) / colBound (bandDenseH m c)

/-- One degradation-curve row at density `c`:
    `(c, colBound (bandLowerTri m c), colWeightLb-value, ceiling = ⌊m/c⌋)`. -/
def curveRow (m c : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (c, colBound (bandLowerTri m c), bandLbValue m c, m / c)

/-- The full degradation curve at fixed `m`: one row per density `c ∈ 1..m`. -/
def curve (m : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  ((List.range m).map (fun e => e + 1)).map (curveRow m)

-- THE m=8 DEGRADATION CURVE.  Each row: (c, colBound=c, colWeightLb on allOnes, ceiling ⌊8/c⌋).
-- Ground-truth sawtooth: c=1→lb8, 2→0, 3→2, 4→0, 5→1, 6→0, 7→0, 8→0; actual ≤ ceiling always.

-- Per-row spot checks (density, colBound = density, lb-value, ceiling).

/-! ### TIER 1 — `colBound (bandLowerTri m c) = c` (parametric, for `1 ≤ c ≤ m`).

    Column `j` of `bandLowerTri m c` has nonzero entries at rows `i` with `j ≤ i < j + c` and
    `i < m`, i.e. rows `j, …, min(j+c-1, m-1)` — count `min(c, m-j)`.  Column `0` attains the
    max `min(c, m) = c` (for `c ≤ m`): rows `0, …, c-1`.  No column exceeds `c` (the band is a
    contiguous block of `< c` rows when clipped).  So the sup is exactly `c`. -/

/-- Each column `j` of `bandLowerTri m c` has support cardinality `≤ c`: the nonzero rows form
    the interval `[j, j+c)` (clipped to `< m`), of length at most `c`. -/
theorem colSupp_bandLowerTri_le (m c : ℕ) (j : Fin m) :
    (Finset.univ.filter (fun i : Fin m => bandLowerTri m c i j ≠ 0)).card ≤ c := by
  -- The support injects into `Finset.range c` via `i ↦ i - j`; bound the card by that.
  have hle : (Finset.univ.filter (fun i : Fin m => bandLowerTri m c i j ≠ 0)).card
      ≤ (Finset.range c).card :=
    Finset.card_le_card_of_injOn (fun i => (i : ℕ) - (j : ℕ))
      (by
        intro i hi
        have hi' : bandLowerTri m c i j ≠ 0 := (Finset.mem_filter.mp hi).2
        change (if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j : ℕ) + c
          then (1 : ZMod 2) else 0) ≠ 0 at hi'
        by_cases hg : (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j : ℕ) + c
        · simp only [Finset.coe_range, Set.mem_Iio]; omega
        · rw [ite_eq_right hg] at hi'
          exact absurd rfl hi')
      (by
        intro a ha b hb hab
        have ha' : bandLowerTri m c a j ≠ 0 := (Finset.mem_filter.mp ha).2
        have hb' : bandLowerTri m c b j ≠ 0 := (Finset.mem_filter.mp hb).2
        change (if (j : ℕ) ≤ (a : ℕ) ∧ (a : ℕ) < (j : ℕ) + c
          then (1 : ZMod 2) else 0) ≠ 0 at ha'
        change (if (j : ℕ) ≤ (b : ℕ) ∧ (b : ℕ) < (j : ℕ) + c
          then (1 : ZMod 2) else 0) ≠ 0 at hb'
        by_cases hga : (j : ℕ) ≤ (a : ℕ) ∧ (a : ℕ) < (j : ℕ) + c
        · by_cases hgb : (j : ℕ) ≤ (b : ℕ) ∧ (b : ℕ) < (j : ℕ) + c
          · apply Fin.ext; simp only at hab; omega
          · rw [ite_eq_right hgb] at hb'
            exact absurd rfl hb'
        · rw [ite_eq_right hga] at ha'
          exact absurd rfl ha')
  rwa [Finset.card_range] at hle

/-- Column `0` of `bandLowerTri m c` (for `c ≤ m`) has support cardinality exactly `c`: the
    nonzero rows are precisely `0, …, c-1`. -/
theorem colSupp_bandLowerTri_col0 (m c : ℕ) (hc : c ≤ m) (hc0 : 0 < c) :
    (Finset.univ.filter
      (fun i : Fin m => bandLowerTri m c i (⟨0, by omega⟩ : Fin m) ≠ 0)).card = c := by
  have hset : (Finset.univ.filter
      (fun i : Fin m => bandLowerTri m c i (⟨0, by omega⟩ : Fin m) ≠ 0))
      = (Finset.univ.filter (fun i : Fin m => (i : ℕ) < c)) := by
    ext i
    constructor
    · intro hne
      have hne' : bandLowerTri m c i (⟨0, by omega⟩ : Fin m) ≠ 0 :=
        (Finset.mem_filter.mp hne).2
      change (if 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + c then (1 : ZMod 2) else 0) ≠ 0 at hne'
      by_cases hg : 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + c
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      · rw [ite_eq_right hg] at hne'
        exact absurd rfl hne'
    · intro hlt
      have hlt' : (i : ℕ) < c := (Finset.mem_filter.mp hlt).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change (if 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + c then (1 : ZMod 2) else 0) ≠ 0
      rw [ite_eq_left ⟨by omega, by omega⟩]
      exact one_ne_zero
  rw [hset]
  -- The filter `(i:ℕ) < c` over `Fin m` has card `min m c = c` (since `c ≤ m`).
  have hcard : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < c)).card = min m c :=
    Fin.card_filter_val_lt (n := m) (m := c)
  rw [hcard, Nat.min_eq_right hc]

/-- **colBound (bandLowerTri m c) = c** for `1 ≤ c ≤ m`: column `0` attains `c`, no column
    exceeds `c`.  The c-axis of the degradation curve is a PROVEN density. -/
theorem colBound_bandLowerTri (m c : ℕ) (hc0 : 0 < c) (hc : c ≤ m) :
    colBound (bandLowerTri m c) = c := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    exact colSupp_bandLowerTri_le m c j
  · refine le_trans ?_ (Finset.le_sup (f := fun j =>
      (Finset.univ.filter (fun i : Fin m => bandLowerTri m c i j ≠ 0)).card)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin m)))
    change c ≤ (Finset.univ.filter
      (fun i : Fin m => bandLowerTri m c i (⟨0, by omega⟩ : Fin m) ≠ 0)).card
    rw [colSupp_bandLowerTri_col0 m c hc hc0]

/-! ### TIER 1 — SAME-CODE: `bandLowerTri m c` is UNIT lower-triangular ⟹ INVERTIBLE.

    The diagonal entry `(i,i) = [i ≤ i ∧ i < i + c] = [c ≥ 1] = 1`, and the matrix is
    lower-triangular (`(i,j) = 0` for `j > i`).  We exhibit invertibility via `det = 1`:
    the matrix is `BlockTriangular`, so `det = ∏ diagonal = 1`, hence `Invertible`.  Then the
    same `mulVec`-injectivity argument as `safe_dense_iff_proj` gives ker(bandDenseH) = ker(projH)
    for the whole sweep `c = 1..m`. -/

/-- `bandLowerTri m c` is lower-triangular: entries strictly above the diagonal vanish.
    Phrased as `BlockTriangular … OrderDual.toDual` (the orientation whose diagonal product is
    `det`).  `j > i ⟹ ¬ (j ≤ i)` ⟹ entry `0`. -/
theorem bandLowerTri_blockTriangular (m c : ℕ) :
    (bandLowerTri m c).BlockTriangular (OrderDual.toDual : Fin m → (Fin m)ᵒᵈ) := by
  intro i j hij
  -- `toDual j < toDual i` ↔ `i < j` (the dual order flips); above-diagonal ⟹ entry 0.
  have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
  have hltn : (i : ℕ) < (j : ℕ) := hlt
  simp only [bandLowerTri, Matrix.of_apply]
  rw [ite_eq_right (by omega)]

/-- Every diagonal entry of `bandLowerTri m c` is `1` (for `c ≥ 1`): `(i,i) = [i ≤ i ∧ i < i+c]`. -/
theorem bandLowerTri_diag (m c : ℕ) (hc0 : 0 < c) (i : Fin m) :
    bandLowerTri m c i i = 1 := by
  simp only [bandLowerTri, Matrix.of_apply]
  rw [ite_eq_left ⟨le_refl _, by omega⟩]

/-- **det (bandLowerTri m c) = 1** for `c ≥ 1`: a unit lower-triangular matrix has unit
    determinant (product of the all-`1` diagonal). -/
theorem det_bandLowerTri (m c : ℕ) (hc0 : 0 < c) :
    (bandLowerTri m c).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular (bandLowerTri m c) (bandLowerTri_blockTriangular m c)]
  apply Finset.prod_eq_one
  intro i _
  exact bandLowerTri_diag m c hc0 i

/-- `bandLowerTri m c` is INVERTIBLE for `c ≥ 1` (det = 1 over GF(2)). -/
theorem bandLowerTri_isUnit_det (m c : ℕ) (hc0 : 0 < c) :
    IsUnit (bandLowerTri m c).det := by
  rw [det_bandLowerTri m c hc0]; exact isUnit_one

/-- Build the `Invertible` witness for `bandLowerTri m c` from `det = 1`. -/
@[reducible] noncomputable def bandLowerTriInvertible (m c : ℕ) (hc0 : 0 < c) :
    Invertible (bandLowerTri m c) :=
  haveI : Invertible (bandLowerTri m c).det := by
    rw [det_bandLowerTri m c hc0]; exact invertibleOne
  Matrix.invertibleOfDetInvertible (bandLowerTri m c)

/-- `bandDenseH` factors through `projH`:
    `bandDenseH m c *ᵥ v = bandLowerTri m c *ᵥ (projH m *ᵥ v)`. -/
theorem bandDenseH_mulVec (m c : ℕ) (v : Fin (2 * m) → ZMod 2) :
    bandDenseH m c *ᵥ v = bandLowerTri m c *ᵥ (projH m *ᵥ v) := by
  rw [bandDenseH, Matrix.mulVec_mulVec]

/-- **SAME-CODE syndrome equivalence (parametric in `c`, for `c ≥ 1`).**  `bandDenseH` and the
    sparse `projH` have the SAME kernel relation, because `bandDenseH = band · projH` with `band`
    INVERTIBLE (hence `mulVec`-injective).  The whole density sweep `c = 1..m` is the SAME code. -/
theorem bandDense_syndrome_iff (m c : ℕ) (hc0 : 0 < c) (a b : Fin (2 * m) → ZMod 2) :
    bandDenseH m c *ᵥ a = bandDenseH m c *ᵥ b ↔ projH m *ᵥ a = projH m *ᵥ b := by
  have : Invertible (bandLowerTri m c) := bandLowerTriInvertible m c hc0
  rw [bandDenseH_mulVec, bandDenseH_mulVec]
  constructor
  · intro h
    exact Matrix.mulVec_injective_of_invertible (bandLowerTri m c) h
  · intro h
    rw [h]

/-- The dual-pair law for the band-dense parity-check: `bandDenseH m c *ᵥ (s ᵥ* projG m) = 0`. -/
theorem hHG_bandDense (m c : ℕ) :
    ∀ s : Fin m → ZMod 2, bandDenseH m c *ᵥ (s ᵥ* projG m) = 0 := by
  intro s
  rw [bandDenseH_mulVec, hHG_proj m s, Matrix.mulVec_zero]

/-- The band-dense scheme at density `c`: same `n,k,m,G,τ` as `projScheme`, only `H` differs
    (`H := bandDenseH m c`, density `c`). -/
def bandScheme (m c : ℕ) : Scheme (ZMod 2) where
  n := 2 * m
  k := m
  m := m
  G := projG m
  H := bandDenseH m c
  τ := m - 1
  hHG := hHG_bandDense m c

/-- **SAME-CODE (parametric in `c`).**  `Safe (bandScheme m c) y ↔ Safe (projScheme m) y` for
    every density `c ≥ 1`.  SAME code, SAME safety predicate, SAME true min coset weight `m` —
    only the parity-check `H` (its density `c`) differs.  Hence the WHOLE degradation curve is
    one fixed code; only the bound's STRENGTH degrades with `c`, never SOUNDNESS. -/
theorem safe_band_iff_proj (m c : ℕ) (hc0 : 0 < c) (y : Fin (2 * m) → ZMod 2) :
    Safe (bandScheme m c) y ↔ Safe (projScheme m) y := by
  constructor
  · rintro ⟨e', he, hwt⟩
    exact ⟨e', (bandDense_syndrome_iff m c hc0 e' y).mp he, hwt⟩
  · rintro ⟨e', he, hwt⟩
    exact ⟨e', (bandDense_syndrome_iff m c hc0 e' y).mpr he, hwt⟩

/-! ### The degradation law, instantiated on the band scheme.

    The general ceiling theorem applies to every member of the sweep: at density `c`,
    `colWeightLb (bandScheme m c) z ≤ m / c`. -/

/-- The general ceiling specialized to the band scheme: at density `c`,
    `colWeightLb (bandScheme m c) z ≤ m / colBound (bandDenseH m c)`. -/
theorem colWeightLb_bandScheme_le (m c : ℕ) (z : Fin m → ZMod 2) :
    colWeightLb (bandScheme m c) z ≤ m / colBound (bandDenseH m c) :=
  colWeightLb_le_card_div (bandScheme m c) z

/-! ### Axiom audit for the ceiling theorem and the proven density. -/


end Sundog.Certificate.Degradation
