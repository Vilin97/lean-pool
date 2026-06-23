/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.Certificate
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Z

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000WeakDuality

open scoped BigOperators
open Matrix

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Z
open Distributed2Coloring.LowerBound.N1000000 -- from `Certificate.lean`

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := Fin numVars
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := Fin 7
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mu := Fin muSupport.size

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def xEdge (x : Var → Q) : Q :=
  x ⟨edgeVar, by decide⟩

private def defaultMu : Nat × Array Int × Int := (0, #[], 0)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def muNumD (k : Mu) : Int :=
  (muSupport.getD k.1 defaultMu).2.2

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def muVal (k : Mu) : Q :=
  (muNumD k : Q) / (D : Q)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def aVec (k : Mu) : Array Int :=
  (muSupport.getD k.1 defaultMu).2.1

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def aCoeffInt (k : Mu) (i : Var) : Int :=
  coeffAt (aVec k) i.1

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def aCoeff (k : Mu) (i : Var) : Q :=
  (aCoeffInt k i : Q)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def aDot (k : Mu) (x : Var → Q) : Q :=
  ∑ i : Var, (aCoeff k i) * x i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def muSum : Q :=
  ∑ k : Mu, muVal k

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def S0Num (r : Block) : Array (Array Int) :=
  S0Blocks.getD r.1 #[]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def SiNum (r : Block) (i : Var) : Array (Array Int) :=
  (SiBlocks.getD r.1 #[]).getD i.1 #[]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def S0 (r : Block) : Matrix (Fin 3) (Fin 3) Q :=
  toMat3Scaled D (S0Num r)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Si (r : Block) (i : Var) : Matrix (Fin 3) (Fin 3) Q :=
  toMat3Scaled D (SiNum r i)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def S (x : Var → Q) (r : Block) : Matrix (Fin 3) (Fin 3) Q :=
  S0 r + ∑ i : Var, x i • Si r i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def frobInner (A B : Matrix (Fin 3) (Fin 3) Q) : Q :=
  (A * Matrix.transpose B).trace

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def zSum0 : Q :=
  ∑ r : Block, frobInner (Z r) (S0 r)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def zCoeff (i : Var) : Q :=
  ∑ r : Block, frobInner (Z r) (Si r i)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def dualObjective : Q :=
  (dualObjectiveComputedD2 : Q) / ((D : Q) * (D : Q))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def PrimalFeasibleForCertificate (x : Var → Q) : Prop :=
  (∀ k : Mu, aDot k x ≤ (1 : Q)) ∧ ∀ r : Block, (S x r).PosSemidef

theorem muVal_nonneg (k : Mu) : 0 ≤ muVal k := by
  have hDpos : 0 < (D : Q) := by exact_mod_cast (show 0 < D by decide)
  have hnum : 0 ≤ muNumD k := by fin_cases k <;> decide
  simpa [muVal, div_eq_mul_inv] using
    mul_nonneg (show (0 : Q) ≤ muNumD k by exact_mod_cast hnum) (inv_nonneg.2 (le_of_lt hDpos))

private def innerNum (A B : Array (Array Int)) : Int :=
  (Finset.univ : Finset (Fin 3)).sum fun i =>
    (Finset.univ : Finset (Fin 3)).sum fun j =>
      (matGet A i.1 j.1) * (matGet B i.1 j.1)

private theorem frobInner_toMat3Scaled (A B : Array (Array Int)) :
    frobInner (toMat3Scaled D A) (toMat3Scaled D B)
      = ((innerNum A B : Q) / ((D : Q) * (D : Q))) := by
  classical
  -- Expand `trace (A * Bᵀ)`; for `3×3` this is the entrywise Frobenius sum.
  simp [frobInner, innerNum, toMat3Scaled, matGet, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]

private def muCoeff (i : Var) : Q :=
  ∑ k : Mu, (muVal k) * (aCoeff k i)

private def muCoeffNumD (i : Var) : Int :=
  ∑ k : Mu, (muNumD k) * (aCoeffInt k i)

private theorem muCoeff_eq_num (i : Var) :
    muCoeff i = ((muCoeffNumD i : Q) / (D : Q)) := by
  classical
  -- Everything has denominator `D`.
  have hDne : (D : Q) ≠ 0 := by exact_mod_cast (show (D : Nat) ≠ 0 by decide)
  -- Expand both sides and factor out `1/D`.
  simp [muCoeff,
    muCoeffNumD,
    muVal,
    aCoeff,
    div_eq_mul_inv,
    mul_left_comm,
    mul_comm,
    Finset.mul_sum]

private theorem muCoeffNumD_eq_linNumD (i : Var) : muCoeffNumD i = linNumD i.1 := by
  fin_cases i <;> decide

private theorem muCoeff_eq_lin (i : Var) :
    muCoeff i = (linNumD i.1 : Q) / (D : Q) := by
  simp [muCoeff_eq_num i, muCoeffNumD_eq_linNumD i]

private def zCoeffNumD2 (i : Var) : Int :=
  ∑ r : Block, innerNum (ZBlocks.getD r.1 #[]) (SiNum r i)

private theorem fintype_sum_div_const {α : Type*} [Fintype α] (f : α → Q) (c : Q) :
    (∑ x : α, f x / c) = (∑ x : α, f x) / c := by
  classical
  -- Rewrite division as multiplication by a constant, then commute that constant out of the sum.
  -- No nonzero hypothesis is needed since `c⁻¹` is defined for all `c`.
  simpa [div_eq_mul_inv] using
    (Finset.sum_mul (s := (Finset.univ : Finset α)) (f := f) (a := c⁻¹)).symm

private theorem zCoeff_eq_num (i : Var) :
    zCoeff i = ((zCoeffNumD2 i : Q) / ((D : Q) * (D : Q))) := by
  classical
  have hstep :
      zCoeff i =
        ∑ r : Block, (innerNum (ZBlocks.getD r.1 #[]) (SiNum r i) : Q) / ((D : Q) * (D : Q)) := by
    simp [zCoeff, Z, Si, frobInner_toMat3Scaled]
  rw [hstep, fintype_sum_div_const]
  simp [zCoeffNumD2]

private theorem zCoeffNumD2_eq_psdNumD2 (i : Var) : zCoeffNumD2 i = psdNumD2 i.1 := by
  fin_cases i <;> decide

private theorem zCoeff_eq_psd (i : Var) :
    zCoeff i = (psdNumD2 i.1 : Q) / ((D : Q) * (D : Q)) := by
  simp [zCoeff_eq_num i, zCoeffNumD2_eq_psdNumD2 i]

private def zSum0NumD2 : Int :=
  ∑ r : Block, innerNum (ZBlocks.getD r.1 #[]) (S0Num r)

private theorem zSum0_eq_num :
    zSum0 = ((zSum0NumD2 : Q) / ((D : Q) * (D : Q))) := by
  classical
  have hstep :
      zSum0 =
        ∑ r : Block, (innerNum (ZBlocks.getD r.1 #[]) (S0Num r) : Q) / ((D : Q) * (D : Q)) := by
    simp [zSum0, Z, S0, frobInner_toMat3Scaled]
  rw [hstep, fintype_sum_div_const]
  simp [zSum0NumD2]

private def psdSumD2 : Int :=
  ∑ r : Block, innerD2 (S0Blocks.getD r.1 #[]) (ZBlocks.getD r.1 #[])

private theorem zSum0NumD2_eq_psdSumD2 : zSum0NumD2 = psdSumD2 := by decide

private theorem psdSumD2_eq_psdSumD2_cert :
    psdSumD2 =
      (Finset.range S0Blocks.size).sum
        (fun r => innerD2 (S0Blocks.getD r #[]) (ZBlocks.getD r #[])) := by
  -- `S0Blocks.size = 7`.
  decide

private theorem zSum0_eq_psdSum :
    zSum0 = (psdSumD2 : Q) / ((D : Q) * (D : Q)) := by
  simp [zSum0_eq_num, zSum0NumD2_eq_psdSumD2]

private def muSumNumD : Int :=
  ∑ k : Mu, muNumD k

private theorem muSum_eq_num :
    muSum = ((muSumNumD : Q) / (D : Q)) := by
  classical
  simp [muSum, muSumNumD, muVal, div_eq_mul_inv, mul_comm, Finset.mul_sum]

private def muSumD_fold : Int :=
  muSupport.foldl (fun acc t => acc + t.2.2) 0

private theorem muSumNumD_eq_muSumD_fold : muSumNumD = muSumD_fold := by decide

private theorem dualObjective_eq_expression :
    dualObjective = -muSum - zSum0 := by
  classical
  have hDne : (D : Q) ≠ 0 := by exact_mod_cast (show (D : Nat) ≠ 0 by decide)
  -- Unfold and clear denominators; the remaining goal is exactly the definition of
  -- `dualObjectiveComputedD2`.
  unfold dualObjective
  rw [muSum_eq_num, zSum0_eq_psdSum]
  field_simp [hDne]
  -- The `μ`-sum is represented both as a `Fintype` sum and as a `foldl`; relate them,
  -- and rewrite the `S0`-sum into the `Finset.range` form used by `dualObjectiveComputedD2`.
  simp [dualObjectiveComputedD2,
    muSumD_fold,
    muSumNumD_eq_muSumD_fold,
    psdSumD2_eq_psdSumD2_cert,
    sub_eq_add_neg,
    mul_comm, add_comm]

private theorem stationarity (i : Var) :
    (if i.1 = edgeVar then (1 : Q) else 0) + muCoeff i - zCoeff i = 0 := by
  classical
  -- Integer stationarity is checked coordinatewise; convert and rewrite the coefficients.
  have hInt : stationarityLHSD2 i.1 = -(c i.1) * ((D : Int) * (D : Int)) := by
    fin_cases i <;> decide
  have hDne : (D : Q) ≠ 0 := by exact_mod_cast (show (D : Nat) ≠ 0 by decide)
  have hD2ne : ((D : Q) * (D : Q)) ≠ 0 := by simp [hDne]
  have hQ :
      ((linNumD i.1 : Q) * (D : Q) - (psdNumD2 i.1 : Q)) =
        (-(c i.1) : Q) * ((D : Q) * (D : Q)) := by
    simpa [stationarityLHSD2] using (show
      (stationarityLHSD2 i.1 : Q) =
        (-(c i.1) * ((D : Int) * (D : Int)) : Q) by
      exact_mod_cast hInt)
  have hc : (-(c i.1) : Q) = if i.1 = edgeVar then (-1 : Q) else 0 := by
    by_cases h : i.1 = edgeVar <;> simp [c, h]
  -- Divide the `D^2`-cleared equality and rewrite the coefficients.
  have hDiv :
      (linNumD i.1 : Q) / (D : Q) - (psdNumD2 i.1 : Q) / ((D : Q) * (D : Q))
        = if i.1 = edgeVar then (-1 : Q) else 0 := by
    -- Clear denominators with `field_simp`; the resulting goal is exactly `hQ`.
    have h' :
        (linNumD i.1 : Q) / (D : Q) - (psdNumD2 i.1 : Q) / ((D : Q) * (D : Q))
          = (-(c i.1) : Q) := by
      field_simp [hDne]
      -- `field_simp` produces `linNumD*D - psdNumD2 = -(c)*D^2`.
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hQ
    simpa [hc] using h'
  calc
    (if i.1 = edgeVar then (1 : Q) else 0) + muCoeff i - zCoeff i
        = (if i.1 = edgeVar then (1 : Q) else 0)
            + ((linNumD i.1 : Q) / (D : Q)) - ((psdNumD2 i.1 : Q) / ((D : Q) * (D : Q))) := by
            simp [muCoeff_eq_lin i, zCoeff_eq_psd i, sub_eq_add_neg, add_assoc]
    _ = (if i.1 = edgeVar then (1 : Q) else 0) + (if i.1 = edgeVar then (-1 : Q) else 0) := by
            -- Reassociate so that `hDiv` rewrites the parenthesized difference.
            have := congrArg (fun t : Q => (if i.1 = edgeVar then (1 : Q) else 0) + t) hDiv
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    _ = 0 := by by_cases h : i.1 = edgeVar <;> simp [h]

theorem weakDuality (x : Var → Q) (hx : PrimalFeasibleForCertificate x) :
    dualObjective ≤ xEdge x := by
  classical
  -- Sum the stationarity identities weighted by `x i`.
  have hstatSum :
      (∑ i : Var, x i *
        ((if i.1 = edgeVar then (1 : Q) else 0) + muCoeff i - zCoeff i)) = 0 := by
    simp [stationarity]
  -- Edge contribution.
  have hedge :
      (∑ i : Var, x i * (if i.1 = edgeVar then (1 : Q) else 0)) = xEdge x := by
    let e : Var := ⟨edgeVar, by decide⟩
    have :
        (∑ i : Var, x i * (if i.1 = edgeVar then (1 : Q) else 0)) = x e := by
      refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro i _ hi
        have : i.1 ≠ edgeVar := by
          intro hEq
          apply hi
          apply Fin.ext
          exact hEq
        simp [this]
      · intro he
        simp at he
      · simp [e]
    simpa [xEdge, e] using this
  -- Commute the finite sums for the μ term.
  have hMuComm :
      (∑ i : Var, x i * muCoeff i) = ∑ k : Mu, (muVal k) * aDot k x := by
    classical
    -- Expand both sides, then commute the two finite sums.
    unfold muCoeff aDot
    -- LHS: ∑ i, x_i * ∑ k, μ_k * a_{k,i} = ∑ i ∑ k ...
    -- Commute to ∑ k ∑ i ..., then refactor μ_k.
    calc
      (∑ i : Var, x i * ∑ k : Mu, muVal k * aCoeff k i)
          = ∑ i : Var, ∑ k : Mu, x i * (muVal k * aCoeff k i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [Finset.mul_sum]
      _ = ∑ k : Mu, ∑ i : Var, x i * (muVal k * aCoeff k i) := by
              simpa using
                (Finset.sum_comm (s := (Finset.univ : Finset Var)) (t := (Finset.univ : Finset Mu))
                  (f := fun i k => x i * (muVal k * aCoeff k i)))
      _ = ∑ k : Mu, muVal k * ∑ i : Var, aCoeff k i * x i := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
      _ = ∑ k : Mu, muVal k * aDot k x := by simp [aDot]
  -- Commute the finite sums for the Z term.
  have hZComm :
      (∑ i : Var, x i * zCoeff i) = ∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i) := by
    classical
    -- Expand `zCoeff`, commute the two finite sums, then refactor using linearity of `frobInner`
    -- in the right argument.
    unfold zCoeff
    calc
      (∑ i : Var, x i * ∑ r : Block, frobInner (Z r) (Si r i))
          = ∑ i : Var, ∑ r : Block, x i * frobInner (Z r) (Si r i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [Finset.mul_sum]
      _ = ∑ r : Block, ∑ i : Var, x i * frobInner (Z r) (Si r i) := by
              simpa using
                (Finset.sum_comm (s := (Finset.univ : Finset Var))
                  (t := (Finset.univ : Finset Block))
                  (f := fun i r => x i * frobInner (Z r) (Si r i)))
      _ = ∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              -- Expand `frobInner` and use linearity of `trace` and `mul` over sums.
              simp [frobInner,
                Matrix.transpose_sum,
                Matrix.transpose_smul,
                Matrix.trace_sum,
                Matrix.trace_smul,
                Finset.mul_sum]
  -- Rearrange stationarity to solve for `xEdge x`.
  have hxEdge :
      xEdge x =
        - (∑ k : Mu, (muVal k) * aDot k x)
          + ∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i) := by
    have h0' :
        (∑ i : Var, x i * (if i.1 = edgeVar then (1 : Q) else 0))
          + (∑ i : Var, x i * muCoeff i) - (∑ i : Var, x i * zCoeff i) = 0 := by
      -- Expand the summand `x i * (edge + mu - z)` and distribute sums.
      simpa [sub_eq_add_neg,
        mul_add,
        add_mul,
        Finset.sum_add_distrib,
        Finset.sum_sub_distrib,
        add_assoc,
        add_left_comm, add_comm] using hstatSum
    have h0 :
        xEdge x + (∑ i : Var, x i * muCoeff i) - (∑ i : Var, x i * zCoeff i) = 0 := by
      -- Rewrite the edge-indicator sum to `xEdge x` without letting `simp` change its shape first.
      have h := h0'
      rw [hedge] at h
      simpa using h
    have :
        xEdge x = - (∑ i : Var, x i * muCoeff i) + (∑ i : Var, x i * zCoeff i) := by
      linarith
    simpa [hMuComm, hZComm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Linear constraints: `∑ μ_k aDot_k(x) ≤ ∑ μ_k`.
  have hMuIneq :
      - (∑ k : Mu, (muVal k) * aDot k x) ≥ - (∑ k : Mu, muVal k) := by
    have hsumLe : (∑ k : Mu, (muVal k) * aDot k x) ≤ ∑ k : Mu, muVal k := by
      refine Finset.sum_le_sum ?_
      intro k _
      have hk : aDot k x ≤ (1 : Q) := hx.1 k
      have hμ : 0 ≤ muVal k := muVal_nonneg k
      have : muVal k * aDot k x ≤ muVal k * (1 : Q) := mul_le_mul_of_nonneg_left hk hμ
      simpa using this
    simpa using (neg_le_neg hsumLe)
  -- PSD constraints: for each block, `frobInner(Z_r, S_r(x)) ≥ 0`.
  have hPsdNonneg : ∀ r : Block, 0 ≤ frobInner (Z r) (S x r) := by
    intro r
    have hS : (S x r).PosSemidef := hx.2 r
    have hSt : (Matrix.transpose (S x r)).PosSemidef := hS.transpose
    simpa [frobInner, Matrix.mul_assoc] using
      (trace_mul_nonneg_of_Z_posSemidef (r := r) (S := Matrix.transpose (S x r)) hSt)
  -- PSD implies `frobInner(Z_r, ∑ x_i Si_r_i) ≥ -frobInner(Z_r,S0_r)`.
  have hPsdIneq :
      (∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i))
        ≥ - ∑ r : Block, frobInner (Z r) (S0 r) := by
    have hblock :
        ∀ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i) ≥ -frobInner (Z r) (S0 r) := by
      intro r
      have hadd :
          frobInner (Z r) (S x r) =
            frobInner (Z r) (S0 r) + frobInner (Z r) (∑ i : Var, x i • Si r i) := by
        simp [S, frobInner, Matrix.mul_add, Matrix.trace_add, Matrix.transpose_add]
      linarith [hPsdNonneg r, hadd]
    have : (∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i))
        ≥ ∑ r : Block, (-frobInner (Z r) (S0 r)) := by
      refine Finset.sum_le_sum ?_
      intro r _
      exact hblock r
    simpa [Finset.sum_neg_distrib] using this
  -- Combine and rewrite the dual objective.
  have hDual : dualObjective = -muSum - zSum0 := dualObjective_eq_expression
  -- Finish.
  rw [hDual]
  -- Use `hxEdge` to rewrite `xEdge x` and apply the two bounds.
  have : xEdge x ≥ -muSum - zSum0 := by
    -- Rewrite `muSum` and `zSum0` as sums to match the inequalities.
    have h1 : - (∑ k : Mu, (muVal k) * aDot k x) ≥ -muSum := by simpa [muSum] using hMuIneq
    have h2 :
        (∑ r : Block, frobInner (Z r) (∑ i : Var, x i • Si r i)) ≥ -zSum0 := by
      simpa [zSum0] using hPsdIneq
    -- Combine with `hxEdge`.
    rw [hxEdge]
    linarith
  simpa [xEdge] using this

end N1000000WeakDuality

end Distributed2Coloring.LowerBound
