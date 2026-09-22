/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Diophantine.CoordinateCoprimeProduct

/-!
# Exact coordinate-zero patterns over a squarefree modulus

This file continues the elementary finite counting in published Section 7.  It counts points
whose first coordinate vanishes at exactly a prescribed collection of prime factors.  The result
is an exact finite product; no real asymptotic estimate is used.
-/

namespace BGS.Markoff

open Finset

/-- Primewise-punctured points whose first coordinate vanishes exactly at the indices in `R`. -/
def primewisePuncturedFirstCoordinateZeroExactlyOn
    {ι : Type*} [DecidableEq ι] (a : ι → ℕ) (R : Finset ι) :
    Set (PrimewisePuncturedMarkoffSurface a) :=
  {x | ∀ i,
    x i ∈ if i ∈ R then puncturedMarkoffFirstCoordinateZero (ZMod (a i))
      else puncturedMarkoffFirstCoordinateNonzero (ZMod (a i))}

@[simp] theorem mem_primewisePuncturedFirstCoordinateZeroExactlyOn_iff
    {ι : Type*} [DecidableEq ι] {a : ι → ℕ} {R : Finset ι}
    (x : PrimewisePuncturedMarkoffSurface a) :
    x ∈ primewisePuncturedFirstCoordinateZeroExactlyOn a R ↔
      ∀ i, x i ∈ puncturedMarkoffFirstCoordinateZero (ZMod (a i)) ↔ i ∈ R := by
  constructor
  · intro hx i
    specialize hx i
    by_cases hi : i ∈ R
    · simpa [primewisePuncturedFirstCoordinateZeroExactlyOn, hi] using hx
    · have hxNonzero :
          x i ∈ puncturedMarkoffFirstCoordinateNonzero (ZMod (a i)) := by
        simpa [primewisePuncturedFirstCoordinateZeroExactlyOn, hi] using hx
      simp only [puncturedMarkoffFirstCoordinateNonzero, Set.mem_compl_iff] at hxNonzero
      exact iff_of_false hxNonzero hi
  · intro hx i
    by_cases hi : i ∈ R
    · simpa [primewisePuncturedFirstCoordinateZeroExactlyOn, hi] using (hx i).mpr hi
    · have hzero : x i ∉ puncturedMarkoffFirstCoordinateZero (ZMod (a i)) := by
        intro h
        exact hi ((hx i).mp h)
      simpa [primewisePuncturedFirstCoordinateZeroExactlyOn, hi,
        puncturedMarkoffFirstCoordinateNonzero] using hzero

/-- An exact zero pattern is the product of the corresponding local zero and nonzero loci. -/
def primewisePuncturedFirstCoordinateZeroExactlyOnEquivPi
    {ι : Type*} [DecidableEq ι] (a : ι → ℕ) (R : Finset ι) :
    ↑(primewisePuncturedFirstCoordinateZeroExactlyOn a R) ≃
      ∀ i, ↑(if i ∈ R then puncturedMarkoffFirstCoordinateZero (ZMod (a i))
        else puncturedMarkoffFirstCoordinateNonzero (ZMod (a i))) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; funext i; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

/-- Exact product count for a prescribed set `R` of zero-coordinate prime factors. -/
theorem primewisePuncturedFirstCoordinateZeroExactlyOn_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, Fact (a i).Prime] (hmod : ∀ i, a i % 4 = 1) (R : Finset ι) :
    Nat.card ↑(primewisePuncturedFirstCoordinateZeroExactlyOn a R) =
      ∏ i, if i ∈ R then 2 * a i - 2 else a i ^ 2 + a i + 2 := by
  rw [Nat.card_congr (primewisePuncturedFirstCoordinateZeroExactlyOnEquivPi a R),
    Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ R
  · simp only [hi, ite_true]
    exact puncturedMarkoffFirstCoordinateZero_zmod_card_eq_of_mod_four_eq_one
      (a i) (hmod i)
  · simp only [hi, ite_false]
    exact puncturedMarkoffFirstCoordinateNonzero_zmod_card_eq_of_mod_four_eq_one
      (a i) (hmod i)

/-- The same prescribed zero pattern on the single-residue-ring CRT carrier. -/
def crtPrimewisePuncturedFirstCoordinateZeroExactlyOn
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) (R : Finset ι) :
    Set (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  {x | primewisePuncturedCRTEquiv a coprime x ∈
    primewisePuncturedFirstCoordinateZeroExactlyOn a R}

/-- CRT restricts to each prescribed zero-pattern carrier. -/
noncomputable def crtPrimewisePuncturedFirstCoordinateZeroExactlyOnEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) (R : Finset ι) :
    ↑(crtPrimewisePuncturedFirstCoordinateZeroExactlyOn a coprime R) ≃
      ↑(primewisePuncturedFirstCoordinateZeroExactlyOn a R) :=
  (primewisePuncturedCRTEquiv a coprime).subtypeEquiv fun _ => Iff.rfl

/-- Exact prescribed-pattern count in the CRT presentation. -/
theorem crtPrimewisePuncturedFirstCoordinateZeroExactlyOn_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, Fact (a i).Prime] (coprime : Pairwise (Function.onFun Nat.Coprime a))
    (hmod : ∀ i, a i % 4 = 1) (R : Finset ι) :
    Nat.card ↑(crtPrimewisePuncturedFirstCoordinateZeroExactlyOn a coprime R) =
      ∏ i, if i ∈ R then 2 * a i - 2 else a i ^ 2 + a i + 2 := by
  rw [Nat.card_congr
    (crtPrimewisePuncturedFirstCoordinateZeroExactlyOnEquiv a coprime R)]
  exact primewisePuncturedFirstCoordinateZeroExactlyOn_card_eq_of_mod_four_eq_one
    a hmod R

end BGS.Markoff
