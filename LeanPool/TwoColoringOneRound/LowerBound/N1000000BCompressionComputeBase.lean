/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.BigOperators.Field
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WedderburnData

/-!
Algebraic cancellation lemma used to keep integer cross-multiplication checks from ballooning:
we replace a term `(s : ℚ) / (D : ℚ)` by the reduced fraction obtained by cancelling
`g = gcd(|s|, D)`.
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000WedderburnData

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := N1000000WeakDuality.Block
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev qOfNat (m : Nat) : Q := (m : Q)
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev iOfNat (m : Nat) : Int := Int.ofNat m

private theorem tTr_lt (d : DirIdx) : tTr[d.1]! < masks.size := by
  fin_cases d <;> decide

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def invDir (d : DirIdx) : DirIdx :=
  ⟨tTr[d.1]!, tTr_lt d⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev basisDen (r : Block) : Nat :=
  moduleBasisDen[r.1]!

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def bValNum (r : Block) (j : Fin 3) (k : DirIdx) : Int :=
  if j.1 < blockSizes[r.1]! then
    ((moduleBasisNum[r.1]!).getD j.1 #[]).getD (tTr[k.1]!) 0
  else
    0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def bVal (r : Block) (j : Fin 3) (k : DirIdx) : Q :=
  (bValNum r j k : Q) / (basisDen r : Q)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def compBasis (r : Block) (d : DirIdx) : Matrix (Fin 3) (Fin 3) Q :=
  fun p q =>
    (Finset.univ.sum fun k : DirIdx =>
      (Finset.univ.sum fun a : DirIdx =>
        qOfNat (baseTypeCount k) * qOfNat (N k a d) * bVal r p k * bVal r q a))

private theorem D_pos : 0 < N1000000Data.D := by
  decide

private theorem DQ_ne_zero : (N1000000Data.D : Q) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt D_pos)

theorem div_by_D_eq_div_by_div_gcd (s : Int) :
    let g : Nat := Nat.gcd s.natAbs D
    (s : Q) / (D : Q) = ((s / (g : Int)) : Q) / ((D / g : Nat) : Q) := by
  classical
  let g : Nat := Nat.gcd s.natAbs D
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ D_pos
  have hg_le : g ≤ D := Nat.le_of_dvd D_pos (Nat.gcd_dvd_right s.natAbs D)
  have hDdiv_pos : 0 < D / g := Nat.div_pos hg_le hgpos
  have hD0 : (Int.ofNat D) ≠ 0 := by
    exact (Int.ofNat_ne_zero).2 (Nat.ne_of_gt D_pos)
  have hDdiv0 : (Int.ofNat (D / g)) ≠ 0 := by
    exact (Int.ofNat_ne_zero).2 (Nat.ne_of_gt hDdiv_pos)
  have hs_dvd : (g : Int) ∣ s := by
    exact (Int.natCast_dvd (n := s)).2 (Nat.gcd_dvd_left s.natAbs D)
  have hD_dvd : g ∣ D := Nat.gcd_dvd_right s.natAbs D
  -- Rewrite both sides into `Rat.divInt` form and use the exact `divInt_eq_divInt_iff` criterion.
  have hRat :
      Rat.divInt s (Int.ofNat D) = Rat.divInt (s / (g : Int)) (Int.ofNat (D / g)) := by
    -- Cross-multiply in `ℤ` via `divInt_eq_divInt_iff`.
    apply (Rat.divInt_eq_divInt_iff hD0 hDdiv0).2
    have hs_mul : (s / (g : Int)) * (g : Int) = s := by
      simpa using (Int.ediv_mul_cancel hs_dvd)
    have hD_mul : (D / g) * g = D := Nat.div_mul_cancel hD_dvd
    -- Target: `s * (D/g) = (s/g) * D`.
    -- Rewrite `s` as `(s/g) * g` and `D` as `(D/g) * g`.
    calc
      s * Int.ofNat (D / g)
          = ((s / (g : Int)) * (g : Int)) * Int.ofNat (D / g) := by
              -- rewrite `s` using `hs_mul` (reverse direction)
              simpa using congrArg (fun t => t * Int.ofNat (D / g)) (Eq.symm hs_mul)
      _ = (s / (g : Int)) * ((g : Int) * Int.ofNat (D / g)) := by
            simp [mul_assoc]
      _ = (s / (g : Int)) * Int.ofNat D := by
            -- `g * (D/g) = D` in `ℤ` (proved by casting the exact `Nat` identity).
            have hNat : (D / g) * g = D := hD_mul
            have hInt' : (Int.ofNat (D / g) : Int) * (g : Int) = Int.ofNat D := by
              -- Cast `hNat` to `ℤ` and rewrite `Nat` multiplication under the cast.
              have hCast : (Int.ofNat ((D / g) * g) : Int) = Int.ofNat D :=
                congrArg Int.ofNat hNat
              -- `↑((D/g) * g) = ↑(D/g) * ↑g`.
              simpa [Int.natCast_mul] using hCast
            have hInt : (g : Int) * Int.ofNat (D / g) = Int.ofNat D := by
              -- swap factors
              simpa [mul_comm, mul_left_comm, mul_assoc] using hInt'
            exact congrArg (fun t => (s / (g : Int)) * t) hInt
  -- Convert back from `Rat.divInt` to `/` in `ℚ`.
  calc
    (s : Q) / (D : Q) = Rat.divInt s (Int.ofNat D) := by
      -- `Rat.divInt_eq_div` plus coercions from `Nat`/`Int` to `ℚ`.
      simp [Rat.divInt_eq_div]
    _ = Rat.divInt (s / (g : Int)) (Int.ofNat (D / g)) := hRat
    _ = ((s / (g : Int)) : Q) / ((D / g : Nat) : Q) := by
      simp only [Rat.divInt_eq_div]
      have hs_cast : ((s / (g : Int) : Int) : Q) = (s : Q) / (g : Q) := by
        exact Int.cast_div_charZero (k := Q) (m := s) (n := (g : Int)) hs_dvd
      have hD_cast : (((D : Int) / (g : Int) : Int) : Q) = ((D / g : Nat) : Q) := by
        have hZ : ((D : Int) / (g : Int) : Int) = (D / g : Nat) := by
          exact Int.ofNat_ediv_ofNat (a := D) (b := g)
        have hQ1 :
            (((D : Int) / (g : Int) : Int) : Q) = (((D / g : Nat) : Int) : Q) :=
          congrArg (fun z : Int => (z : Q)) hZ
        have hQ2 : (((D / g : Nat) : Int) : Q) = ((D / g : Nat) : Q) := by
          rfl
        exact hQ1.trans hQ2
      simp [hs_cast, hD_cast]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def compBasisIntEntry (r : Block) (d : DirIdx) (p q : Fin 3) : Int :=
  (Finset.univ : Finset DirIdx).sum fun k =>
    (Finset.univ : Finset DirIdx).sum fun a =>
      (iOfNat (baseTypeCount k)) * (iOfNat (N k a d)) * (bValNum r p k) * (bValNum r q a)

private theorem basisDen_pos (r : Block) : 0 < basisDen r := by
  fin_cases r <;> decide

theorem basisDenQ_ne_zero (r : Block) : (basisDen r : Q) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (basisDen_pos r))

theorem compBasis_entry_eq_div (r : Block) (d : DirIdx) (p q : Fin 3) :
    compBasis r d p q =
      ((compBasisIntEntry r d p q : Int) : Q) / ((basisDen r : Q) * (basisDen r : Q)) := by
  classical
  set den : Q := (basisDen r : Q)
  have hden : den ≠ 0 := by
    simpa [den] using (basisDenQ_ne_zero r)
  have hden2 : den * den ≠ 0 := mul_ne_zero hden hden
  let num (k a : DirIdx) : Int :=
    iOfNat (baseTypeCount k) * iOfNat (N k a d) * bValNum r p k * bValNum r q a
  have hterm :
      ∀ k a : DirIdx,
        qOfNat (baseTypeCount k) * qOfNat (N k a d) * bVal r p k * bVal r q a =
          ((num k a : Int) : Q) / (den * den) := by
    intro k a
    apply (eq_div_iff hden2).2
    simp [bVal, den, num, qOfNat, iOfNat, div_eq_mul_inv]
    field_simp [hden]
    -- Cancel the remaining `basisDen` factor against its inverse.
    have hb : (basisDen r : Q) ≠ 0 := basisDenQ_ne_zero r
    -- Regroup into a `d * d⁻¹` subterm using associativity+commutativity, then simplify.
    let x : Q :=
      (↑(baseTypeCount k) * ↑(N k a d) * ↑(bValNum r p k) * ↑(bValNum r q a) : Q)
    have hx :
        (↑(baseTypeCount k) * ↑(N k a d) * ↑(bValNum r p k) * ↑(basisDen r) * ↑(bValNum r q a) *
              (↑(basisDen r))⁻¹ : Q)
          =
          x * (↑(basisDen r) * (↑(basisDen r))⁻¹) := by
      dsimp [x]
      ac_rfl
    have hx' : x * (↑(basisDen r) * (↑(basisDen r))⁻¹) = x := by
      simp [hb]
    simpa [x, div_eq_mul_inv] using hx.trans hx'
  have hsum :
      (Finset.univ.sum fun k : DirIdx =>
        Finset.univ.sum fun a : DirIdx =>
          qOfNat (baseTypeCount k) * qOfNat (N k a d) * bVal r p k * bVal r q a) =
        (Finset.univ.sum fun k : DirIdx =>
          Finset.univ.sum fun a : DirIdx =>
            ((num k a : Int) : Q) / (den * den)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    refine Finset.sum_congr rfl ?_
    intro a ha
    simpa using hterm k a
  have hinner (k : DirIdx) :
      (Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q) / (den * den)) =
        (Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) / (den * den) := by
    simpa using
      (Finset.sum_div (s := (Finset.univ : Finset DirIdx))
          (f := fun a : DirIdx => ((num k a : Int) : Q)) (a := den * den)).symm
  have houter :
      (Finset.univ.sum fun k : DirIdx =>
        Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q) / (den * den)) =
        (Finset.univ.sum fun k : DirIdx =>
          Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) / (den * den) := by
    calc
      (Finset.univ.sum fun k : DirIdx =>
          Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q) / (den * den))
          =
          (Finset.univ.sum fun k : DirIdx =>
            (Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) / (den * den)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa using hinner k
      _ =
          (Finset.univ.sum fun k : DirIdx =>
              Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) / (den * den) := by
            simpa using
              (Finset.sum_div (s := (Finset.univ : Finset DirIdx))
                  (f := fun k : DirIdx =>
                    Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) (a := den * den)).symm
  have hcast :
      (Finset.univ.sum fun k : DirIdx =>
        Finset.univ.sum fun a : DirIdx => ((num k a : Int) : Q)) =
        ((compBasisIntEntry r d p q : Int) : Q) := by
    simp [compBasisIntEntry, compBasisIntEntry, num]
  have hmain :
      compBasis r d p q = ((compBasisIntEntry r d p q : Int) : Q) / (den * den) := by
    dsimp [compBasis]
    rw [hsum, houter, hcast]
  simpa [den, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def compBasisSymm (r : Block) (d : DirIdx) : Matrix (Fin 3) (Fin 3) Q :=
  if tTr[d.1]! = d.1 then
    compBasis r d
  else
    compBasis r d + compBasis r (invDir d)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def idDirIdx : DirIdx :=
  ⟨idIndex, by decide⟩

private theorem varToOrbitRep_lt (i : Var) : varToOrbitRep[i.1]! < masks.size := by
  fin_cases i <;> decide

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varOrbit (i : Var) : DirIdx :=
  ⟨varToOrbitRep[i.1]!, varToOrbitRep_lt i⟩

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
