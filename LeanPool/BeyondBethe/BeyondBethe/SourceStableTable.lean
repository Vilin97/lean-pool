/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.SourceStableClosure
public import LeanPool.BeyondBethe.BeyondBethe.SourceStableBivariate
public import Mathlib.Tactic

/-! # Source Stable Table -/

@[expose] public section

namespace BeyondBethe

/-!
# A coefficient-table model for the multilinear source induction

A table records the coefficient of every pair of squarefree monomials.  The
recursive variable type places the next left variable first and the next
right variable second.  With this ordering, sign reversal on the right turns
one recursion step into two nested `linearExtension`s, exactly the form used
by the formal Lieb--Sokal contraction.
-/

/-- A real coefficient table indexed by two Boolean selectors on `n` coordinates. -/
abbrev PairTable (n : ℕ) :=
  (Fin n → Bool) → (Fin n → Bool) → ℝ

/-- Prepends one Boolean head coordinate to a finite Boolean selector. -/
def prependBool {n : ℕ} (b : Bool) (S : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cases b S

/-- Fixes the two head selector bits and retains a table on the remaining coordinates. -/
def pairTableSection {n : ℕ} (c : PairTable (n + 1))
    (left right : Bool) : PairTable n :=
  fun S T ↦ c (prependBool left S) (prependBool right T)

/-- A recursively encoded type containing two fresh optional variables for each coordinate. -/
def PairVariables : ℕ → Type
  | 0 => PEmpty
  | n + 1 => Option (Option (PairVariables n))

noncomputable instance pairVariablesFintype (n : ℕ) : Fintype (PairVariables n) := by
  induction n with
  | zero =>
      change Fintype PEmpty
      exact inferInstance
  | succ n ih =>
      letI : Fintype (PairVariables n) := ih
      change Fintype (Option (Option (PairVariables n)))
      exact inferInstance

/-- Builds the signed polynomial associated with a pair table using two linear extensions per
coordinate and negative right-variable coefficients. -/
noncomputable def pairTableStablePolynomial :
    ∀ n : ℕ, PairTable n → MvPolynomial (PairVariables n) ℂ
  | 0, c => MvPolynomial.C (c (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) : ℂ)
  | n + 1, c =>
      let A := pairTableStablePolynomial n (pairTableSection c true true)
      let B := pairTableStablePolynomial n (pairTableSection c true false)
      let C := pairTableStablePolynomial n (pairTableSection c false true)
      let D := pairTableStablePolynomial n (pairTableSection c false false)
      linearExtension (linearExtension D (-C)) (linearExtension B (-A))

/-- Requires every coefficient-table entry to be nonnegative. -/
def PairTableNonnegative {n : ℕ} (c : PairTable n) : Prop :=
  ∀ S T, 0 ≤ c S T

/-- Requires the associated signed polynomial to be zero or upper-half-plane stable. -/
def PairTableStableOrZero {n : ℕ} (c : PairTable n) : Prop :=
  pairTableStablePolynomial n c = 0 ∨
    IsUpperHalfPlaneStable (pairTableStablePolynomial n c)

/-- Recursively evaluates a pair table on real vectors by its four head-coordinate sections. -/
noncomputable def pairTableEval :
    ∀ n : ℕ, PairTable n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, c, _, _ => c (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  | n + 1, c, y, z =>
      let yt : Fin n → ℝ := fun i ↦ y i.succ
      let zt : Fin n → ℝ := fun i ↦ z i.succ
      let a := pairTableEval n (pairTableSection c true true) yt zt
      let b := pairTableEval n (pairTableSection c true false) yt zt
      let cc := pairTableEval n (pairTableSection c false true) yt zt
      let d := pairTableEval n (pairTableSection c false false) yt zt
      a * y 0 * z 0 + b * y 0 + cc * z 0 + d

/-- Sums diagonal table coefficients by recursively retaining only equal head-selector pairs. -/
noncomputable def pairTableDiagonalSum : ∀ n : ℕ, PairTable n → ℝ
  | 0, c => c (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  | n + 1, c =>
      pairTableDiagonalSum n (pairTableSection c false false) +
        pairTableDiagonalSum n (pairTableSection c true true)

/-- Multiplies the scalar stability-boundary factors over all coordinates. -/
noncomputable def pairTableBoundary : ∀ n : ℕ, (Fin n → ℝ) → ℝ
  | 0, _ => 1
  | n + 1, α =>
      stableBoundaryScalar (α 0) * pairTableBoundary n (fun i ↦ α i.succ)

/-- Multiplies the coordinate powers `x i ^ α i` with real exponents. -/
noncomputable def pairTableMonomial :
    ∀ n : ℕ, (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, _ => 1
  | n + 1, x, α =>
      (x 0) ^ (α 0) * pairTableMonomial n (fun i ↦ x i.succ) (fun i ↦ α i.succ)

theorem pairTableStablePolynomial_multiaffine :
    ∀ {n : ℕ} (c : PairTable n),
      IsComplexMultiaffine (pairTableStablePolynomial n c) := by
  intro n
  induction n with
  | zero =>
      intro c i
      exact PEmpty.elim i
  | succ n ih =>
      intro c
      dsimp only [pairTableStablePolynomial]
      apply linearExtension_multiaffine
      · apply linearExtension_multiaffine
        · exact ih _
        · intro i
          simpa using ih (pairTableSection c false true) i
      · apply linearExtension_multiaffine
        · exact ih _
        · intro i
          simpa using ih (pairTableSection c true true) i

theorem pairTableSection_nonnegative
    {n : ℕ} {c : PairTable (n + 1)} (hc : PairTableNonnegative c)
    (left right : Bool) :
    PairTableNonnegative (pairTableSection c left right) := by
  intro S T
  exact hc _ _

/-- Adds pair tables entrywise. -/
def pairTableAdd {n : ℕ} (c d : PairTable n) : PairTable n :=
  fun S T ↦ c S T + d S T

/-- Contracts a head coordinate by adding its false-false and true-true coefficient sections. -/
def pairTableContract {n : ℕ} (c : PairTable (n + 1)) : PairTable n :=
  pairTableAdd (pairTableSection c false false)
    (pairTableSection c true true)

theorem linearExtension_add {ι : Type*}
    (g₁ f₁ g₂ f₂ : MvPolynomial ι ℂ) :
    linearExtension (g₁ + g₂) (f₁ + f₂) =
      linearExtension g₁ f₁ + linearExtension g₂ f₂ := by
  simp only [linearExtension, map_add, mul_add]
  abel

theorem pairTableStablePolynomial_add :
    ∀ {n : ℕ} (c d : PairTable n),
      pairTableStablePolynomial n (pairTableAdd c d) =
        pairTableStablePolynomial n c + pairTableStablePolynomial n d := by
  intro n
  induction n with
  | zero =>
      intro c d
      simp [pairTableStablePolynomial, pairTableAdd]
  | succ n ih =>
      intro c d
      simp only [pairTableStablePolynomial]
      have hsection (l r : Bool) :
          pairTableSection (pairTableAdd c d) l r =
            pairTableAdd (pairTableSection c l r) (pairTableSection d l r) := by
        rfl
      simp_rw [hsection, ih]
      simp only [neg_add_rev, add_comm, linearExtension_add]
      rfl

theorem pairTableEval_add :
    ∀ {n : ℕ} (c d : PairTable n) (y z : Fin n → ℝ),
      pairTableEval n (pairTableAdd c d) y z =
        pairTableEval n c y z + pairTableEval n d y z := by
  intro n
  induction n with
  | zero =>
      intro c d y z
      simp [pairTableEval, pairTableAdd]
  | succ n ih =>
      intro c d y z
      simp only [pairTableEval]
      have hsection (l r : Bool) :
          pairTableSection (pairTableAdd c d) l r =
            pairTableAdd (pairTableSection c l r) (pairTableSection d l r) := by
        rfl
      simp_rw [hsection, ih]
      ring

theorem pairTableEval_nonnegative :
    ∀ {n : ℕ} {c : PairTable n} {y z : Fin n → ℝ},
      PairTableNonnegative c →
      (∀ i, 0 ≤ y i) → (∀ i, 0 ≤ z i) →
      0 ≤ pairTableEval n c y z := by
  intro n
  induction n with
  | zero =>
      intro c y z hc hy hz
      exact hc _ _
  | succ n ih =>
      intro c y z hc hy hz
      simp only [pairTableEval]
      have hyt : ∀ i : Fin n, 0 ≤ y i.succ := fun i ↦ hy i.succ
      have hzt : ∀ i : Fin n, 0 ≤ z i.succ := fun i ↦ hz i.succ
      have ha := ih (pairTableSection_nonnegative hc true true) hyt hzt
      have hb := ih (pairTableSection_nonnegative hc true false) hyt hzt
      have hcc := ih (pairTableSection_nonnegative hc false true) hyt hzt
      have hd := ih (pairTableSection_nonnegative hc false false) hyt hzt
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (mul_nonneg ha (hy 0)) (hz 0))
            (mul_nonneg hb (hy 0)))
          (mul_nonneg hcc (hz 0))) hd

theorem pairTableDiagonalSum_add :
    ∀ {n : ℕ} (c d : PairTable n),
      pairTableDiagonalSum n (pairTableAdd c d) =
        pairTableDiagonalSum n c + pairTableDiagonalSum n d := by
  intro n
  induction n with
  | zero =>
      intro c d
      simp [pairTableDiagonalSum, pairTableAdd]
  | succ n ih =>
      intro c d
      simp only [pairTableDiagonalSum]
      have hsection (l r : Bool) :
          pairTableSection (pairTableAdd c d) l r =
            pairTableAdd (pairTableSection c l r) (pairTableSection d l r) := by
        rfl
      simp_rw [hsection, ih]
      ring

theorem pairTableContract_nonnegative
    {n : ℕ} {c : PairTable (n + 1)}
    (hc : PairTableNonnegative c) :
    PairTableNonnegative (pairTableContract c) := by
  intro S T
  exact add_nonneg (hc _ _) (hc _ _)

/-- The diagonal contraction is stable or zero.  This is the exact operator
step in the Anari--Oveis Gharan induction. -/
theorem pairTableContract_stableOrZero
    {n : ℕ} (c : PairTable (n + 1))
    (hstable : PairTableStableOrZero c) :
    PairTableStableOrZero (pairTableContract c) := by
  let A := pairTableStablePolynomial n (pairTableSection c true true)
  let B := pairTableStablePolynomial n (pairTableSection c true false)
  let C := pairTableStablePolynomial n (pairTableSection c false true)
  let D := pairTableStablePolynomial n (pairTableSection c false false)
  have hcontract :
      pairTableStablePolynomial n (pairTableContract c) = D + A := by
    rw [pairTableContract, pairTableStablePolynomial_add]
  rcases hstable with hzero | hstable
  · change
      linearExtension (linearExtension D (-C)) (linearExtension B (-A)) = 0 at hzero
    have hout : linearExtension D (-C) = 0 :=
      (linearExtension_eq_zero_iff.mp (by
        exact hzero)).1
    have hD : D = 0 := (linearExtension_eq_zero_iff.mp hout).1
    have hin : linearExtension B (-A) = 0 :=
      (linearExtension_eq_zero_iff.mp (by
        exact hzero)).2
    have hA : A = 0 := by
      have := (linearExtension_eq_zero_iff.mp hin).2
      simpa using this
    left
    rw [hcontract, hD, hA, add_zero]
  · change
      IsUpperHalfPlaneStable
        (linearExtension (linearExtension D (-C)) (linearExtension B (-A))) at hstable
    have hLS := liebSokal_linear_contraction
        (linearExtension D (-C)) B (-A) (by
          exact hstable)
    have hrewrite :
        linearExtension D (-C) - MvPolynomial.rename some (-A) =
          linearExtension (D + A) (-C) := by
      simp [linearExtension]
      ring
    rw [hrewrite] at hLS
    rcases hLS with hzero | hLS
    · have hDA := (linearExtension_eq_zero_iff.mp hzero).1
      left
      rwa [hcontract]
    · have hboundary := linearExtension_constantCoefficient_stableOrZero hLS
      change pairTableStablePolynomial n (pairTableContract c) = 0 ∨
        IsUpperHalfPlaneStable (pairTableStablePolynomial n (pairTableContract c))
      rw [hcontract]
      exact hboundary

end BeyondBethe
