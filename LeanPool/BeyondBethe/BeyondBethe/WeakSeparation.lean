/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.DirectedOptimizerOracle
public import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby
public import LeanPool.BeyondBethe.BeyondBethe.NumericalPotentials
public import Mathlib.Tactic

/-! # Weak Separation -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Supporting cuts in rational affine coordinates

The affine pullback of a full matrix gradient has a four-corner formula.
Making this formula explicit avoids any appeal to an abstract adjoint and is
the algebraic core of the separation oracle.
-/

/-- Pull a full matrix covector back through the upper-left affine
parametrization of the Birkhoff affine hull. -/
def affinePullbackGradient {n : ℕ} {R : Type*} [AddCommGroup R]
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ G i.castSucc j.castSucc - G i.castSucc (Fin.last n) -
    G (Fin.last n) j.castSucc + G (Fin.last n) (Fin.last n)

/-- Matrix pairing written as an explicit finite sum. -/
def matrixPairing {m n : Type*} [Fintype m] [Fintype n]
    {R : Type*} [Semiring R] (G D : Matrix m n R) : R :=
  ∑ i, ∑ j, G i j * D i j

/-- Exact adjoint identity for the affine recovery map. -/
theorem matrixPairing_affineMap_sub {n : ℕ} {R : Type*} [CommRing R]
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (Y Z : Matrix (Fin n) (Fin n) R) :
    matrixPairing G
        (fun i j ↦ birkhoffAffineMap Z i j - birkhoffAffineMap Y i j) =
      matrixPairing (affinePullbackGradient G)
        (fun i j ↦ Z i j - Y i j) := by
  simp only [matrixPairing]
  have hpull : ∀ i j,
      affinePullbackGradient G i j * (Z i j - Y i j) =
        G i.castSucc j.castSucc * Z i j -
          G i.castSucc j.castSucc * Y i j -
          G i.castSucc (Fin.last n) * Z i j +
          G i.castSucc (Fin.last n) * Y i j -
          G (Fin.last n) j.castSucc * Z i j +
          G (Fin.last n) j.castSucc * Y i j +
          G (Fin.last n) (Fin.last n) * Z i j -
          G (Fin.last n) (Fin.last n) * Y i j := by
    intro i j
    rw [affinePullbackGradient]
    ring
  simp_rw [hpull]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp only [birkhoffAffineMap_castSucc_castSucc,
    birkhoffAffineMap_castSucc_last, birkhoffAffineMap_last_castSucc,
    birkhoffAffineMap_last_last]
  ring_nf
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hcolZ :
      (∑ j, ∑ i, G (Fin.last n) j.castSucc * Z i j) =
        ∑ i, ∑ j, G (Fin.last n) j.castSucc * Z i j := by
    exact Finset.sum_comm
  have hcolY :
      (∑ j, ∑ i, G (Fin.last n) j.castSucc * Y i j) =
        ∑ i, ∑ j, G (Fin.last n) j.castSucc * Y i j := by
    exact Finset.sum_comm
  rw [hcolZ, hcolY]
  repeat' first
    | rw [Finset.sum_add_distrib]
    | rw [Finset.sum_sub_distrib]
    | rw [Finset.sum_neg_distrib]
  have hupperBlock :
      (∑ i, ∑ j,
          (G i.castSucc j.castSucc * Z i j -
            G i.castSucc j.castSucc * Y i j)) =
        (∑ i, ∑ j, G i.castSucc j.castSucc * Z i j) -
          ∑ i, ∑ j, G i.castSucc j.castSucc * Y i j := by
    simp only [Finset.sum_sub_distrib]
  rw [hupperBlock]
  module

/-- The negative regularized objective in upper-left affine coordinates. -/
noncomputable def affineNegativeObjective {n : ℕ}
    (τ : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -regularizedBetheObjective τ A (birkhoffAffineMap Y)

/-- The exact full negative gradient at a rational or real interior point. -/
noncomputable def negativeGradientMatrix {n : ℕ}
    (τ : ℝ) (A X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ negativeRegularizedBetheGradientCoordinate τ (A i j) (X i j)

theorem negativeGradientMatrix_eq_neg_gradient {n : ℕ}
    (τ : ℝ) (A X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    negativeGradientMatrix τ A X i j =
      -regularizedBetheGradient τ A X i j := by
  rw [negativeGradientMatrix, regularizedBetheGradient,
    negativeRegularizedBetheGradientCoordinate_eq_neg]

/-- Convexity gives the exact supporting-hyperplane inequality in the
explicit affine coordinates. -/
theorem affineNegativeObjective_support
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 ≤ τ)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Y Z : Matrix (Fin n) (Fin n) ℝ}
    (hY : IsDoublyStochastic (birkhoffAffineMap Y))
    (hZ : IsDoublyStochastic (birkhoffAffineMap Z))
    (hYint : ∀ i, IsInteriorProbabilityVector (birkhoffAffineMap Y i)) :
    affineNegativeObjective τ A Y +
        matrixPairing
          (affinePullbackGradient
            (negativeGradientMatrix τ A (birkhoffAffineMap Y)))
          (fun i j ↦ Z i j - Y i j) ≤
      affineNegativeObjective τ A Z := by
  have hsupp := regularizedBetheObjective_sub_le_gradient
    (show 1 < Fintype.card (Fin (n + 1)) by simp; omega)
    (A := A) (X := birkhoffAffineMap Y) (Y := birkhoffAffineMap Z)
    hτ hY hZ hYint
  have hpair := matrixPairing_affineMap_sub
    (negativeGradientMatrix τ A (birkhoffAffineMap Y)) Y Z
  have hG : negativeGradientMatrix τ A (birkhoffAffineMap Y) =
      fun i j ↦ -regularizedBetheGradient τ A (birkhoffAffineMap Y) i j := by
    ext i j
    exact negativeGradientMatrix_eq_neg_gradient τ A (birkhoffAffineMap Y) i j
  rw [hG] at hpair ⊢
  simp only [matrixPairing, neg_mul] at hpair ⊢
  rw [← hpair]
  simp_rw [Finset.sum_neg_distrib]
  simp only [affineNegativeObjective]
  linarith

/-- Executable rational full-gradient lower endpoint. -/
def directedNegativeGradientLowerMatrix {n : ℕ}
    (τ : ℚ) (A X : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ directedNegativeGradientLower τ (A i j) (X i j) p

/-- Every pullback coordinate combines four full-gradient coordinates.  Thus
an entrywise full-gradient error `e` becomes at most `4e`. -/
theorem affinePullbackGradient_error_le_four
    {n : ℕ} {G H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {e : ℝ}
    (h : ∀ i j, abs (G i j - H i j) ≤ e) (i j : Fin n) :
    abs (affinePullbackGradient G i j -
        affinePullbackGradient H i j) ≤ 4 * e := by
  rw [affinePullbackGradient, affinePullbackGradient]
  have hid :
      (G i.castSucc j.castSucc - G i.castSucc (Fin.last n) -
          G (Fin.last n) j.castSucc + G (Fin.last n) (Fin.last n)) -
        (H i.castSucc j.castSucc - H i.castSucc (Fin.last n) -
          H (Fin.last n) j.castSucc + H (Fin.last n) (Fin.last n)) =
      (G i.castSucc j.castSucc - H i.castSucc j.castSucc) -
        (G i.castSucc (Fin.last n) - H i.castSucc (Fin.last n)) -
        (G (Fin.last n) j.castSucc - H (Fin.last n) j.castSucc) +
        (G (Fin.last n) (Fin.last n) - H (Fin.last n) (Fin.last n)) := by ring
  rw [hid]
  exact abs_sub_sub_add_le_four
    (h i.castSucc j.castSucc) (h i.castSucc (Fin.last n))
    (h (Fin.last n) j.castSucc) (h (Fin.last n) (Fin.last n))

/-- At precision `p`, the executable pullback gradient is within
`16·2⁻ᵖ` in every coordinate. -/
theorem directedAffineGradient_error
    {n : ℕ} {τ : ℚ} {A X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : ∀ i j, 0 < A i j)
    (hX0 : ∀ i j, 0 < X i j) (hX1 : ∀ i j, X i j < 1)
    (p : ℕ) (i j : Fin n) :
    abs (affinePullbackGradient
          (negativeGradientMatrix (τ : ℝ)
            (fun i j ↦ (A i j : ℝ)) (fun i j ↦ (X i j : ℝ))) i j -
        (affinePullbackGradient
          (fun i j ↦ ((directedNegativeGradientLowerMatrix τ A X p i j : ℚ) : ℝ))) i j) ≤
      16 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  apply (affinePullbackGradient_error_le_four
    (e := 4 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ)) ?_ i j).trans_eq
  · ring
  intro a b
  have hb := directedNegativeGradient_bounds hτ0 hτ1
    (hA a b) (hX0 a b) (hX1 a b) p
  have hlo := hb.1
  have hwidth := hb.2.2
  change abs (negativeRegularizedBetheGradientCoordinate
      (τ : ℝ) (A a b : ℝ) (X a b : ℝ) -
    (directedNegativeGradientLower τ (A a b) (X a b) p : ℝ)) ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith [hb.2.1]

/-- Entrywise `ℓ1` size of a matrix displacement. -/
def matrixL1 {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, abs (D i j)

theorem matrixL1_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (D : Matrix m n ℝ) : 0 ≤ matrixL1 D := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _

/-- Coordinatewise covector error controls pairing error by the `ℓ1` size
of the displacement. -/
theorem matrixPairing_sub_le_error_mul_l1
    {m n : Type*} [Fintype m] [Fintype n]
    {G H D : Matrix m n ℝ} {e : ℝ}
    (herr : ∀ i j, abs (G i j - H i j) ≤ e) :
    matrixPairing G D - matrixPairing H D ≤ e * matrixL1 D := by
  rw [matrixPairing, matrixPairing, matrixL1, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hpoint :
      (G i j - H i j) * D i j ≤ e * abs (D i j) := by
    calc
      (G i j - H i j) * D i j ≤
          abs ((G i j - H i j) * D i j) := le_abs_self _
      _ = abs (G i j - H i j) * abs (D i j) := abs_mul _ _
      _ ≤ e * abs (D i j) :=
        mul_le_mul_of_nonneg_right (herr i j) (abs_nonneg _)
  convert hpoint using 1 <;> ring

/-- Generic tolerant epigraph-cut lemma.  It records all three losses used by
the executable oracle: a one-sided value approximation, a coordinatewise
gradient approximation, and a known `ℓ1` radius for candidate displacements. -/
theorem approximateEpigraphCut_valid
    {m n : Type*} [Fintype m] [Fintype n]
    {fY fZ lower t s e Dmax : ℝ}
    {G H D : Matrix m n ℝ}
    (hsupport : fY + matrixPairing G D ≤ fZ)
    (hlower : lower ≤ fY)
    (hgradient : ∀ i j, abs (H i j - G i j) ≤ e)
    (hD : matrixL1 D ≤ Dmax)
    (he : 0 ≤ e) (hepigraph : fZ ≤ s) :
    matrixPairing H D - (s - t) ≤
      t - lower + e * Dmax := by
  have hpair := matrixPairing_sub_le_error_mul_l1
    (G := H) (H := G) (D := D) hgradient
  have hscale := mul_le_mul_of_nonneg_left hD he
  linarith

/-- If the certified lower value exceeds the query height by more than the
gradient-error budget, the approximate supporting hyperplane strictly
separates the query from every epigraph point in the prescribed radius. -/
theorem approximateEpigraphCut_strict
    {m n : Type*} [Fintype m] [Fintype n]
    {fY fZ lower t s e Dmax margin : ℝ}
    {G H D : Matrix m n ℝ}
    (hsupport : fY + matrixPairing G D ≤ fZ)
    (hlower : lower ≤ fY)
    (hgradient : ∀ i j, abs (H i j - G i j) ≤ e)
    (hD : matrixL1 D ≤ Dmax)
    (he : 0 ≤ e) (hepigraph : fZ ≤ s)
    (hviolation : t - lower + e * Dmax ≤ -margin) :
    matrixPairing H D - (s - t) ≤ -margin :=
  (approximateEpigraphCut_valid hsupport hlower hgradient hD he hepigraph).trans
    hviolation

end BeyondBethe
