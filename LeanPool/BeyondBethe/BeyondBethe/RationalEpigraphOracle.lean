/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RationalLinearOracle
public import Mathlib.Tactic

/-! # Rational Epigraph Oracle -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Directed rational cuts for a convex epigraph

The first `d` coordinates are base variables and the last coordinate is the
epigraph height.  A lower objective endpoint and an approximate gradient give
an entirely rational violation test.  When the test succeeds, convexity and
the explicit gradient-error budget prove that the returned normal is a strict
central cut for the exact epigraph.
-/

def epigraphBase {d : ℕ} {R : Type*}
    (x : Fin (d + 1) → R) : Fin d → R :=
  fun i ↦ x i.castSucc

def epigraphHeight {d : ℕ} {R : Type*}
    (x : Fin (d + 1) → R) : R :=
  x (Fin.last d)

def epigraphNormal {d : ℕ} {R : Type*} [Neg R] [OfNat R 1]
    (g : Fin d → R) : Fin (d + 1) → R :=
  Fin.snoc g (-1)

@[simp] theorem epigraphNormal_castSucc {d : ℕ} {R : Type*}
    [Neg R] [OfNat R 1] (g : Fin d → R) (i : Fin d) :
    epigraphNormal g i.castSucc = g i := by
  simp [epigraphNormal]

@[simp] theorem epigraphNormal_last {d : ℕ} {R : Type*}
    [Neg R] [OfNat R 1] (g : Fin d → R) :
    epigraphNormal g (Fin.last d) = -1 := by
  simp [epigraphNormal]

theorem epigraphNormal_ne_zero {d : ℕ} (g : Fin d → ℚ) :
    epigraphNormal g ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (Fin.last d)
  norm_num at hlast

/-- Entrywise `l1` size of a vector. -/
def vectorL1 {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ i, abs (x i)

theorem vectorL1_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ vectorL1 x :=
  Finset.sum_nonneg fun i _ ↦ abs_nonneg (x i)

theorem finiteDot_sub_le_error_mul_vectorL1 {d : ℕ}
    {G H D : Fin d → ℝ} {e : ℝ}
    (herr : ∀ i, abs (H i - G i) ≤ e) :
    finiteDot H D - finiteDot G D ≤ e * vectorL1 D := by
  rw [finiteDot, finiteDot, vectorL1, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hpoint : (H i - G i) * D i ≤ e * abs (D i) := by
    calc
      (H i - G i) * D i ≤ abs ((H i - G i) * D i) := le_abs_self _
      _ = abs (H i - G i) * abs (D i) := abs_mul _ _
      _ ≤ e * abs (D i) :=
        mul_le_mul_of_nonneg_right (herr i) (abs_nonneg _)
  convert hpoint using 1 <;> ring

/-- Dot product of an epigraph normal with an epigraph displacement. -/
theorem epigraphNormal_dot_displacement {d : ℕ}
    (H : Fin d → ℝ) (z q : Fin (d + 1) → ℝ) :
    finiteDot (epigraphNormal H) (fun i ↦ z i - q i) =
      finiteDot H (fun i ↦ epigraphBase z i - epigraphBase q i) -
        (epigraphHeight z - epigraphHeight q) := by
  rw [finiteDot, Fin.sum_univ_castSucc]
  simp [finiteDot, epigraphBase, epigraphHeight]
  ring

/-- Vector version of the tolerant supporting-hyperplane estimate. -/
theorem approximateVectorEpigraphCut_valid {d : ℕ}
    {fY fZ lower t s e Dmax : ℝ}
    {G H D : Fin d → ℝ}
    (hsupport : fY + finiteDot G D ≤ fZ)
    (hlower : lower ≤ fY)
    (hgradient : ∀ i, abs (H i - G i) ≤ e)
    (hD : vectorL1 D ≤ Dmax)
    (he : 0 ≤ e) (hepigraph : fZ ≤ s) :
    finiteDot H D - (s - t) ≤ t - lower + e * Dmax := by
  have hpair := finiteDot_sub_le_error_mul_vectorL1 (D := D) hgradient
  have hscale := mul_le_mul_of_nonneg_left hD he
  linarith

/-- Executable lower endpoint and executable approximate gradient. -/
structure DirectedEpigraphData (d : ℕ) where
  lower : (Fin d → ℚ) → ℚ
  gradient : (Fin d → ℚ) → Fin d → ℚ

/-- The nonlinear oracle accepts unless the rational lower endpoint exceeds
the query height by more than the full gradient-error budget. -/
def directedEpigraphOracle {d : ℕ}
    (data : DirectedEpigraphData d) (e Dmax : ℚ) :
    RationalCentralOracle (d + 1) :=
  fun E ↦
    let y := epigraphBase E.center
    let t := epigraphHeight E.center
    if t + e * Dmax < data.lower y then
      .cut (epigraphNormal (data.gradient y))
    else .accept

theorem directedEpigraphOracle_cut_ne_zero {d : ℕ}
    (data : DirectedEpigraphData d) (e Dmax : ℚ)
    (E : RationalEllipsoidState (d + 1))
    {a : Fin (d + 1) → ℚ}
    (hresponse : directedEpigraphOracle data e Dmax E = .cut a) :
    a ≠ 0 := by
  rw [directedEpigraphOracle] at hresponse
  split at hresponse
  · cases hresponse
    exact epigraphNormal_ne_zero _
  · contradiction

/-- A reported nonlinear cut is valid for any exact epigraph point satisfying
the displayed support, directed-value, directed-gradient, and radius bounds. -/
theorem directedEpigraphOracle_cut_valid {d : ℕ}
    (data : DirectedEpigraphData d) {e Dmax : ℚ}
    (he : 0 ≤ e) (E : RationalEllipsoidState (d + 1))
    {a : Fin (d + 1) → ℚ}
    (hresponse : directedEpigraphOracle data e Dmax E = .cut a)
    {fY fZ : ℝ} {G : Fin d → ℝ} {z : Fin (d + 1) → ℝ}
    (hsupport : fY + finiteDot G
      (fun i ↦ epigraphBase z i -
        ((epigraphBase E.center i : ℚ) : ℝ)) ≤ fZ)
    (hlower : (data.lower (epigraphBase E.center) : ℝ) ≤ fY)
    (hgradient : ∀ i, abs
      ((data.gradient (epigraphBase E.center) i : ℝ) - G i) ≤ (e : ℝ))
    (hD : vectorL1
      (fun i ↦ epigraphBase z i -
        ((epigraphBase E.center i : ℚ) : ℝ)) ≤
        (Dmax : ℝ))
    (hepigraph : fZ ≤ epigraphHeight z) :
    a ≠ 0 ∧ finiteDot (fun i ↦ (a i : ℝ))
      (fun i ↦ z i - rationalCenterReal E i) < 0 := by
  rw [directedEpigraphOracle] at hresponse
  split at hresponse <;> rename_i hviolation
  · cases hresponse
    refine ⟨epigraphNormal_ne_zero _, ?_⟩
    have hbound := approximateVectorEpigraphCut_valid
      (t := ((epigraphHeight E.center : ℚ) : ℝ))
      (s := epigraphHeight z) hsupport hlower hgradient hD
      (Rat.cast_nonneg.mpr he) hepigraph
    have hviolationReal :
        ((epigraphHeight E.center : ℚ) : ℝ) + (e : ℝ) * (Dmax : ℝ) <
          (data.lower (epigraphBase E.center) : ℝ) := by
      exact_mod_cast hviolation
    have hdot : finiteDot
        (fun i ↦ ((epigraphNormal
          (data.gradient (epigraphBase E.center)) i : ℚ) : ℝ))
        (fun i ↦ z i - rationalCenterReal E i) =
      finiteDot
          (fun i ↦ (data.gradient (epigraphBase E.center) i : ℝ))
          (fun i ↦ epigraphBase z i -
            ((epigraphBase E.center i : ℚ) : ℝ)) -
        (epigraphHeight z - ((epigraphHeight E.center : ℚ) : ℝ)) := by
      rw [finiteDot, Fin.sum_univ_castSucc]
      simp [finiteDot, epigraphNormal, rationalCenterReal,
        epigraphBase, epigraphHeight]
      ring
    rw [hdot]
    norm_num only [Rat.cast_mul] at hbound
    linarith
  · contradiction

end BeyondBethe
