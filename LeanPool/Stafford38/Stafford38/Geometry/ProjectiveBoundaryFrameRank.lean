/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CanonicalAsymptoticLaurentProducer

/-!
# Projective residue frames and the generic tangent rank bound

This file extracts two consequences which are already forced by the completed
projective/DVR certificate but were previously left as consumer hypotheses.

First, full column rank of an augmented projective matrix `[q | B]` implies
linear independence of the affine columns obtained by differentiating in any
chart where `q` is nonzero.  The chart is arbitrary: the completed certificate
does not identify its normalized chart coordinate with coordinate zero.

Second, the stored Laurent tangent inclusion bounds the generic tangent
dimension by the number of nonposition columns, namely `tangentCount + 1`.
This is a generic-fibre statement.  No equality with an arc-derivation frame
and no closed-boundary tangent bound is asserted; either conclusion needs an
additional geometric comparison.
-/

namespace Stafford38.Geometry.ProjectiveBoundaryFrameRank

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryResidueMinorSelection

noncomputable section

universe u v w

variable {K : Type u} [Field K]

/-- Coordinates remaining after choosing an arbitrary projective chart. -/
abbrev ChartAffineIndex (ι : Type v) (chart : ι) := {i : ι // i ≠ chart}

/-- Differential of `q_i / q_chart` in the projective direction `w`. -/
def chartDehomogenizedTangentColumn {ι : Type v} (chart : ι)
    (q w : ι → K) : ChartAffineIndex ι chart → K :=
  fun i ↦ (w i.1 * q chart - q i.1 * w chart) / q chart ^ 2

/-- Adjoin the projective position column to a family of tangent columns. -/
def augmentedProjectiveMatrix {ι : Type v} {κ : Type w}
    (q : ι → K) (B : Matrix ι κ K) : Matrix ι (Unit ⊕ κ) K
  | i, Sum.inl _ => q i
  | i, Sum.inr j => B i j

/-- The nonposition part of the formal power-series tangent matrix. -/
def nonpositionPowerSeriesMatrix {k : Type u} {ι : Type v} {κ : Type w}
     (Z : Matrix ι κ (PowerSeries k))
    (tau : ι → PowerSeries k) : Matrix ι (κ ⊕ Unit) (PowerSeries k)
  | i, Sum.inl j => Z i j
  | i, Sum.inr _ => tau i

/-- Independent projective position and tangent columns remain independent
after passing to affine tangent vectors in any nonvanishing chart. -/
theorem linearIndependent_chartDehomogenizedTangentColumns
    {ι : Type v} {κ : Type w} [Fintype κ]
    (chart : ι) (q : ι → K) (B : Matrix ι κ K)
    (hq : q chart ≠ 0)
    (hinjective : Function.Injective (augmentedProjectiveMatrix q B).mulVec) :
    LinearIndependent K
      (fun j ↦ chartDehomogenizedTangentColumn chart q (fun i ↦ B i j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let s : K := -(∑ a, c a * B chart a) / q chart
  let c' : Unit ⊕ κ → K
    | Sum.inl _ => s
    | Sum.inr a => c a
  have hc' : (augmentedProjectiveMatrix q B).mulVec c' = 0 := by
    funext i
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct,
      augmentedProjectiveMatrix, c', Fintype.sum_sum_type,
      Fintype.sum_unique]
    change q i * s + ∑ a, B i a * c a = 0
    by_cases hi : i = chart
    · subst i
      rw [show s = -(∑ a, c a * B chart a) / q chart by rfl,
        mul_div_cancel₀ _ hq]
      simp [mul_comm]
    · have hcoordinate := congrFun hc ⟨i, hi⟩
      simp only [Pi.zero_apply] at hcoordinate
      simp? [chartDehomogenizedTangentColumn] at hcoordinate
      simp_rw [← mul_div_assoc] at hcoordinate
      rw [← Finset.sum_div] at hcoordinate
      simp only [s]
      field_simp [hq] at hcoordinate ⊢
      have hcoordinate' :
          q chart * (∑ a, B i a * c a) -
            q i * (∑ a, B chart a * c a) = 0 := by
        simpa [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
          ← Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hcoordinate
      have hchartSum : (∑ a, c a * B chart a) =
          ∑ a, B chart a * c a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact mul_comm _ _
      rw [hchartSum]
      linear_combination hcoordinate'
  have hc'_zero : c' = 0 := by
    apply hinjective
    simpa using hc'
  exact congrFun hc'_zero (Sum.inr j)

/-- Entrywise reduction of a power-series left inverse remains a left inverse
of the residue matrix. -/
theorem residueMatrix_mul_eq_one_of_mul_eq_one
    {k : Type u} [Field k] {ι : Type v} {κ : Type w}
    [Fintype ι]  [DecidableEq κ]
    (C : Matrix κ ι (PowerSeries k)) (B : Matrix ι κ (PowerSeries k))
    (hCB : C * B = 1) :
    residueMatrix C * residueMatrix B = 1 := by
  ext i j
  have hij := congrArg (PowerSeries.constantCoeff)
    (congrFun (congrFun hCB i) j)
  simpa [Matrix.mul_apply, Matrix.one_apply, residueMatrix, map_sum] using hij

/-- A power-series left inverse therefore gives full column rank after
reduction modulo the uniformizer. -/
theorem residueMatrix_mulVec_injective_of_leftInverse
    {k : Type u} [Field k] {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix κ ι (PowerSeries k)) (B : Matrix ι κ (PowerSeries k))
    (hCB : C * B = 1) :
    Function.Injective (residueMatrix B).mulVec := by
  intro x y hxy
  have h := congrArg (residueMatrix C).mulVec hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    residueMatrix_mul_eq_one_of_mul_eq_one C B hCB,
    Matrix.one_mulVec] at h
  simpa using h

/-- The completed certificate's split formal matrix produces a genuinely
independent affine residue frame in its normalized projective chart. -/
theorem completedBoundaryChart_residueFrame_linearIndependent
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    LinearIndependent k
      (fun j : (Fin W.tangentCount ⊕ Unit) ↦
        chartDehomogenizedTangentColumn W.chart
          (fun i ↦ PowerSeries.constantCoeff (W.q i))
          (fun i ↦ PowerSeries.constantCoeff
            (nonpositionPowerSeriesMatrix W.Z W.tau i j))) := by
  apply linearIndependent_chartDehomogenizedTangentColumns W.chart
  · simp [W.q_chart]
  · have hinj := residueMatrix_mulVec_injective_of_leftInverse
      W.C (formalTangentMatrix W.q W.Z W.tau) W.left_inverse
    have hmatrix :
        residueMatrix (formalTangentMatrix W.q W.Z W.tau) =
          augmentedProjectiveMatrix
            (fun i ↦ PowerSeries.constantCoeff (W.q i))
            (fun i j ↦ PowerSeries.constantCoeff
              (nonpositionPowerSeriesMatrix W.Z W.tau i j)) := by
      ext i j
      rcases j with (_ | (j | _)) <;>
        rfl
    rw [hmatrix] at hinj
    exact hinj

/-- The stored generic tangent inclusion gives the exact numerical bound by
the number of supplied nonposition columns. -/
theorem completedBoundaryChart_genericTangent_finrank_le
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    Module.finrank (LaurentSeries k)
        (zariskiTangentSpace (dehomogenizedPoint (laurentColumn W.q))
          (I.map (Stafford38.Geometry.ScalarExtensionPoints.scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m)))) ≤
      W.tangentCount + 1 := by
  calc
    Module.finrank (LaurentSeries k)
        (zariskiTangentSpace (dehomogenizedPoint (laurentColumn W.q))
          (I.map (Stafford38.Geometry.ScalarExtensionPoints.scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m)))) ≤
        Module.finrank (LaurentSeries k)
          (dehomogenizedTangentSpan (laurentColumn W.q)
            (laurentNonpositionTangentMatrix W.Z W.tau)) :=
      Submodule.finrank_mono W.tangent_inclusion
    _ ≤ Fintype.card (Fin W.tangentCount ⊕ Unit) :=
      finrank_range_le_card
        (fun j ↦ dehomogenizedTangentColumn (laurentColumn W.q)
          (fun i ↦ laurentNonpositionTangentMatrix W.Z W.tau i j))
    _ = W.tangentCount + 1 := by simp


end

end Stafford38.Geometry.ProjectiveBoundaryFrameRank
