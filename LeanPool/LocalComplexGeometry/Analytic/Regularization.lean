/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Coordinates
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.ExactOrder
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Regularizing a nonzero analytic germ

The first nonzero homogeneous term of a convergent Taylor series is nonzero on
some complex line.  Extending that line to coordinates makes the germ regular
in the last variable.  This is the coordinate-change input required before
Weierstrass preparation can be applied in Rückert's arguments.
-/

open Filter
open scoped ENNReal Topology


namespace LocalComplexGeometry

noncomputable section

/-! ## Extending one nonzero direction to coordinates -/

/--
An explicit linear coordinate system whose distinguished axis is `v`.

The coordinate `j`, at which `v` is nonzero, is used as the pivot.  The map is
the elementary shear-and-rescaling
`(z,w) ↦ insert_j (w v_j) (z_i + w v_i)`.
-/
def directionExtensionLinearEquiv {n : ℕ}
    (v : ComplexEuclidean (n + 1)) (j : Fin (n + 1)) (hvj : v j ≠ 0) :
    ClassicalComplexWPT.Ambient n ≃ₗ[ℂ] ComplexEuclidean (n + 1) where
  toFun x := Fin.insertNth j (x.2 * v j)
    (fun i ↦ x.1 i + x.2 * v (j.succAbove i))
  invFun y :=
    (fun i ↦ y (j.succAbove i) - (y j / v j) * v (j.succAbove i),
      y j / v j)
  left_inv x := by
    ext i
    · simp [hvj]
    · simp [hvj]
  right_inv y := by
    funext k
    refine j.succAboveCases ?_ (fun i ↦ ?_) k
    · simp [hvj]
    · simp [hvj]
  map_add' x y := by
    funext k
    refine j.succAboveCases ?_ (fun i ↦ ?_) k
    · simp [add_mul]
    · simp [add_mul, add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    funext k
    refine j.succAboveCases ?_ (fun i ↦ ?_) k
    · simp [mul_assoc]
    · simp [mul_add, mul_assoc]

/-- The preceding finite-dimensional linear equivalence is continuous. -/
def directionExtensionEquiv {n : ℕ}
    (v : ComplexEuclidean (n + 1)) (j : Fin (n + 1)) (hvj : v j ≠ 0) :
    ClassicalComplexWPT.Ambient n ≃L[ℂ] ComplexEuclidean (n + 1) :=
  (directionExtensionLinearEquiv v j hvj).toContinuousLinearEquiv

@[simp]
theorem directionExtensionEquiv_axis {n : ℕ}
    (v : ComplexEuclidean (n + 1)) (j : Fin (n + 1)) (hvj : v j ≠ 0)
    (w : ℂ) :
    directionExtensionEquiv v j hvj (0, w) = w • v := by
  funext k
  refine j.succAboveCases ?_ (fun i ↦ ?_) k
  · simp [directionExtensionEquiv, directionExtensionLinearEquiv]
  · simp [directionExtensionEquiv, directionExtensionLinearEquiv]

/-! ## A nonzero germ has a nonzero homogeneous term on a line -/

/--
If an analytic function is not the zero germ, one of the diagonal values of
one of its homogeneous Taylor coefficients is nonzero.

This formulation is deliberate: multivariable formal multilinear series are
only unique on their diagonals, and no unjustified symmetry assertion is used.
-/
theorem HasFPowerSeriesAt.exists_nonzero_diagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hp : HasFPowerSeriesAt f p 0)
    (hf : ¬ f =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    ∃ (d : ℕ) (v : E), p d (fun _ ↦ v) ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  filter_upwards [hp.eventually_hasSum_sub] with z hz
  have hzero : HasSum (fun d : ℕ ↦ p d (fun _ ↦ z - 0)) 0 := by
    simpa only [h] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)
  exact hz.unique hzero

/-- A direction witnessing a nonzero homogeneous term is itself nonzero. -/
theorem nonzero_of_diagonal_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ E ℂ) (d : ℕ) (v : E)
    (hd : 0 < d) (h : p d (fun _ ↦ v) ≠ 0) : v ≠ 0 := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  intro hv
  subst v
  exact h (show (p d) (0 : Fin d → E) = 0 from (p d).map_zero)

/--
The restriction of a nonzero analytic germ to a suitable complex line is not
the zero one-variable germ.  The proof retains the witnessing nonzero Taylor
coefficient.
-/
theorem exists_nonzero_analytic_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf_ne : ¬ f =ᶠ[𝓝 0] (fun _ ↦ 0)) (hf_zero : f 0 = 0) :
    ∃ (v : E) (p : FormalMultilinearSeries ℂ E ℂ) (d : ℕ),
      v ≠ 0 ∧ 0 < d ∧ HasFPowerSeriesAt f p 0 ∧
      p d (fun _ ↦ v) ≠ 0 ∧
      ¬ (fun w : ℂ ↦ f (w • v)) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨d, v, hdv⟩ :=
    HasFPowerSeriesAt.exists_nonzero_diagonal hp hf_ne
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    subst d
    exact hdv ((hp.coeff_zero (fun _ : Fin 0 ↦ v)).trans hf_zero)
  have hv : v ≠ 0 := nonzero_of_diagonal_ne_zero p d v hd hdv
  let line : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ v
  have hline : HasFPowerSeriesAt (f ∘ line)
      (p.compContinuousLinearMap line) 0 := by
    have hp' : HasFPowerSeriesAt f p (line 0) := by rw [map_zero]; exact hp
    exact hp'.compContinuousLinearMap (u := line) (x := 0)
  have hcoeff : (p.compContinuousLinearMap line) d (fun _ ↦ 1) ≠ 0 := by
    change p d (line ∘ (fun _ : Fin d ↦ (1 : ℂ))) ≠ 0
    simpa [line, Function.comp_def] using hdv
  have hline_ne : ¬ (f ∘ line) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    intro hzero
    have hseriesZero := hline.eq_zero_of_eventually hzero
    exact hcoeff (by rw [hseriesZero]; simp)
  refine ⟨v, p, d, hv, hd, hp, hdv, ?_⟩
  simpa [line, Function.comp_def] using hline_ne

/-! ## Regularizing coordinate change -/

/--
Every nonzero analytic germ on `ℂⁿ⁺¹` becomes regular in the last variable
after an invertible complex-linear coordinate change.

The returned natural number is the actual analytic order of the chosen line
slice.  Thus it is the least nonzero homogeneous order on that slice, not merely
an arbitrary finite bound.
-/
theorem exists_regularizing_coordinateEquiv
    {n : ℕ} {f : ComplexEuclidean (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hf_ne : ¬ f =ᶠ[𝓝 0] (fun _ ↦ 0)) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
      (d : ℕ),
      ClassicalComplexWPT.ExactOrderInLastVariable
        (fun x : ClassicalComplexWPT.Ambient n ↦
          f (L ((wptAmbientEquiv n).symm x))) d := by
  by_cases hf_zero : f 0 = 0
  · obtain ⟨v, p, k, hv, hk, hp, hpk, hline_ne⟩ :=
      exists_nonzero_analytic_line hf hf_ne hf_zero
    obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
      contrapose! hv
      exact funext hv
    let A : ClassicalComplexWPT.Ambient n ≃L[ℂ] ComplexEuclidean (n + 1) :=
      directionExtensionEquiv v j hvj
    let L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1) :=
      (wptAmbientEquiv n).trans A
    let F : ClassicalComplexWPT.Ambient n → ℂ := fun x ↦
      f (L ((wptAmbientEquiv n).symm x))
    have hF : AnalyticAt ℂ F 0 := by
      have hfA : AnalyticAt ℂ f (A 0) := by rw [map_zero]; exact hf
      have hcomp := hfA.compContinuousLinearMap
        (u := (A : ClassicalComplexWPT.Ambient n →L[ℂ]
          ComplexEuclidean (n + 1))) (x := 0)
      simpa [F, L, A, Function.comp_def] using hcomp
    have hslice : ClassicalComplexWPT.lastSlice F =
        (fun w : ℂ ↦ f (w • v)) := by
      funext w
      simp [ClassicalComplexWPT.lastSlice, F, L, A]
    have horder_ne_top : analyticOrderAt (ClassicalComplexWPT.lastSlice F) 0 ≠ ⊤ := by
      intro htop
      apply hline_ne
      rw [← hslice]
      exact analyticOrderAt_eq_top.mp htop
    let d := analyticOrderNatAt (ClassicalComplexWPT.lastSlice F) 0
    have horder : analyticOrderAt (ClassicalComplexWPT.lastSlice F) 0 = d := by
      exact (Nat.cast_analyticOrderNatAt horder_ne_top).symm
    refine ⟨L, d, ?_⟩
    exact (ClassicalComplexWPT.exactOrderInLastVariable_iff_analyticOrderAt hF).2 horder
  · let L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1) :=
      ContinuousLinearEquiv.refl ℂ _
    refine ⟨L, 0, ?_⟩
    apply ClassicalComplexWPT.exactOrderInLastVariable_zero_iff.mpr
    have harg : L ((wptAmbientEquiv n).symm (0 : ClassicalComplexWPT.Ambient n)) = 0 := by
      rw [map_zero, map_zero]
    rw [harg]
    exact hf_zero

/-- If the germ vanishes at the origin, the regularized order is positive. -/
theorem exists_regularizing_coordinateEquiv_pos
    {n : ℕ} {f : ComplexEuclidean (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hf_ne : ¬ f =ᶠ[𝓝 0] (fun _ ↦ 0))
    (hf_zero : f 0 = 0) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ] ComplexEuclidean (n + 1))
      (d : ℕ),
      0 < d ∧
      ClassicalComplexWPT.ExactOrderInLastVariable
        (fun x : ClassicalComplexWPT.Ambient n ↦
          f (L ((wptAmbientEquiv n).symm x))) d := by
  obtain ⟨L, d, horder⟩ := exists_regularizing_coordinateEquiv hf hf_ne
  refine ⟨L, d, ?_, horder⟩
  have hF : AnalyticAt ℂ
      (fun x : ClassicalComplexWPT.Ambient n ↦
        f (L ((wptAmbientEquiv n).symm x))) 0 := by
    let A := L.toContinuousLinearMap.comp
      (wptAmbientEquiv n).symm.toContinuousLinearMap
    have hfA : AnalyticAt ℂ f (A 0) := by rw [map_zero]; exact hf
    have hcomp := hfA.compContinuousLinearMap (u := A) (x := 0)
    change AnalyticAt ℂ (f ∘ A) 0
    exact hcomp
  by_contra hd
  have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
  subst d
  have hne0 :=
    (ClassicalComplexWPT.exactOrderInLastVariable_zero_iff).1 horder
  apply hne0
  have harg : L ((wptAmbientEquiv n).symm (0 : ClassicalComplexWPT.Ambient n)) = 0 := by
    rw [map_zero, map_zero]
  rw [harg]
  exact hf_zero

end

end LocalComplexGeometry
