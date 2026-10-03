/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Geometry
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.ExteriorSphere
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.MeanValue
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.WeakHarmonic.SecondDifference

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Transport between `EuclideanSpace ℝ (Fin d)` and `Point d`

The viscosity theory in this repository lives on `Point d = Fin d → ℝ` with the
sup norm, while the harmonic-function statements are phrased on
`EuclideanSpace ℝ (Fin d)` with Mathlib's Laplacian. The coordinate map
`toPoint` is a continuous linear equivalence (so it preserves topology,
boundedness, and Lebesgue measure), and it converts Euclidean distances into
`eucSq`.

* `eucSq_toPoint`: `eucSq (toPoint x) (toPoint y) = dist x y ^ 2`.
* `UniformExteriorSphere.image_toPoint`: the exterior sphere condition
  transfers to `UniformExteriorSphereSq`.
* `laplacian_eq_lapTrace`: Mathlib's Laplacian is the coordinate trace of
  the second derivative in `Point d`.
* `weaklyHarmonicOn_of_forall_integral_lapTrace`: the weak harmonicity
  statement in `Point d` coordinates gives `WeaklyHarmonicOn` on the Euclidean
  side.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Laplacian ContDiff

namespace ViscositySolns

variable {d : Nat}

/-- The coordinate map `EuclideanSpace ℝ (Fin d) ≃L[ℝ] Point d`. -/
abbrev toPoint : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Point d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

@[simp]
theorem toPoint_apply (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : toPoint x i = x i :=
  rfl

theorem eucSq_toPoint (x y : EuclideanSpace ℝ (Fin d)) :
    eucSq (toPoint x) (toPoint y) = dist x y ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [eucSq, dotProduct, Real.dist_eq, sq]

theorem eucSq_eq_dist_symm (x y : Point d) :
    eucSq x y = dist (toPoint.symm x) (toPoint.symm y) ^ 2 := by
  rw [← eucSq_toPoint]
  rfl

theorem image_toPoint_frontier (U : Set (EuclideanSpace ℝ (Fin d))) :
    toPoint '' frontier U = frontier (toPoint '' U) :=
  (toPoint (d := d)).toHomeomorph.image_frontier U

theorem image_toPoint_closure (U : Set (EuclideanSpace ℝ (Fin d))) :
    toPoint '' closure U = closure (toPoint '' U) :=
  (toPoint (d := d)).toHomeomorph.image_closure U

theorem isOpen_image_toPoint {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    IsOpen (toPoint '' U) :=
  (toPoint (d := d)).toHomeomorph.isOpenMap U hU

theorem isBounded_image_toPoint {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : Bornology.IsBounded U) : Bornology.IsBounded (toPoint '' U) :=
  (toPoint (d := d)).lipschitzWith.isBounded_image hU

/-- The Euclidean exterior sphere condition in `Point d` coordinates. -/
theorem UniformExteriorSphere.image_toPoint {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : UniformExteriorSphere U) : ∃ R : Real, UniformExteriorSphereSq (toPoint '' U) R := by
  obtain ⟨R, hR, hext⟩ := hU
  refine ⟨R, hR, ?_⟩
  intro z₀ hz₀
  rw [← image_toPoint_frontier] at hz₀
  obtain ⟨x₀, hx₀, rfl⟩ := hz₀
  obtain ⟨y, hy, hyU⟩ := hext x₀ hx₀
  refine ⟨toPoint y, by rw [eucSq_toPoint, hy], ?_⟩
  intro z hz
  rw [← image_toPoint_closure] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [eucSq_toPoint]
  exact pow_le_pow_left₀ hR.le (hyU x hx) 2

/-- A Euclidean-Lipschitz function gives the `eucSq` Lipschitz bound in `Point d`. -/
theorem LipschitzOnWith.abs_sub_le_eucSq {U : Set (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → Real} {L : NNReal} (hg : LipschitzOnWith L g (closure U)) :
    ∀ x ∈ closure (toPoint '' U), ∀ y ∈ closure (toPoint '' U),
      |g (toPoint.symm x) - g (toPoint.symm y)| <= L * Real.sqrt (eucSq x y) := by
  intro x hx y hy
  rw [← image_toPoint_closure] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  rw [eucSq_toPoint, Real.sqrt_sq dist_nonneg, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, ← Real.dist_eq]
  exact hg.dist_le_mul x hx y hy

theorem toPoint_single (i : Fin d) :
    toPoint (EuclideanSpace.single i (1 : Real)) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

/-- Mathlib's Laplacian is the coordinate trace of the second derivative after
passing to `Point d` coordinates. -/
theorem laplacian_eq_lapTrace {χ : EuclideanSpace ℝ (Fin d) → Real} (hχ : ContDiff ℝ 2 χ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Δ χ x = lapTrace (χ ∘ toPoint.symm) (toPoint x) := by
  have hψ : ContDiff ℝ 2 (χ ∘ toPoint.symm) := hχ.comp toPoint.symm.contDiff
  have hχeq : χ = (χ ∘ toPoint.symm) ∘ (toPoint (d := d)).toContinuousLinearMap := by
    funext y
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis χ
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [lapTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hχeq]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply, toPoint_single]

/--
Weak harmonicity in `Point d` coordinates, tested against the coordinate
trace `lapTrace`, gives Mathlib's `WeaklyHarmonicOn` for the transported
function on `EuclideanSpace ℝ (Fin d)`.
-/
theorem weaklyHarmonicOn_of_forall_integral_lapTrace
    {U : Set (EuclideanSpace ℝ (Fin d))} {w : Point d → Real}
    (hw : ∀ χ : Point d → Real, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ toPoint '' U → ∫ x, lapTrace χ x * w x = 0) :
    Analysis.WeaklyHarmonicOn volume (w ∘ toPoint) U := by
  intro χ hχ hχc hχU
  have hψ : ContDiff ℝ ∞ (χ ∘ toPoint.symm) := hχ.comp toPoint.symm.contDiff
  have hψc : HasCompactSupport (χ ∘ toPoint.symm) :=
    hχc.comp_homeomorph (toPoint (d := d)).symm.toHomeomorph
  have hψU : tsupport (χ ∘ toPoint.symm) ⊆ toPoint '' U := by
    intro z hz
    have hz' : toPoint.symm z ∈ tsupport χ :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage χ (toPoint (d := d)).symm.toHomeomorph) z).mp hz
    exact ⟨toPoint.symm z, hχU hz', rfl⟩
  have h := hw _ hψ hψc hψU
  have hlap : ∀ x, Δ χ x • (w ∘ toPoint) x =
      (fun z => lapTrace (χ ∘ toPoint.symm) z * w z) (toPoint x) := by
    intro x
    rw [laplacian_eq_lapTrace (hχ.of_le (WithTop.coe_le_coe.mpr le_top)) x, smul_eq_mul]
    rfl
  simp_rw [hlap]
  rw [← h]
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (fun z => lapTrace (χ ∘ toPoint.symm) z * w z)

end ViscositySolns
