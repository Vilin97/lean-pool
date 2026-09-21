/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.OriginCubeBridge
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.MatrixIdentities

/-!
# Coupled representation: weak-form definition and algebraic scaffolding

This module holds the `G0` weak-form definition together with the
pointwise matrix/vector algebra and Sobolev scaffolding consumed by the `G1`
existence package in `Coupled/Representation.lean`.

All coefficients act on `Vec d = Fin d → ℝ`; no `EuclideanSpace`.  The file is
deliberately factored into small named lemmas.
-/

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## G0 — the weak-form predicate -/

/-- **G0.**  The variational-identity component of the coupled boundary problem
`e.coupled.weak`, to be paired with its affine trace condition.  For flux data
`q`, the identity requires that every test pair `(φ, φ*)` of `H¹(U)` functions
whose sum lies in `H¹₀(U)` satisfy
`∫_U ∇φ·(a ∇v) + ∫_U ∇φ*·(aᵗ ∇v*) = ∫_U q·∇φ`. -/
def CoupledWeakForm (a : CoeffField d) (U : Set (Vec d)) (q : Vec d)
    (v vstar : H1Function U) : Prop :=
  ∀ (φ φstar : H1Function U), MemH10 U (fun x => φ.toFun x + φstar.toFun x) →
    (∫ x in U, vecDot (φ.grad x) (matVecMul (a x) (v.grad x)) ∂volume)
      + (∫ x in U, vecDot (φstar.grad x)
          (matVecMul (matTranspose (a x)) (vstar.grad x)) ∂volume)
      = ∫ x in U, vecDot q (φ.grad x) ∂volume

/-! ## Finite-measure instance on the open cube -/

/-- The restricted Lebesgue measure on a centered open triadic cube is finite. -/
theorem isFiniteMeasure_openCubeSet_originCube (m : ℤ) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) := by
  let : Fact (MeasureTheory.volume (openCubeSet (originCube d m)) < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) m⟩
  change MeasureTheory.IsFiniteMeasure
    (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))
  infer_instance

/-! ## Sums of `H¹` functions -/

theorem H1Function.sum_grad {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (f : ι → H1Function U) :
    (∑ i ∈ s, f i).grad = fun x => ∑ i ∈ s, (f i).grad x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [Homogenization.H1Function.add_grad, Finset.sum_insert ha, ih]

theorem H1Function.sum_toFun {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (f : ι → H1Function U) :
    (∑ i ∈ s, f i).toFun = fun x => ∑ i ∈ s, (f i).toFun x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [Homogenization.H1Function.add_toFun, Finset.sum_insert ha, ih]

/-! ## The affine coordinate `H¹` function `x ↦ p·x` -/

/-- The affine map `x ↦ p·x` as an `H¹` function on the centered open cube, with
constant gradient `p`.  This is the coordinate construction assembled from
the library's coordinate projections `coordOnOpenCubeSetOriginCube`. -/
def affineH1 (m : ℤ) (p : Vec d) : H1Function (openCubeSet (originCube d m)) :=
  ∑ i : Fin d, p i • H1Function.coordOnOpenCubeSetOriginCube (n := m) i

@[simp] theorem affineH1_grad (m : ℤ) (p : Vec d) :
    (affineH1 m p).grad = fun _ => p := by
  rw [affineH1, H1Function.sum_grad]
  funext x
  simp only [Homogenization.H1Function.smul_grad]
  show (∑ i : Fin d, p i • basisVec i) = p
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVec, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => p i)]
  simp

@[simp] theorem affineH1_toFun (m : ℤ) (p : Vec d) :
    (affineH1 m p).toFun = fun x => vecDot p x := by
  rw [affineH1, H1Function.sum_toFun]
  funext x
  simp only [Homogenization.H1Function.smul_toFun]
  rfl

/-! ## Symmetric/skew decomposition of the transpose action -/

/-- `matVecMul Aᵀ w = matVecMul s w − matVecMul k w` where `s = symmPart A`,
`k = skewPart A`. -/
theorem matVecMul_matTranspose_eq (A : Mat d) (w : Vec d) :
    matVecMul (matTranspose A) w =
      matVecMul (symmPart A) w - matVecMul (skewPart A) w := by
  have h := matVecMul_eq_symmPart_add_skewPart (matTranspose A) w
  rw [symmPart_matTranspose, skewPart_matTranspose, neg_matVecMul, ← sub_eq_add_neg] at h
  exact h

/-- Symmetric-part regrouping of `a∇v + aᵀ∇v*`:
`A vg + Aᵀ vsg = s (vg + vsg) + k (vg − vsg)`. -/
theorem matVecMul_sub_vec (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

theorem matVecMul_add_matTranspose_eq (A : Mat d) (vg vsg : Vec d) :
    matVecMul A vg + matVecMul (matTranspose A) vsg =
      matVecMul (symmPart A) (vg + vsg) + matVecMul (skewPart A) (vg - vsg) := by
  rw [matVecMul_add (symmPart A) vg vsg, matVecMul_sub_vec (skewPart A) vg vsg,
    matVecMul_eq_symmPart_add_skewPart A vg, matVecMul_matTranspose_eq]
  abel

/-- Symmetric-part regrouping of `a∇v − aᵀ∇v*`:
`A vg − Aᵀ vsg = s (vg − vsg) + k (vg + vsg)`. -/
theorem matVecMul_sub_matTranspose_eq (A : Mat d) (vg vsg : Vec d) :
    matVecMul A vg - matVecMul (matTranspose A) vsg =
      matVecMul (symmPart A) (vg - vsg) + matVecMul (skewPart A) (vg + vsg) := by
  rw [matVecMul_sub_vec (symmPart A) vg vsg, matVecMul_add (skewPart A) vg vsg,
    matVecMul_eq_symmPart_add_skewPart A vg, matVecMul_matTranspose_eq]
  abel

/-! ## The `α/β` bilinear split of the weak-form integrand -/

/-- Bilinear `α/β` split: `Pv·X + Ps·Y = α·(X+Y) + β·(X−Y)` where
`α = ½(Pv+Ps)`, `β = ½(Pv−Ps)`. -/
theorem vecDot_alpha_beta_split (Pv Ps X Y : Vec d) :
    vecDot Pv X + vecDot Ps Y =
      vecDot ((1 / 2 : ℝ) • (Pv + Ps)) (X + Y) +
        vecDot ((1 / 2 : ℝ) • (Pv - Ps)) (X - Y) := by
  simp only [vecDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ## The symmetric parallelogram identity -/

/-- Bilinear parallelogram identity:
`2 (½(p+τ))·(½(A+B)) + 2 (½(p−τ))·(½(A−B)) = p·A + τ·B`. -/
theorem vecDot_half_parallelogram (p τ A B : Vec d) :
    2 * vecDot ((1 / 2 : ℝ) • (p + τ)) ((1 / 2 : ℝ) • (A + B))
        + 2 * vecDot ((1 / 2 : ℝ) • (p - τ)) ((1 / 2 : ℝ) • (A - B)) =
      vecDot p A + vecDot τ B := by
  simp only [vecDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Parallelogram identity for the symmetric form `s`:
`2 (½(p+τ))·s(½(p+τ)) + 2 (½(p−τ))·s(½(p−τ)) = p·s p + τ·s τ`. -/
theorem two_vecDot_symmPart_half_add_sub (s : Mat d) (p τ : Vec d) :
    2 * vecDot ((1 / 2 : ℝ) • (p + τ)) (matVecMul s ((1 / 2 : ℝ) • (p + τ)))
        + 2 * vecDot ((1 / 2 : ℝ) • (p - τ)) (matVecMul s ((1 / 2 : ℝ) • (p - τ))) =
      vecDot p (matVecMul s p) + vecDot τ (matVecMul s τ) := by
  have h1 : matVecMul s ((1 / 2 : ℝ) • (p + τ)) =
      (1 / 2 : ℝ) • (matVecMul s p + matVecMul s τ) := by
    rw [matVecMul_smul, matVecMul_add]
  have h2 : matVecMul s ((1 / 2 : ℝ) • (p - τ)) =
      (1 / 2 : ℝ) • (matVecMul s p - matVecMul s τ) := by
    rw [matVecMul_smul, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  rw [h1, h2]
  exact vecDot_half_parallelogram p τ (matVecMul s p) (matVecMul s τ)

/-! ## The pointwise energy identity (A7 + Schur inverse) -/

/-- The doubled quadratic form of `bfA` equals `p·s p + τ·s τ` with
`τ := s⁻¹(j − k p)`.  This is the `A7` factorization with the Schur term
rewritten through `s s⁻¹ = 1`. -/
theorem blockEnergy_pointwise_eq {A : Mat d} (hdet : IsUnit (symmPart A).det)
    (p j : Vec d) :
    blockVecDot (p, j) (blockMatVecMul (blockMatrixOfCoeff A) (p, j)) =
      vecDot p (matVecMul (symmPart A) p) +
        vecDot (matVecMul (symmPart A)⁻¹ (j - matVecMul (skewPart A) p))
          (matVecMul (symmPart A)
            (matVecMul (symmPart A)⁻¹ (j - matVecMul (skewPart A) p))) := by
  set w := j - matVecMul (skewPart A) p with hw
  have hsτ : matVecMul (symmPart A) (matVecMul (symmPart A)⁻¹ w) = w := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hdet, matVecMul_one]
  rw [blockMatrixOfCoeff_quadratic A p j, hsτ]
  rw [vecDot_comm (matVecMul (symmPart A)⁻¹ w) w]

end

end Homogenization
