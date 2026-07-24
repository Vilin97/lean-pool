/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Euclidean

/-!
# Radial Geometry
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The `i`-th coordinate vector in `ℝⁿ`. -/
def coordUnit {n : ℕ} (i : Fin n) : Domain n :=
  domainCoordUnit i

/-- The classical coordinate derivative `∂ᵢ u`, in the smooth model. -/
def partialDerivative {n m : ℕ} (u : Domain n → Target m) (i : Fin n)
    (x : Domain n) : Target m :=
  fderiv ℝ u x (coordUnit i)

/-- Coordinate derivative of a vector field component: `∂ᵢ Xⱼ`. -/
def vectorFieldPartial {n : ℕ} (X : Domain n → Domain n) (i j : Fin n)
    (x : Domain n) : ℝ :=
  partialDerivative X i x j

/-- Divergence of a smooth vector field in coordinates: `div X = ∑ᵢ ∂ᵢ Xᵢ`. -/
def divergence {n : ℕ} (X : Domain n → Domain n) (x : Domain n) : ℝ :=
  ∑ i : Fin n, vectorFieldPartial X i i x

/-- The radial unit vector based at `a`.  At `x = a` this definition gives `0`,
which is harmless for integral identities. -/
def radialUnit {n : ℕ} (a x : Domain n) : Domain n :=
  (‖x - a‖)⁻¹ • (x - a)

/-- Pointwise Hilbert-Schmidt energy of a gradient matrix. -/
def gradientEnergy {n m : ℕ} (A : Gradient n m) : ℝ :=
  ∑ i : Fin n, ‖A i‖ ^ 2

/-- Radial derivative associated to a pointwise gradient matrix, evaluated in the
radial direction from the origin to `x`. -/
def gradientRadialDerivative {n m : ℕ} (A : Gradient n m) (x : Domain n) : Target m :=
  SMul.smul (‖x‖⁻¹) (∑ i : Fin n, SMul.smul (x i) (A i))

/-- Radial energy associated to a pointwise gradient matrix. -/
def gradientRadialEnergy {n m : ℕ} (A : Gradient n m) (x : Domain n) : ℝ :=
  ‖gradientRadialDerivative A x‖ ^ 2

/-- A smooth map gives a pointwise gradient matrix by classical coordinate derivatives. -/
def smoothGradient {n m : ℕ} (u : Domain n → Target m) (x : Domain n) : Gradient n m :=
  fun i => partialDerivative u i x

/-- Energy density built from an arbitrary gradient field. -/
def weakEnergyDensity {n m : ℕ} (Du : Domain n → Gradient n m) (x : Domain n) : ℝ :=
  gradientEnergy (Du x)

/-- Radial derivative built from an arbitrary gradient field. -/
def weakRadialDerivative {n m : ℕ}
    (Du : Domain n → Gradient n m) (a x : Domain n) : Target m :=
  gradientRadialDerivative (Du x) (x - a)

/-- Radial energy density built from an arbitrary gradient field. -/
def weakRadialEnergyDensity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a x : Domain n) : ℝ :=
  ‖weakRadialDerivative Du a x‖ ^ 2

/-- Smooth-model radial derivative of `u` based at `a`. -/
def radialDerivative {n m : ℕ} (u : Domain n → Target m) (a x : Domain n) : Target m :=
  fderiv ℝ u x (radialUnit a x)

/-- Smooth-model Dirichlet energy density: `|∇u|² = ∑ᵢ |∂ᵢ u|²`.

Do not replace this by the operator norm squared of `fderiv`; the Dirichlet energy density uses the
Hilbert-Schmidt/Frobenius norm of the derivative. -/
def energyDensity {n m : ℕ} (u : Domain n → Target m) (x : Domain n) : ℝ :=
  ∑ i : Fin n, ‖partialDerivative u i x‖ ^ 2

/-- Radial energy density of a smooth map: the squared norm of its radial derivative. -/
def radialEnergyDensity {n m : ℕ} (u : Domain n → Target m) (a x : Domain n) : ℝ :=
  ‖radialDerivative u a x‖ ^ 2

/-- The radial test vector field `X(x) = φ(|x|) x`, centered at the origin. -/
def radialVectorField {n : ℕ} (phi : ℝ → ℝ) (x : Domain n) : Domain n :=
  phi ‖x‖ • x

/-- The differential of the Euclidean norm away from the origin:
`d|x|(v) = <x,v>/|x|`. -/
theorem fderiv_norm_apply {n : ℕ} {x v : Domain n} (hx : x ≠ 0) :
    fderiv ℝ (fun y : Domain n => ‖y‖) x v = inner ℝ x v / ‖x‖ := by
  have hnorm : DifferentiableAt ℝ (fun y : Domain n => ‖y‖) x := by
    exact (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt (by norm_num)
  have hsq_left :
      fderiv ℝ (fun y : Domain n => ‖y‖ ^ 2) x v = 2 * inner ℝ x v := by
    rw [fderiv_norm_sq_apply]
    simp
  have hsq_chain :
      fderiv ℝ (fun y : Domain n => ‖y‖ ^ 2) x v =
        2 * ‖x‖ * fderiv ℝ (fun y : Domain n => ‖y‖) x v := by
    rw [show (fun y : Domain n => ‖y‖ ^ 2) =
        (fun t : ℝ => t ^ 2) ∘ (fun y : Domain n => ‖y‖) by rfl]
    rw [fderiv_comp x (by fun_prop) hnorm]
    simp [fderiv_fun_pow]
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hmain :
      ‖x‖ * fderiv ℝ (fun y : Domain n => ‖y‖) x v = inner ℝ x v := by
    nlinarith [hsq_left, hsq_chain]
  rw [eq_div_iff hnorm_ne]
  simpa [mul_comm] using hmain

/-- The differential of `phi |x|` away from the origin. -/
theorem fderiv_phi_norm_apply {n : ℕ} {phi : ℝ → ℝ} {x v : Domain n}
    (hphi : DifferentiableAt ℝ phi ‖x‖) (hx : x ≠ 0) :
    fderiv ℝ (fun y : Domain n => phi ‖y‖) x v =
      deriv phi ‖x‖ * (inner ℝ x v / ‖x‖) := by
  have hnorm : DifferentiableAt ℝ (fun y : Domain n => ‖y‖) x := by
    exact (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt (by norm_num)
  rw [show (fun y : Domain n => phi ‖y‖) =
      phi ∘ (fun y : Domain n => ‖y‖) by rfl]
  rw [fderiv_comp x hphi hnorm]
  simp [fderiv_eq_smul_deriv, fderiv_norm_apply hx, mul_comm]

/-- Component-wise derivative formula for `X(x) = φ(|x|) x`.

This is the formal version of
`∂ᵢ Xⱼ = φ(r) δᵢⱼ + φ'(r) xᵢ xⱼ / r`.
-/
def RadialVectorFieldDerivativeFormula {n : ℕ} (phi : ℝ → ℝ) : Prop :=
  ∀ x : Domain n, x ≠ 0 → ∀ i j : Fin n,
    vectorFieldPartial (radialVectorField phi) i j x =
      phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖)

/-- Proof of
`∂ᵢ(φ(|x|) xⱼ) = φ(|x|) δᵢⱼ + φ'(|x|) xᵢxⱼ/|x|`.

This is exactly the coordinate computation in the manuscript: differentiate the product
`φ(r) xⱼ`, use `∂ᵢ r = xᵢ/r`, and then rewrite `δᵢⱼ` as the `j`-th component of `eᵢ`. -/
theorem radialVectorFieldDerivativeFormula {n : ℕ} {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) :
    RadialVectorFieldDerivativeFormula (n := n) phi := by
  intro x hx i j
  have hnorm : DifferentiableAt ℝ (fun y : Domain n => ‖y‖) x := by
    exact (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt (by norm_num)
  have hscalar : DifferentiableAt ℝ (fun y : Domain n => phi ‖y‖) x :=
    (hphi ‖x‖).comp x hnorm
  have hprod :=
    fderiv_fun_smul (𝕜 := ℝ) (x := x)
      (c := fun y : Domain n => phi ‖y‖)
      (f := fun y : Domain n => y) hscalar differentiableAt_id
  have hcoord :
      inner ℝ x (coordUnit i) = x i := by
    simpa [coordUnit] using inner_domainCoordUnit_right i x
  calc
    vectorFieldPartial (radialVectorField phi) i j x
        = (fderiv ℝ (radialVectorField phi) x (coordUnit i)) j := rfl
    _ =
        (phi ‖x‖ • fderiv ℝ (fun y : Domain n => y) x (coordUnit i)
          + (fderiv ℝ (fun y : Domain n => phi ‖y‖) x).smulRight x (coordUnit i)) j := by
          change
            (fderiv ℝ
              (fun y : Domain n => (fun y : Domain n => phi ‖y‖) y • (fun y : Domain n => y) y)
              x (coordUnit i)) j = _
          simpa using
            congrArg (fun L : Domain n →L[ℝ] Domain n => (L (coordUnit i)) j) hprod
    _ =
        phi ‖x‖ * coordUnit i j
          + (deriv phi ‖x‖ * (x i / ‖x‖)) * x j := by
          simp [fderiv_phi_norm_apply (hphi ‖x‖) hx, hcoord]
    _ =
        phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖) := by
          ring_nf

/-- Divergence formula for the radial vector field:
`div X = n φ(r) + r φ'(r)`. -/
def RadialVectorFieldDivergenceFormula {n : ℕ} (phi : ℝ → ℝ) : Prop :=
  ∀ x : Domain n, x ≠ 0 →
    divergence (radialVectorField phi) x =
      (n : ℝ) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖

/-- Proof of `div (φ(|x|)x) = n φ(|x|) + |x| φ'(|x|)`.

This is obtained by taking `j = i` in `RadialVectorFieldDerivativeFormula` and summing over `i`. -/
theorem radialVectorFieldDivergenceFormula {n : ℕ} {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) :
    RadialVectorFieldDivergenceFormula (n := n) phi := by
  intro x hx
  have hdiag :
      ∀ i : Fin n,
        vectorFieldPartial (radialVectorField phi) i i x =
          phi ‖x‖ * coordUnit i i + deriv phi ‖x‖ * (x i * x i / ‖x‖) := by
    intro i
    exact radialVectorFieldDerivativeFormula hphi x hx i i
  have hsum_sq : (∑ i : Fin n, x i * x i) = ‖x‖ ^ 2 := by
    simpa [pow_two] using domain_sum_sq_eq_norm_sq x
  have hsum_diag : (∑ i : Fin n, coordUnit i i) = (n : ℝ) := by
    simp [coordUnit, domainCoordUnit]
  have hfirst :
      (∑ i : Fin n, phi ‖x‖ * coordUnit i i) = (n : ℝ) * phi ‖x‖ := by
    calc
      (∑ i : Fin n, phi ‖x‖ * coordUnit i i)
          = phi ‖x‖ * (∑ i : Fin n, coordUnit i i) := by
            simpa using
              (Finset.mul_sum Finset.univ (fun i : Fin n => coordUnit i i)
                (phi ‖x‖)).symm
      _ = (n : ℝ) * phi ‖x‖ := by
            rw [hsum_diag]
            ring
  have hsecond :
      (∑ i : Fin n, deriv phi ‖x‖ * (x i * x i / ‖x‖)) =
        deriv phi ‖x‖ * ((∑ i : Fin n, x i * x i) / ‖x‖) := by
    calc
      (∑ i : Fin n, deriv phi ‖x‖ * (x i * x i / ‖x‖))
          = deriv phi ‖x‖ * (∑ i : Fin n, x i * x i / ‖x‖) := by
            simpa using
              (Finset.mul_sum Finset.univ
                (fun i : Fin n => x i * x i / ‖x‖) (deriv phi ‖x‖)).symm
      _ = deriv phi ‖x‖ * ((∑ i : Fin n, x i * x i) / ‖x‖) := by
            congr 1
            exact (Finset.sum_div Finset.univ (fun i : Fin n => x i * x i) ‖x‖).symm
  have hsum :
      (∑ i : Fin n,
        (phi ‖x‖ * coordUnit i i + deriv phi ‖x‖ * (x i * x i / ‖x‖))) =
          (n : ℝ) * phi ‖x‖
            + deriv phi ‖x‖ * ((∑ i : Fin n, x i * x i) / ‖x‖) := by
    rw [Finset.sum_add_distrib]
    rw [hfirst, hsecond]
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  calc
    divergence (radialVectorField phi) x
        = ∑ i : Fin n,
            (phi ‖x‖ * coordUnit i i + deriv phi ‖x‖ * (x i * x i / ‖x‖)) := by
          unfold divergence
          exact Finset.sum_congr rfl (fun i _ => hdiag i)
    _ = (n : ℝ) * phi ‖x‖
          + deriv phi ‖x‖ * ((∑ i : Fin n, x i * x i) / ‖x‖) := hsum
    _ = (n : ℝ) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖ := by
          rw [hsum_sq]
          field_simp [hnorm_ne]

/-- Coordinate expansion in the standard basis of `EuclideanSpace`. -/
theorem euclideanSpace_sum_coordUnit {n : ℕ} (x : Domain n) :
    (∑ i : Fin n, SMul.smul (x i) (coordUnit i)) = x := by
  change (∑ i : Fin n, (x i) • (coordUnit i)) = x
  simpa [PiLp.basisFun_repr, PiLp.basisFun_apply, coordUnit, domainCoordUnit,
    EuclideanSpace.single] using
    (PiLp.basisFun 2 ℝ (Fin n)).sum_repr x

/-- Apply the linear map `fderiv u x` to the coordinate expansion of `x`. -/
theorem fderiv_apply_eq_sum_partial {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    fderiv ℝ u x x =
      ∑ i : Fin n, SMul.smul (x i) (partialDerivative u i x) := by
  calc
    fderiv ℝ u x x
        = fderiv ℝ u x (∑ i : Fin n, SMul.smul (x i) (coordUnit i)) := by
          rw [euclideanSpace_sum_coordUnit x]
    _ = ∑ i : Fin n, fderiv ℝ u x (SMul.smul (x i) (coordUnit i)) := by
          rw [map_sum]
    _ = ∑ i : Fin n, SMul.smul (x i) (partialDerivative u i x) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (fderiv ℝ u x).map_smul (x i) (coordUnit i)

/-- Real scalar factors pull out of both entries of the inner product. -/
theorem inner_smul_smul_real {m : ℕ} (a b : ℝ) (v w : Target m) :
    inner ℝ (SMul.smul a v) (SMul.smul b w) =
      a * b * inner ℝ v w := by
  calc
    inner ℝ (SMul.smul a v) (SMul.smul b w)
        = a * inner ℝ v (SMul.smul b w) := by
          exact inner_smul_left v (SMul.smul b w) a
    _ = a * (b * inner ℝ v w) := by
          exact congrArg (fun t : ℝ => a * t) (inner_smul_right v w b)
    _ = a * b * inner ℝ v w := by
          ring

/-- The square norm of a finite real linear combination, expanded as a double sum. -/
theorem norm_sq_sum_smul {n m : ℕ}
    (a : Fin n → ℝ) (v : Fin n → Target m) :
    ‖(∑ i : Fin n, SMul.smul (a i) (v i))‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * inner ℝ (v i) (v j) := by
  refine (real_inner_self_eq_norm_sq
    (∑ i : Fin n, SMul.smul (a i) (v i))).symm.trans ?_
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact inner_smul_smul_real (a i) (a j) (v i) (v j)

/-- Cauchy-Schwarz for a finite real linear combination of target vectors. -/
theorem norm_sum_smul_le_sqrt_mul_sqrt {n m : ℕ}
    (a : Fin n → ℝ) (v : Fin n → Target m) :
    ‖(∑ i : Fin n, SMul.smul (a i) (v i))‖
      ≤ √(∑ i : Fin n, a i ^ 2) * √(∑ i : Fin n, ‖v i‖ ^ 2) := by
  have htri :
      ‖(∑ i : Fin n, SMul.smul (a i) (v i))‖
        ≤ ∑ i : Fin n, ‖SMul.smul (a i) (v i)‖ := by
    simpa using
      (norm_sum_le (Finset.univ : Finset (Fin n))
        (fun i : Fin n => SMul.smul (a i) (v i)))
  have hnorm :
      (∑ i : Fin n, ‖SMul.smul (a i) (v i)‖)
        = ∑ i : Fin n, |a i| * ‖v i‖ := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      ‖SMul.smul (a i) (v i)‖ = ‖a i‖ * ‖v i‖ := by
        exact norm_smul (a i) (v i)
      _ = |a i| * ‖v i‖ := by
        rw [Real.norm_eq_abs]
  have hcs :
      (∑ i : Fin n, |a i| * ‖v i‖)
        ≤ √(∑ i : Fin n, |a i| ^ 2) * √(∑ i : Fin n, ‖v i‖ ^ 2) := by
    simpa using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
        (fun i : Fin n => |a i|) (fun i : Fin n => ‖v i‖))
  have habs :
      (∑ i : Fin n, |a i| ^ 2) = ∑ i : Fin n, a i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact sq_abs (a i)
  calc
    ‖(∑ i : Fin n, SMul.smul (a i) (v i))‖
        ≤ ∑ i : Fin n, ‖SMul.smul (a i) (v i)‖ := htri
    _ = ∑ i : Fin n, |a i| * ‖v i‖ := hnorm
    _ ≤ √(∑ i : Fin n, |a i| ^ 2) * √(∑ i : Fin n, ‖v i‖ ^ 2) := hcs
    _ = √(∑ i : Fin n, a i ^ 2) * √(∑ i : Fin n, ‖v i‖ ^ 2) := by
          rw [habs]

/-- The squared coefficients of the radial unit direction have sum at most `1`. -/
theorem radialCoeff_sq_sum_le_one {n : ℕ} (x : Domain n) :
    (∑ i : Fin n, (‖x‖⁻¹ * x i) ^ 2) ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnorm_sq : ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
      simpa using domain_norm_sq_eq_sum x
    calc
      (∑ i : Fin n, (‖x‖⁻¹ * x i) ^ 2)
          = (‖x‖⁻¹) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
            calc
              (∑ i : Fin n, (‖x‖⁻¹ * x i) ^ 2)
                  = ∑ i : Fin n, (‖x‖⁻¹) ^ 2 * x i ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ = (‖x‖⁻¹) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
                    rw [Finset.mul_sum]
      _ = (‖x‖⁻¹) ^ 2 * ‖x‖ ^ 2 := by
            rw [← hnorm_sq]
      _ = 1 := by
            field_simp [hnorm_ne]
      _ ≤ 1 := le_rfl

/-- The radial energy of an arbitrary gradient matrix as a double contraction. -/
theorem gradientRadialEnergy_eq_sum {n m : ℕ}
    (A : Gradient n m) (x : Domain n) :
    gradientRadialEnergy A x =
      (‖x‖⁻¹) ^ 2 *
        (∑ i : Fin n, ∑ j : Fin n,
          x i * x j * inner ℝ (A i) (A j)) := by
  let S : Target m := ∑ i : Fin n, SMul.smul (x i) (A i)
  have hS :
      ‖S‖ ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          x i * x j * inner ℝ (A i) (A j) := by
    simpa [S] using
      norm_sq_sum_smul (n := n) (m := m)
        (fun i : Fin n => x i) A
  have hnorm_smul :
      ‖SMul.smul (‖x‖⁻¹) S‖ = ‖(‖x‖⁻¹ : ℝ)‖ * ‖S‖ := by
    exact norm_smul (‖x‖⁻¹ : ℝ) S
  have hinv_nonneg : 0 ≤ (‖x‖⁻¹ : ℝ) := inv_nonneg.mpr (norm_nonneg x)
  calc
    gradientRadialEnergy A x
        = ‖SMul.smul (‖x‖⁻¹) S‖ ^ 2 := by
          unfold gradientRadialEnergy gradientRadialDerivative
          rfl
    _ = (‖x‖⁻¹) ^ 2 * ‖S‖ ^ 2 := by
          rw [hnorm_smul]
          rw [Real.norm_of_nonneg hinv_nonneg]
          ring
    _ = (‖x‖⁻¹) ^ 2 *
        (∑ i : Fin n, ∑ j : Fin n,
          x i * x j * inner ℝ (A i) (A j)) := by
          rw [hS]

/-- The radial part of a pointwise gradient matrix is bounded by its full
Hilbert-Schmidt energy. -/
theorem gradientRadialEnergy_le_gradientEnergy {n m : ℕ}
    (A : Gradient n m) (x : Domain n) :
    gradientRadialEnergy A x ≤ gradientEnergy A := by
  let a : Fin n → ℝ := fun i => ‖x‖⁻¹ * x i
  have hradial_deriv :
      gradientRadialDerivative A x = ∑ i : Fin n, SMul.smul (a i) (A i) := by
    calc
      gradientRadialDerivative A x
          = SMul.smul (‖x‖⁻¹) (∑ i : Fin n, SMul.smul (x i) (A i)) := rfl
      _ = ∑ i : Fin n, SMul.smul (‖x‖⁻¹) (SMul.smul (x i) (A i)) := by
            exact
              (Finset.smul_sum
                (s := Finset.univ)
                (f := fun i : Fin n => SMul.smul (x i) (A i))
                (r := (‖x‖⁻¹ : ℝ)))
      _ = ∑ i : Fin n, SMul.smul (a i) (A i) := by
            apply Finset.sum_congr rfl
            intro i _
            change
              SMul.smul (‖x‖⁻¹) (SMul.smul (x i) (A i)) =
                SMul.smul (‖x‖⁻¹ * x i) (A i)
            exact smul_smul (‖x‖⁻¹ : ℝ) (x i) (A i)
  have hnorm :
      ‖gradientRadialDerivative A x‖
        ≤ √(∑ i : Fin n, a i ^ 2) * √(gradientEnergy A) := by
    simpa [hradial_deriv, gradientEnergy] using
      norm_sum_smul_le_sqrt_mul_sqrt (n := n) (m := m) a A
  have ha_nonneg : 0 ≤ ∑ i : Fin n, a i ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
  have henergy_nonneg : 0 ≤ gradientEnergy A := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖A i‖
  have hsqrt_nonneg :
      0 ≤ √(∑ i : Fin n, a i ^ 2) * √(gradientEnergy A) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare :
      ‖gradientRadialDerivative A x‖ ^ 2
        ≤ (√(∑ i : Fin n, a i ^ 2) * √(gradientEnergy A)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hsqrt_nonneg).mpr hnorm
  have hsqrt_sq :
      (√(∑ i : Fin n, a i ^ 2) * √(gradientEnergy A)) ^ 2 =
        (∑ i : Fin n, a i ^ 2) * gradientEnergy A := by
    rw [mul_pow, Real.sq_sqrt ha_nonneg, Real.sq_sqrt henergy_nonneg]
  have ha_le_one : (∑ i : Fin n, a i ^ 2) ≤ 1 := by
    simpa [a] using radialCoeff_sq_sum_le_one (n := n) x
  have hmul_le :
      (∑ i : Fin n, a i ^ 2) * gradientEnergy A ≤ 1 * gradientEnergy A := by
    exact mul_le_mul_of_nonneg_right ha_le_one henergy_nonneg
  calc
    gradientRadialEnergy A x
        = ‖gradientRadialDerivative A x‖ ^ 2 := rfl
    _ ≤ (√(∑ i : Fin n, a i ^ 2) * √(gradientEnergy A)) ^ 2 := hsquare
    _ = (∑ i : Fin n, a i ^ 2) * gradientEnergy A := hsqrt_sq
    _ ≤ 1 * gradientEnergy A := hmul_le
    _ = gradientEnergy A := by ring

/-- The weak radial energy density is pointwise bounded by the full weak energy density. -/
theorem weakRadialEnergyDensity_le_weakEnergyDensity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a x : Domain n) :
    weakRadialEnergyDensity Du a x ≤ weakEnergyDensity Du x := by
  simpa [weakRadialEnergyDensity, weakRadialDerivative, weakEnergyDensity,
    gradientRadialEnergy] using
    gradientRadialEnergy_le_gradientEnergy (Du x) (x - a)

/-- Norm form of `weakRadialEnergyDensity_le_weakEnergyDensity`, convenient for
`Integrable.mono'`. -/
theorem norm_weakRadialEnergyDensity_le_weakEnergyDensity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a x : Domain n) :
    ‖weakRadialEnergyDensity Du a x‖ ≤ weakEnergyDensity Du x := by
  have hnonneg : 0 ≤ weakRadialEnergyDensity Du a x := by
    simp [weakRadialEnergyDensity]
  rw [Real.norm_of_nonneg hnonneg]
  exact weakRadialEnergyDensity_le_weakEnergyDensity Du a x

/-- Pure pointwise algebraic contraction for a radial vector-field derivative,
with an arbitrary gradient matrix `A`.  This is the version that will survive
unchanged in the `W^{1,2}_{loc}` proof. -/
theorem gradientRadialStressContractionFormula {n m : ℕ}
    (A : Gradient n m) (phi : ℝ → ℝ) {x : Domain n} (hx : x ≠ 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (A i) (A j) *
        (phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖)))
      =
    phi ‖x‖ * gradientEnergy A
      + ‖x‖ * deriv phi ‖x‖ * gradientRadialEnergy A x := by
  have hfirst :
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (phi ‖x‖ * coordUnit i j)) =
        phi ‖x‖ * gradientEnergy A := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (phi ‖x‖ * coordUnit i j))
          = ∑ i : Fin n, phi ‖x‖ * ‖A i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · simp [coordUnit, domainCoordUnit, mul_comm]
            · intro j _ hji
              have hcoord : coordUnit i j = 0 := by
                simp [coordUnit, domainCoordUnit, hji]
              simp [hcoord]
            · intro hi
              simp at hi
      _ = phi ‖x‖ * gradientEnergy A := by
            rw [gradientEnergy]
            exact (Finset.mul_sum Finset.univ
              (fun i : Fin n => ‖A i‖ ^ 2) (phi ‖x‖)).symm
  have hsecond :
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) *
          (deriv phi ‖x‖ * (x i * x j / ‖x‖))) =
        deriv phi ‖x‖ *
          ((∑ i : Fin n, ∑ j : Fin n,
            x i * x j * inner ℝ (A i) (A j)) / ‖x‖) := by
    simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) *
          (phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖))) =
        phi ‖x‖ * gradientEnergy A +
          deriv phi ‖x‖ *
            ((∑ i : Fin n, ∑ j : Fin n,
              x i * x j * inner ℝ (A i) (A j)) / ‖x‖) := by
    rw [← hfirst, ← hsecond]
    simp [mul_add, Finset.sum_add_distrib]
  have hradial := gradientRadialEnergy_eq_sum A x
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hradial_term :
      deriv phi ‖x‖ *
          ((∑ i : Fin n, ∑ j : Fin n,
            x i * x j * inner ℝ (A i) (A j)) / ‖x‖) =
        ‖x‖ * deriv phi ‖x‖ * gradientRadialEnergy A x := by
    rw [hradial]
    field_simp [hnorm_ne]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (A i) (A j) *
        (phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖)))
        = phi ‖x‖ * gradientEnergy A +
          deriv phi ‖x‖ *
            ((∑ i : Fin n, ∑ j : Fin n,
              x i * x j * inner ℝ (A i) (A j)) / ‖x‖) := hsplit
    _ = phi ‖x‖ * gradientEnergy A
        + ‖x‖ * deriv phi ‖x‖ * gradientRadialEnergy A x := by
          rw [hradial_term]

/-- At the origin, the radial derivative is `|x|⁻¹ ∑ᵢ xᵢ ∂ᵢu`. -/
theorem radialDerivative_zero_eq_sum {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    radialDerivative u 0 x =
      SMul.smul (‖x‖⁻¹)
        (∑ i : Fin n, SMul.smul (x i) (partialDerivative u i x)) := by
  calc
    radialDerivative u 0 x = SMul.smul (‖x‖⁻¹) (fderiv ℝ u x x) := by
      simp [radialDerivative, radialUnit]
      rfl
    _ = SMul.smul (‖x‖⁻¹)
        (∑ i : Fin n, SMul.smul (x i) (partialDerivative u i x)) := by
      rw [fderiv_apply_eq_sum_partial u x]

@[simp]
theorem gradientEnergy_smoothGradient {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    gradientEnergy (smoothGradient u x) = energyDensity u x := rfl

theorem gradientRadialDerivative_smoothGradient_zero {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    gradientRadialDerivative (smoothGradient u x) x = radialDerivative u 0 x :=
  (radialDerivative_zero_eq_sum u x).symm

@[simp]
theorem gradientRadialEnergy_smoothGradient_zero {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    gradientRadialEnergy (smoothGradient u x) x = radialEnergyDensity u 0 x := by
  unfold gradientRadialEnergy radialEnergyDensity
  rw [gradientRadialDerivative_smoothGradient_zero]

/-- The radial energy density at the origin as the double contraction
`|x|⁻² ∑ᵢⱼ xᵢxⱼ <∂ᵢu,∂ⱼu>`. -/
theorem radialEnergyDensity_zero_eq_sum {n m : ℕ}
    (u : Domain n → Target m) (x : Domain n) :
    radialEnergyDensity u 0 x =
      (‖x‖⁻¹) ^ 2 *
        (∑ i : Fin n, ∑ j : Fin n,
          x i * x j *
            inner ℝ (partialDerivative u i x) (partialDerivative u j x)) := by
  let S : Target m :=
    ∑ i : Fin n, SMul.smul (x i) (partialDerivative u i x)
  have hS :
      ‖S‖ ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          x i * x j *
            inner ℝ (partialDerivative u i x) (partialDerivative u j x) := by
    simpa [S] using
      norm_sq_sum_smul (n := n) (m := m)
        (fun i : Fin n => x i) (fun i : Fin n => partialDerivative u i x)
  have hnorm_smul :
      ‖SMul.smul (‖x‖⁻¹) S‖ = ‖(‖x‖⁻¹ : ℝ)‖ * ‖S‖ := by
    exact norm_smul (‖x‖⁻¹ : ℝ) S
  have hinv_nonneg : 0 ≤ (‖x‖⁻¹ : ℝ) := inv_nonneg.mpr (norm_nonneg x)
  calc
    radialEnergyDensity u 0 x
        = ‖SMul.smul (‖x‖⁻¹) S‖ ^ 2 := by
          unfold radialEnergyDensity
          rw [radialDerivative_zero_eq_sum u x]
    _ = (‖x‖⁻¹) ^ 2 * ‖S‖ ^ 2 := by
          rw [hnorm_smul]
          rw [Real.norm_of_nonneg hinv_nonneg]
          ring
    _ = (‖x‖⁻¹) ^ 2 *
        (∑ i : Fin n, ∑ j : Fin n,
          x i * x j *
            inner ℝ (partialDerivative u i x) (partialDerivative u j x)) := by
          rw [hS]

/-- The algebraic stress-energy contraction for the radial vector field.

This is the formal target corresponding to
`∑ᵢⱼ <∂ᵢu,∂ⱼu> ∂ᵢXⱼ
 = φ(r)|∇u|² + rφ'(r)|∂ᵣu|²`.
-/
def RadialStressContractionFormula {n m : ℕ}
    (u : Domain n → Target m) (phi : ℝ → ℝ) : Prop :=
  ∀ x : Domain n, x ≠ 0 →
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (partialDerivative u i x) (partialDerivative u j x) *
        vectorFieldPartial (radialVectorField phi) i j x)
      =
    phi ‖x‖ * energyDensity u x
      + ‖x‖ * deriv phi ‖x‖ * radialEnergyDensity u 0 x

/-- Proof of the stress-energy contraction identity for `X(x) = φ(|x|)x`.

This is the formal version of substituting
`∂ᵢXⱼ = φ(r)δᵢⱼ + φ'(r)xᵢxⱼ/r` into the double contraction. -/
theorem radialStressContractionFormula {n m : ℕ}
    (u : Domain n → Target m) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) :
    RadialStressContractionFormula u phi := by
  intro x hx
  have hderiv :
      ∀ i j : Fin n,
        vectorFieldPartial (radialVectorField phi) i j x =
          phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖) := by
    intro i j
    exact radialVectorFieldDerivativeFormula hphi x hx i j
  have hpure := gradientRadialStressContractionFormula
    (smoothGradient u x) phi hx
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (partialDerivative u i x) (partialDerivative u j x) *
        vectorFieldPartial (radialVectorField phi) i j x)
        =
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (partialDerivative u i x) (partialDerivative u j x) *
          (phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hderiv i j]
    _ = phi ‖x‖ * gradientEnergy (smoothGradient u x)
          + ‖x‖ * deriv phi ‖x‖ *
            gradientRadialEnergy (smoothGradient u x) x := by
            simpa [smoothGradient] using hpure
    _ = phi ‖x‖ * energyDensity u x
          + ‖x‖ * deriv phi ‖x‖ * radialEnergyDensity u 0 x := by
            simp

/-- The stress contraction formula for an arbitrary gradient field. -/
theorem weakRadialStressContractionFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) :
    ∀ x : Domain n, x ≠ 0 →
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          vectorFieldPartial (radialVectorField phi) i j x)
        =
      phi ‖x‖ * weakEnergyDensity Du x
        + ‖x‖ * deriv phi ‖x‖ * weakRadialEnergyDensity Du 0 x := by
  intro x hx
  have hderiv :
      ∀ i j : Fin n,
        vectorFieldPartial (radialVectorField phi) i j x =
          phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖) := by
    intro i j
    exact radialVectorFieldDerivativeFormula hphi x hx i j
  have hpure := gradientRadialStressContractionFormula (Du x) phi hx
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (Du x i) (Du x j) *
        vectorFieldPartial (radialVectorField phi) i j x)
        =
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (phi ‖x‖ * coordUnit i j + deriv phi ‖x‖ * (x i * x j / ‖x‖)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hderiv i j]
    _ = phi ‖x‖ * weakEnergyDensity Du x
          + ‖x‖ * deriv phi ‖x‖ * weakRadialEnergyDensity Du 0 x := by
            simpa [weakEnergyDensity, weakRadialEnergyDensity, weakRadialDerivative,
              gradientRadialEnergy] using hpure

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
