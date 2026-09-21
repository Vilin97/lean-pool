/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.SchurRigidity

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Schur rigidity: an independent statement using explicit connection curvature.
Ricci and scalar curvature are the displayed orthonormal contractions of that
curvature. The covariant divergence uses the actual manifold differential and
both connection corrections. No differential identity is an assumption. -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff BigOperators

namespace SchurEntry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

def along (X Z : ∀ x : M, (TangentSpace I : M → Type _) x) : ∀ x : M, (TangentSpace I : M → Type _) x := fun x ↦ cov Z x (X x)

/-- The actual connection curvature, including its Lie-bracket correction. -/
def curvature (X Y Z : ∀ x : M, (TangentSpace I : M → Type _) x) : ∀ x : M, (TangentSpace I : M → Type _) x :=
  along cov X (along cov Y Z) - along cov Y (along cov X Z) -
    along cov (VectorField.mlieBracket I X Y) Z

def MetricCompatible : Prop :=
  ∀ {x : M} {U V : ∀ y : M, (TangentSpace I : M → Type _) y}, MDiffAt (T% U) x → MDiffAt (T% V) x →
    ∀ w : (TangentSpace I : M → Type _) x, mvfderiv (I := I) (fun y ↦ inner ℝ (U y) (V y)) x w =
      inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)

variable (extension : ∀ x : M, (TangentSpace I : M → Type _) x → ∀ y : M, (TangentSpace I : M → Type _) y)

/-- Ricci is the first/output trace of the explicit curvature operator. -/
def ricci (x : M) (u v : (TangentSpace I : M → Type _) x) : ℝ :=
  letI : FiniteDimensional ℝ ((TangentSpace I : M → Type _) x) := VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ ((TangentSpace I : M → Type _) x)
  ∑ i, inner ℝ (curvature cov (extension x (b i)) (extension x u) (extension x v) x) (b i)

def scalar (x : M) : ℝ :=
  letI : FiniteDimensional ℝ ((TangentSpace I : M → Type _) x) := VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ ((TangentSpace I : M → Type _) x)
  ∑ i, ricci cov extension x (b i) (b i)

def einstein (x : M) (u v : (TangentSpace I : M → Type _) x) : ℝ :=
  ricci cov extension x u v - scalar cov extension x / 2 * inner ℝ u v

/-- Corrected derivative of a bilinear tensor field, not an abstract derivative. -/
def tensorDerivative (A : ∀ x : M, (TangentSpace I : M → Type _) x → (TangentSpace I : M → Type _) x → ℝ)
    (x : M) (p u v : (TangentSpace I : M → Type _) x) : ℝ :=
  mvfderiv (I := I) (fun y ↦ A y (extension x u y) (extension x v y)) x p -
    A x (cov (extension x u) x p) v - A x u (cov (extension x v) x p)

def divergence (A : ∀ x : M, (TangentSpace I : M → Type _) x → (TangentSpace I : M → Type _) x → ℝ)
    (x : M) (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) : ℝ :=
  ∑ i, tensorDerivative cov extension A x (b i) (b i) w

variable
  (hvalue : ∀ (x : M) (v : (TangentSpace I : M → Type _) x), extension x v x = v)
  (hext : ∀ (x : M) (v : (TangentSpace I : M → Type _) x), ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (extension x v)))
  (hT : cov.torsion = 0) (hmetric : MetricCompatible cov)


include hvalue hext

private theorem curvature_eq (x : M) (u v z : (TangentSpace I : M → Type _) x) :
    curvature cov (extension x u) (extension x v) (extension x z) x =
      cov.curvatureTensor x u v z := by
  change cov.curvatureAux (extension x u) (extension x v) (extension x z) x = _
  simpa only [hvalue] using cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff
    ((hext x u).of_le (by norm_num)) ((hext x v).of_le (by norm_num))
    ((hext x z).of_le (by norm_num)) x

private theorem ricci_eq (x : M) (u v : (TangentSpace I : M → Type _) x) :
    ricci cov extension x u v = cov.ricciCurvature x u v := by
  unfold ricci
  rw [CovariantDerivative.ricciCurvature_apply,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ ((TangentSpace I : M → Type _) x))]
  apply Finset.sum_congr rfl
  intro i _
  rw [curvature_eq cov extension hvalue hext]
  exact real_inner_comm _ _

private theorem scalar_eq (x : M) : scalar cov extension x = cov.scalarCurvature x := by
  unfold scalar
  simp_rw [ricci_eq cov extension hvalue hext]
  rfl

private theorem einstein_eq (x : M) (u v : (TangentSpace I : M → Type _) x) :
    einstein cov extension x u v = SchurRigidity.einsteinTensor cov x u v := by
  rw [einstein, ricci_eq cov extension hvalue hext, scalar_eq cov extension hvalue hext]
  rfl

private theorem divergence_eq (A : ∀ x : M, (TangentSpace I : M → Type _) x →ₗ[ℝ] (TangentSpace I : M → Type _) x →ₗ[ℝ] ℝ)
    (x : M) (hA : SchurRigidity.BilinearEvaluationMDifferentiableAt A x)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) :
    divergence cov extension (fun y u v ↦ A y u v) x b w =
      SchurRigidity.divergenceInBasis cov A x b w := by
  unfold divergence SchurRigidity.divergenceInBasis
  apply Finset.sum_congr rfl
  intro i _
  have he (v : (TangentSpace I : M → Type _) x) : MDiffAt (T% (extension x v)) x :=
    ((hext x v) x).mdifferentiableAt (by norm_num)
  have hs (v : (TangentSpace I : M → Type _) x) : MDiffAt
      (T% (CovariantDerivative.smoothExtend (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v)) x :=
    ((CovariantDerivative.smoothExtend_contMDiff_three x v) x).mdifferentiableAt (by norm_num)
  have hd := SchurRigidity.bilinearDerivative_extension_independent cov A hA
    (he (b i)) (hs (b i)) (he w) (hs w)
    (by simp only [hvalue, CovariantDerivative.smoothExtend_apply])
    (by simp only [hvalue, CovariantDerivative.smoothExtend_apply]) (b i)
  simpa only [tensorDerivative, SchurRigidity.bilinearDerivative, hvalue,
    CovariantDerivative.schurFrame, OrthonormalBasis.coe_toBasis] using! hd

omit hvalue hext in
private theorem einstein_regular (x : M) :
    SchurRigidity.BilinearEvaluationMDifferentiableAt (SchurRigidity.einsteinTensor cov) x := by
  have hg : SchurRigidity.BilinearEvaluationMDifferentiableAt
      (SchurRigidity.metricTensor (I := I) (M := M)) x := by
    intro U V hU hV
    exact CovariantDerivative.mdiffAt_inner_sections hU hV
  have hf : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ cov.scalarCurvature y / 2) x := by
    simpa only [div_eq_mul_inv, Pi.mul_apply] using!
      (SchurRigidity.scalarCurvature_mdifferentiableAt cov x).mul
        (mdifferentiableAt_const (c := (2 : ℝ)⁻¹))
  exact (cov.ricciDerivative_ricci_evaluation_regular x).sub (hg.smul hf)

include hvalue hext hT hmetric

theorem geometricContractedBianchi (x : M)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) :
    divergence cov extension (ricci cov extension) x b w =
      (1 / 2 : ℝ) * mvfderiv (I := I) (scalar cov extension) x w := by
  have hr : ricci cov extension = (fun y u v ↦ cov.ricciCurvature y u v) :=
    funext fun y ↦ funext fun u ↦ funext fun v ↦ ricci_eq cov extension hvalue hext y u v
  have hs : scalar cov extension = cov.scalarCurvature :=
    funext (scalar_eq cov extension hvalue hext)
  rw [hr, hs, divergence_eq cov extension hvalue hext _ x
    (cov.ricciDerivative_ricci_evaluation_regular x)]
  exact SchurRigidity.divergenceRicci_eq_half_differential_scalarCurvature
    cov ⟨hT, hmetric⟩ x b w

theorem divergenceEinstein (x : M)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) :
    divergence cov extension (einstein cov extension) x b w = 0 := by
  have he : einstein cov extension = (fun y u v ↦ SchurRigidity.einsteinTensor cov y u v) :=
    funext fun y ↦ funext fun u ↦ funext fun v ↦ einstein_eq cov extension hvalue hext y u v
  rw [he, divergence_eq cov extension hvalue hext _ x (einstein_regular cov x)]
  exact SchurRigidity.divergenceEinstein_eq_zero cov ⟨hT, hmetric⟩ x b w

theorem schur [ConnectedSpace M]
    (hn : 3 ≤ Module.finrank ℝ E) (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ x u v, ricci cov extension x u v = f x * inner ℝ u v) :
    ∃ c : ℝ, ∀ x, f x = c := by
  apply SchurRigidity.schur cov ⟨hT, hmetric⟩ hn f hf
  intro x u v
  rw [← ricci_eq cov extension hvalue hext, hRic]

theorem threeDimensionalEinstein_constantCurvature [ConnectedSpace M]
    (hn : Module.finrank ℝ E = 3) (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ x u v, ricci cov extension x u v = f x * inner ℝ u v) :
    ∃ K : ℝ, ∀ (x : M) (u v z t : (TangentSpace I : M → Type _) x),
      inner ℝ (curvature cov (extension x u) (extension x v) (extension x z) x) t =
        K * (inner ℝ u t * inner ℝ v z - inner ℝ u z * inner ℝ v t) := by
  have h := SchurRigidity.threeDimensionalEinstein_constantCurvature cov ⟨hT, hmetric⟩
    hn f hf (fun x u v ↦ (ricci_eq cov extension hvalue hext x u v).symm.trans (hRic x u v))
  simpa only [curvature_eq cov extension hvalue hext] using h

end SchurEntry
