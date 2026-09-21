/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.SchurMetricDerivative
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Tactic
/-!
# Tensoriality of the covariant derivative of a bilinear field

The regularity hypothesis below asks only for differentiability of evaluations
against differentiable sections. It assumes no covariant derivative identity.
The Leibniz rule cancels the derivatives of scalar multipliers, making the
section formula independent of the chosen extensions at the evaluation point.
-/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SchurRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Pointwise regularity of a bilinear field, tested on differentiable sections.
This is a regularity condition, not a differential or curvature identity. -/
def BilinearEvaluationMDifferentiableAt
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (x : M) : Prop :=
  ∀ U V : ∀ y : M, TM y, MDiffAt (T% U) x → MDiffAt (T% V) x →
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ A y (U y) (V y)) x

/-- Evaluation regularity is preserved by addition. -/
theorem BilinearEvaluationMDifferentiableAt.add
    {A B : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ} {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    (hB : BilinearEvaluationMDifferentiableAt B x) :
    BilinearEvaluationMDifferentiableAt (fun y ↦ A y + B y) x := by
  intro U V hU hV
  simpa only [LinearMap.add_apply, Pi.add_apply] using! (hA U V hU hV).add (hB U V hU hV)

/-- Evaluation regularity is preserved by subtraction. -/
theorem BilinearEvaluationMDifferentiableAt.sub
    {A B : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ} {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    (hB : BilinearEvaluationMDifferentiableAt B x) :
    BilinearEvaluationMDifferentiableAt (fun y ↦ A y - B y) x := by
  intro U V hU hV
  simpa only [LinearMap.sub_apply, Pi.sub_apply] using! (hA U V hU hV).sub (hB U V hU hV)

/-- Multiplication by a differentiable scalar preserves evaluation regularity. -/
theorem BilinearEvaluationMDifferentiableAt.smul
    {A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ} {x : M} {f : M → ℝ}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    BilinearEvaluationMDifferentiableAt (fun y ↦ f y • A y) x := by
  intro U V hU hV
  simpa only [LinearMap.smul_apply, smul_eq_mul, Pi.mul_apply] using! hf.mul (hA U V hU hV)

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  (A : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

variable [FiniteDimensional ℝ E]

/-- The section formula bundled in its directional argument. -/
def bilinearDerivativeAux (U V : ∀ y : M, TM y) (x : M) : TM x →L[ℝ] ℝ := by
  let L : TM x →L[ℝ] ℝ := ⟨(A x).flip (V x),
    ((A x).flip (V x)).continuous_of_finiteDimensional⟩
  let R : TM x →L[ℝ] ℝ := ⟨A x (U x),
    (A x (U x)).continuous_of_finiteDimensional⟩
  let dU : TM x →L[ℝ] TM x := cov U x
  let dV : TM x →L[ℝ] TM x := cov V x
  exact mvfderiv (I := I) (fun y ↦ A y (U y) (V y)) x - L.comp dU - R.comp dV


@[simp] theorem bilinearDerivativeAux_apply (U V : ∀ y : M, TM y)
    (x : M) (w : TM x) :
    bilinearDerivativeAux cov A U V x w = bilinearDerivative cov A U V x w := rfl

/-- Leibniz cancellation and additivity in the first section. -/
theorem tensorial_bilinearDerivativeAux₁ {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    (V : ∀ y : M, TM y) (hV : MDiffAt (T% V) x) :
    TensorialAt I E (bilinearDerivativeAux cov A · V x) x where
  smul hf hU := by
    ext w
    simp [bilinearDerivativeAux, mvfderiv_fun_mul hf (hA _ _ hU hV),
      cov.isCovariantDerivativeOn.leibniz hU hf, map_smul]
    ring
  add hU hU' := by
    ext w
    simp [bilinearDerivativeAux,
      mvfderiv_fun_add (hA _ _ hU hV) (hA _ _ hU' hV),
      cov.isCovariantDerivativeOn.add hU hU', map_add]
    abel

/-- Leibniz cancellation and additivity in the second section. -/
theorem tensorial_bilinearDerivativeAux₂ {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    (U : ∀ y : M, TM y) (hU : MDiffAt (T% U) x) :
    TensorialAt I E (bilinearDerivativeAux cov A U · x) x where
  smul hf hV := by
    ext w
    simp [bilinearDerivativeAux, mvfderiv_fun_mul hf (hA _ _ hU hV),
      cov.isCovariantDerivativeOn.leibniz hV hf, map_smul]
    ring
  add hV hV' := by
    ext w
    simp [bilinearDerivativeAux,
      mvfderiv_fun_add (hA _ _ hU hV) (hA _ _ hU hV'),
      cov.isCovariantDerivativeOn.add hV hV', map_add]
    abel

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- Differentiability of the finitely many components in the preferred actual
bundle trivialization implies differentiability of all section evaluations. -/
theorem bilinearEvaluationMDifferentiableAt_of_localFrame
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (x : M)
    (hcomp : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y ((trivializationAt E TM x).localFrame b i y)
        ((trivializationAt E TM x).localFrame b j y)) x) :
    BilinearEvaluationMDifferentiableAt A x := by
  classical
  intro U V hU hV
  let t := trivializationAt E TM x
  let s := t.localFrame b
  let c := t.localFrameCoeff I b
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  have hcU (i) : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ c i y (U y)) x :=
    mdifferentiableAt_localFrameCoeff b hx hU i
  have hcV (i) : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ c i y (V y)) x :=
    mdifferentiableAt_localFrameCoeff b hx hV i
  have hd : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ ∑ i, ∑ j, c i y (U y) * (c j y (V y) * A y (s i y) (s j y))) x := by
    have hij (i j) : MDifferentiableAt I 𝓘(ℝ)
        (fun y ↦ c i y (U y) * (c j y (V y) * A y (s i y) (s j y))) x := by
      simpa only [Pi.mul_apply] using! (hcU i).mul ((hcV j).mul (hcomp i j))
    have hi (i) := MDifferentiableAt.sum (t := Finset.univ) (fun j _ ↦ hij i j)
    simpa only [Finset.sum_fn] using! MDifferentiableAt.sum
      (t := Finset.univ) (fun i _ ↦ hi i)
  apply hd.congr_of_eventuallyEq
  filter_upwards [t.eventually_eq_localFrame_sum_coeff_smul (I := I) b hx (s := U),
    t.eventually_eq_localFrame_sum_coeff_smul (I := I) b hx (s := V)] with y hyU hyV
  change A y (U y) (V y) = _
  conv_lhs => rw [hyU, hyV]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c, s]
  ring

/-- The intrinsic covariant derivative, ordered as the two tensor slots and
then the differentiation direction. -/
def bilinearDerivativeTensor (x : M) (hA : BilinearEvaluationMDifferentiableAt A x) :
    TM x →L[ℝ] TM x →L[ℝ] (TM x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (bilinearDerivativeAux cov A · · x) x
    (tensorial_bilinearDerivativeAux₁ cov A hA)
    (tensorial_bilinearDerivativeAux₂ cov A hA)

/-- Evaluation of the bundled tensor using any differentiable extensions. -/
theorem bilinearDerivativeTensor_apply {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    {U V : ∀ y : M, TM y} (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x)
    (w : TM x) :
    bilinearDerivativeTensor cov A x hA (U x) (V x) w =
      bilinearDerivative cov A U V x w := by
  unfold bilinearDerivativeTensor
  rw [TensorialAt.mkHom₂_apply _ _ hU hV]
  rfl

/-- A canonical extension formula for arbitrary tangent vectors. -/
theorem bilinearDerivativeTensor_apply_eq_extend (x : M)
    (hA : BilinearEvaluationMDifferentiableAt A x) (u v w : TM x) :
    bilinearDerivativeTensor cov A x hA u v w =
      bilinearDerivative cov A (FiberBundle.extend E u) (FiberBundle.extend E v) x w := by
  unfold bilinearDerivativeTensor
  rw [TensorialAt.mkHom₂_apply_eq_extend]
  rfl

/-- The section formula depends only on the values of its differentiable
extensions at the point, not on their germs or their derivatives. -/
theorem bilinearDerivative_extension_independent {x : M}
    (hA : BilinearEvaluationMDifferentiableAt A x)
    {U U' V V' : ∀ y : M, TM y}
    (hU : MDiffAt (T% U) x) (hU' : MDiffAt (T% U') x)
    (hV : MDiffAt (T% V) x) (hV' : MDiffAt (T% V') x)
    (hUU' : U x = U' x) (hVV' : V x = V' x) (w : TM x) :
    bilinearDerivative cov A U V x w = bilinearDerivative cov A U' V' x w := by
  rw [← bilinearDerivativeTensor_apply cov A hA hU hV,
    ← bilinearDerivativeTensor_apply cov A hA hU' hV', hUU', hVV']

end SchurRigidity
