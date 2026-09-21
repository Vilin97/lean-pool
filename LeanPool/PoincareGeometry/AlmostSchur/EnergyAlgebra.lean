/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GradientL2
public import LeanPool.PoincareGeometry.AlmostSchur.MeanZeroEnergy

/-! # Algebra of the intrinsic Dirichlet form

These identities provide the rescaling and bilinearity needed for normalized
Poincaré counterexamples and for the mean-zero energy inner product.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] in
/-- Addition commutes with the intrinsic gradient of C1 functions. -/
theorem gradient_add_of_contMDiff (f g : M → ℝ) (hf : CMDiff 1 f) (hg : CMDiff 1 g)
    (x : M) : gradient (I := I) (fun y => f y + g y) x =
      gradient (I := I) f x + gradient (I := I) g x := by
  unfold gradient
  rw [mvfderiv_fun_add ((hf x).mdifferentiableAt one_ne_zero)
    ((hg x).mdifferentiableAt one_ne_zero), map_add]

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] in
/-- Constant scalar multiplication commutes with the intrinsic gradient. -/
theorem gradient_const_mul_of_contMDiff (a : ℝ) (f : M → ℝ) (hf : CMDiff 1 f)
    (x : M) : gradient (I := I) (fun y => a * f y) x =
      a • gradient (I := I) f x := by
  unfold gradient
  rw [mvfderiv_fun_mul mdifferentiableAt_const ((hf x).mdifferentiableAt one_ne_zero)]
  simp only [mvfderiv_const, smul_zero, add_zero, map_smul]

/-- The actual Dirichlet form is additive in its first argument. -/
theorem dirichletForm_add_left_of_contMDiff (f g h : M → ℝ)
    (hf : CMDiff 1 f) (hg : CMDiff 1 g) (hh : CMDiff 1 h) :
    dirichletForm (I := I) (fun x => f x + g x) h =
      dirichletForm (I := I) f h + dirichletForm (I := I) g h := by
  simp only [dirichletForm, gradient_add_of_contMDiff f g hf hg, inner_add_left]
  exact integral_add (integrable_inner_gradients f h hf hh)
    (integrable_inner_gradients g h hg hh)

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- The actual Dirichlet form is homogeneous in its first argument. -/
theorem dirichletForm_const_mul_left_of_contMDiff (a : ℝ) (f g : M → ℝ)
    (hf : CMDiff 1 f) :
    dirichletForm (I := I) (fun x => a * f x) g = a * dirichletForm (I := I) f g := by
  simp only [dirichletForm, gradient_const_mul_of_contMDiff a f hf, real_inner_smul_left]
  exact integral_const_mul _ _

/-- Rescaling a C1 function multiplies its intrinsic energy by the scalar squared. -/
theorem dirichletForm_const_mul_self_of_contMDiff (a : ℝ) (f : M → ℝ)
    (hf : CMDiff 1 f) :
    dirichletForm (I := I) (fun x => a * f x) (fun x => a * f x) =
      a ^ 2 * dirichletForm (I := I) f f := by
  rw [dirichletForm_const_mul_left_of_contMDiff a f _ hf, dirichletForm_symm f,
    dirichletForm_const_mul_left_of_contMDiff a f f hf]
  ring

/-- The square-root energy is absolutely homogeneous. -/
theorem sqrt_dirichletForm_const_mul_self (a : ℝ) (f : M → ℝ)
    (hf : CMDiff 1 f) :
    Real.sqrt (dirichletForm (I := I) (fun x => a * f x) (fun x => a * f x)) =
      |a| * Real.sqrt (dirichletForm (I := I) f f) := by
  rw [dirichletForm_const_mul_self_of_contMDiff a f hf,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

end AlmostSchur
