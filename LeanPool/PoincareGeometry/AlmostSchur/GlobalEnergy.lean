/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GlobalGreen
public import LeanPool.PoincareGeometry.AlmostSchur.GradientRegularity
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Global gradient energy and the Laplace–Beltrami operator

These identities use the intrinsic gradient, the trace of its covariant
derivative and the constructed Riemannian volume. All integration by parts
is inherited from the proved global Green theorem.
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

local notation "TM" => (TangentSpace I : M → Type _)

local instance globalEnergyMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance globalEnergyMetricOne : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Global Dirichlet form for the actual Riemannian gradient. -/
def dirichletForm (f g : M → ℝ) : ℝ :=
  ∫ x, inner ℝ (gradient (I := I) f x) (gradient (I := I) g x) ∂riemannianVolume (I := I)

/-- Symmetry of the global gradient pairing. -/
theorem dirichletForm_symm (f g : M → ℝ) :
    dirichletForm (I := I) f g = dirichletForm (I := I) g f := by
  unfold dirichletForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => real_inner_comm _ _

/-- The diagonal Dirichlet form is the integral of the gradient's squared norm. -/
theorem dirichletForm_self (f : M → ℝ) :
    dirichletForm (I := I) f f = ∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂riemannianVolume (I := I) := by
  simp only [dirichletForm, real_inner_self_eq_norm_sq]

/-- Nonnegativity of gradient energy. -/
theorem dirichletForm_self_nonneg (f : M → ℝ) : 0 ≤ dirichletForm (I := I) f f := by
  rw [dirichletForm_self]
  exact integral_nonneg fun _ => sq_nonneg _

/-- A C1 pair has an integrable intrinsic gradient pairing on the compact manifold. -/
theorem integrable_inner_gradients (f g : M → ℝ) (hf : CMDiff 1 f) (hg : CMDiff 1 g) :
    Integrable (fun x => inner ℝ (gradient (I := I) f x) (gradient (I := I) g x))
      (riemannianVolume (I := I)) := by
  have hfg : Continuous (fun x => inner ℝ (gradient (I := I) f x) (gradient (I := I) g x)) :=
    Continuous.inner_bundle (F := E) (E := TM)
      (contMDiff_gradient (I := I) 0 hf).continuous (contMDiff_gradient (I := I) 0 hg).continuous
  exact hfg.integrable_of_hasCompactSupport isClosed_closure.isCompact

/-- The Laplace–Beltrami operator is the negative adjoint of the gradient. -/
theorem integral_mul_laplacian
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f g : M → ℝ) (hf : CMDiff 1 f) (hg : CMDiff 2 g) :
    ∫ x, f x * laplacian cov g x ∂riemannianVolume (I := I) = -dirichletForm (I := I) f g := by
  have h := integral_mul_divergence cov hm ht f (gradient (I := I) g) hf
    (contMDiff_gradient (I := I) 1 hg)
  simpa only [divergence_gradient, ← inner_gradient, dirichletForm] using h

/-- The actual Laplacian of a C2 function is continuous. -/
theorem continuous_laplacian
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) : Continuous (laplacian cov f) :=
  continuous_divergence cov hm ht (gradient (I := I) f) (contMDiff_gradient (I := I) 1 hf)

/-- Compactness makes the actual C2 Laplacian integrable. -/
theorem integrable_laplacian
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) : Integrable (laplacian cov f) (riemannianVolume (I := I)) :=
  (continuous_laplacian cov hm ht f hf).integrable_of_hasCompactSupport isClosed_closure.isCompact

/-- The Laplacian has zero integral on the closed manifold. -/
theorem integral_laplacian_eq_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) :
    ∫ x, laplacian cov f x ∂riemannianVolume (I := I) = 0 := by
  have h := integral_mul_divergence cov hm ht (fun _ => (1 : ℝ)) (gradient (I := I) f)
    contMDiff_const (contMDiff_gradient (I := I) 1 hf)
  simpa only [one_mul, divergence_gradient, mvfderiv_const, ContinuousLinearMap.zero_apply,
    integral_zero, neg_zero] using h

/-- The global energy identity with the `div grad` sign convention. -/
theorem integral_mul_laplacian_self
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) :
    ∫ x, f x * laplacian cov f x ∂riemannianVolume (I := I) =
      -∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂riemannianVolume (I := I) := by
  rw [integral_mul_laplacian cov hm ht f f (hf.of_le (by norm_num)) hf, dirichletForm_self]

/-- Zero Dirichlet energy forces the actual continuous gradient to vanish
everywhere, not merely almost everywhere. -/
theorem dirichletForm_self_eq_zero_iff (f : M → ℝ) (hf : CMDiff 1 f) :
    dirichletForm (I := I) f f = 0 ↔ ∀ x, gradient (I := I) f x = 0 := by
  letI : (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
    ⟨fun _ hs hne => ne_of_gt (riemannianVolume_open_pos (I := I) hs hne)⟩
  have hcont : Continuous (fun x => inner ℝ (gradient (I := I) f x)
      (gradient (I := I) f x)) :=
    Continuous.inner_bundle (F := E) (E := TM)
      (contMDiff_gradient (I := I) 0 hf).continuous
      (contMDiff_gradient (I := I) 0 hf).continuous
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => real_inner_self_nonneg)
      (integrable_inner_gradients f f hf hf)).mp h
    have heq := MeasureTheory.Measure.eq_of_ae_eq hae hcont continuous_const
    intro x
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (congrFun heq x)
  · intro h
    simp [dirichletForm, h]

/-- Equivalent formulation of the energy kernel in terms of the intrinsic
differential. This does not assert a uniform Poincaré estimate. -/
theorem dirichletForm_self_eq_zero_iff_differential (f : M → ℝ) (hf : CMDiff 1 f) :
    dirichletForm (I := I) f f = 0 ↔ ∀ x, mvfderiv I f x = 0 := by
  rw [dirichletForm_self_eq_zero_iff f hf]
  exact forall_congr' fun x => gradient_eq_zero_iff f x

end AlmostSchur
