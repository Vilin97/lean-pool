/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GlobalEnergy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Scalar L2 norm of the intrinsic gradient

Scalar norms avoid introducing a space of measurable dependent tangent sections.
The measure and energy below are the constructed Riemannian ones.
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

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M] in
/-- The scalar intrinsic-gradient norm of a C1 function is continuous. -/
theorem continuous_norm_gradient {f : M → ℝ} (hf : CMDiff 1 f) :
    Continuous (fun x => ‖gradient (I := I) f x‖) := by
  have hi := Continuous.inner_bundle (F := E) (E := TangentSpace I)
    (contMDiff_gradient (I := I) 0 hf).continuous
    (contMDiff_gradient (I := I) 0 hf).continuous
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using hi.sqrt

/-- Compactness makes the scalar gradient norm square integrable. -/
theorem memLp_norm_gradient {f : M → ℝ} (hf : CMDiff 1 f) :
    MemLp (fun x => ‖gradient (I := I) f x‖) 2 (riemannianVolume (I := I)) :=
  (continuous_norm_gradient hf).memLp_of_hasCompactSupport isClosed_closure.isCompact

/-- The scalar L2 gradient norm squared is exactly the intrinsic energy. -/
theorem norm_toLp_gradient_sq {f : M → ℝ} (hf : CMDiff 1 f) :
    ‖(memLp_norm_gradient hf).toLp (fun x => ‖gradient (I := I) f x‖)‖ ^ 2 =
      dirichletForm (I := I) f f := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, dirichletForm_self]
  apply integral_congr_ae
  filter_upwards [(memLp_norm_gradient hf).coeFn_toLp] with x hx
  simp [hx]

/-- The scalar L2 gradient norm is the square root of intrinsic energy. -/
theorem norm_toLp_gradient {f : M → ℝ} (hf : CMDiff 1 f) :
    ‖(memLp_norm_gradient hf).toLp (fun x => ‖gradient (I := I) f x‖)‖ =
      Real.sqrt (dirichletForm (I := I) f f) := by
  rw [← norm_toLp_gradient_sq hf, Real.sqrt_sq_eq_abs, abs_norm]

end AlmostSchur
