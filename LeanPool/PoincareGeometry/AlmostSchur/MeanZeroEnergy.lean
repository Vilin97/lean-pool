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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyKernel

/-!
# Mean-zero Dirichlet energy and uniqueness

The measure is the constructed `riemannianVolume`, the energy is the actual
`dirichletForm`, and the Laplacian is the trace of the covariant derivative of
the intrinsic gradient. Zero energy gives constancy by the proved differential
kernel theorem. Mean-zero normalization removes the constant because the total
Riemannian volume is positive and finite.

Strict positivity here is qualitative: no Poincaré inequality, coercivity bound,
or elliptic existence theorem is assumed or asserted.
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

local instance meanZeroEnergyContinuousMetric : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance meanZeroEnergyFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

section Connected

variable [PreconnectedSpace M]

/-- Zero actual Dirichlet energy forces equality of all values of a C¹ function. -/
theorem eq_of_dirichletForm_self_eq_zero (f : M → ℝ) (hf : CMDiff 1 f)
    (henergy : dirichletForm (I := I) f f = 0) (x y : M) : f x = f y :=
  eq_of_differential_eq_zero f hf
    ((dirichletForm_self_eq_zero_iff_differential f hf).mp henergy) x y

/-- The kernel of the actual Dirichlet form consists exactly of constant C¹ functions. -/
theorem dirichletForm_self_eq_zero_iff_constant (f : M → ℝ) (hf : CMDiff 1 f) :
    dirichletForm (I := I) f f = 0 ↔ ∃ c : ℝ, ∀ x, f x = c := by
  constructor
  · intro henergy
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
    exact ⟨f x₀, fun x => eq_of_dirichletForm_self_eq_zero f hf henergy x x₀⟩
  · rintro ⟨c, hc⟩
    have hconst : f = fun _ => c := funext hc
    subst f
    simp [dirichletForm, gradient, mvfderiv_const]

/-- A mean-zero C¹ function with zero energy vanishes identically. The proof uses
positivity and finiteness of the actual total Riemannian volume. -/
theorem eq_zero_of_mean_zero_of_dirichletForm_self_eq_zero
    (f : M → ℝ) (hf : CMDiff 1 f)
    (hmean : ∫ x, f x ∂riemannianVolume (I := I) = 0)
    (henergy : dirichletForm (I := I) f f = 0) : f = 0 := by
  obtain ⟨c, hc⟩ := (dirichletForm_self_eq_zero_iff_constant f hf).mp henergy
  have hvol := riemannianVolume_finite_positive (I := I) (M := M)
  have hv : 0 < (riemannianVolume (I := I) (M := M) univ).toReal :=
    ENNReal.toReal_pos hvol.1.ne' (ne_of_lt hvol.2)
  have hprod : (riemannianVolume (I := I) (M := M) univ).toReal * c = 0 := by
    simpa only [hc, integral_const, smul_eq_mul, Measure.real] using hmean
  have hc0 : c = 0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hv)
  funext x
  simpa only [Pi.zero_apply, hc0] using hc x

/-- Every nonzero mean-zero C¹ function has strictly positive Dirichlet energy.
This is not a uniform lower bound in any function norm. -/
theorem dirichletForm_self_pos_of_mean_zero
    (f : M → ℝ) (hf : CMDiff 1 f)
    (hmean : ∫ x, f x ∂riemannianVolume (I := I) = 0) (hne : f ≠ 0) :
    0 < dirichletForm (I := I) f f := by
  apply lt_of_le_of_ne (dirichletForm_self_nonneg f)
  intro hzero
  exact hne (eq_zero_of_mean_zero_of_dirichletForm_self_eq_zero f hf hmean hzero.symm)

end Connected

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E TM I] [IsContMDiffRiemannianBundle I 1 E TM]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] in
/-- Subtraction commutes with the actual Riesz gradient of C¹ functions. -/
theorem gradient_sub_of_contMDiff (f g : M → ℝ) (hf : CMDiff 1 f) (hg : CMDiff 1 g)
    (x : M) : gradient (I := I) (fun y => f y - g y) x =
      gradient (I := I) f x - gradient (I := I) g x := by
  unfold gradient
  rw [mvfderiv_fun_sub ((hf x).mdifferentiableAt one_ne_zero)
    ((hg x).mdifferentiableAt one_ne_zero), map_sub]

/-- Subtracting C¹ functions in the second argument subtracts their Dirichlet pairings. -/
theorem dirichletForm_sub_right_of_contMDiff (h f g : M → ℝ)
    (hh : CMDiff 1 h) (hf : CMDiff 1 f) (hg : CMDiff 1 g) :
    dirichletForm (I := I) h (fun x => f x - g x) =
      dirichletForm (I := I) h f - dirichletForm (I := I) h g := by
  simp only [dirichletForm, gradient_sub_of_contMDiff f g hf hg, inner_sub_right]
  exact integral_sub (integrable_inner_gradients h f hh hf)
    (integrable_inner_gradients h g hh hg)

/-- Equal actual Laplacians force the difference of two C² functions to have
zero Dirichlet energy, by the global Green identity. -/
theorem dirichletForm_sub_self_eq_zero_of_laplacian_eq
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (f g : M → ℝ) (hf : CMDiff 2 f) (hg : CMDiff 2 g)
    (hlap : ∀ x, laplacian cov f x = laplacian cov g x) :
    dirichletForm (I := I) (fun x => f x - g x) (fun x => f x - g x) = 0 := by
  have hf1 : CMDiff 1 f := hf.of_le (by norm_num)
  have hg1 : CMDiff 1 g := hg.of_le (by norm_num)
  have hd : CMDiff 1 (fun x => f x - g x) := hf1.sub hg1
  have hfg :
      (∫ x, (f x - g x) * laplacian cov f x ∂riemannianVolume (I := I)) =
      ∫ x, (f x - g x) * laplacian cov g x ∂riemannianVolume (I := I) := by
    simp_rw [hlap]
  rw [integral_mul_laplacian cov hm ht _ f hd hf,
    integral_mul_laplacian cov hm ht _ g hd hg] at hfg
  rw [dirichletForm_sub_right_of_contMDiff _ f g hd hf1 hg1]
  linarith

/-- C² solutions with equal actual Laplacian differ by a global constant. -/
theorem exists_sub_eq_const_of_laplacian_eq [PreconnectedSpace M]
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (f g : M → ℝ) (hf : CMDiff 2 f) (hg : CMDiff 2 g)
    (hlap : ∀ x, laplacian cov f x = laplacian cov g x) :
    ∃ c : ℝ, ∀ x, f x - g x = c := by
  apply (dirichletForm_self_eq_zero_iff_constant _
    ((hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).sub
      (hg.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)))).mp
  exact dirichletForm_sub_self_eq_zero_of_laplacian_eq cov hm ht f g hf hg hlap

/-- Mean-zero C² solutions with equal actual Laplacian are identical. -/
theorem eq_of_laplacian_eq_of_mean_zero [PreconnectedSpace M]
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (f g : M → ℝ) (hf : CMDiff 2 f) (hg : CMDiff 2 g)
    (hlap : ∀ x, laplacian cov f x = laplacian cov g x)
    (hmeanf : ∫ x, f x ∂riemannianVolume (I := I) = 0)
    (hmeang : ∫ x, g x ∂riemannianVolume (I := I) = 0) : f = g := by
  have hmean : ∫ x, (f x - g x) ∂riemannianVolume (I := I) = 0 := by
    rw [integral_sub
      (hf.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact)
      (hg.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact),
      hmeanf, hmeang, sub_self]
  have hz := eq_zero_of_mean_zero_of_dirichletForm_self_eq_zero
    (fun x => f x - g x)
    ((hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).sub
      (hg.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))) hmean
    (dirichletForm_sub_self_eq_zero_of_laplacian_eq cov hm ht f g hf hg hlap)
  funext x
  exact sub_eq_zero.mp (congrFun hz x)

end AlmostSchur
