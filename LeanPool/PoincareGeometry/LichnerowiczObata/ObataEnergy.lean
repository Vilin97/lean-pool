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

public import LeanPool.PoincareGeometry.LichnerowiczObata.BochnerBound

/-! # The conserved energy of an Obata function

This is a geometric consequence of the actual covariant Hessian equation,
not a replacement for the global sphere-isometry theorem.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

local instance : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

/-- Squared gradient plus the potential term, written using the actual metric. -/
def obataEnergy (K : ℝ) (f : M → ℝ) (x : M) : ℝ :=
  inner ℝ (gradient (I := I) f x) (gradient (I := I) f x) + K * (f x * f x)

theorem obataEnergy_eq (K : ℝ) (f : M → ℝ) (x : M) :
    obataEnergy (I := I) K f x = ‖gradient (I := I) f x‖ ^ 2 + K * f x ^ 2 := by
  simp only [obataEnergy, real_inner_self_eq_norm_sq, pow_two]

theorem contMDiff_obataEnergy {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (K : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (obataEnergy (I := I) K f) := by
  have hg := contMDiff_gradient (I := I) 1 hf
  have hf1 := hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hi : ContMDiff I 𝓘(ℝ, ℝ) 1
      (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y)) := by
    intro x
    exact @ContMDiffAt.inner_bundle E _ _ H _ I (1 : ℕ∞ω) M _ _ E _ _ TM _
      (fun y => inferInstance) (fun y => inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y => y) (gradient (I := I) f) (gradient (I := I) f) x (hg x) (hg x)
  exact hi.add (contMDiff_const.mul (hf1.mul hf1))

/-- Differentiating the actual gradient norm uses metric compatibility. -/
theorem differential_gradient_norm_sq_at {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (v : TM x) :
    mvfderiv I (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y)) x v =
      2 * hessian LC f x v (gradient (I := I) f x) := by
  let e := trivializationAt E TM x
  let X := fun y => e.symmL ℝ y (e.continuousLinearMapAt ℝ x v)
  have hX : X x = v := e.symmL_continuousLinearMapAt (mem_chart_source H x) v
  have hg := mdifferentiableAt_gradient hf
  have hm := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
    leviCivitaConnection_metricCompatible X hg hg
  change mvfderiv I (fun y => inner ℝ (gradient (I := I) f y)
    (gradient (I := I) f y)) x (X x) =
      inner ℝ (LC (gradient (I := I) f) x (X x)) (gradient (I := I) f x) +
      inner ℝ (gradient (I := I) f x) (LC (gradient (I := I) f) x (X x)) at hm
  rw [hX] at hm
  change _ = 2 * inner ℝ (LC (gradient (I := I) f) x v) (gradient (I := I) f x)
  rw [hm]
  have hs := real_inner_comm (gradient (I := I) f x) (LC (gradient (I := I) f) x v)
  linarith

theorem differential_gradient_norm_sq {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) (v : TM x) :
    mvfderiv I (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y)) x v =
      2 * hessian LC f x v (gradient (I := I) f x) :=
  differential_gradient_norm_sq_at (hf x) v

/-- Obata's Hessian equation forces the differential of the conserved energy to vanish. -/
theorem differential_obataEnergy_eq_zero {K : ℝ} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∀ x, mvfderiv I (obataEnergy (I := I) K f) x = 0 := by
  intro x
  have hf' := (hf x).mdifferentiableAt (by norm_num)
  have hg := (contMDiff_gradient (I := I) 1 hf x).mdifferentiableAt (by norm_num)
  ext v
  change mvfderiv I (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y) +
    K * (f y * f y)) x v = 0
  have hi : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => inner ℝ (gradient (I := I) f y) (gradient (I := I) f y)) x :=
    @MDifferentiableAt.inner_bundle E _ _ H _ I M _ _ E _ _ TM _
      (fun y => inferInstance) (fun y => inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y => y) (gradient (I := I) f) (gradient (I := I) f) x hg hg
  have hK : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => K) x := mdifferentiableAt_const
  have ha := mvfderiv_fun_add hi (hK.mul (hf'.mul hf'))
  have hb := mvfderiv_fun_mul hK (hf'.mul hf')
  simp only [Pi.mul_def] at ha hb
  rw [ha, hb, mvfderiv_fun_mul hf' hf',
    mvfderiv_const]
  simp only [add_apply, smul_apply, zero_apply, mul_zero, add_zero, smul_eq_mul]
  rw [differential_gradient_norm_sq hf, hH]
  have hi : inner ℝ v (gradient (I := I) f x) = mvfderiv I f x v := by
    rw [real_inner_comm]
    exact inner_gradient f x v
  rw [hi]
  ring

/-- The energy is constant on the connected manifold. -/
theorem obataEnergy_constant [PreconnectedSpace M] {K : ℝ} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w)
    (x y : M) :
    ‖gradient (I := I) f x‖ ^ 2 + K * f x ^ 2 =
      ‖gradient (I := I) f y‖ ^ 2 + K * f y ^ 2 := by
  simpa only [obataEnergy_eq] using
    eq_of_differential_eq_zero (obataEnergy (I := I) K f) (contMDiff_obataEnergy hf K)
      (differential_obataEnergy_eq_zero hf hH) x y

end LichnerowiczObata
