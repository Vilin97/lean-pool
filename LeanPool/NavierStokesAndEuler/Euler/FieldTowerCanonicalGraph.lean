/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderGraphTrace
import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization

/-! Canonical graph restrictions need no additional representative or
regularity assumptions beyond the actual all-order tower. -/

section

/-! Actual spatial L² restrictions of smooth cylinder fields. The bound is
uniform over every continuous phase graph, including arbitrarily high
oscillation frequencies. -/

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLpBochnerRealization
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]

private theorem norm_sq_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Lp Vector3 2 μ) (f : X → Vector3)
    (hu : (u : X → Vector3) =ᵐ[μ] f) :
    ‖u‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (hu.mono (fun _ hx =>
    congrArg (fun z : Vector3 => ‖z‖^2) hx))

variable (f : LiftDomain P → Vector3)
  (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
  (u v : LiftL2 P)
  (hu : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
  (hv : (v : LiftDomain P → Vector3) =ᵐ[liftMeasure P] fieldDerivative P (0, 1) f)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

include hf hu hv hθ in
theorem graph_memLp_of_representatives :
    MemLp (fun x => f (x,θ x)) 2 volume :=
  (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).1

/-- The actual L² class of the field on the prescribed phase graph. -/
def graphRealization : Lp Vector3 2 (volume : Measure Vector3) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).toLp (fun x => f (x,θ x))

theorem graphRealization_ae :
    (graphRealization P f hf u v hu hv θ hθ : Vector3 → Vector3) =ᵐ[volume]
      fun x => f (x,θ x) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).coeFn_toLp

include hf hu hv hθ in
/-- Any L² representative of this same graph satisfies the genuine trace bound. -/
theorem graph_norm_sq_le (w : Lp Vector3 2 (volume : Measure Vector3))
    (hw : (w : Vector3 → Vector3) =ᵐ[volume] fun x => f (x, θ x)) :
    ‖w‖^2 ≤ (2/P)*‖u‖^2+(2*P)*‖v‖^2 := by
  rw [norm_sq_of_ae volume w _ hw,
    norm_sq_of_ae (liftMeasure P) u f hu,
    norm_sq_of_ae (liftMeasure P) v _ hv]
  exact (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).2

theorem graphRealization_norm_sq_le :
    ‖graphRealization P f hf u v hu hv θ hθ‖^2 ≤
      (2/P)*‖u‖^2+(2*P)*‖v‖^2 :=
  graph_norm_sq_le P f hf u v hu hv θ hθ _
    (graphRealization_ae P f hf u v hu hv θ hθ)

end EulerCylinderGraphTrace

end
end

end

section

/-! Every smooth representative of a genuine all-order field tower has
continuous spatial L² restrictions, including all cylinder derivative words.
The graph estimate loses one angular derivative, with no frequency factor. -/

section

/-! Restriction to a fixed continuous phase graph preserves time continuity
in actual spatial L². The proof uses the uniform trace estimate for differences. -/

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K]
  (u v : C(K, LiftL2 P)) (f : K → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hu : ∀ t, (u t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)
  (hv : ∀ t, (v t : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
    fieldDerivative P (0, 1) (f t))
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

/-- Graph path value, given by `graphRealization P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ`. -/
def graphPathValue (t : K) : Lp Vector3 2 (volume : Measure Vector3) :=
  graphRealization P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ

theorem graphPathValue_ae (t : K) :
    (graphPathValue P u v f hf hu hv θ hθ t : Vector3 → Vector3) =ᵐ[volume]
      fun x => f t (x,θ x) :=
  graphRealization_ae P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ

theorem graphPathValue_sub_norm_sq_le (t s : K) :
    ‖graphPathValue P u v f hf hu hv θ hθ t -
      graphPathValue P u v f hf hu hv θ hθ s‖^2 ≤
      (2/P)*‖u t-u s‖^2+(2*P)*‖v t-v s‖^2 := by
  refine graph_norm_sq_le P (fun x => f t x-f s x)
    (fun x => (hf t x).sub (hf s x)) (u t-u s) (v t-v s) ?_ ?_ θ hθ _ ?_
  · filter_upwards [Lp.coeFn_sub (u t) (u s),hu t,hu s] with x hs ht hu
    exact hs.trans (congrArg₂ (·-·) ht hu)
  · filter_upwards [Lp.coeFn_sub (v t) (v s),hv t,hv s] with x hs ht hu
    exact hs.trans ((congrArg₂ (·-·) ht hu).trans
      (EulerMollifierUniform.fieldDerivative_sub P (0,1) (f t) (f s) (hf t) (hf s) x).symm)
  · filter_upwards [Lp.coeFn_sub
      (graphPathValue P u v f hf hu hv θ hθ t)
      (graphPathValue P u v f hf hu hv θ hθ s),
      graphPathValue_ae P u v f hf hu hv θ hθ t,
      graphPathValue_ae P u v f hf hu hv θ hθ s] with x hs ht hu
    exact hs.trans (congrArg₂ (·-·) ht hu)

theorem graphPathValue_continuous :
    Continuous (graphPathValue P u v f hf hu hv θ hθ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun s => (2/P)*‖u s-u t‖^2+(2*P)*‖v s-v t‖^2)
      (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero,add_zero] using
      ((((u.continuous.tendsto t).sub_const (u t)).norm.pow 2).const_mul (2/P)).add
        ((((v.continuous.tendsto t).sub_const (v t)).norm.pow 2).const_mul (2*P))
  have hsq := squeeze_zero
    (fun s => sq_nonneg ‖graphPathValue P u v f hf hu hv θ hθ s -
      graphPathValue P u v f hf hu hv θ hθ t‖)
    (fun s => graphPathValue_sub_norm_sq_le P u v f hf hu hv θ hθ s t) hlim
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hr

/-- The continuous spatial L² path is constructed from the actual cylinder
path and its actual angular derivative. -/
def graphPath : C(K,Lp Vector3 2 (volume : Measure Vector3)) :=
  ⟨graphPathValue P u v f hf hu hv θ hθ,
    graphPathValue_continuous P u v f hf hu hv θ hθ⟩

end EulerCylinderGraphTrace

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerStrongSmoothJet EulerMetricTransport
  EulerTransportDerivatives EulerCylinderGraphTrace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)

/-- The prescribed derivative coordinate is a genuine continuous L² path. -/
def derivativeWordPath (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s) :
    C(Icc (0 : ℝ) T,LiftL2 P) :=
  (wordOperator P (⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩ : SobolevWord s)).compLeftContinuous
    ℝ (Icc (0 : ℝ) T) (A.realization s)

variable (f : Icc (0 : ℝ) T → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hrep : ∀ t, (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)

include hf hrep in
theorem derivativeWordPath_ae (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s)
    (t : Icc (0 : ℝ) T) :
    (A.derivativeWordPath s n w hn t : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      iteratedFieldDerivative P w (f t) := by
  have h := jet_word_ae P hn (value P (A.realization s t))
    (toJet P (A.realization s t)) w (f t)
    (by simpa only [A.value_eq] using hrep t) (hf t)
  rw [toJet_word P (A.realization s t) hn w] at h
  exact h

theorem derivativeWordPath_norm_le (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s)
    (t : Icc (0 : ℝ) T) :
    ‖A.derivativeWordPath s n w hn t‖ ≤ ‖A.realization s t‖ :=
  word_norm_le P (A.realization s t) (⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩ : SobolevWord s)

variable (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

include hf hrep in
/-- The actual angular derivative used by the graph trace is another
coordinate of the same all-order tower. -/
theorem graphWord_angular_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t :
      LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0,1) (iteratedFieldDerivative P w (f t)) := by
  simpa only [iteratedFieldDerivative_succ,Fin.cons_zero,Fin.tail_cons,
    standardDirection_zero] using
    A.derivativeWordPath_ae f hf hrep (n+1) (n+1) (Fin.cons 0 w) le_rfl t

/-- Graph restriction of an arbitrary actual cylinder derivative word,
constructed directly as a continuous spatial L² path. -/
def graphWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  EulerCylinderGraphTrace.graphPath P
    (A.derivativeWordPath (n+1) n w (by omega))
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl)
    (fun t => iteratedFieldDerivative P w (f t))
    (fun t => iteratedFieldDerivative_smooth P w (f t) (hf t))
    (A.derivativeWordPath_ae f hf hrep (n+1) n w (by omega))
    (A.graphWord_angular_ae f hf hrep n w) θ hθ

theorem graphWordPath_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.graphWordPath f hf hrep θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (f t) (x,θ x) :=
  graphPathValue_ae P _ _ _ _ _ _ θ hθ t

theorem graphWordPath_norm_sq_le (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    ‖A.graphWordPath f hf hrep θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization (n+1) t‖^2 := by
  have h := graph_norm_sq_le P
    (iteratedFieldDerivative P w (f t))
    (iteratedFieldDerivative_smooth P w (f t) (hf t))
    (A.derivativeWordPath (n+1) n w (by omega) t)
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t)
    (A.derivativeWordPath_ae f hf hrep (n+1) n w (by omega) t)
    (A.graphWord_angular_ae f hf hrep n w t) θ hθ _
    (A.graphWordPath_ae f hf hrep θ hθ n w t)
  have h0 := pow_le_pow_left₀ (norm_nonneg _)
    (A.derivativeWordPath_norm_le (n+1) n w (by omega) t) 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _)
    (A.derivativeWordPath_norm_le (n+1) (n+1) (Fin.cons 0 w) le_rfl t) 2
  have hP : 0 < P := Fact.out
  calc
    _ ≤ _ := h
    _ ≤ (2/P)*‖A.realization (n+1) t‖^2+(2*P)*‖A.realization (n+1) t‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
        (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ = _ := by ring

end EulerAllOrderCorrectionData.FieldTower

end
end

end

section

/-! A genuine cylinder L² time derivative, together with its genuine angular
derivative, remains a genuine spatial L² derivative on every fixed phase graph. -/

section

/-! The graph trace estimate applies to the actual affine remainder in a
derivative quotient, with the same constants for all phase frequencies. -/

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff

theorem affine_representative_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Fin 3 → Lp Vector3 2 μ) (f : Fin 3 → X → Vector3)
    (hu : ∀ i, (u i : X → Vector3) =ᵐ[μ] f i) (a : ℝ) :
    ((a • (u 1-u 0)-u 2 : Lp Vector3 2 μ) : X → Vector3) =ᵐ[μ]
      fun x => a • (f 1 x-f 0 x)-f 2 x := by
  filter_upwards [Lp.coeFn_sub (a • (u 1-u 0)) (u 2),
    Lp.coeFn_smul a (u 1-u 0),Lp.coeFn_sub (u 1) (u 0),hu 0,hu 1,hu 2]
    with x h2 hs h1 h0 h1' h2'
  simp only [Pi.sub_apply,Pi.smul_apply,h2,hs,h1,h0,h1',h2']

variable (P : ℝ) [Fact (0 < P)]

omit [Fact (0 < P)] in
theorem affine_fieldDerivative (f : Fin 3 → LiftDomain P → Vector3)
    (hf : ∀ i x, ContDiff ℝ ∞ (localFieldLift P (f i) x))
    (a : ℝ) (z : LiftDomain P) :
    fieldDerivative P (0,1) (fun x => a • (f 1 x-f 0 x)-f 2 x) z =
      a • (fieldDerivative P (0,1) (f 1) z-fieldDerivative P (0,1) (f 0) z) -
        fieldDerivative P (0,1) (f 2) z := by
  have h := (((((hf 1 z).differentiable (by simp)) 0).hasFDerivAt.sub
    ((((hf 0 z).differentiable (by simp)) 0).hasFDerivAt)).const_smul a).sub
    ((((hf 2 z).differentiable (by simp)) 0).hasFDerivAt)
  exact congrArg (fun L : LiftTangent →L[ℝ] Vector3 => L (0,1)) h.fderiv

theorem graph_affine_norm_sq_le
    (f : Fin 3 → LiftDomain P → Vector3)
    (hf : ∀ i x, ContDiff ℝ ∞ (localFieldLift P (f i) x))
    (u v : Fin 3 → LiftL2 P)
    (hu : ∀ i, (u i : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f i)
    (hv : ∀ i, (v i : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0, 1) (f i))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ)
    (w : Fin 3 → Lp Vector3 2 (volume : Measure Vector3))
    (hw : ∀ i, (w i : Vector3 → Vector3) =ᵐ[volume] fun x => f i (x, θ x))
    (a : ℝ) :
    ‖a • (w 1-w 0)-w 2‖^2 ≤
      (2/P)*‖a • (u 1-u 0)-u 2‖^2+(2*P)*‖a • (v 1-v 0)-v 2‖^2 := by
  refine graph_norm_sq_le P (fun x => a • (f 1 x-f 0 x)-f 2 x)
    (fun x => (((hf 1 x).sub (hf 0 x)).const_smul a).sub (hf 2 x))
    (a • (u 1-u 0)-u 2) (a • (v 1-v 0)-v 2)
    (affine_representative_ae (liftMeasure P) u f hu a) ?_ θ hθ _
    (affine_representative_ae volume w (fun i x => f i (x,θ x)) hw a)
  filter_upwards [affine_representative_ae (liftMeasure P) v
    (fun i => fieldDerivative P (0,1) (f i)) hv a] with x hx
  exact hx.trans (affine_fieldDerivative P f hf a x).symm

end EulerCylinderGraphTrace

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]

theorem graph_hasDerivWithinAt
    (u v : ℝ → LiftL2 P) (f : ℝ → LiftDomain P → Vector3)
    (hf : ∀ r x, ContDiff ℝ ∞ (localFieldLift P (f r) x))
    (hu : ∀ r, (u r : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f r)
    (hv : ∀ r, (v r : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0, 1) (f r))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ)
    (w : ℝ → Lp Vector3 2 (volume : Measure Vector3))
    (hw : ∀ r, (w r : Vector3 → Vector3) =ᵐ[volume] fun x => f r (x, θ x))
    (g : LiftDomain P → Vector3) (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift P g x))
    (u' v' : LiftL2 P)
    (hu' : (u' : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g)
    (hv' : (v' : LiftDomain P → Vector3) =ᵐ[liftMeasure P] fieldDerivative P (0, 1) g)
    (w' : Lp Vector3 2 (volume : Measure Vector3))
    (hw' : (w' : Vector3 → Vector3) =ᵐ[volume] fun x => g (x, θ x))
    (s : Set ℝ) (t : ℝ)
    (hdu : HasDerivWithinAt u u' s t) (hdv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt w w' s t := by
  have hb (r : ℝ) : ‖slope w t r-w'‖^2 ≤
      (2/P)*‖slope u t r-u'‖^2+(2*P)*‖slope v t r-v'‖^2 := by
    simpa only [slope_def_module,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,
      Matrix.cons_val_succ] using graph_affine_norm_sq_le P ![f t,f r,g]
      (by
        intro i x
        fin_cases i
        · exact hf t x
        · exact hf r x
        · exact hg x)
      ![u t,u r,u'] ![v t,v r,v']
      (by
        intro i
        fin_cases i
        · exact hu t
        · exact hu r
        · exact hu')
      (by
        intro i
        fin_cases i
        · exact hv t
        · exact hv r
        · exact hv') θ hθ
      ![w t,w r,w']
      (by
        intro i
        fin_cases i
        · exact hw t
        · exact hw r
        · exact hw') (r-t)⁻¹
  have huLim := (hasDerivWithinAt_iff_tendsto_slope.mp hdu).sub_const u'
  have hvLim := (hasDerivWithinAt_iff_tendsto_slope.mp hdv).sub_const v'
  have hlim : Tendsto (fun r => (2/P)*‖slope u t r-u'‖^2+(2*P)*‖slope v t r-v'‖^2)
      (𝓝[s \ {t}] t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero,add_zero] using
      ((huLim.norm.pow 2).const_mul (2/P)).add ((hvLim.norm.pow 2).const_mul (2*P))
  have hsq := squeeze_zero (fun r => sq_nonneg ‖slope w t r-w'‖) hb hlim
  rw [hasDerivWithinAt_iff_tendsto_slope,tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hr

end EulerCylinderGraphTrace

end
end

end

section

/-! Genuine Sobolev time derivatives of coherent towers pass to actual
spatial L² derivatives after restriction to any fixed phase graph. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerMetricTransport EulerTransportDerivatives
  EulerCylinderGraphTrace EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  (A B : EulerAllOrderCorrectionData.FieldTower P T)
  (f g : Icc (0 : ℝ) T → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hg : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (g t) x))
  (ha : ∀ t, (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)
  (hb : ∀ t, (B.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g t)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

theorem graphWordPath_hasDerivWithinAt (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T)
    (hd : HasDerivWithinAt (extendPath T hT (A.realization (n + 1)))
      (B.realization (n + 1) t) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
      (B.graphWordPath g hg hb θ hθ n w t) (Icc (0 : ℝ) T) t := by
  refine graph_hasDerivWithinAt P
    (extendPath T hT (A.derivativeWordPath (n+1) n w (by omega)))
    (extendPath T hT (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl))
    (fun r => iteratedFieldDerivative P w (f (projIcc 0 T hT r)))
    (fun r => iteratedFieldDerivative_smooth P w _ (hf (projIcc 0 T hT r)))
    (fun r => A.derivativeWordPath_ae f hf ha (n+1) n w (by omega) (projIcc 0 T hT r))
    (fun r => A.graphWord_angular_ae f hf ha n w (projIcc 0 T hT r)) θ hθ
    (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
    (fun r => A.graphWordPath_ae f hf ha θ hθ n w (projIcc 0 T hT r))
    (iteratedFieldDerivative P w (g t))
    (iteratedFieldDerivative_smooth P w _ (hg t))
    (B.derivativeWordPath (n+1) n w (by omega) t)
    (B.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t)
    (B.derivativeWordPath_ae g hg hb (n+1) n w (by omega) t)
    (B.graphWord_angular_ae g hg hb n w t)
    (B.graphWordPath g hg hb θ hθ n w t)
    (B.graphWordPath_ae g hg hb θ hθ n w t) (Icc (0 : ℝ) T) t ?_ ?_
  · exact (wordOperator P (⟨⟨n,by omega⟩,w⟩ : SobolevWord (n+1))).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) hd
  · exact (wordOperator P (⟨⟨n+1,by
      omega⟩,Fin.cons 0 w⟩ : SobolevWord (n+1))).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) hd

theorem graphWordPath_hasDerivAt (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4)
    (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hd : HasDerivAt (extendPath T hT (A.realization (n + 1)))
      (B.realization (n + 1) ⟨t, ht.1.le, ht.2.le⟩) t) :
    HasDerivAt (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
      (B.graphWordPath g hg hb θ hθ n w ⟨t,ht.1.le,ht.2.le⟩) t :=
  (A.graphWordPath_hasDerivWithinAt B f g hf hg ha hb θ hθ hT n w
    ⟨t,ht.1.le,ht.2.le⟩ hd.hasDerivWithinAt).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end EulerAllOrderCorrectionData.FieldTower

end
end

end

section

/-! A genuine derivative at one Sobolev order gives the same derivative at
all lower orders of the coherent towers. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set EulerCylinderSobolevSpace EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)]
  (A B : EulerAllOrderCorrectionData.FieldTower P T)

/-- Cache the standard `NormedAddCommGroup (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace P q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace P q) := inferInstance
/-- Cache the standard `TopologicalSpace (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionTopology (q : ℕ) : TopologicalSpace (SobolevSpace P q) :=
  (inferInstance : PseudoMetricSpace (SobolevSpace P q)).toUniformSpace.toTopologicalSpace

theorem realization_hasDerivWithinAt_of_le {p q : ℕ} (h : q ≤ p)
    (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (hd : HasDerivWithinAt (extendPath T hT (A.realization p))
      (B.realization p t) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (extendPath T hT (A.realization q))
      (B.realization q t) (Icc (0 : ℝ) T) t := by
  have hder : HasDerivWithinAt
      (fun r => restrictOperator P h (extendPath T hT (A.realization p) r))
      (restrictOperator P h (B.realization p t)) (Icc (0 : ℝ) T) t :=
    (restrictOperator P h).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hd
  have he : (fun r => restrictOperator P h (extendPath T hT (A.realization p) r)) =
      extendPath T hT (A.realization q) :=
    funext (fun r => A.restrict_realization h (projIcc 0 T hT r))
  rw [he,B.restrict_realization h t] at hder
  exact hder

theorem realization_hasDerivAt_of_le {p q : ℕ} (h : q ≤ p)
    (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (hd : HasDerivAt (extendPath T hT (A.realization p))
      (B.realization p t) t) :
    HasDerivAt (extendPath T hT (A.realization q)) (B.realization q t) t := by
  have hder : HasDerivAt
      (fun r => restrictOperator P h (extendPath T hT (A.realization p) r))
      (restrictOperator P h (B.realization p t)) t :=
    (restrictOperator P h).hasFDerivAt.comp_hasDerivAt (t : ℝ) hd
  have he : (fun r => restrictOperator P h (extendPath T hT (A.realization p) r)) =
      extendPath T hT (A.realization q) :=
    funext (fun r => A.restrict_realization h (projIcc 0 T hT r))
  rw [he,B.restrict_realization h t] at hder
  exact hder

end EulerAllOrderCorrectionData.FieldTower

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerMetricTransport EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  (A : EulerAllOrderCorrectionData.FieldTower P T)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

/-- Canonical graph word path, given by `A.graphWordPath A.pointField A.pointField_smooth
A.pointField_ae θ hθ n w`. -/
def canonicalGraphWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  A.graphWordPath A.pointField A.pointField_smooth A.pointField_ae θ hθ n w

theorem canonicalGraphWordPath_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.canonicalGraphWordPath θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (A.pointField t) (x,θ x) :=
  A.graphWordPath_ae A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t

theorem canonicalGraphWordPath_norm_sq_le (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    ‖A.canonicalGraphWordPath θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization (n+1) t‖^2 :=
  A.graphWordPath_norm_sq_le A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t

theorem canonicalGraphWordPath_norm_sq_le_high (n : ℕ) (w : Fin n → Fin 4)
    (q : ℕ) (hq : n + 1 ≤ q) (t : Icc (0 : ℝ) T) :
    ‖A.canonicalGraphWordPath θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization q t‖^2 := by
  have hn := restrictOperator_bound P hq (A.realization q t)
  rw [A.restrict_realization] at hn
  have hP : 0 < P := Fact.out
  exact (A.canonicalGraphWordPath_norm_sq_le θ hθ n w t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity))

theorem canonicalGraphWordPath_hasDerivAt (B : EulerAllOrderCorrectionData.FieldTower P T)
    (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4) (q : ℕ) (hq : n + 1 ≤ q)
    (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hd : HasDerivAt (extendPath T hT (A.realization q))
      (B.realization q ⟨t, ht.1.le, ht.2.le⟩) t) :
    HasDerivAt (extendPath T hT (A.canonicalGraphWordPath θ hθ n w))
      (B.canonicalGraphWordPath θ hθ n w ⟨t,ht.1.le,ht.2.le⟩) t :=
  A.graphWordPath_hasDerivAt B A.pointField B.pointField A.pointField_smooth B.pointField_smooth
    A.pointField_ae B.pointField_ae θ hθ hT n w t ht
    (A.realization_hasDerivAt_of_le B hq hT ⟨t,ht.1.le,ht.2.le⟩ hd)

end EulerAllOrderCorrectionData.FieldTower
