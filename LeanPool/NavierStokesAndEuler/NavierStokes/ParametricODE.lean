/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TangentODE
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Smooth dependence of finite-interval linear ODE solutions

The coefficient and forcing are elements of spaces of continuous paths with
the supremum norm. The actual integral equation is solved by an invertible
Volterra operator. Smooth inversion then gives parameter dependence without
assuming smoothness of a pre-existing family of solutions.
-/

namespace NavierStokes.ParametricODE

noncomputable section

open Set Function Filter Metric intervalIntegral MeasureTheory
open scoped Topology NNReal Nat Interval ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Curve (a b : ℝ) (E : Type*) [TopologicalSpace E] := C(Icc a b, E)

abbrev Coefficient (a b : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Curve a b (E →L[ℝ] E)

variable {a b : ℝ} (hab : a ≤ b)

def extend (f : Curve a b E) (t : ℝ) : E := f (projIcc a b hab t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_extend (f : Curve a b E) : Continuous (extend hab f) :=
  f.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem extend_coe (f : Curve a b E) (t : Icc a b) : extend hab f t = f t := by
  simp only [extend, projIcc_val]

def integralPath (f : Curve a b E) : Curve a b E :=
  ⟨fun t => ∫ s in a..t, extend hab f s, by
    have hd (t : ℝ) : HasDerivAt (fun t => ∫ s in a..t, extend hab f s)
        (extend hab f t) t :=
      integral_hasDerivAt_right ((continuous_extend hab f).intervalIntegrable _ _)
        ((continuous_extend hab f).stronglyMeasurableAtFilter _ _)
        (continuous_extend hab f).continuousAt
    exact (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).comp
      continuous_subtype_val⟩

theorem norm_integralPath_le (f : Curve a b E) :
    ‖integralPath hab f‖ ≤ (b - a) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg _))).mpr
  intro t
  change ‖∫ s in a..(t : ℝ), extend hab f s‖ ≤ _
  calc
    _ ≤ ‖f‖ * |(t : ℝ) - a| :=
      norm_integral_le_of_norm_le_const fun s _ => f.norm_coe_le_norm _
    _ ≤ ‖f‖ * (b - a) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)]
      exact sub_le_sub_right t.2.2 a
    _ = _ := mul_comm _ _

def integrator : Curve a b E →L[ℝ] Curve a b E :=
  LinearMap.mkContinuous {
    toFun := integralPath hab
    map_add' := by
      intro f g
      ext t
      exact integral_add ((continuous_extend hab f).intervalIntegrable _ _)
        ((continuous_extend hab g).intervalIntegrable _ _)
    map_smul' := by
      intro c f
      ext t
      exact integral_smul c (extend hab f)
  } (b - a) (norm_integralPath_le hab)

theorem integrator_apply (f : Curve a b E) (t : Icc a b) :
    integrator hab f t = ∫ s in a..(t : ℝ), extend hab f s := rfl

noncomputable def applyCoefficient (A : Coefficient a b E) (u : Curve a b E) : Curve a b E :=
  ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩

omit [CompleteSpace E] in
theorem norm_applyCoefficient_le (A : Coefficient a b E) (u : Curve a b E) :
    ‖applyCoefficient A u‖ ≤ ‖A‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le (applyCoefficient A u)
    (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

def coefficientLinear : Coefficient a b E →ₗ[ℝ] Curve a b E →ₗ[ℝ] Curve a b E where
  toFun A := {
    toFun := applyCoefficient A
    map_add' := by intro u w; ext t; exact map_add (A t) _ _
    map_smul' := by intro c u; ext t; exact map_smul (A t) _ _ }
  map_add' := by intro A B; ext u t; rfl
  map_smul' := by intro c A; ext u t; rfl

def coefficientAction : Coefficient a b E →L[ℝ] Curve a b E →L[ℝ] Curve a b E :=
  (coefficientLinear (a := a) (b := b) (E := E)).mkContinuous₂
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) 1
    (fun (A : Coefficient a b E) (u : Curve a b E) => by
      change ‖applyCoefficient A u‖ ≤ 1 * ‖A‖ * ‖u‖
      simpa only [one_mul] using norm_applyCoefficient_le (E := E) A u)

omit [CompleteSpace E] in
theorem coefficientAction_apply (A : Coefficient a b E) (u : Curve a b E) (t : Icc a b) :
    coefficientAction (E := E) A u t = A t (u t) := rfl

def volterra : Coefficient a b E →L[ℝ] Curve a b E →L[ℝ] Curve a b E :=
  ((ContinuousLinearMap.compL ℝ (Curve a b E) (Curve a b E) (Curve a b E))
    (integrator hab)).comp (coefficientAction (E := E))

theorem volterra_apply (A : Coefficient a b E) (u : Curve a b E) (t : Icc a b) :
    volterra (E := E) hab A u t =
      ∫ s in a..(t : ℝ), extend hab A s (extend hab u s) := rfl

theorem norm_volterra_apply_le (A : Coefficient a b E) (u : Curve a b E) :
    ‖volterra (E := E) hab A u‖ ≤ (b - a) * ‖A‖ * ‖u‖ := by
  change ‖integralPath hab (applyCoefficient A u)‖ ≤ _
  exact (norm_integralPath_le hab _).trans
    ((mul_le_mul_of_nonneg_left (norm_applyCoefficient_le A u)
      (sub_nonneg.mpr hab)).trans_eq (mul_assoc _ _ _).symm)

def homogeneousSystem (A : Coefficient a b E) : TangentODE.IntervalSystem E := {
  left := a
  right := b
  ordered := hab
  initial := 0
  field := fun t x => extend hab A t x
  lip := ‖A‖₊
  lipschitz := fun t _ => (extend hab A t).lipschitzWith.weaken (A.norm_coe_le_norm _)
  continuous := by
    have he : Continuous (fun t : Icc a b => extend hab A t) :=
      (continuous_extend hab A).comp continuous_subtype_val
    exact (he.comp continuous_fst).clm_apply continuous_snd }

theorem volterra_eq_next (A : Coefficient a b E) :
    (volterra (E := E) hab A : Curve a b E → Curve a b E) = (homogeneousSystem hab A).next := by
  funext u
  ext t
  change (∫ s in a..(t : ℝ), extend hab A s (extend hab u s)) =
    0 + ∫ s in a..(t : ℝ), extend hab A (projIcc a b hab s) (u (projIcc a b hab s))
  simp only [zero_add, extend, projIcc_val]

theorem volterra_contracting_iterate (A : Coefficient a b E) :
    ∃ (N : ℕ) (K : ℝ≥0), ContractingWith K (volterra (E := E) hab A)^[N] := by
  rw [volterra_eq_next]
  exact (homogeneousSystem hab A).exists_contracting_iterate

section AbstractInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem affine_iterate_sub (L : X →L[ℝ] X) (g : X) (n : ℕ) (u w : X) :
    (fun x => g + L x)^[n] u - (fun x => g + L x)^[n] w =
      L^[n] u - L^[n] w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterate_succ_apply', add_sub_add_left_eq_sub]
    rw [← L.map_sub, ih, L.map_sub]

theorem id_sub_isInvertible (L : X →L[ℝ] X)
    (hL : ∃ (N : ℕ) (K : ℝ≥0), ContractingWith K L^[N]) :
    (ContinuousLinearMap.id ℝ X - L).IsInvertible := by
  obtain ⟨N, K, hK⟩ := hL
  have htrans (g : X) : ContractingWith K (fun x => g + L x)^[N] := by
    refine ⟨hK.1, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    simpa only [dist_eq_norm, affine_iterate_sub] using hK.2.dist_le_mul u w
  have hsurj : Surjective (ContinuousLinearMap.id ℝ X - L) := by
    intro g
    let x := (htrans g).fixedPoint (fun x => g + L x)^[N]
    have hf : g + L x = x := (htrans g).isFixedPt_fixedPoint_iterate.eq
    refine ⟨x, ?_⟩
    change x - L x = g
    exact sub_eq_iff_eq_add.mpr hf.symm
  have hinj : Injective (ContinuousLinearMap.id ℝ X - L) := by
    intro u w huv
    let g := (ContinuousLinearMap.id ℝ X - L) u
    have hu : IsFixedPt (fun x => g + L x) u := by
      change (u - L u) + L u = u
      exact sub_add_cancel _ _
    have hw : IsFixedPt (fun x => g + L x) w := by
      change ((ContinuousLinearMap.id ℝ X - L) u) + L w = w
      rw [huv]
      exact sub_add_cancel _ _
    exact (htrans g).fixedPoint_unique' (hu.iterate N) (hw.iterate N)
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

end AbstractInverse

theorem contDiff_inverse_family {X Q : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (L : Q → X →L[ℝ] X) (hL : ContDiff ℝ ∞ L) (hInv : ∀ q, (L q).IsInvertible) :
    ContDiff ℝ ∞ (fun q => (L q).inverse) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  exact (hInv q).contDiffAt_map_inverse.comp q hL.contDiffAt

def equationOperator (A : Coefficient a b E) : Curve a b E →L[ℝ] Curve a b E :=
  ContinuousLinearMap.id ℝ (Curve a b E) - volterra (E := E) hab A

theorem equationOperator_isInvertible (A : Coefficient a b E) :
    (equationOperator hab A).IsInvertible :=
  id_sub_isInvertible _ (volterra_contracting_iterate hab A)

/-- Resolvent of the actual Volterra integral equation on the full finite interval. -/
def resolvent (A : Coefficient a b E) : Curve a b E →L[ℝ] Curve a b E :=
  (equationOperator hab A).inverse

theorem contDiff_resolvent : ContDiff ℝ ∞ (resolvent (E := E) hab) := by
  change ContDiff ℝ ∞ (fun A : Coefficient a b E => (equationOperator hab A).inverse)
  apply contDiff_inverse_family (equationOperator (E := E) hab)
  · unfold equationOperator
    apply ContDiff.sub contDiff_const
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := Coefficient a b E) (F := Curve a b E →L[ℝ] Curve a b E)
      (volterra (E := E) hab)
  · exact equationOperator_isInvertible hab

def constantCurve : E →L[ℝ] Curve a b E :=
  LinearMap.mkContinuous {
    toFun := ContinuousMap.const (Icc a b)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (fun x => by
    change ‖ContinuousMap.const (Icc a b) x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using
      (ContinuousMap.norm_le (ContinuousMap.const (Icc a b) x) (norm_nonneg x)).mpr
        (fun _ => le_rfl))

def source (x₀ : E) (f : Curve a b E) : Curve a b E :=
  constantCurve x₀ + integrator hab f

/-- The constructed solution as a continuous path, not an assumed solution family. -/
def solution (A : Coefficient a b E) (x₀ : E) (f : Curve a b E) : Curve a b E :=
  resolvent hab A (source hab x₀ f)

theorem resolvent_equation (A : Coefficient a b E) (g : Curve a b E) :
    equationOperator hab A (resolvent hab A g) = g := by
  exact ((equationOperator_isInvertible hab A).inverse_apply_eq.mp rfl).symm

theorem solution_integralEquation (A : Coefficient a b E) (x₀ : E) (f : Curve a b E) :
    solution hab A x₀ f = constantCurve x₀ +
      integrator hab (applyCoefficient A (solution hab A x₀ f) + f) := by
  have h := resolvent_equation hab A (source hab x₀ f)
  change solution hab A x₀ f - volterra (E := E) hab A (solution hab A x₀ f) =
    source hab x₀ f at h
  rw [map_add]
  change solution hab A x₀ f = constantCurve x₀ +
    (volterra (E := E) hab A (solution hab A x₀ f) + integrator hab f)
  rw [sub_eq_iff_eq_add] at h
  calc
    _ = source hab x₀ f + volterra (E := E) hab A (solution hab A x₀ f) := h
    _ = _ := by unfold source; abel

theorem solution_initial (A : Coefficient a b E) (x₀ : E) (f : Curve a b E) :
    solution hab A x₀ f ⟨a, le_rfl, hab⟩ = x₀ := by
  have h := congrArg (fun u : Curve a b E => u ⟨a, le_rfl, hab⟩)
    (solution_integralEquation hab A x₀ f)
  dsimp [constantCurve] at h
  simp only [integrator_apply, intervalIntegral.integral_same, add_zero] at h
  exact h

def solutionExtension (A : Coefficient a b E) (x₀ : E) (f : Curve a b E) (t : ℝ) : E :=
  x₀ + ∫ s in a..t, extend hab (applyCoefficient A (solution hab A x₀ f) + f) s

theorem solutionExtension_coe (A : Coefficient a b E) (x₀ : E)
    (f : Curve a b E) (t : Icc a b) :
    solutionExtension hab A x₀ f t = solution hab A x₀ f t := by
  have h := congrArg (fun u : Curve a b E => u t) (solution_integralEquation hab A x₀ f)
  exact h.symm

/-- The constructed path has a differentiable extension satisfying the actual ODE
at every point of the prescribed interval. -/
theorem solutionExtension_hasDerivAt (A : Coefficient a b E) (x₀ : E)
    (f : Curve a b E) (t : Icc a b) :
    HasDerivAt (solutionExtension hab A x₀ f)
      (A t (solutionExtension hab A x₀ f t) + f t) t := by
  let g := applyCoefficient A (solution hab A x₀ f) + f
  have hd := (integral_hasDerivAt_right ((continuous_extend hab g).intervalIntegrable a t)
    ((continuous_extend hab g).stronglyMeasurableAtFilter _ _)
    (continuous_extend hab g).continuousAt).const_add x₀
  rw [extend_coe] at hd
  rw [solutionExtension_coe]
  unfold solutionExtension
  simpa only [g, ContinuousMap.add_apply, applyCoefficient, ContinuousMap.coe_mk] using hd

theorem solution_hasDerivWithinAt (A : Coefficient a b E) (x₀ : E)
    (f : Curve a b E) (t : Icc a b) :
    HasDerivWithinAt (extend hab (solution hab A x₀ f))
      (A t (solution hab A x₀ f t) + f t) (Icc a b) t := by
  have hd := (solutionExtension_hasDerivAt hab A x₀ f t).hasDerivWithinAt (s := Icc a b)
  rw [solutionExtension_coe] at hd
  apply hd.congr_of_eventuallyEq_of_mem _ t.2
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := solutionExtension_coe hab A x₀ f ⟨s, hs⟩
  simpa only [extend, projIcc_of_mem hab hs] using h.symm

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Differentiating the actual inverse equation gives the first variation in
every direction of an arbitrary normed parameter space. -/
theorem fderiv_resolvent_family (A : P → Coefficient a b E) (g : P → Curve a b E)
    {p : P} {A' : P →L[ℝ] Coefficient a b E} {g' : P →L[ℝ] Curve a b E}
    (hA : HasFDerivAt A A' p) (hg : HasFDerivAt g g' p) (v : P) :
    fderiv ℝ (fun q => resolvent hab (A q) (g q)) p v =
      resolvent hab (A p) (g' v + volterra (E := E) hab (A' v)
        (resolvent hab (A p) (g p))) := by
  let u := fun q => resolvent hab (A q) (g q)
  have hr : DifferentiableAt ℝ (fun q => resolvent hab (A q)) p :=
    ((contDiff_resolvent hab).differentiable (by simp) (A p)).comp p hA.differentiableAt
  have hu : DifferentiableAt ℝ u p := hr.clm_apply hg.differentiableAt
  have hV : HasFDerivAt (fun q => volterra (E := E) hab (A q))
      ((volterra (E := E) hab).comp A') p := by
    have hlin : HasFDerivAt (fun B : Coefficient a b E => volterra (E := E) hab B)
        (volterra (E := E) hab) (A p) :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
        (E := Coefficient a b E) (F := Curve a b E →L[ℝ] Curve a b E)
        (volterra (E := E) hab)
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := Coefficient a b E)
      (G := Curve a b E →L[ℝ] Curve a b E) p hlin hA
  have hd := hu.hasFDerivAt.fun_sub (hV.clm_apply hu.hasFDerivAt)
  have heq : (fun q => u q - volterra (E := E) hab (A q) (u q)) = g := by
    funext q
    exact resolvent_equation hab (A q) (g q)
  rw [heq] at hd
  have hdir := congrArg (fun D : P →L[ℝ] Curve a b E => D v) (hd.unique hg)
  change fderiv ℝ u p v - (volterra (E := E) hab (A p) (fderiv ℝ u p v) +
    volterra (E := E) hab (A' v) (u p)) = g' v at hdir
  change fderiv ℝ u p v = (equationOperator hab (A p)).inverse
    (g' v + volterra (E := E) hab (A' v) (u p))
  symm
  apply (equationOperator_isInvertible hab (A p)).inverse_apply_eq.mpr
  change g' v + volterra (E := E) hab (A' v) (u p) =
    fderiv ℝ u p v - volterra (E := E) hab (A p) (fderiv ℝ u p v)
  rw [sub_add_eq_sub_sub] at hdir
  exact (sub_eq_iff_eq_add.mp hdir).symm

/-- The actual parameter derivative is the solution of the variational equation,
with source `(∂A)u + ∂f` and initial value `∂x₀`. -/
theorem parameter_derivative_eq_solution
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    {p : P} {A' : P →L[ℝ] Coefficient a b E} {x₀' : P →L[ℝ] E}
    {f' : P →L[ℝ] Curve a b E}
    (hA : HasFDerivAt A A' p) (hx₀ : HasFDerivAt x₀ x₀' p)
    (hf : HasFDerivAt f f' p) (v : P) :
    fderiv ℝ (fun q => solution hab (A q) (x₀ q) (f q)) p v =
      solution hab (A p) (x₀' v)
        (applyCoefficient (A' v) (solution hab (A p) (x₀ p) (f p)) + f' v) := by
  have hs : HasFDerivAt (fun q => source hab (x₀ q) (f q))
      ((constantCurve (a := a) (b := b)).comp x₀' + (integrator hab).comp f') p := by
    have hc : HasFDerivAt (constantCurve (E := E) (a := a) (b := b))
        (constantCurve (a := a) (b := b)) (x₀ p) :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := Curve a b E)
        (constantCurve (a := a) (b := b))
    have hi : HasFDerivAt (integrator (E := E) hab) (integrator hab) (f p) :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Curve a b E) (F := Curve a b E)
        (integrator hab)
    exact (hc.comp p hx₀).add (hi.comp p hf)
  have h := fderiv_resolvent_family hab A (fun q => source hab (x₀ q) (f q)) hA hs v
  calc
    _ = resolvent hab (A p) (constantCurve (x₀' v) + integrator hab (f' v) +
        volterra (E := E) hab (A' v) (solution hab (A p) (x₀ p) (f p))) := h
    _ = _ := by
      unfold solution source
      apply congrArg (resolvent hab (A p))
      rw [(integrator hab).map_add]
      change _ = constantCurve (x₀' v) +
        (volterra (E := E) hab (A' v) (resolvent hab (A p)
          (constantCurve (x₀ p) + integrator hab (f p))) + integrator hab (f' v))
      abel

theorem parameter_derivative_hasDerivWithinAt
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    {p : P} {A' : P →L[ℝ] Coefficient a b E} {x₀' : P →L[ℝ] E}
    {f' : P →L[ℝ] Curve a b E}
    (hA : HasFDerivAt A A' p) (hx₀ : HasFDerivAt x₀ x₀' p)
    (hf : HasFDerivAt f f' p) (v : P) (t : Icc a b) :
    HasDerivWithinAt
      (extend hab (fderiv ℝ (fun q => solution hab (A q) (x₀ q) (f q)) p v))
      (A p t ((fderiv ℝ (fun q => solution hab (A q) (x₀ q) (f q)) p v) t) +
        A' v t (solution hab (A p) (x₀ p) (f p) t) + f' v t) (Icc a b) t := by
  rw [parameter_derivative_eq_solution hab A x₀ f hA hx₀ hf v]
  simpa only [ContinuousMap.add_apply, applyCoefficient, ContinuousMap.coe_mk, add_assoc]
    using solution_hasDerivWithinAt hab (A p) (x₀' v)
      (applyCoefficient (A' v) (solution hab (A p) (x₀ p) (f p)) + f' v) t

omit [CompleteSpace E] in
theorem norm_constantCurve_le (x : E) :
    ‖constantCurve (a := a) (b := b) x‖ ≤ ‖x‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg x)).mpr (fun _ => le_rfl)

theorem norm_source_le (x₀ : E) (f : Curve a b E) :
    ‖source hab x₀ f‖ ≤ ‖x₀‖ + (b - a) * ‖f‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_constantCurve_le x₀) (norm_integralPath_le hab f))

/-- A finite stability bound in terms of the norm of the actual inverse operator. -/
theorem norm_solution_le (A : Coefficient a b E) (x₀ : E) (f : Curve a b E) :
    ‖solution hab A x₀ f‖ ≤ ‖resolvent hab A‖ * (‖x₀‖ + (b - a) * ‖f‖) :=
  ((resolvent hab A).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_source_le hab x₀ f) (norm_nonneg _))

theorem norm_parameter_derivative_le
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    {p : P} {A' : P →L[ℝ] Coefficient a b E} {x₀' : P →L[ℝ] E}
    {f' : P →L[ℝ] Curve a b E}
    (hA : HasFDerivAt A A' p) (hx₀ : HasFDerivAt x₀ x₀' p)
    (hf : HasFDerivAt f f' p) (v : P) :
    ‖fderiv ℝ (fun q => solution hab (A q) (x₀ q) (f q)) p v‖ ≤
      ‖resolvent hab (A p)‖ * (‖x₀' v‖ + (b - a) *
        (‖A' v‖ * ‖solution hab (A p) (x₀ p) (f p)‖ + ‖f' v‖)) := by
  rw [parameter_derivative_eq_solution hab A x₀ f hA hx₀ hf v]
  apply (norm_solution_le hab (A p) (x₀' v) _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg (resolvent hab (A p)))
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  exact (norm_add_le _ _).trans (add_le_add_left (norm_applyCoefficient_le _ _) _)

/-- Full smooth dependence in the supremum-norm spaces of coefficient and forcing
paths. Smoothness of the solution map is a conclusion. -/
theorem contDiff_solution_family (A : P → Coefficient a b E) (x₀ : P → E)
    (f : P → Curve a b E) (hA : ContDiff ℝ ∞ A) (hx₀ : ContDiff ℝ ∞ x₀)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => solution hab (A p) (x₀ p) (f p)) := by
  change ContDiff ℝ ∞ (fun p => resolvent hab (A p)
    (constantCurve (a := a) (b := b) (x₀ p) + integrator hab (f p)))
  exact ((contDiff_resolvent hab).comp hA).clm_apply
    (((constantCurve (E := E) (a := a) (b := b)).contDiff.comp hx₀).add
      ((integrator (E := E) hab).contDiff.comp hf))

theorem contDiffOn_solution_family {s : Set P}
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    (hA : ContDiffOn ℝ ∞ A s) (hx₀ : ContDiffOn ℝ ∞ x₀ s)
    (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun p => solution hab (A p) (x₀ p) (f p)) s := by
  change ContDiffOn ℝ ∞ (fun p => resolvent hab (A p)
    (constantCurve (a := a) (b := b) (x₀ p) + integrator hab (f p))) s
  exact ((contDiff_resolvent hab).comp_contDiffOn hA).clm_apply
    (((constantCurve (E := E) (a := a) (b := b)).contDiff.comp_contDiffOn hx₀).add
      ((integrator (E := E) hab).contDiff.comp_contDiffOn hf))

/-- Every parameter derivative has a finite uniform bound on a compact parameter
set. This does not assert polynomial dependence of those bounds on a band index. -/
theorem parameter_derivatives_bounded_on_compact
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    (hA : ContDiff ℝ ∞ A) (hx₀ : ContDiff ℝ ∞ x₀) (hf : ContDiff ℝ ∞ f)
    {s : Set P} (hs : IsCompact s) (m : ℕ) :
    ∃ C : ℝ, ∀ p ∈ s,
      ‖iteratedFDeriv ℝ m (fun q => solution hab (A q) (x₀ q) (f q)) p‖ ≤ C := by
  exact hs.exists_bound_of_continuousOn
    ((contDiff_solution_family hab A x₀ f hA hx₀ hf).continuous_iteratedFDeriv
      (m := m) (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).continuousOn

end

end NavierStokes.ParametricODE
