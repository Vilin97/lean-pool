/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteSourceExtension

/-!
# Initial traces on finite parabolic cylinders

A parabolic `C^{0,α}` class on `(t₀,T] × X` has a canonical bounded-continuous
trace at the missing initial face.  This file packages that trace as a bounded
linear map and, by projection to the value component, defines the initial trace
of a genuine finite-cylinder `C^{2+α,1+α/2}` jet.

The trace is obtained from the endpoint completion constructed in
`FiniteSourceExtension`; no boundary value is chosen independently of the
positive-time function.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace ParabolicC0AlphaBanach

variable {X : Type*} [PseudoMetricSpace X]
variable {t₀ T α : ℝ}

/-- The canonical initial trace of finite-cylinder parabolic Hölder data. -/
def finiteInitialTrace (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    BoundedContinuousFunction X E :=
  finiteClosedTimeSlice hT hα q ⟨t₀, le_rfl, hT.le⟩

@[simp]
theorem finiteInitialTrace_zero (hT : t₀ < T) (hα : 0 < α) :
    finiteInitialTrace (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  simp [finiteInitialTrace]

@[simp]
theorem finiteInitialTrace_add (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTrace hT hα (q + r) =
      finiteInitialTrace hT hα q + finiteInitialTrace hT hα r := by
  simp [finiteInitialTrace]

@[simp]
theorem finiteInitialTrace_smul (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTrace hT hα (c • q) = c • finiteInitialTrace hT hα q := by
  simp [finiteInitialTrace]

/-- Initial trace has operator bound one in the finite-cylinder Hölder norm. -/
theorem norm_finiteInitialTrace_le (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ‖finiteInitialTrace hT hα q‖ ≤ ‖q‖ :=
  norm_finiteClosedTimeSlice_le hT hα q ⟨t₀, le_rfl, hT.le⟩

/-- Initial trace as a bounded linear map. -/
def finiteInitialTraceL (hT : t₀ < T) (hα : 0 < α) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      BoundedContinuousFunction X E :=
  LinearMap.mkContinuous
    { toFun := finiteInitialTrace hT hα
      map_add' := finiteInitialTrace_add hT hα
      map_smul' := finiteInitialTrace_smul hT hα }
    1 (by simpa using norm_finiteInitialTrace_le hT hα)

@[simp]
theorem finiteInitialTraceL_apply (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTraceL hT hα q = finiteInitialTrace hT hα q :=
  rfl

theorem norm_finiteInitialTraceL_le (hT : t₀ < T) (hα : 0 < α) :
    ‖finiteInitialTraceL (X := X) (E := E) hT hα‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The canonical completed slice path is characterized by continuity and
agreement with the datum at positive times. -/
theorem finiteClosedTimeSlice_eq_of_continuous
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction X E)
    (hg : Continuous g)
    (hpositive : ∀ t : positiveTimeInIcc t₀ T,
      g t = finiteTimeSlice hα q t) :
    finiteClosedTimeSlice hT hα q = g := by
  apply (dense_positiveTimeInIcc hT).denseRange_val.equalizer
    (continuous_finiteClosedTimeSlice hT hα q) hg
  funext t
  change finiteClosedTimeSlice hT hα q
    (t : ↥(Set.Icc t₀ T)) = g (t : ↥(Set.Icc t₀ T))
  rw [finiteClosedTimeSlice_apply_positive]
  exact (hpositive t).symm

/-- Endpoint form of the uniqueness characterization: any continuous closed
path agreeing with the positive-time slices has the canonical initial value. -/
theorem finiteInitialTrace_eq_of_continuous
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction X E)
    (hg : Continuous g)
    (hpositive : ∀ t : positiveTimeInIcc t₀ T,
      g t = finiteTimeSlice hα q t) :
    finiteInitialTrace hT hα q = g ⟨t₀, le_rfl, hT.le⟩ := by
  exact congrFun
    (finiteClosedTimeSlice_eq_of_continuous hT hα q g hg hpositive)
    ⟨t₀, le_rfl, hT.le⟩

/-- Quantitative convergence of every positive-time slice to the canonical
initial trace in the bounded-continuous spatial norm. -/
theorem dist_finiteTimeSlice_initial_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    dist (finiteTimeSlice hα q t) (finiteInitialTrace hT hα q) ≤
      ‖q‖ * |(t : ℝ) - t₀| ^ (α / 2) := by
  simpa [finiteInitialTrace, finiteClosedTimeSlice_apply_positive] using
    dist_finiteClosedTimeSlice_le hT hα q
      (t : ↥(Set.Icc t₀ T)) ⟨t₀, le_rfl, hT.le⟩

end ParabolicC0AlphaBanach

section HigherTrace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

/-- Initial trace of the value component of a genuine finite-cylinder
`C^{2+α,1+α/2}` jet. -/
def initialTraceL (hT : t₀ < T) (hα : 0 < α) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      BoundedContinuousFunction X E :=
  (ParabolicC0AlphaBanach.finiteInitialTraceL hT hα).comp valueComponentL

@[simp]
theorem initialTraceL_apply (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    initialTraceL hT hα u =
      ParabolicC0AlphaBanach.finiteInitialTrace hT hα (valueComponentL u) :=
  rfl

theorem norm_initialTraceL_le (hT : t₀ < T) (hα : 0 < α) :
    ‖initialTraceL (X := X) (E := E) hT hα‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro u
  calc
    ‖initialTraceL hT hα u‖ ≤ ‖valueComponentL u‖ :=
      ParabolicC0AlphaBanach.norm_finiteInitialTrace_le hT hα _
    _ ≤ ‖u‖ := by
      change ‖u.1.1‖ ≤ ‖u.1‖
      exact le_max_left _ _
    _ = 1 * ‖u‖ := by rw [one_mul]

/-- Restricting a finite-cylinder higher function to an earlier terminal time
does not change its canonical initial trace. -/
theorem initialTraceL_restrictTerminal
    {S : ℝ} (hS : t₀ < S) (hST : S ≤ T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    initialTraceL hS hα (restrictTerminal hST u) =
      initialTraceL (hS.trans_le hST) hα u := by
  let hT : t₀ < T := hS.trans_le hST
  let g : ↥(Set.Icc t₀ S) → BoundedContinuousFunction X E := fun t =>
    ParabolicC0AlphaBanach.finiteClosedTimeSlice hT hα (valueComponentL u)
      ⟨t, t.2.1, t.2.2.trans hST⟩
  have hg : Continuous g := by
    exact (ParabolicC0AlphaBanach.continuous_finiteClosedTimeSlice
      hT hα (valueComponentL u)).comp
        (continuous_subtype_val.subtype_mk fun t => ⟨t.2.1, t.2.2.trans hST⟩)
  have hpositive : ∀ t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ S,
      g t = ParabolicC0AlphaBanach.finiteTimeSlice hα
        (valueComponentL (restrictTerminal hST u)) t := by
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    let tT : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T :=
      ⟨⟨t, t.1.2.1, t.1.2.2.trans hST⟩, t.2⟩
    change ParabolicC0AlphaBanach.finiteClosedTimeSlice hT hα
        (valueComponentL u) (tT : ↥(Set.Icc t₀ T)) x =
      ParabolicC0AlphaBanach.finiteTimeSlice hα
        (valueComponentL (restrictTerminal hST u)) t x
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply,
      ParabolicC0AlphaBanach.finiteClosedTimeSlice_apply_positive]
    rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
    rw [FiniteParabolicC2AlphaBanach.value_restrictTerminal hST u
      (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)]
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply,
      FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
  change ParabolicC0AlphaBanach.finiteInitialTrace hS hα
      (valueComponentL (restrictTerminal hST u)) =
    ParabolicC0AlphaBanach.finiteInitialTrace hT hα (valueComponentL u)
  calc
    ParabolicC0AlphaBanach.finiteInitialTrace hS hα
        (valueComponentL (restrictTerminal hST u)) =
      g ⟨t₀, le_rfl, hS.le⟩ :=
        ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
          hS hα _ g hg hpositive
    _ = ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (valueComponentL u) := rfl

/-- The canonical trace of the first spatial-derivative component is the
genuine Fréchet derivative of the canonical value trace.  This closes an
important endpoint gap: compatibility on `(t₀,T]` and Hölder control of both
components force compatibility at the completed initial face as well.

The proof approaches `t₀` through an explicit sequence of positive times.
The completed value and derivative slices converge in bounded-continuous
norm, hence uniformly in space, so the uniform limit theorem for derivatives
passes the positive-time derivative identity to the initial trace. -/
theorem hasFDerivAt_initialTrace
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (x : X) :
    HasFDerivAt
      (initialTraceL hT hα u : X → E)
      ((ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (spaceDerivComponentL u)) x) x := by
  let δ : ℝ := T - t₀
  have hδ : 0 < δ := sub_pos.mpr hT
  let τ : ℕ → ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T := fun n =>
    ⟨⟨t₀ + δ / ((n : ℝ) + 1),
        ⟨by
            have hn0 : 0 < (n : ℝ) + 1 := by positivity
            exact le_add_of_nonneg_right (div_nonneg hδ.le hn0.le),
          by
            have hn : 1 ≤ (n : ℝ) + 1 := by
              have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
              linarith
            dsimp [δ]
            have := div_le_self hδ.le hn
            linarith⟩⟩,
      by
        have hn0 : 0 < (n : ℝ) + 1 := by positivity
        exact lt_add_of_pos_right _ (div_pos hδ hn0)⟩
  let tzero : ↥(Set.Icc t₀ T) := ⟨t₀, le_rfl, hT.le⟩
  have hτreal : Tendsto (fun n : ℕ => ((τ n :
      ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T) : ℝ)) atTop (𝓝 t₀) := by
    have hdiv : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa [τ] using tendsto_const_nhds.add hdiv
  have hτ : Tendsto (fun n : ℕ => (τ n).1) atTop (𝓝 tzero) := by
    apply tendsto_subtype_rng.mpr
    simpa [tzero] using hτreal
  let qx := spaceDerivComponentL u
  have hvalueSlices : Tendsto
      (fun n : ℕ => ParabolicC0AlphaBanach.finiteTimeSlice hα
        (valueComponentL u) (τ n)) atTop
      (𝓝 (ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (valueComponentL u))) := by
    have h := (ParabolicC0AlphaBanach.continuous_finiteClosedTimeSlice
      hT hα (valueComponentL u)).tendsto tzero |>.comp hτ
    convert h using 1
    · funext n
      exact (ParabolicC0AlphaBanach.finiteClosedTimeSlice_apply_positive
        hT hα (valueComponentL u) (τ n)).symm
    · rfl
  have hderivSlices : Tendsto
      (fun n : ℕ => ParabolicC0AlphaBanach.finiteTimeSlice hα qx (τ n)) atTop
      (𝓝 (ParabolicC0AlphaBanach.finiteInitialTrace hT hα qx)) := by
    have h := (ParabolicC0AlphaBanach.continuous_finiteClosedTimeSlice
      hT hα qx).tendsto tzero |>.comp hτ
    convert h using 1
    · funext n
      exact (ParabolicC0AlphaBanach.finiteClosedTimeSlice_apply_positive
        hT hα qx (τ n)).symm
    · rfl
  have huniform : TendstoUniformly
      (fun n : ℕ => (ParabolicC0AlphaBanach.finiteTimeSlice hα qx (τ n) :
        X → (X →L[ℝ] E)))
      (ParabolicC0AlphaBanach.finiteInitialTrace hT hα qx :
        X → (X →L[ℝ] E)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hderivSlices ε hε] with n hn y
    have hn' : dist (ParabolicC0AlphaBanach.finiteInitialTrace hT hα qx)
        (ParabolicC0AlphaBanach.finiteTimeSlice hα qx (τ n)) < ε := by
      rw [dist_comm]
      exact hn
    exact (BoundedContinuousFunction.dist_coe_le_dist y).trans_lt hn'
  refine hasFDerivAt_of_tendstoUniformly
    (f := fun n y => ParabolicC0AlphaBanach.finiteTimeSlice hα
      (valueComponentL u) (τ n) y)
    (f' := fun n y => ParabolicC0AlphaBanach.finiteTimeSlice hα qx (τ n) y)
    (g := (initialTraceL hT hα u : X → E))
    (g' := (ParabolicC0AlphaBanach.finiteInitialTrace hT hα qx :
      X → (X →L[ℝ] E))) huniform ?_ ?_ x
  · intro n y
    have hmem : ((τ n : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T) : ℝ)
        ∈ Set.Ioc t₀ T := ⟨(τ n).2, (τ n).1.2.2⟩
    have hd := hasFDerivAt_space u hmem y
    convert hd using 1
    · funext z
      exact FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL u _ _
    · dsimp [qx]
      exact FiniteParabolicC2AlphaBanach.evalCLM_spaceDerivComponentL u _ _
  · intro y
    have hy := hvalueSlices.eval_const y
    simpa [initialTraceL_apply] using hy

/-- A zero value trace forces a zero trace for the first spatial derivative.
Thus every zero-initial finite-cylinder solution has both lower-order terms
appearing in a cutoff commutator vanishing at the initial face. -/
theorem finiteInitialTrace_spaceDeriv_eq_zero_of_initialTrace_eq_zero
    (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α)
    (hu0 : initialTraceL hT hα u = 0) :
    ParabolicC0AlphaBanach.finiteInitialTrace hT hα
      (spaceDerivComponentL u) = 0 := by
  apply BoundedContinuousFunction.ext
  intro x
  have hzero : HasFDerivAt (initialTraceL hT hα u : X → E)
      (0 : X →L[ℝ] E) x := by
    convert hasFDerivAt_const (x := x) (c := (0 : E)) using 1
    funext y
    rw [hu0]
    rfl
  exact (hasFDerivAt_initialTrace hT hα u x).unique hzero

/-- Genuine finite-cylinder higher functions with zero canonical initial
trace.  This is a closed subspace because it is the kernel of a bounded
linear map. -/
def zeroInitialSubmodule (hT : t₀ < T) (hα : 0 < α) :
    Submodule ℝ (FiniteParabolicC2AlphaBanach X E t₀ T α) :=
  (initialTraceL hT hα).ker

@[simp]
theorem mem_zeroInitialSubmodule_iff (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    u ∈ zeroInitialSubmodule hT hα ↔ initialTraceL hT hα u = 0 :=
  LinearMap.mem_ker

end FiniteParabolicC2AlphaBanach

end HigherTrace

end AnalyticPDE
end RicciFlow
