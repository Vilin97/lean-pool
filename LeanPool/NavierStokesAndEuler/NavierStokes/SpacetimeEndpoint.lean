/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement

@[expose] public section

/-!
# Joint spacetime endpoint regularity from locally uniform derivative limits

The domain is the concrete four-dimensional spacetime `ℝ × ℝ³`. All derivative
data below are full Frechet derivative tensors, and convergence is locally
uniform in the spatial variable in the tensor norm. Closed-side smoothness is
proved from these data, rather than included as a hypothesis.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.SpacetimeEndpoint

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

def openPast (T : ℝ) : Set SpaceTime := Iio T ×ˢ univ
def closedPast (T : ℝ) : Set SpaceTime := Iic T ×ˢ univ

theorem openPast_isOpen (T : ℝ) : IsOpen (openPast T) :=
  isOpen_Iio.prod isOpen_univ

theorem openPast_convex (T : ℝ) : Convex ℝ (openPast T) :=
  (convex_Iio T).prod convex_univ

theorem closure_openPast (T : ℝ) : closure (openPast T) = closedPast T := by
  simp only [openPast, closedPast, closure_prod_eq, closure_Iio, closure_univ]

theorem closedPast_uniqueDiff (T : ℝ) : UniqueDiffOn ℝ (closedPast T) :=
  (uniqueDiffOn_Iic T).prod uniqueDiffOn_univ

/-- Extend by the boundary trace. Only closed-past smoothness is claimed. -/
def extendTrace {V : Type*} (T : ℝ) (f : SpaceTime → V) (L : Space → V)
    (z : SpaceTime) : V := if z.1 < T then f z else L z.2

theorem extendTrace_of_lt {V : Type*} {T : ℝ} {f : SpaceTime → V} {L : Space → V}
    {z : SpaceTime} (hz : z.1 < T) : extendTrace T f L z = f z := by
  simp only [extendTrace, ite_eq_left hz]

@[simp] theorem extendTrace_at {V : Type*} (T : ℝ) (f : SpaceTime → V)
    (L : Space → V) (x : Space) : extendTrace T f L (T, x) = L x := by
  simp only [extendTrace, lt_self_iff_false, ite_false]

section Normed

variable {V : Type*} [NormedAddCommGroup V]

theorem hasFDerivAt_extendTrace [NormedSpace ℝ V] {T : ℝ} {f : SpaceTime → V} {L : Space → V}
    {z : SpaceTime} {f' : SpaceTime →L[ℝ] V} (hz : z.1 < T)
    (hf : HasFDerivAt f f' z) : HasFDerivAt (extendTrace T f L) f' z := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto z).eventually (Iio_mem_nhds hz)] with y hy
  exact extendTrace_of_lt hy

/-- Local-uniform limits of continuous spatial slices are continuous traces. -/
theorem trace_continuous {T : ℝ} {f : SpaceTime → V} {L : Space → V}
    (hcont : ∀ t < T, Continuous (fun x : Space => f (t, x)))
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T)) :
    Continuous L := by
  apply hlim.continuous
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hcont t ht

/-- The local-uniform hypothesis controls simultaneous motion in time and
space; this is stronger than convergence at each fixed spatial point. -/
theorem joint_tendsto_at_boundary {T : ℝ} {f : SpaceTime → V} {L : Space → V}
    (hL : Continuous L)
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T)) (x : Space) :
    Tendsto f (𝓝[openPast T] (T, x)) (𝓝 (L x)) := by
  have ht : Tendsto (fun z : SpaceTime => z.1) (𝓝[openPast T] (T, x)) (𝓝[<] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (continuous_fst.tendsto (T, x)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hz.1
  have hx : Tendsto (fun z : SpaceTime => z.2) (𝓝[openPast T] (T, x)) (𝓝 x) :=
    (continuous_snd.tendsto (T, x)).mono_left nhdsWithin_le_nhds
  apply tendsto_comp_of_locally_uniform_limit
    (F := fun z : SpaceTime => fun y : Space => f (z.1, y)) hL.continuousAt hx
  intro u hu
  obtain ⟨s, hs, hU⟩ := hlim u hu x
  exact ⟨s, hs, ht.eventually hU⟩

theorem extendTrace_continuousWithinAt_boundary {T : ℝ} {f : SpaceTime → V}
    {L : Space → V} (hL : Continuous L)
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T)) (x : Space) :
    ContinuousWithinAt (extendTrace T f L) (openPast T) (T, x) := by
  change Tendsto (extendTrace T f L) (𝓝[openPast T] (T, x))
    (𝓝 (extendTrace T f L (T, x)))
  rw [extendTrace_at]
  apply (joint_tendsto_at_boundary hL hlim x).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (extendTrace_of_lt hz.1).symm

/-- Every spatial period of the slices passes to the boundary trace. -/
theorem trace_periodic {T : ℝ} {f : SpaceTime → V} {L : Space → V} (v : Space)
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T))
    (hperiod : ∀ t < T, ∀ x : Space, f (t, x + v) = f (t, x)) (x : Space) :
    L (x + v) = L x := by
  have h₁ := (hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ (x + v))
  have h₂ := (hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ x)
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hperiod t ht x).symm

theorem extendTrace_periodic {T : ℝ} {f : SpaceTime → V} {L : Space → V} (v : Space)
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T))
    (hperiod : ∀ t < T, ∀ x : Space, f (t, x + v) = f (t, x))
    (t : ℝ) (x : Space) :
    extendTrace T f L (t, x + v) = extendTrace T f L (t, x) := by
  by_cases ht : t < T
  · simp only [extendTrace, ite_eq_left ht]
    exact hperiod t ht x
  · simp only [extendTrace, ite_eq_right ht]
    exact trace_periodic v hlim hperiod x

variable [NormedSpace ℝ V]

/-- A fixed continuous linear map preserves the locally uniform limit. -/
theorem locallyUniform_linearMap {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T : ℝ} {f : SpaceTime → V} {L : Space → V} (A : V →L[ℝ] W)
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T)) :
    TendstoLocallyUniformly (fun t x => A (f (t, x))) (fun x => A (L x)) (𝓝[<] T) := by
  intro u hu x
  exact hlim _ (A.uniformContinuous hu) x

/-- The full Frechet derivative extends to the boundary. The proof uses
the mean-value theorem on the convex open past halfspace. -/
theorem hasFDerivWithinAt_extendTrace {T : ℝ}
    {f : SpaceTime → V} {f' : SpaceTime → SpaceTime →L[ℝ] V}
    {L : Space → V} {L' : Space → SpaceTime →L[ℝ] V}
    (hderiv : ∀ z : SpaceTime, z.1 < T → HasFDerivAt f (f' z) z)
    (hL : Continuous L) (hL' : Continuous L')
    (hlim : TendstoLocallyUniformly (fun t x => f (t, x)) L (𝓝[<] T))
    (hlim' : TendstoLocallyUniformly (fun t x => f' (t, x)) L' (𝓝[<] T))
    (z : SpaceTime) (hz : z ∈ closedPast T) :
    HasFDerivWithinAt (extendTrace T f L) (extendTrace T f' L' z) (closedPast T) z := by
  rcases z with ⟨t, x⟩
  rcases lt_or_eq_of_le (show t ≤ T from hz.1) with hlt | heq
  · rw [extendTrace_of_lt hlt]
    exact (hasFDerivAt_extendTrace hlt (hderiv (t, x) hlt)).hasFDerivWithinAt
  · subst t
    rw [extendTrace_at]
    have hd : DifferentiableOn ℝ (extendTrace T f L) (openPast T) := by
      intro y hy
      exact (hasFDerivAt_extendTrace hy.1 (hderiv y hy.1)).differentiableAt.differentiableWithinAt
    have hc : ∀ y ∈ closure (openPast T),
        ContinuousWithinAt (extendTrace T f L) (openPast T) y := by
      rintro ⟨s, y⟩ hy
      rw [closure_openPast] at hy
      rcases lt_or_eq_of_le (show s ≤ T from hy.1) with hs | hs
      · exact (hasFDerivAt_extendTrace hs (hderiv (s, y) hs)).continuousAt.continuousWithinAt
      · subst s
        exact extendTrace_continuousWithinAt_boundary hL hlim y
    have hdf : Tendsto (fun y => fderiv ℝ (extendTrace T f L) y)
        (𝓝[openPast T] (T, x)) (𝓝 (L' x)) := by
      apply (joint_tendsto_at_boundary hL' hlim' x).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hasFDerivAt_extendTrace (L := L) hy.1 (hderiv y hy.1)).fderiv.symm
    simpa only [closure_openPast] using
      hasFDerivWithinAt_closure_of_tendsto_fderiv hd (openPast_convex T)
        (openPast_isOpen T) hc hdf

/-- Extend every actual mixed derivative tensor by its spatial boundary trace. -/
def extendJets (T : ℝ) (J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime V)
    (z : SpaceTime) : FormalMultilinearSeries ℝ SpaceTime V :=
  fun n => extendTrace T (fun y => J y n) (fun x => L x n) z

theorem derivative_trace_continuous {T : ℝ}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) :
    Continuous (fun x => L x n) := by
  apply trace_continuous (T := T) (f := fun z => J z n) (L := fun x => L x n)
    _ (hlim n)
  intro t ht
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hderiv n (t, x) ht).continuousAt.comp
    (continuous_const.prodMk continuous_id).continuousAt

/-- All tensor derivatives remain compatible after taking boundary limits.
This is an actual `HasFDerivWithinAt` statement on the closed halfspace. -/
theorem extendedJets_hasFDerivWithinAt {T : ℝ}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ closedPast T) :
    HasFDerivWithinAt (fun y => extendJets T J L y n)
      (extendJets T J L z (n + 1)).curryLeft (closedPast T) z := by
  let A : (SpaceTime[×(n + 1)]→L[ℝ] V) →L[ℝ]
      (SpaceTime →L[ℝ] (SpaceTime[×n]→L[ℝ] V)) :=
    (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (n + 1) => SpaceTime) V).toContinuousLinearEquiv.toContinuousLinearMap
  have hLC : Continuous (fun x => (L x (n + 1)).curryLeft) :=
    A.continuous.comp (derivative_trace_continuous hderiv hlim (n + 1))
  have hlimC : TendstoLocallyUniformly (fun t x => (J (t, x) (n + 1)).curryLeft)
      (fun x => (L x (n + 1)).curryLeft) (𝓝[<] T) := by
    intro u hu x
    exact hlim (n + 1) _ (A.uniformContinuous hu) x
  have h := hasFDerivWithinAt_extendTrace (T := T) (f := fun z => J z n)
    (f' := fun z => (J z (n + 1)).curryLeft)
    (L := fun x => L x n) (L' := fun x => (L x (n + 1)).curryLeft) (hderiv n)
    (derivative_trace_continuous hderiv hlim n) hLC (hlim n) hlimC z hz
  unfold extendJets extendTrace
  unfold extendTrace at h
  split_ifs at h ⊢ <;> exact h

/-- The limiting derivative tensors form the actual smooth Taylor family
of the extended field. All fields of this predicate are proved. -/
theorem hasFTaylorSeriesUpToOn_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) :
    HasFTaylorSeriesUpToOn ∞ (extendTrace T f (fun x => (L x 0).curry0))
      (extendJets T J L) (closedPast T) := by
  constructor
  · intro z hz
    by_cases hzt : z.1 < T
    · simpa only [extendJets, extendTrace, ite_eq_left hzt] using hzero z hzt
    · simp only [extendJets, extendTrace, ite_eq_right hzt]
  · intro n hn z hz
    exact extendedJets_hasFDerivWithinAt hderiv hlim n z hz
  · intro n hn z hz
    exact (extendedJets_hasFDerivWithinAt hderiv hlim n z hz).continuousWithinAt

/-- Main joint endpoint theorem: local-uniform limits of every compatible
full Frechet derivative imply joint `C∞` regularity on the closed past. -/
theorem contDiffOn_joint_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) :
    ContDiffOn ℝ ∞ (extendTrace T f (fun x => (L x 0).curry0)) (closedPast T) :=
  (hasFTaylorSeriesUpToOn_extension hzero hderiv hlim).contDiffOn

/-- The limit tensors are the genuine mixed derivative jets of the extension. -/
theorem iteratedFDerivWithin_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ closedPast T) :
    iteratedFDerivWithin ℝ n (extendTrace T f (fun x => (L x 0).curry0))
      (closedPast T) z = extendJets T J L z n := by
  have h := hasFTaylorSeriesUpToOn_extension hzero hderiv hlim
  exact (h.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le (closedPast_uniqueDiff T) hz).symm

theorem boundary_jets_eq_limits {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ n (extendTrace T f (fun y => (L y 0).curry0))
      (closedPast T) (T, x) = L x n := by
  rw [iteratedFDerivWithin_extension hzero hderiv hlim n (T, x) ⟨le_refl T, mem_univ x⟩]
  exact extendTrace_at T _ _ x

/-- Every extended mixed-derivative tensor is itself jointly smooth. -/
theorem extendedJets_contDiffOn {T : ℝ}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z => extendJets T J L z n) (closedPast T) := by
  have hfinite : ∀ m n : ℕ,
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun z => extendJets T J L z n) (closedPast T) := by
    intro m
    induction m with
    | zero =>
      intro n
      apply contDiffOn_zero.mpr
      intro z hz
      exact (extendedJets_hasFDerivWithinAt hderiv hlim n z hz).continuousWithinAt
    | succ m ih =>
      intro n
      let A : (SpaceTime[×(n + 1)]→L[ℝ] V) →L[ℝ]
          (SpaceTime →L[ℝ] (SpaceTime[×n]→L[ℝ] V)) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => SpaceTime)
          V).toContinuousLinearEquiv.toContinuousLinearMap
      have hA : ContDiff ℝ (m : WithTop ℕ∞) A :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ)
          (E := SpaceTime[×(n + 1)]→L[ℝ] V)
          (F := SpaceTime →L[ℝ] (SpaceTime[×n]→L[ℝ] V)) A
      have hd : ContDiffOn ℝ (m : WithTop ℕ∞)
          (fun z => (extendJets T J L z (n + 1)).curryLeft) (closedPast T) := by
        exact hA.comp_contDiffOn (ih (n + 1))
      have hsucc : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
          (fun z => extendJets T J L z n) (closedPast T) := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (closedPast_uniqueDiff T)).mpr
        refine ⟨by simp, ?_⟩
        exact ⟨_, hd, fun z hz => extendedJets_hasFDerivWithinAt hderiv hlim n z hz⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hsucc
  exact contDiffOn_infty.mpr (fun m => hfinite m n)

/-- The boundary limits are smooth spatial coefficient functions, as required
for a spatial Taylor--Borel construction. This regularity is derived. -/
theorem boundary_tensors_contDiff {T : ℝ}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => L x n) := by
  have h := (extendedJets_contDiffOn hderiv hlim n).comp_contDiff
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun x : Space => (T, x)))
    (fun x => show (T, x) ∈ closedPast T from ⟨le_refl T, mem_univ x⟩)
  simpa only [Function.comp_def, extendJets, extendTrace_at] using h

theorem field_locallyUniform_limit {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hlim : TendstoLocallyUniformly (fun t x => J (t, x) 0)
      (fun x => L x 0) (𝓝[<] T)) :
    TendstoLocallyUniformly (fun t x => f (t, x)) (fun x => (L x 0).curry0) (𝓝[<] T) := by
  let A : (SpaceTime[×0]→L[ℝ] V) →L[ℝ] V :=
    (continuousMultilinearCurryFin0 ℝ SpaceTime V).toContinuousLinearEquiv.toContinuousLinearMap
  intro u hu x
  obtain ⟨s, hs, hU⟩ := hlim _ (A.uniformContinuous hu) x
  refine ⟨s, hs, ?_⟩
  filter_upwards [hU, self_mem_nhdsWithin] with t ht htime y hy
  rw [← hzero (t, y) htime]
  exact ht y hy

/-- Unit spatial periods are retained by the constructed endpoint extension. -/
theorem unit_periods_joint_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hlim : TendstoLocallyUniformly (fun t x => J (t, x) 0)
      (fun x => L x 0) (𝓝[<] T))
    (hperiod : ProblemStatement.UnitSpatialPeriodsOn (Iio T) f) :
    ProblemStatement.UnitSpatialPeriodsOn univ
      (extendTrace T f (fun x => (L x 0).curry0)) := by
  intro t ht x i
  exact extendTrace_periodic (ProblemStatement.coordinateVector i)
    (field_locallyUniform_limit hzero hlim) (fun s hs y => hperiod s hs y i) t x

/-- A constructive endpoint extension theorem with exact full boundary jets. -/
theorem exists_joint_endpoint_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) :
    ∃ g : SpaceTime → V, EqOn g f (openPast T) ∧ ContDiffOn ℝ ∞ g (closedPast T) ∧
      ∀ n : ℕ, ∀ x : Space, iteratedFDerivWithin ℝ n g (closedPast T) (T, x) = L x n := by
  exact ⟨extendTrace T f (fun x => (L x 0).curry0), fun z hz => extendTrace_of_lt hz.1,
    contDiffOn_joint_extension hzero hderiv hlim, boundary_jets_eq_limits hzero hderiv hlim⟩

end Normed

end NavierStokes.SpacetimeEndpoint
