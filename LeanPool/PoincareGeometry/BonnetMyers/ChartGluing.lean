/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.CurveConnection

/-!
# Coordinate-chart gluing for local geodesics

This module supplies the analytic chart-transition facts used to pass a
geodesic curve from one extended chart to an overlapping one.  In particular,
it keeps the two genuinely different issues separate:

* a smooth change of coordinates transports both a coordinate curve and its
  velocity; and
* the tangent vector represented by those new coordinates is the actual
  manifold derivative of the same curve.

The subsequent local uniqueness theorem will combine these facts with the
intrinsic zero-acceleration bridge in `CurveConnection`.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

namespace CurveConnection

/-! ### Ordinary coordinate calculus -/

section Calculus

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The velocity of a curve after an ordinary smooth coordinate change. -/
theorem hasDerivAt_comp_fderiv_apply
    {φ : E → E} {z u : ℝ → E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (z t))
    (hz : HasDerivAt z (u t) t) :
    HasDerivAt (φ ∘ z) ((fderiv ℝ φ (z t)) (u t)) t := by
  exact hφ.hasFDerivAt.comp_hasDerivAt t hz

/-- A `C²` coordinate change transports a differentiable velocity to another
differentiable velocity.  The derivative need not be expanded here: the
intrinsic acceleration theorem supplies its coordinate equation later. -/
theorem differentiableAt_fderiv_apply
    {φ : E → E} {z u : ℝ → E} {t : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (z t))
    (hz : DifferentiableAt ℝ z t)
    (hu : DifferentiableAt ℝ u t) :
    DifferentiableAt ℝ (fun s ↦ (fderiv ℝ φ (z s)) (u s)) t := by
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) (z t) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDcomp : DifferentiableAt ℝ (fun s ↦ fderiv ℝ φ (z s)) t :=
    hD.comp t hz
  exact hDcomp.clm_apply hu

end Calculus

/-! ### Smoothness of extended-chart transitions -/

section Transition

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The transition from the extended chart based at `c₁` to that based at
`c₂` is `C²` at every point where the two chart sources overlap. -/
theorem contDiffAt_extendedChartTransition
    (c₁ c₂ : M) {y : M}
    (hy₁ : y ∈ (extChartAt I c₁).source)
    (hy₂ : y ∈ (extChartAt I c₂).source) :
    ContDiffAt ℝ 2 ((extChartAt I c₂) ∘ (extChartAt I c₁).symm)
      (extChartAt I c₁ y) := by
  have hz : extChartAt I c₁ y ∈ (extChartAt I c₁).target :=
    (extChartAt I c₁).map_source hy₁
  have hsymmWithin : ContMDiffWithinAt 𝓘(ℝ, E) I 2
      (extChartAt I c₁).symm (extChartAt I c₁).target (extChartAt I c₁ y) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) (n := (2 : WithTop ℕ∞))
      (x := c₁) (y := extChartAt I c₁ y) hz
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2
      (extChartAt I c₁).symm (extChartAt I c₁ y) :=
    hsymmWithin.contMDiffAt (extChartAt_target_mem_nhds' (I := I) hz)
  have hchart0 : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I c₂) y := by
    exact contMDiffAt_extChartAt' (I := I) (n := (2 : WithTop ℕ∞)) (x := c₂)
      (x' := y) (by rw [← extChartAt_source (I := I) c₂]; exact hy₂)
  have hchart : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I c₂)
      ((extChartAt I c₁).symm (extChartAt I c₁ y)) := by
    rw [(extChartAt I c₁).left_inv hy₁]
    exact hchart0
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      ((extChartAt I c₂) ∘ (extChartAt I c₁).symm) (extChartAt I c₁ y) := by
    exact hchart.comp (extChartAt I c₁ y) hsymm
  exact hcomp.contDiffAt

end Transition

/-! ### Reading a coordinate velocity in the tangent fibre -/

section TangentReadout

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- On a chart source, the existing coordinate-frame combination is exactly
the derivative of the inverse extended chart, with the model tangent-space
identification made explicit. -/
theorem coordinateFrameCombination_eq_mfderiv_symm_apply
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (u : E) {y : M} (hy : y ∈ (extChartAt I x₀).source) :
    LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y =
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (extChartAt I x₀ y))
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
          (extChartAt I x₀ y)).symm u) := by
  let e := trivializationAt E TM x₀
  have hybase : y ∈ e.baseSet := by
    change y ∈ (trivializationAt E TM x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) x₀]
    rw [← extChartAt_source (I := I) x₀]
    exact hy
  have hclm_inj : Function.Injective (e.continuousLinearMapAt ℝ y) := by
    intro p q hpq
    calc
      p = e.symmL ℝ y (e.continuousLinearMapAt ℝ y p) :=
        (e.symmL_continuousLinearMapAt hybase p).symm
      _ = e.symmL ℝ y (e.continuousLinearMapAt ℝ y q) := by rw [hpq]
      _ = q := e.symmL_continuousLinearMapAt hybase q
  have hframe : ∀ i, e.localFrame b i y = e.symmL ℝ y (b i) := by
    intro i
    apply hclm_inj
    calc
      e.continuousLinearMapAt ℝ y (e.localFrame b i y) =
          e.continuousLinearMapAt ℝ y
            ((e.linearEquivAt ℝ y hybase).symm (b i)) := by
              rw [e.localFrame_apply_of_mem_baseSet b hybase]
              congr 1
      _ = b i := by
        rw [e.continuousLinearMapAt_apply_of_mem ℝ hybase]
        exact (e.linearEquivAt ℝ y hybase).apply_symm_apply (b i)
      _ = e.continuousLinearMapAt ℝ y (e.symmL ℝ y (b i)) :=
        (e.continuousLinearMapAt_symmL hybase (b i)).symm
  change (∑ i, (b.repr u i) • e.localFrame b i y) = _
  rw [show (∑ i, (b.repr u i) • e.localFrame b i y) =
      ∑ i, (b.repr u i) • e.symmL ℝ y (b i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hframe i]]
  have hcomb : ∑ i, (b.repr u i) • e.symmL ℝ y (b i) = e.symmL ℝ y u := by
    apply hclm_inj
    calc
      e.continuousLinearMapAt ℝ y
          (∑ i, (b.repr u i) • e.symmL ℝ y (b i)) =
          ∑ i, (b.repr u i) • e.continuousLinearMapAt ℝ y
            (e.symmL ℝ y (b i)) := by
              rw [map_sum]
              simp only [map_smul]
      _ = ∑ i, (b.repr u i) • b i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [e.continuousLinearMapAt_symmL hybase (b i)]
      _ = u := b.sum_repr u
      _ = e.continuousLinearMapAt ℝ y (e.symmL ℝ y u) :=
        (e.continuousLinearMapAt_symmL hybase u).symm
  rw [hcomb]
  change e.symmL ℝ y u = _
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ)
    (x₀ := x₀) (x := y) (by rw [← extChartAt_source (I := I) x₀]; exact hy)]
  rfl

/-- A coordinate curve with velocity `u` has the manifold derivative whose
tangent-fibre value is the coordinate-frame combination of `u`. -/
theorem hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (z : ℝ → E) {t : ℝ} {u : E}
    (hz : z t ∈ (extChartAt I x₀).target)
    (hderiv : HasDerivAt z u t) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I ((extChartAt I x₀).symm ∘ z) t
      (timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b u ((extChartAt I x₀).symm (z t)))) := by
  have hcoord : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) z t
      (ContinuousLinearMap.toSpanSingleton ℝ u) :=
    hderiv.hasFDerivAt.hasMFDerivAt
  have hsymmWithin : HasMFDerivWithinAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm
      (range (I : H → E)) (z t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (z t)) := by
    exact (mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := x₀) (z := z t) hz).hasMFDerivWithinAt
  have hsymm : HasMFDerivAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm (z t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (z t)) := by
    apply hsymmWithin.hasMFDerivAt
    rw [I.range_eq_univ]
    exact Filter.univ_mem
  have hcomp := hsymm.comp t hcoord
  have hy : (extChartAt I x₀).symm (z t) ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hframe := coordinateFrameCombination_eq_mfderiv_symm_apply
    (I := I) (M := M) x₀ b u hy
  have hmap :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (z t)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ u =
      CurveConnection.timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b u ((extChartAt I x₀).symm (z t))) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    have hright : (extChartAt I x₀) ((extChartAt I x₀).symm (z t)) = z t :=
      (extChartAt I x₀).right_inv hz
    rw [hright] at hframe
    change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (z t))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E) (z t)).symm (s • u)) = _
    rw [(NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E) (z t)).symm.map_smul]
    rw [map_smul, hframe]
  exact hcomp.congr_mfderiv hmap

end TangentReadout

/-! ### Local uniqueness for recharted second-order data -/

section ODEUniqueness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A coordinate pair which has the same initial data as a local chart
solution and satisfies the same second-order system agrees with that solution
as a germ. -/
theorem secondOrder_pair_eventuallyEq_localChartSolution
    {F : E → E → E} {c : M} {u₀ : E}
    (z u : ℝ → E)
    (sol : LocalChartSecondOrderSolution I F c u₀)
    (hF : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q)
      (extChartAt I c c, u₀))
    (hinitial : (z 0, u 0) = (extChartAt I c c, u₀))
    (hpair : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t) :
    (fun t ↦ (z t, u t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ (sol.coordinate t, sol.velocity t)) := by
  obtain ⟨K, S, hS, hK⟩ := hF.exists_lipschitzOnWith
  let pair : ℝ → E × E := fun t ↦ (z t, u t)
  let solPair : ℝ → E × E := fun t ↦ (sol.coordinate t, sol.velocity t)
  have hpairZero : HasDerivAt pair (secondOrderSystem F (pair 0)) 0 := by
    exact Filter.Eventually.self_of_nhds
      (p := fun t : ℝ => HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t) hpair
  have hsolZeroMem : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hsolZero : HasDerivAt solPair
      (secondOrderSystem F (solPair 0)) 0 := by
    simpa [solPair] using sol.pair_hasDerivAt hsolZeroMem
  have hpairInitial : pair 0 = (extChartAt I c c, u₀) := by
    exact hinitial
  have hsolInitial : solPair 0 = (extChartAt I c c, u₀) := by
    simp [solPair, sol.coordinate_initial, sol.velocity_initial]
  have hpairMem : pair ⁻¹' S ∈ 𝓝 (0 : ℝ) := by
    have : S ∈ 𝓝 (pair 0) := by rwa [hpairInitial]
    exact hpairZero.continuousAt.preimage_mem_nhds this
  have hsolMem : solPair ⁻¹' S ∈ 𝓝 (0 : ℝ) := by
    have : S ∈ 𝓝 (solPair 0) := by rwa [hsolInitial]
    exact hsolZero.continuousAt.preimage_mem_nhds this
  have hsolInterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [sol.radius_pos]) (by linarith [sol.radius_pos])
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt pair (secondOrderSystem F (pair t)) t ∧ pair t ∈ S := by
    filter_upwards [hpair, hpairMem] with t ht hmem
    exact ⟨by simpa [pair] using ht, hmem⟩
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt solPair (secondOrderSystem F (solPair t)) t ∧ solPair t ∈ S := by
    filter_upwards [hsolInterval, hsolMem] with t ht hmem
    exact ⟨by simpa [solPair] using sol.pair_hasDerivAt ht, hmem⟩
  have hv : ∀ᶠ t in 𝓝 (0 : ℝ), LipschitzOnWith K (secondOrderSystem F) S :=
    Filter.Eventually.of_forall (fun _ ↦ hK)
  have heq : pair 0 = solPair 0 := hpairInitial.trans hsolInitial.symm
  exact ODE_solution_unique_of_eventually
    (v := fun _ q ↦ secondOrderSystem F q) (s := fun _ ↦ S)
    (f := pair) (g := solPair) (t₀ := 0) hv hf hg heq

end ODEUniqueness

/-! ### Neighbourhood-germ bookkeeping -/

section NeighbourhoodGerms

/-- If a set is a neighbourhood of a point, then it is a neighbourhood of
every point in some neighbourhood.  This makes the nested germ hypotheses in
the recharting theorem explicit without assuming agreement sets themselves
are open. -/
theorem eventually_mem_nhds_of_mem_nhds
    {X : Type u} [TopologicalSpace X] {x : X} {s : Set X}
    (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, s ∈ 𝓝 y := by
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hs
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  exact Filter.mem_of_superset (hUopen.mem_nhds hy) hUsub

/-- A neighbourhood set remains eventually true in a neighbourhood of every
nearby point. -/
theorem eventually_eventually_mem_of_mem_nhds
    {X : Type u} [TopologicalSpace X] {x : X} {s : Set X}
    (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, z ∈ s := by
  exact eventually_mem_nhds_of_mem_nhds hs

end NeighbourhoodGerms

/-! ### Reexpressing an existing coordinate solution on an overlap -/

section Recharting

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- The coordinate curve of `sol`, read through the extended chart based at
`c`.  It is defined globally as a function, but its calculus properties are
only used where the two chart sources overlap. -/
def rechartCoordinate
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) : ℝ → E :=
  ((extChartAt I c) ∘ (extChartAt I p).symm) ∘ sol.coordinate

/-- The coordinates in chart `c` of an arbitrary model-fibre tangent field
along `sol`.  This is the linear differential of the chart transition, so it
specializes to `rechartVelocity` when the supplied field is the coordinate
velocity of `sol`, but it also applies to a parallel-transport solution. -/
def rechartTangent
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (w : ℝ → E) (c : M) : ℝ → E :=
  fun t ↦ (fderiv ℝ ((extChartAt I c) ∘ (extChartAt I p).symm)
    (sol.coordinate t)) (w t)

/-- The corresponding coordinate velocity, obtained by differentiating the
chart transition. -/
def rechartVelocity
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) : ℝ → E :=
  rechartTangent (I := I) (M := M) sol sol.velocity c

@[simp] theorem rechartTangent_velocity
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) :
    rechartTangent (I := I) (M := M) sol sol.velocity c =
      rechartVelocity (I := I) (M := M) sol c := rfl

theorem rechartTransition_contDiffAt
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    ContDiffAt ℝ 2 ((extChartAt I c) ∘ (extChartAt I p).symm)
      (sol.coordinate t) := by
  have hp : LocalChartSecondOrderSolution.curve sol t ∈
      (extChartAt I p).source := by
    rw [LocalChartSecondOrderSolution.curve]
    exact (extChartAt I p).map_target (sol.coordinate_mem_target t ht)
  rw [← LocalChartSecondOrderSolution.curve_eq_chart sol ht]
  exact contDiffAt_extendedChartTransition (I := I) p c hp hc

theorem rechartCoordinate_hasDerivAt
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    HasDerivAt (rechartCoordinate (I := I) (M := M) sol c)
      (rechartVelocity (I := I) (M := M) sol c t) t := by
  let φ := (extChartAt I c) ∘ (extChartAt I p).symm
  have hφ : ContDiffAt ℝ 2 φ (sol.coordinate t) :=
    rechartTransition_contDiffAt (I := I) (M := M) sol c ht hc
  change HasDerivAt (φ ∘ sol.coordinate)
    ((fderiv ℝ φ (sol.coordinate t)) (sol.velocity t)) t
  exact hasDerivAt_comp_fderiv_apply (hφ.differentiableAt (by norm_num))
    (sol.coordinate_hasDeriv t ht)

theorem rechartVelocity_differentiableAt
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    DifferentiableAt ℝ (rechartVelocity (I := I) (M := M) sol c) t := by
  let φ := (extChartAt I c) ∘ (extChartAt I p).symm
  have hφ : ContDiffAt ℝ 2 φ (sol.coordinate t) :=
    rechartTransition_contDiffAt (I := I) (M := M) sol c ht hc
  change DifferentiableAt ℝ (fun s ↦ (fderiv ℝ φ (sol.coordinate s))
    (sol.velocity s)) t
  exact differentiableAt_fderiv_apply hφ
    (sol.coordinate_hasDeriv t ht).differentiableAt
    (sol.velocity_hasDeriv t ht).differentiableAt

/-- A differentiable tangent-field coefficient function remains
differentiable after an overlapping chart change.  The result separates the
ordinary analytic recharting of a transported vector from the later
covariant-derivative calculation that identifies its ODE. -/
theorem rechartTangent_differentiableAt
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (w : ℝ → E) (c : M) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source)
    (hw : DifferentiableAt ℝ w t) :
    DifferentiableAt ℝ (rechartTangent (I := I) (M := M) sol w c) t := by
  let φ := (extChartAt I c) ∘ (extChartAt I p).symm
  have hφ : ContDiffAt ℝ 2 φ (sol.coordinate t) :=
    rechartTransition_contDiffAt (I := I) (M := M) sol c ht hc
  change DifferentiableAt ℝ (fun s ↦ (fderiv ℝ φ (sol.coordinate s)) (w s)) t
  exact differentiableAt_fderiv_apply hφ
    (sol.coordinate_hasDeriv t ht).differentiableAt hw

/-- Reading a source-chart tangent coefficient through an overlapping target
trivialization is exactly the ordinary derivative of the chart transition.
The proof realizes the coefficient as the derivative of a short affine
coordinate curve, compares its two manifold derivatives, and only then
reads the resulting tangent vector in the target chart.  This avoids treating
model tangent spaces as definitionally interchangeable across charts. -/
theorem rechartTangent_eq_trivialization_readout_of_coordinateFrameCombination
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (w : ℝ → E) (c : M) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    rechartTangent (I := I) (M := M) sol w c t =
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (LocalChartSecondOrderSolution.curve sol t)
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := p) bsource (w t) (LocalChartSecondOrderSolution.curve sol t)) := by
  let z : ℝ → E := fun s ↦ sol.coordinate t + (s - t) • w t
  let φ : E → E := (extChartAt I c) ∘ (extChartAt I p).symm
  have hzt : z t = sol.coordinate t := by simp [z]
  have hsourceP : (extChartAt I p).symm (z t) ∈ (extChartAt I c).source := by
    rw [hzt]
    change LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source
    exact hc
  have hzP : z t ∈ (extChartAt I p).target := by
    rw [hzt]
    exact sol.coordinate_mem_target t ht
  have hφz : (φ ∘ z) t ∈ (extChartAt I c).target := by
    change (extChartAt I c) ((extChartAt I p).symm (z t)) ∈
      (extChartAt I c).target
    exact (extChartAt I c).map_source hsourceP
  have hline : HasDerivAt z (w t) t := by
    change HasDerivAt (fun s ↦ sol.coordinate t + (s - t) • w t) (w t) t
    convert (hasDerivAt_const t (sol.coordinate t)).add
      (((hasDerivAt_id' t).sub_const t).smul_const (w t)) using 1 <;> simp
  have hφdiff : DifferentiableAt ℝ φ (z t) := by
    change DifferentiableAt ℝ ((extChartAt I c) ∘ (extChartAt I p).symm) (z t)
    rw [hzt]
    exact (rechartTransition_contDiffAt (I := I) (M := M) sol c ht hc).differentiableAt
      (by norm_num)
  have hφline : HasDerivAt (φ ∘ z) ((fderiv ℝ φ (z t)) (w t)) t :=
    hasDerivAt_comp_fderiv_apply hφdiff hline
  have hsourceDeriv := hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) p bsource z hzP hline
  have htargetDeriv := hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) c btarget (φ ∘ z) hφz hφline
  have hzcont : ContinuousAt z t := hline.continuousAt
  have hinvcont : ContinuousAt ((extChartAt I p).symm ∘ z) t :=
    (continuousAt_extChartAt_symm'' hzP).comp hzcont
  have hnear : ∀ᶠ s in 𝓝 t, (extChartAt I p).symm (z s) ∈
      (extChartAt I c).source :=
    hinvcont.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) c).mem_nhds hsourceP)
  have heq : ((extChartAt I p).symm ∘ z) =ᶠ[𝓝 t]
      ((extChartAt I c).symm ∘ (φ ∘ z)) := by
    filter_upwards [hnear] with s hs
    change (extChartAt I p).symm (z s) =
      (extChartAt I c).symm ((extChartAt I c) ((extChartAt I p).symm (z s)))
    exact ((extChartAt I c).left_inv hs).symm
  have hsourceDeriv' := hsourceDeriv.congr_of_eventuallyEq heq.symm
  have hmaps := htargetDeriv.mfderiv.symm.trans hsourceDeriv'.mfderiv
  have hbaseP : (extChartAt I p).symm (z t) =
      LocalChartSecondOrderSolution.curve sol t := by
    change (extChartAt I p).symm (z t) = (extChartAt I p).symm (sol.coordinate t)
    rw [hzt]
  have hbaseC : (extChartAt I c).symm ((φ ∘ z) t) =
      LocalChartSecondOrderSolution.curve sol t := by
    change (extChartAt I c).symm
      ((extChartAt I c) ((extChartAt I p).symm (z t))) = _
    rw [(extChartAt I c).left_inv hsourceP]
    exact hbaseP
  have hfield :
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) btarget (rechartTangent (I := I) (M := M) sol w c t)
        (LocalChartSecondOrderSolution.curve sol t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := p) bsource (w t) (LocalChartSecondOrderSolution.curve sol t) := by
    have hfieldCast := timeTangentMap_injective (I := I)
      (x := (extChartAt I c).symm ((φ ∘ z) t)) t hmaps
    rw [hbaseP, hbaseC] at hfieldCast
    simpa [rechartTangent, φ, hzt] using hfieldCast
  have hcchart : LocalChartSecondOrderSolution.curve sol t ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact hc
  have hread :
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (LocalChartSecondOrderSolution.curve sol t)
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) btarget (rechartTangent (I := I) (M := M) sol w c t)
          (LocalChartSecondOrderSolution.curve sol t)) =
      rechartTangent (I := I) (M := M) sol w c t := by
    rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) c btarget hcchart]
    exact (trivializationAt E (TangentSpace I : M → Type _) c)
      |>.continuousLinearMapAt_symmL hcchart _
  calc
    rechartTangent (I := I) (M := M) sol w c t =
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (LocalChartSecondOrderSolution.curve sol t)
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := c) btarget (rechartTangent (I := I) (M := M) sol w c t)
            (LocalChartSecondOrderSolution.curve sol t)) := hread.symm
    _ = _ := by rw [hfield]

/-- The target-chart coordinate frame built from a recharted tangent
coefficient is the same actual tangent vector as the original source-chart
coordinate frame.  This is the fibre-valued version of
`rechartTangent_eq_trivialization_readout_of_coordinateFrameCombination`,
suited to transporting covariant-derivative certificates between charts. -/
theorem rechartTangent_coordinateFrameCombination_eq
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (w : ℝ → E) (c : M) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
      (x₀ := c) btarget (rechartTangent (I := I) (M := M) sol w c t)
      (LocalChartSecondOrderSolution.curve sol t) =
    LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
      (x₀ := p) bsource (w t) (LocalChartSecondOrderSolution.curve sol t) := by
  let e := trivializationAt E (TangentSpace I : M → Type _) c
  have hcchart : LocalChartSecondOrderSolution.curve sol t ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact hc
  have hcbase : LocalChartSecondOrderSolution.curve sol t ∈ e.baseSet := by
    dsimp [e]
    exact hcchart
  have hinj : Function.Injective
      (e.continuousLinearMapAt ℝ (LocalChartSecondOrderSolution.curve sol t)) := by
    intro u v huv
    calc
      u = e.symmL ℝ (LocalChartSecondOrderSolution.curve sol t)
          (e.continuousLinearMapAt ℝ (LocalChartSecondOrderSolution.curve sol t) u) :=
        (e.symmL_continuousLinearMapAt hcbase u).symm
      _ = e.symmL ℝ (LocalChartSecondOrderSolution.curve sol t)
          (e.continuousLinearMapAt ℝ (LocalChartSecondOrderSolution.curve sol t) v) := by
        rw [huv]
      _ = v := e.symmL_continuousLinearMapAt hcbase v
  apply hinj
  have htarget : e.continuousLinearMapAt ℝ (LocalChartSecondOrderSolution.curve sol t)
      (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) btarget (rechartTangent (I := I) (M := M) sol w c t)
        (LocalChartSecondOrderSolution.curve sol t)) =
      rechartTangent (I := I) (M := M) sol w c t := by
    rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) c btarget hcchart]
    exact e.continuousLinearMapAt_symmL hcbase _
  have hread := rechartTangent_eq_trivialization_readout_of_coordinateFrameCombination
    (I := I) (M := M) sol bsource btarget w c ht hc
  exact htarget.trans hread

theorem inverse_rechartCoordinate_eventuallyEq_curve
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    ((extChartAt I c).symm ∘ rechartCoordinate (I := I) (M := M) sol c) =ᶠ[𝓝 t]
      LocalChartSecondOrderSolution.curve sol := by
  have hcont : ContinuousAt (LocalChartSecondOrderSolution.curve sol) t :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt sol ht).continuousAt
  have hsource : {s | LocalChartSecondOrderSolution.curve sol s ∈
      (extChartAt I c).source} ∈ 𝓝 t :=
    hcont.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) c).mem_nhds hc)
  have hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 t :=
    Ioo_mem_nhds ht.1 ht.2
  filter_upwards [hsource, hinterval] with s hcs hs
  change (extChartAt I c).symm
    ((extChartAt I c) ((extChartAt I p).symm (sol.coordinate s))) =
      (extChartAt I p).symm (sol.coordinate s)
  change (extChartAt I p).symm (sol.coordinate s) ∈
    (extChartAt I c).source at hcs
  rw [(extChartAt I c).left_inv hcs]

/-- On an overlap, the derivative of the original manifold curve is represented
by the recharted velocity in the frame based at `c`. -/
theorem rechartCurve_hasMFDerivAt
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I (LocalChartSecondOrderSolution.curve sol) t
      (timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t))) := by
  have hz : rechartCoordinate (I := I) (M := M) sol c t ∈
      (extChartAt I c).target := by
    change (extChartAt I c) (LocalChartSecondOrderSolution.curve sol t) ∈
      (extChartAt I c).target
    exact (extChartAt I c).map_source hc
  have hderiv := rechartCoordinate_hasDerivAt (I := I) (M := M)
    sol c ht hc
  have hraw := hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) c b (rechartCoordinate (I := I) (M := M) sol c)
    hz hderiv
  have heq := inverse_rechartCoordinate_eventuallyEq_curve (I := I) (M := M)
    sol c ht hc
  have hpoint : ((extChartAt I c).symm ∘
      rechartCoordinate (I := I) (M := M) sol c) t =
      LocalChartSecondOrderSolution.curve sol t :=
    heq.eq_of_nhds
  have hpoint' : (extChartAt I c).symm
      (rechartCoordinate (I := I) (M := M) sol c t) =
      LocalChartSecondOrderSolution.curve sol t := by
    exact hpoint
  rw [hpoint'] at hraw
  exact hraw.congr_of_eventuallyEq heq.symm

/-- If a tangent vector is known to be the actual derivative of the source
curve, then the recharted velocity is its standard coordinate velocity in the
chart centered at that curve point. -/
theorem rechartVelocity_eq_coordinateVelocity_of_hasMFDerivAt
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (v : TangentSpace I (LocalChartSecondOrderSolution.curve sol t))
    (hderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve sol) t
      (ContinuousLinearMap.toSpanSingleton ℝ v)) :
    rechartVelocity (I := I) (M := M) sol
      (LocalChartSecondOrderSolution.curve sol t) t =
    LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      (LocalChartSecondOrderSolution.curve sol t) v := by
  let c := LocalChartSecondOrderSolution.curve sol t
  have hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source := by
    dsimp [c]
    exact mem_extChartAt_source (I := I) _
  have hrec := rechartCurve_hasMFDerivAt
    (I := I) (M := M) sol c b ht hc
  have hmaps : timeTangentMap (I := I) t
      (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
        (LocalChartSecondOrderSolution.curve sol t)) =
      ContinuousLinearMap.toSpanSingleton ℝ v :=
    hrec.mfderiv.symm.trans hderiv.mfderiv
  rw [timeTangentMap_eq_toSpanSingleton] at hmaps
  have hcomb : LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
      (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
      (LocalChartSecondOrderSolution.curve sol t) = v := by
    have hone := congrArg (fun f => f 1) hmaps
    change (1 : ℝ) •
        LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t) = (1 : ℝ) • v at hone
    simpa using hone
  have hcoordinate : LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      c (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t) c) =
      rechartVelocity (I := I) (M := M) sol c t := by
    rw [LocalGeodesicData.coordinateVelocity,
      LocalGeodesicData.coordinateFrameCombination_eq_symmL (I := I) (M := M)
        c b (mem_chart_source H c)]
    let e := trivializationAt E (TangentSpace I : M → Type _) c
    change e.continuousLinearMapAt ℝ c (e.symmL ℝ c
      (rechartVelocity (I := I) (M := M) sol c t)) = _
    exact e.continuousLinearMapAt_symmL
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) c) _
  dsimp [c] at hcomb hcoordinate ⊢
  rw [← hcomb]
  exact hcoordinate.symm

/-- The same velocity identification holds in any overlapping extended chart,
read through that chart's tangent-bundle trivialization. -/
theorem rechartVelocity_eq_trivialization_readout_of_hasMFDerivAt
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {F : E → E → E} {p : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F p v₀)
    (c : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hc : LocalChartSecondOrderSolution.curve sol t ∈ (extChartAt I c).source)
    (v : TangentSpace I (LocalChartSecondOrderSolution.curve sol t))
    (hderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve sol) t
      (ContinuousLinearMap.toSpanSingleton ℝ v)) :
    rechartVelocity (I := I) (M := M) sol c t =
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (LocalChartSecondOrderSolution.curve sol t) v := by
  have hrec := rechartCurve_hasMFDerivAt
    (I := I) (M := M) sol c b ht hc
  have hmaps : timeTangentMap (I := I) t
      (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
        (LocalChartSecondOrderSolution.curve sol t)) =
      ContinuousLinearMap.toSpanSingleton ℝ v :=
    hrec.mfderiv.symm.trans hderiv.mfderiv
  rw [timeTangentMap_eq_toSpanSingleton] at hmaps
  have hcomb : LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
      (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
      (LocalChartSecondOrderSolution.curve sol t) = v := by
    have hone := congrArg (fun f => f 1) hmaps
    change (1 : ℝ) •
        LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t) = (1 : ℝ) • v at hone
    simpa using hone
  have hc' : LocalChartSecondOrderSolution.curve sol t ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact hc
  have hcoordinate :
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (LocalChartSecondOrderSolution.curve sol t)
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t)) =
      rechartVelocity (I := I) (M := M) sol c t := by
    rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL (I := I) (M := M)
      c b hc']
    let e := trivializationAt E (TangentSpace I : M → Type _) c
    change e.continuousLinearMapAt ℝ (LocalChartSecondOrderSolution.curve sol t)
      (e.symmL ℝ (LocalChartSecondOrderSolution.curve sol t)
        (rechartVelocity (I := I) (M := M) sol c t)) = _
    exact e.continuousLinearMapAt_symmL
      (by simpa [e] using hc') _
  calc
    rechartVelocity (I := I) (M := M) sol c t =
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (LocalChartSecondOrderSolution.curve sol t)
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := c) b (rechartVelocity (I := I) (M := M) sol c t)
            (LocalChartSecondOrderSolution.curve sol t)) := hcoordinate.symm
    _ = (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (LocalChartSecondOrderSolution.curve sol t) v := by
      rw [hcomb]

/-! ### Transporting the intrinsic zero equation -/

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]

/-- On an overlap, the smooth-frame velocities in the old and new chart are
the same tangent vector.  This is proved from their common manifold
derivative, rather than by identifying chart coefficients by hand. -/
theorem rechart_frameField_eq_source_frameField
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hsource : LocalChartSecondOrderSolution.curve sol t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : LocalChartSecondOrderSolution.curve sol t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget) :
    IntrinsicAcceleration.frameField (I := I) (M := M) btarget
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i)
      (rechartVelocity (I := I) (M := M) sol c t)
      (LocalChartSecondOrderSolution.curve sol t) =
    IntrinsicAcceleration.frameField (I := I) (M := M) bsource
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
      (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t) := by
  apply timeTangentMap_injective (I := I) t
  have htargetFrame := frameField_eq_coordinateFrameCombination_of_mem_agreement
    (I := I) (M := M) c btarget
      (rechartVelocity (I := I) (M := M) sol c t) htarget
  have hsourceFrame := frameField_eq_coordinateFrameCombination_of_mem_agreement
    (I := I) (M := M) p bsource (sol.velocity t) hsource
  have htargetDeriv := rechartCurve_hasMFDerivAt (I := I) (M := M)
    sol c btarget ht htarget.1
  have hsourceRaw := LocalGeodesicData.curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov p bsource sol ht
  have hsourceDeriv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve sol) t
      (timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := p) bsource (sol.velocity t)
          (LocalChartSecondOrderSolution.curve sol t))) := by
    rw [timeTangentMap_eq_toSpanSingleton]
    exact hsourceRaw
  rw [htargetFrame, hsourceFrame]
  calc
    timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) btarget (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t)) =
      mfderiv (𝓘(ℝ, ℝ)) I (LocalChartSecondOrderSolution.curve sol) t :=
        htargetDeriv.mfderiv.symm
    _ = timeTangentMap (I := I) t
        (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := p) bsource (sol.velocity t)
          (LocalChartSecondOrderSolution.curve sol t)) :=
        hsourceDeriv.mfderiv

/-- The time-dependent frame field after recharting agrees, as a germ, with
the old frame field whenever both smooth-frame agreement neighbourhoods are
available. -/
theorem rechart_timeFrameField_eq_source_timeFrameField
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {t : ℝ}
    (hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 t)
    (hsource : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget) :
    (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) btarget
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i)
      (rechartVelocity (I := I) (M := M) sol c) s
      (LocalChartSecondOrderSolution.curve sol s)) =ᶠ[𝓝 t]
    (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
      sol.velocity s (LocalChartSecondOrderSolution.curve sol s)) := by
  filter_upwards [hinterval, hsource, htarget] with s hs hsrc htgt
  change IntrinsicAcceleration.frameField (I := I) (M := M) btarget
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i)
      (rechartVelocity (I := I) (M := M) sol c s)
      (LocalChartSecondOrderSolution.curve sol s) =
    IntrinsicAcceleration.frameField (I := I) (M := M) bsource
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s)
  exact rechart_frameField_eq_source_frameField (I := I) (M := M) cov
    bsource btarget sol c hs hsrc htgt

/-- An intrinsic zero-acceleration certificate in the source chart forces the
ordinary coordinate geodesic equation in every overlapping target chart.
This is the chart-transformation theorem used by local uniqueness and gluing. -/
theorem rechart_coordinateCovariantAcceleration_eq_zero_of_intrinsic_zero
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hsource : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
        sol.velocity s (LocalChartSecondOrderSolution.curve sol s)) t
      (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) 0) :
    LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
      cov c btarget (rechartCoordinate (I := I) (M := M) sol c t)
      (rechartVelocity (I := I) (M := M) sol c t)
      (deriv (rechartVelocity (I := I) (M := M) sol c) t) = 0 := by
  have hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 t :=
    Ioo_mem_nhds ht.1 ht.2
  have htime := rechart_timeFrameField_eq_source_timeFrameField
    (I := I) (M := M) cov bsource btarget sol c hinterval hsource htarget
  have hpoint := htime.eq_of_nhds
  change IntrinsicAcceleration.frameField (I := I) (M := M) btarget
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i)
      (rechartVelocity (I := I) (M := M) sol c t)
      (LocalChartSecondOrderSolution.curve sol t) =
    IntrinsicAcceleration.frameField (I := I) (M := M) bsource
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
      (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t) at hpoint
  have hzero' := hzero.congr_of_eventuallyEq htime.symm
  rw [← hpoint] at hzero'
  have htargetAt : LocalChartSecondOrderSolution.curve sol t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget :=
    Filter.Eventually.self_of_nhds
      (p := fun s : ℝ => LocalChartSecondOrderSolution.curve sol s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
      htarget
  have hu : HasDerivAt (rechartVelocity (I := I) (M := M) sol c)
      (deriv (rechartVelocity (I := I) (M := M) sol c) t) t :=
    (rechartVelocity_differentiableAt (I := I) (M := M) sol c ht htargetAt.1).hasDerivAt
  have hcoeff : ∀ i, HasDerivAt (fun s ↦ btarget.repr
      (rechartVelocity (I := I) (M := M) sol c s) i)
      (btarget.repr (deriv (rechartVelocity (I := I) (M := M) sol c) t) i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (btarget.coord i).toContinuousLinearMap) 0 t :=
      hasDerivAt_const t (btarget.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hu
  have hframe := frameField_eq_coordinateFrameCombination_of_mem_agreement
    (I := I) (M := M) c btarget
      (rechartVelocity (I := I) (M := M) sol c t) htargetAt
  have hcurveRaw := rechartCurve_hasMFDerivAt (I := I) (M := M)
    sol c btarget ht htargetAt.1
  have hcurve : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve sol) t
      (timeTangentMap (I := I) t
        (IntrinsicAcceleration.frameField (I := I) (M := M) btarget
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i)
          (rechartVelocity (I := I) (M := M) sol c t)
          (LocalChartSecondOrderSolution.curve sol t))) := by
    rw [hframe]
    exact hcurveRaw
  change LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
    cov c btarget (extChartAt I c (LocalChartSecondOrderSolution.curve sol t))
    (rechartVelocity (I := I) (M := M) sol c t)
    (deriv (rechartVelocity (I := I) (M := M) sol c) t) = 0
  exact coordinateCovariantAcceleration_eq_zero_of_intrinsic_zero
    (I := I) (M := M) cov c btarget
    (rechartVelocity (I := I) (M := M) sol c)
    (fun s ↦ deriv (rechartVelocity (I := I) (M := M) sol c) s)
    (LocalChartSecondOrderSolution.curve sol) hcurve hcoeff hmetric htargetAt rfl hzero'

/-- The recharted pair satisfies the ordinary target-coordinate ODE whenever
the source curve has intrinsic zero acceleration. -/
theorem rechartVelocity_hasDerivAt_of_intrinsic_zero
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hsource : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ s in 𝓝 t, LocalChartSecondOrderSolution.curve sol s ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
        sol.velocity s (LocalChartSecondOrderSolution.curve sol s)) t
      (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) 0) :
    HasDerivAt (rechartVelocity (I := I) (M := M) sol c)
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget
        (rechartCoordinate (I := I) (M := M) sol c t)
        (rechartVelocity (I := I) (M := M) sol c t)) t := by
  have hdiff := rechartVelocity_differentiableAt (I := I) (M := M)
    sol c ht
      (Filter.Eventually.self_of_nhds
        (p := fun s : ℝ => LocalChartSecondOrderSolution.curve sol s ∈
          IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
        htarget).1
  have hderiv : HasDerivAt (rechartVelocity (I := I) (M := M) sol c)
      (deriv (rechartVelocity (I := I) (M := M) sol c) t) t := hdiff.hasDerivAt
  have hzero' := rechart_coordinateCovariantAcceleration_eq_zero_of_intrinsic_zero
    (I := I) (M := M) cov bsource btarget sol c ht hsource htarget hmetric hzero
  have hacc : deriv (rechartVelocity (I := I) (M := M) sol c) t =
      LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget
        (rechartCoordinate (I := I) (M := M) sol c t)
        (rechartVelocity (I := I) (M := M) sol c t) := by
    rw [LocalGeodesicData.coordinateCovariantAcceleration] at hzero'
    rw [LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm]
    exact eq_neg_of_add_eq_zero_left hzero'
  rw [hacc] at hderiv
  exact hderiv

/-- After translating time by `τ`, the recharted coordinate pair solves the
target second-order system near zero.  The nested neighbourhood hypotheses
record exactly the germs needed at each nearby time. -/
theorem rechartShift_pair_eventually_hasDerivAt
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {τ : ℝ} (hτ : τ ∈ Ioo (-sol.radius) sol.radius)
    (hsource : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : ∀ᶠ r in 𝓝 τ,
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
        (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun h ↦
        (rechartCoordinate (I := I) (M := M) sol c (τ + h),
          rechartVelocity (I := I) (M := M) sol c (τ + h)))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration
          (I := I) (M := M) cov c btarget)
          (rechartCoordinate (I := I) (M := M) sol c (τ + s),
            rechartVelocity (I := I) (M := M) sol c (τ + s))) s := by
  have hshift : Filter.Tendsto (fun s : ℝ ↦ τ + s) (𝓝 0) (𝓝 τ) := by
    have hconst : ContinuousAt (fun _ : ℝ ↦ τ) 0 := continuousAt_const
    have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
    change Filter.Tendsto ((fun _ : ℝ ↦ τ) + fun s : ℝ ↦ s) (𝓝 0) (𝓝 τ)
    convert (hconst.add hid).tendsto using 1 <;> simp
  have hinterval : ∀ᶠ s in 𝓝 (0 : ℝ), τ + s ∈ Ioo (-sol.radius) sol.radius :=
    hshift.eventually (Ioo_mem_nhds hτ.1 hτ.2)
  have hsource' := hshift.eventually hsource
  have htarget' := hshift.eventually htarget
  have hzero' := hshift.eventually hzero
  filter_upwards [hinterval, hsource', htarget', hzero'] with s hs hsrc htgt hzeroAt
  have htargetAt : LocalChartSecondOrderSolution.curve sol (τ + s) ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget :=
    Filter.Eventually.self_of_nhds
      (p := fun q : ℝ => LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
      htgt
  have hadd : HasDerivAt (fun h : ℝ ↦ τ + h) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).const_add τ
  have hz := rechartCoordinate_hasDerivAt (I := I) (M := M)
    sol c hs htargetAt.1
  have hzu : HasDerivAt (fun h ↦ rechartCoordinate (I := I) (M := M)
      sol c (τ + h)) (rechartVelocity (I := I) (M := M) sol c (τ + s)) s := by
    simpa [Function.comp_def] using HasDerivAt.scomp s hz hadd
  have hu := rechartVelocity_hasDerivAt_of_intrinsic_zero
    (I := I) (M := M) cov bsource btarget sol c hs hsrc htgt hmetric hzeroAt
  have huv : HasDerivAt (fun h ↦ rechartVelocity (I := I) (M := M)
      sol c (τ + h))
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget
        (rechartCoordinate (I := I) (M := M) sol c (τ + s))
        (rechartVelocity (I := I) (M := M) sol c (τ + s))) s := by
    simpa [Function.comp_def] using HasDerivAt.scomp s hu hadd
  simpa [secondOrderSystem] using hzu.prodMk huv

/-- The time-shifted rechart agrees, as an ordinary coordinate pair, with a
local solution constructed in the target chart from the transported initial
velocity. -/
theorem rechartShift_pair_eventuallyEq_targetSolution
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {τ : ℝ} (hτ : τ ∈ Ioo (-sol.radius) sol.radius)
    (hcenter : LocalChartSecondOrderSolution.curve sol τ = c)
    (target : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget) c
      (rechartVelocity (I := I) (M := M) sol c τ))
    (hsource : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : ∀ᶠ r in 𝓝 τ,
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
        (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0) :
    (fun s ↦ (rechartCoordinate (I := I) (M := M) sol c (τ + s),
      rechartVelocity (I := I) (M := M) sol c (τ + s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ (target.coordinate s, target.velocity s)) := by
  apply secondOrder_pair_eventuallyEq_localChartSolution
    (I := I) (M := M)
  · exact LocalGeodesicData.coordinateAcceleration_system_contDiffAt
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := c) (b := btarget)
      (rechartVelocity (I := I) (M := M) sol c τ)
  · simp only [add_zero]
    apply Prod.ext
    · change (extChartAt I c) (LocalChartSecondOrderSolution.curve sol τ) =
        extChartAt I c c
      rw [hcenter]
    · rfl
  · exact rechartShift_pair_eventually_hasDerivAt
      (I := I) (M := M) cov bsource btarget sol c hτ hsource htarget hmetric hzero

/-- The preceding coordinate equality is a genuine chart-overlap gluing
statement: after time translation, the old manifold curve agrees with the
curve of the independently constructed target-chart solution. -/
theorem rechartShift_curve_eventuallyEq_targetSolution
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {τ : ℝ} (hτ : τ ∈ Ioo (-sol.radius) sol.radius)
    (hcenter : LocalChartSecondOrderSolution.curve sol τ = c)
    (target : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget) c
      (rechartVelocity (I := I) (M := M) sol c τ))
    (hsource : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource)
    (htarget : ∀ᶠ r in 𝓝 τ, ∀ᶠ q in 𝓝 r,
      LocalChartSecondOrderSolution.curve sol q ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : ∀ᶠ r in 𝓝 τ,
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
        (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0) :
    (fun s ↦ LocalChartSecondOrderSolution.curve sol (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
      LocalChartSecondOrderSolution.curve target := by
  have hpair := rechartShift_pair_eventuallyEq_targetSolution
    (I := I) (M := M) cov bsource btarget sol c hτ hcenter target
      hsource htarget hmetric hzero
  have hcoord : (fun s ↦ rechartCoordinate (I := I) (M := M) sol c (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
      target.coordinate := by
    filter_upwards [hpair] with s hs
    exact congrArg Prod.fst hs
  have hcurveAt : LocalChartSecondOrderSolution.curve sol τ ∈
      (extChartAt I c).source := by
    rw [hcenter]
    exact mem_extChartAt_source (I := I) c
  have hinverse := inverse_rechartCoordinate_eventuallyEq_curve
    (I := I) (M := M) sol c hτ hcurveAt
  have hshift : Filter.Tendsto (fun s : ℝ ↦ τ + s) (𝓝 0) (𝓝 τ) := by
    have hconst : ContinuousAt (fun _ : ℝ ↦ τ) 0 := continuousAt_const
    have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
    change Filter.Tendsto ((fun _ : ℝ ↦ τ) + fun s : ℝ ↦ s) (𝓝 0) (𝓝 τ)
    convert (hconst.add hid).tendsto using 1 <;> simp
  have hinverseShift := hinverse.comp_tendsto hshift
  filter_upwards [hcoord, hinverseShift] with s hs hcurve
  change LocalChartSecondOrderSolution.curve sol (τ + s) =
    (extChartAt I c).symm (target.coordinate s)
  have hchart : (extChartAt I c).symm
      (rechartCoordinate (I := I) (M := M) sol c (τ + s)) =
      (extChartAt I c).symm (target.coordinate s) := by
    rw [hs]
  exact hcurve.symm.trans hchart

/-- A source coordinate geodesic has, at every sufficiently small restart
time, the chart-agreement and intrinsic-zero germs required by the overlap
gluing theorem.  The source agreement set need not be open; an open witness
inside it is propagated along the continuous curve. -/
theorem local_solution_eventually_recharting_germs
    {p : M} (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p b) p v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := p) (b := b) sol)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      τ ∈ Ioo (-sol.radius) sol.radius ∧
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p b ∈
        𝓝 (LocalChartSecondOrderSolution.curve sol τ) ∧
      ∀ᶠ r in 𝓝 τ,
        IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
          (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b
            (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p b i)
            sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
          (IntrinsicAcceleration.frameField (I := I) (M := M) b
            (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p b i)
            (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0 := by
  have hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [sol.radius_pos]) (by linarith [sol.radius_pos])
  have hzero : ∀ᶠ r in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p b i)
          sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
        (IntrinsicAcceleration.frameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p b i)
          (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0 :=
    local_solution_eventually_isCovariantAccelerationAt_zero
      (I := I) (M := M) cov p b sol hsol hmetric
  have hzeroGerm := eventually_mem_nhds_of_mem_nhds hzero
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
      (I := I) (M := M) p b)
  have hzeroInterval : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcurveCont : ContinuousAt (LocalChartSecondOrderSolution.curve sol) 0 :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt sol hzeroInterval).continuousAt
  have hUAtCurve : U ∈ 𝓝 (LocalChartSecondOrderSolution.curve sol 0) := by
    rw [LocalChartSecondOrderSolution.curve_initial (I := I) (M := M) (E := E)
      (H := H) sol]
    exact hUopen.mem_nhds hpU
  have hpreU : (LocalChartSecondOrderSolution.curve sol) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hcurveCont.preimage_mem_nhds hUAtCurve
  have hsourceGerm : ∀ᶠ τ in 𝓝 (0 : ℝ),
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p b ∈
        𝓝 (LocalChartSecondOrderSolution.curve sol τ) := by
    filter_upwards [hpreU] with τ hτ
    exact Filter.mem_of_superset (hUopen.mem_nhds hτ) hUsub
  filter_upwards [hinterval, hsourceGerm, hzeroGerm] with τ hτ hsource hzeroAt
  exact ⟨hτ, hsource, hzeroAt⟩

/-- A packaged local geodesic satisfies the coordinate second-order equation
in any chart whose smooth frame agrees along its germ.  This is the
pointwise recharting bridge used for a limiting endpoint chart. -/
theorem localGeodesic_rechart_pair_hasDerivAt_at_zero
    {x₀ : M} {v₀ : TangentSpace I x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (htarget : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hmetric : cov.IsMetricCompatibleTangent) :
    HasDerivAt (fun s ↦
      (rechartCoordinate (I := I) (M := M) γ.solution c s,
        rechartVelocity (I := I) (M := M) γ.solution c s))
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
        (rechartCoordinate (I := I) (M := M) γ.solution c 0,
          rechartVelocity (I := I) (M := M) γ.solution c 0)) 0 := by
  let bsource : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hgerms := local_solution_eventually_recharting_germs
    (I := I) (M := M) cov bsource γ.solution γ.isGeodesic hmetric
  have hdata := hgerms.self_of_nhds
  have hcont : ContinuousAt (LocalChartSecondOrderSolution.curve γ.solution) 0 :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt γ.solution hdata.1).continuousAt
  have hsource : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M)
          x₀ bsource :=
    hcont.preimage_mem_nhds hdata.2.1
  have htarget0 : LocalChartSecondOrderSolution.curve γ.solution 0 ∈
      (extChartAt I c).source :=
    (htarget.self_of_nhds).1
  have hz := rechartCoordinate_hasDerivAt (I := I) (M := M)
    γ.solution c hdata.1 htarget0
  have hu := rechartVelocity_hasDerivAt_of_intrinsic_zero
    (I := I) (M := M) cov bsource btarget γ.solution c hdata.1
      hsource htarget hmetric hdata.2.2.self_of_nhds
  simpa [secondOrderSystem] using hz.prodMk hu

/-- A local source germ supplies all nested agreement hypotheses automatically,
so its recharted and time-shifted curve glues to any target-chart solution
with the transported coordinate velocity. -/
theorem rechartShift_curve_eventuallyEq_targetSolution_of_local_germs
    {p : M} (bsource btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (c : M) {τ : ℝ} (hτ : τ ∈ Ioo (-sol.radius) sol.radius)
    (hcenter : LocalChartSecondOrderSolution.curve sol τ = c)
    (target : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov c btarget) c
      (rechartVelocity (I := I) (M := M) sol c τ))
    (hsourceAt : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) p bsource ∈
        𝓝 (LocalChartSecondOrderSolution.curve sol τ))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzero : ∀ᶠ r in 𝓝 τ,
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun q ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          sol.velocity q (LocalChartSecondOrderSolution.curve sol q)) r
        (IntrinsicAcceleration.frameField (I := I) (M := M) bsource
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) p bsource i)
          (sol.velocity r) (LocalChartSecondOrderSolution.curve sol r)) 0) :
    (fun s ↦ LocalChartSecondOrderSolution.curve sol (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
      LocalChartSecondOrderSolution.curve target := by
  have hcont : ContinuousAt (LocalChartSecondOrderSolution.curve sol) τ :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt sol hτ).continuousAt
  have hsourcePre : (LocalChartSecondOrderSolution.curve sol) ⁻¹'
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) p bsource ∈ 𝓝 τ :=
    hcont.preimage_mem_nhds hsourceAt
  have hsourceNested := eventually_eventually_mem_of_mem_nhds hsourcePre
  have htargetAt : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c btarget ∈
        𝓝 (LocalChartSecondOrderSolution.curve sol τ) := by
    rw [hcenter]
    exact IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
      (I := I) (M := M) c btarget
  have htargetPre : (LocalChartSecondOrderSolution.curve sol) ⁻¹'
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget ∈ 𝓝 τ :=
    hcont.preimage_mem_nhds htargetAt
  have htargetNested := eventually_eventually_mem_of_mem_nhds htargetPre
  exact rechartShift_curve_eventuallyEq_targetSolution
    (I := I) (M := M) cov bsource btarget sol c hτ hcenter target
    hsourceNested htargetNested hmetric hzero

/-- **Chart-independent local restart.**  At every sufficiently small time,
the old curve, after translating time, agrees with every local solution of
the coordinate geodesic equation in a chart centered at the current point
and initialized with the transported coordinate velocity.  Thus the local
geodesic germ is independent of the chart used to continue it. -/
theorem local_solution_eventually_rechartShift_curve_eventuallyEq_targetSolution
    {p : M} (bsource : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := p) (b := bsource) sol)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      ∀ btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E,
      ∀ target : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov
          (LocalChartSecondOrderSolution.curve sol τ) btarget)
        (LocalChartSecondOrderSolution.curve sol τ)
        (rechartVelocity (I := I) (M := M) sol
          (LocalChartSecondOrderSolution.curve sol τ) τ),
      (fun s ↦ LocalChartSecondOrderSolution.curve sol (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
        LocalChartSecondOrderSolution.curve target := by
  have hgerms := local_solution_eventually_recharting_germs
    (I := I) (M := M) cov bsource sol hsol hmetric
  filter_upwards [hgerms] with τ hdata
  intro btarget target
  exact rechartShift_curve_eventuallyEq_targetSolution_of_local_germs
    (I := I) (M := M) cov bsource btarget sol
      (LocalChartSecondOrderSolution.curve sol τ) hdata.1 rfl target hdata.2.1 hmetric hdata.2.2

/-- The chart-independent restart theorem supplies an actual new local
coordinate solution at every sufficiently small time, not only a conditional
comparison: its curve joins the translated source curve on a neighbourhood of
the new initial time. -/
theorem local_solution_eventually_exists_recharting_target
    {p : M} (bsource : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov p bsource) p v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := p) (b := bsource) sol)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      ∃ target : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov
          (LocalChartSecondOrderSolution.curve sol τ) bsource)
        (LocalChartSecondOrderSolution.curve sol τ)
        (rechartVelocity (I := I) (M := M) sol
          (LocalChartSecondOrderSolution.curve sol τ) τ),
      (fun s ↦ LocalChartSecondOrderSolution.curve sol (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
        LocalChartSecondOrderSolution.curve target := by
  have hrestart := local_solution_eventually_rechartShift_curve_eventuallyEq_targetSolution
    (I := I) (M := M) cov bsource sol hsol hmetric
  filter_upwards [hrestart] with τ hτ
  obtain ⟨target⟩ := LocalGeodesicData.exists_local_geodesic_solution
    (I := I) (M := M) (E := E) (cov := cov)
    (x₀ := LocalChartSecondOrderSolution.curve sol τ) (b := bsource)
    (rechartVelocity (I := I) (M := M) sol
      (LocalChartSecondOrderSolution.curve sol τ) τ)
  exact ⟨target, hτ bsource target⟩

end Recharting

end CurveConnection

/-! ### Restarting packaged manifold geodesics -/

namespace IntrinsicGeodesic.LocalGeodesic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  {x₀ : M} {v₀ : TangentSpace I x₀}

private theorem localChart_curve_eq_cast_initialVelocity
    {F : E → E → E} {c : M} {u v : E} (h : u = v)
    (sol : LocalChartSecondOrderSolution I F c v) :
    LocalChartSecondOrderSolution.curve
      (Eq.mpr (congrArg (fun w ↦ LocalChartSecondOrderSolution I F c w) h) sol) =
    LocalChartSecondOrderSolution.curve sol := by
  cases h
  rfl

/-- A packaged manifold-valued local geodesic can be restarted at every
sufficiently small time with its actual tangent velocity.  The curve of the
new packaged geodesic agrees with the time-shifted original curve as a germ,
so this is a genuine chart-independent local continuation statement. -/
theorem eventually_exists_restartedLocalGeodesic
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      ∃ δ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
        (IntrinsicGeodesic.LocalGeodesic.curve γ τ)
        (IntrinsicGeodesic.LocalGeodesic.velocity γ τ),
      (fun s ↦ IntrinsicGeodesic.LocalGeodesic.curve γ (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
        IntrinsicGeodesic.LocalGeodesic.curve δ := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hgerms := CurveConnection.local_solution_eventually_recharting_germs
    (I := I) (M := M) cov b γ.solution γ.isGeodesic hmetric
  filter_upwards [hgerms] with τ hdata
  obtain ⟨δ⟩ := IntrinsicGeodesic.exists_localGeodesic
    (I := I) (M := M) cov
    (IntrinsicGeodesic.LocalGeodesic.curve γ τ)
    (IntrinsicGeodesic.LocalGeodesic.velocity γ τ)
  have hderivRaw := IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve γ hdata.1
  have hderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve γ.solution) τ
      (ContinuousLinearMap.toSpanSingleton ℝ
        (IntrinsicGeodesic.LocalGeodesic.velocity γ τ)) := by
    convert hderivRaw using 1 <;> rfl
  have hvelocity := CurveConnection.rechartVelocity_eq_coordinateVelocity_of_hasMFDerivAt
    (I := I) (M := M) γ.solution b hdata.1
    (IntrinsicGeodesic.LocalGeodesic.velocity γ τ) hderiv
  let target : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov
        (IntrinsicGeodesic.LocalGeodesic.curve γ τ) b)
      (IntrinsicGeodesic.LocalGeodesic.curve γ τ)
      (CurveConnection.rechartVelocity (I := I) (M := M) γ.solution
        (IntrinsicGeodesic.LocalGeodesic.curve γ τ) τ) :=
    Eq.mpr (congrArg (fun u ↦ LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov
        (IntrinsicGeodesic.LocalGeodesic.curve γ τ) b)
      (IntrinsicGeodesic.LocalGeodesic.curve γ τ) u) hvelocity) δ.solution
  have htargetCurve : LocalChartSecondOrderSolution.curve target =
      LocalChartSecondOrderSolution.curve δ.solution := by
    exact localChart_curve_eq_cast_initialVelocity hvelocity δ.solution
  have hglue := CurveConnection.rechartShift_curve_eventuallyEq_targetSolution_of_local_germs
    (I := I) (M := M) cov b b γ.solution
    (IntrinsicGeodesic.LocalGeodesic.curve γ τ) hdata.1 rfl target
    hdata.2.1 hmetric hdata.2.2
  have hglue' : (fun s ↦ IntrinsicGeodesic.LocalGeodesic.curve γ (τ + s)) =ᶠ[𝓝 (0 : ℝ)]
      LocalChartSecondOrderSolution.curve δ.solution := by
    filter_upwards [hglue] with s hs
    exact hs.trans (congrFun htargetCurve s)
  exact ⟨δ, by simpa [IntrinsicGeodesic.LocalGeodesic.curve] using hglue'⟩

/-- The local restart theorem is coherent at the full tangent-bundle state
level, not only at the base curve level.  This is the form used when taking
unions of compatible local geodesic pieces. -/
theorem eventually_exists_restartedLocalGeodesic_state
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      ∃ δ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
        (IntrinsicGeodesic.LocalGeodesic.curve γ τ)
        (IntrinsicGeodesic.LocalGeodesic.velocity γ τ),
      (fun s ↦
        (⟨IntrinsicGeodesic.LocalGeodesic.curve γ (τ + s),
          IntrinsicGeodesic.LocalGeodesic.velocity γ (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 (0 : ℝ)]
        fun s ↦ ⟨IntrinsicGeodesic.LocalGeodesic.curve δ s,
          IntrinsicGeodesic.LocalGeodesic.velocity δ s⟩ := by
  have hinterval : Ioo (-γ.solution.radius) γ.solution.radius ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
      (by linarith [γ.solution.radius_pos])
  have hrestart := eventually_exists_restartedLocalGeodesic γ hmetric
  filter_upwards [hinterval, hrestart] with τ hτ hdata
  obtain ⟨δ, hcurve⟩ := hdata
  refine ⟨δ, ?_⟩
  exact IntrinsicGeodesic.eventuallyEq_state_of_eventuallyEq_curve_shift
    (I := I) (M := M) γ δ hτ hcurve

end IntrinsicGeodesic.LocalGeodesic

end BonnetMyersEntry
