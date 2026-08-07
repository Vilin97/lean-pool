/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.Trace
import LeanPool.JacobianDiffgeo.Path
import LeanPool.JacobianDiffgeo.JacobianConstruction.OfCurve

/-!
# The trace–period relation (jacobian-functoriality §7, period-level form)

Unit: jacobian-functoriality. For a loop `δ` in `Y` running through regular values of `f`, the
path integral of `Tr_f η` along `δ` decomposes as a finite sum of `X`-loop integrals of `η` —
with loops *independent of `η`* — so the trace maps period vectors into `periodSubgroup X`.

Route (cheaper than the design's full `FiberChain`/monodromy construction, same conclusion):
* Over a regular value's canonical stack all sheets are unramified, so each branch chart pair
  gives a genuine local section `RS.sectionAt S i` of `f` on `S.V`.
* **Segment lemma** (`RS.pathIntegral_traceForm_segment`): for a path inside one `traceChart`
  source, `∫ Tr_f η = ∑ sheets ∫ (section∘path) η`, by exhibiting the sum of per-sheet disc
  primitives as a primitive of the trace (its chart coefficient is *literally* the sum of the
  transported sheet coefficients at regular values).
* **Chain** (`RS.TraceChain`, Lebesgue-number subdivision) + telescoping of a fixed primitive
  over the subdivision (`RS.pathIntegral_segMap`).
* **Loop closing without monodromy bookkeeping**: conjugate each sheet segment by fixed
  connecting paths from a basepoint (`PathConnectedSpace.somePath`); the correction terms are
  fibre sums *as sets*, independent of the enumerating stack, and telescope to `0` around the
  loop. No cycle decomposition, no lifted-path concatenation.
-/

open scoped ContDiff Manifold Topology unitInterval
open Set Filter Metric IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {f : X → Y}

/-! ### Local sections of `f` over a regular stack -/

/-- The `i`-th local section of `f` associated to a fibre stack (an honest section on `S.V`
when the `i`-th sheet is unramified). -/
def sectionAt {y₀ : Y} (S : RS.FiberStack f y₀) (i : Fin S.n) (y : Y) : X :=
  (S.A i).e.symm ((S.A i).e' y)

variable {y₀ : Y} {S : RS.FiberStack f y₀} {i : Fin S.n}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem e'_mem_e_target_of_regular (hm : multiplicity f (S.pt i) = 1) {y : Y} (hy : y ∈ S.V) :
    (S.A i).e' y ∈ (S.A i).e.target := by
  have hball := S.map_V_mem_ball i y hy
  have hpow : (S.A i).radius ^ multiplicity f (S.pt i) = (S.A i).radius := by
    generalize (S.A i).radius = r
    rw [hm, pow_one]
  rw [hpow] at hball
  rw [(S.A i).target_eq]
  exact hball

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem sectionAt_mem_source (hm : multiplicity f (S.pt i) = 1) {y : Y} (hy : y ∈ S.V) :
    sectionAt S i y ∈ (S.A i).e.source :=
  (S.A i).e.map_target (e'_mem_e_target_of_regular hm hy)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem e_sectionAt (hm : multiplicity f (S.pt i) = 1) {y : Y} (hy : y ∈ S.V) :
    (S.A i).e (sectionAt S i y) = (S.A i).e' y :=
  (S.A i).e.right_inv (e'_mem_e_target_of_regular hm hy)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- The sections are genuine sections: `f ∘ sectionAt S i = id` on `S.V`. -/
theorem f_sectionAt (hm : multiplicity f (S.pt i) = 1) {y : Y} (hy : y ∈ S.V) :
    f (sectionAt S i y) = y := by
  have hxs := sectionAt_mem_source hm hy
  have hpow : (S.A i).e' (f (sectionAt S i y)) = ((S.A i).e' y) ^ multiplicity f (S.pt i) := by
    rw [(S.A i).eqOn_pow _ hxs, e_sectionAt hm hy]
  have hone : ((S.A i).e' y) ^ multiplicity f (S.pt i) = (S.A i).e' y := by
    generalize (S.A i).e' y = w
    rw [hm, pow_one]
  exact (S.A i).e'.injOn ((S.A i).mapsTo hxs) (S.V_subset i hy) (by rw [hpow, hone])

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem continuousOn_sectionAt (hm : multiplicity f (S.pt i) = 1) :
    ContinuousOn (sectionAt S i) S.V := by
  apply ContinuousOn.comp ((S.A i).e.continuousOn_symm)
    (((S.A i).e'.continuousOn).mono (S.V_subset i))
  intro y hy
  exact e'_mem_e_target_of_regular hm hy

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Fibre sums over any point of a regular stack's neighborhood enumerate along the sections. -/
theorem finsum_mem_fiber_eq_sum_sectionAt (hm : ∀ j : Fin S.n, multiplicity f (S.pt j) = 1)
    {y : Y} (hy : y ∈ S.V) (t : X → ℂ) :
    ∑ᶠ x ∈ f ⁻¹' {y}, t x = ∑ j, t (sectionAt S j y) := by
  rw [← RS.MTrace.sum_traceZk_stack S hy (h := t)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : ∀ (g : ℂ → ℂ) (k : ℕ), k = 1 → ∀ w, RS.MTrace.traceZk g k w = g w := by
    rintro g k rfl w
    exact RS.MTrace.traceZk_one g w
  rw [h1 (t ∘ ⇑(S.A j).e.symm) (multiplicity f (S.pt j)) (hm j) ((S.A j).e' y)]
  rfl

/-- The lift of a path through the `i`-th section of a regular stack. -/
def liftSeg (hm : multiplicity f (S.pt i) = 1) {a b : Y} (p : Path a b)
    (hV : ∀ s : I, p s ∈ S.V) : Path (sectionAt S i a) (sectionAt S i b) where
  toFun s := sectionAt S i (p s)
  continuous_toFun := (continuousOn_sectionAt hm).comp_continuous p.continuous hV
  source' := by rw [Path.source]
  target' := by rw [Path.target]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] in
@[simp] theorem liftSeg_coe (hm : multiplicity f (S.pt i) = 1) {a b : Y} (p : Path a b)
    (hV : ∀ s : I, p s ∈ S.V) : ⇑(liftSeg hm p hV) = fun s => sectionAt S i (p s) := rfl

/-! ### The segment lemma -/

variable (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ c, ∀ x, f x = c)

/-- Multiplicities of the canonical stack at a regular value are all `1`. -/
theorem stackAt_mult_eq_one {y₀ : Y} (hy₀ : RS.IsRegularValue f y₀)
    (i : Fin (stackAt hf hne y₀).n) : multiplicity f ((stackAt hf hne y₀).pt i) = 1 :=
  multiplicity_eq_one_of_isRegularValue hf hne hy₀ ((stackAt hf hne y₀).maps_pt_eq i)

/-- **The segment lemma**: over a single (regular-centered) trace chart, the integral of the
trace is the sum of the per-sheet lifted integrals. -/
theorem pathIntegral_traceForm_segment {y₀ : Y} (hy₀ : RS.IsRegularValue f y₀)
    {a b : Y} (p : Path a b) (hV : ∀ s : I, p s ∈ (stackAt hf hne y₀).V)
    (hsrc : ∀ s : I, p s ∈ (chartAt ℂ y₀).source) (η : Form1 X) :
    pathIntegral p (traceForm hf hne η)
      = ∑ i, pathIntegral (liftSeg (stackAt_mult_eq_one hf hne hy₀ i) p hV) η := by
  set S := stackAt hf hne y₀ with hS_def
  have hm : ∀ i : Fin S.n, multiplicity f (S.pt i) = 1 := stackAt_mult_eq_one hf hne hy₀
  -- per-sheet disc primitives
  have hcoe : ∀ i : Fin S.n,
      AnalyticOnNhd ℂ (coeffIn (S.A i).e η) (Metric.ball 0 ((S.A i).radius)) := by
    intro i
    rw [← (S.A i).target_eq]
    exact η.analyticOnNhd_coeffIn (S.A i).mem_maximalAtlas
  choose g hg0 hg using fun i : Fin S.n =>
    exists_hasDerivAt_ball (hcoe i) (subset_refl _)
      (Metric.mem_ball_self ((S.radius_pos i))) (w := (0 : ℂ))
  -- extension facts
  have hextV : ∀ u : ℝ, p.extend u ∈ S.V := by
    intro u
    have hmem : p.extend u ∈ range ⇑p := by
      rw [← Path.extend_range]
      exact mem_range_self u
    obtain ⟨s, hs⟩ := hmem
    rw [← hs]
    exact hV s
  have hextsrc : ∀ u : ℝ, p.extend u ∈ (chartAt ℂ y₀).source := by
    intro u
    have hmem : p.extend u ∈ range ⇑p := by
      rw [← Path.extend_range]
      exact mem_range_self u
    obtain ⟨s, hs⟩ := hmem
    rw [← hs]
    exact hsrc s
  have hextsrc' : ∀ u : ℝ, p.extend u ∈ (traceChart hf hne y₀).source := by
    intro u
    rw [traceChart_source]
    exact ⟨hextsrc u, hextV u⟩
  -- the per-sheet primitives
  set L : (i : Fin S.n) → Path (sectionAt S i a) (sectionAt S i b) :=
    fun i => liftSeg (hm i) p hV with hL_def
  set F : Fin S.n → ℝ → ℂ := fun i u => g i ((S.A i).e' (p.extend u)) with hF_def
  have hLext : ∀ (i : Fin S.n) (u : ℝ), (L i).extend u = sectionAt S i (p.extend u) := by
    intro i u
    show (L i).extend u = sectionAt S i (p.extend u)
    unfold Path.extend IccExtend
    rfl
  have hFprim : ∀ i : Fin S.n, IsPrimitiveAlong (L i) η (F i) := by
    intro i
    have hof := isPrimitiveAlongMap_of_ball (K := (L i).extend) (s := Set.univ)
      (S.A i).mem_maximalAtlas (hg i) (fun u _ => by
        rw [hLext i u]
        refine ⟨sectionAt_mem_source (hm i) (hextV u), ?_⟩
        rw [e_sectionAt (hm i) (hextV u), ← (S.A i).target_eq]
        exact e'_mem_e_target_of_regular (hm i) (hextV u))
    apply hof.congr
    intro u _
    change g i ((S.A i).e ((L i).extend u)) = F i u
    rw [hLext i u, e_sectionAt (hm i) (hextV u)]
  -- the summed primitive is a primitive of the trace
  have hGprim : IsPrimitiveAlong p (traceForm hf hne η) (fun u => ∑ i, F i u) := by
    intro u₀ _
    refine ⟨traceChart hf hne y₀, traceChart_mem_maximalAtlas hf hne y₀, hextsrc' u₀,
      fun w => ∑ i, g i (branchTrans hf hne y₀ i w), ?_, ?_⟩
    · have hpt : (traceChart hf hne y₀) (p.extend u₀) ∈ (traceChart hf hne y₀).target :=
        (traceChart hf hne y₀).map_source (hextsrc' u₀)
      filter_upwards [(traceChart hf hne y₀).open_target.mem_nhds hpt] with w hw
      have hderiv : ∀ i : Fin S.n, HasDerivAt (fun w' => g i (branchTrans hf hne y₀ i w'))
          (coeffIn (S.A i).e η (branchTrans hf hne y₀ i w)
            * deriv (branchTrans hf hne y₀ i) w) w := by
        intro i
        have hψ : AnalyticAt ℂ (branchTrans hf hne y₀ i) w :=
          analyticAt_branchTrans hf hne y₀ hw i
        have hgd : HasDerivAt (g i) (coeffIn (S.A i).e η (branchTrans hf hne y₀ i w))
            (branchTrans hf hne y₀ i w) := by
          apply hg i
          have hball := branchTrans_mem_ball hf hne y₀ hw i
          have hpow : (S.A i).radius ^ multiplicity f (S.pt i) = (S.A i).radius := by
            generalize (S.A i).radius = r
            rw [hm i, pow_one]
          rwa [hpow] at hball
        exact hgd.comp w hψ.differentiableAt.hasDerivAt
      have hval : coeffIn (traceChart hf hne y₀) (traceForm hf hne η) w
          = ∑ i, coeffIn (S.A i).e η (branchTrans hf hne y₀ i w)
              * deriv (branchTrans hf hne y₀ i) w := by
        rw [coeffIn_traceChart_traceForm hf hne η y₀ hw]
        unfold traceCoeffFun
        apply Finset.sum_congr rfl
        intro i _
        rw [traceCoeff_eq_of_eq_one (hm i) (analyticAt_coeffIn_stack_zero hf hne η y₀ i)]
        ring
      rw [hval]
      exact HasDerivAt.fun_sum fun i _ => hderiv i
    · apply Filter.Eventually.of_forall
      intro u
      refine ⟨hextsrc' u, ?_⟩
      apply Finset.sum_congr rfl
      intro i _
      change g i ((S.A i).e' (p.extend u))
        = g i ((S.A i).e' ((chartAt ℂ y₀).symm ((chartAt ℂ y₀) (p.extend u))))
      rw [(chartAt ℂ y₀).left_inv (hextsrc u)]
  -- assemble
  rw [hGprim.pathIntegral_eq]
  have hs : ∀ i : Fin S.n, pathIntegral (L i) η = F i 1 - F i 0 :=
    fun i => (hFprim i).pathIntegral_eq
  calc (∑ i, F i 1) - ∑ i, F i 0 = ∑ i, (F i 1 - F i 0) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ i, pathIntegral (L i) η := Finset.sum_congr rfl fun i _ => (hs i).symm

/-! ### Affine segment reparametrizations and telescoping -/

/-- The affine segment `[t₀, t₁]` of a path, as a path between the extended endpoints. -/
def Path.segMap {a b : Y} (δ : Path a b) (t₀ t₁ : ℝ) : Path (δ.extend t₀) (δ.extend t₁) where
  toFun s := δ.extend ((1 - (s : ℝ)) * t₀ + (s : ℝ) * t₁)
  continuous_toFun := by
    apply δ.continuous_extend.comp
    fun_prop
  source' := by norm_num
  target' := by norm_num

omit [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
@[simp] theorem Path.segMap_coe {a b : Y} (δ : Path a b) (t₀ t₁ : ℝ) :
    ⇑(Path.segMap δ t₀ t₁) = fun s : I => δ.extend ((1 - (s : ℝ)) * t₀ + (s : ℝ) * t₁) := rfl

omit [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
theorem Path.segMap_mem_Icc {a b : Y} (_δ : Path a b) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (s : I) :
    (1 - (s : ℝ)) * t₀ + (s : ℝ) * t₁ ∈ Icc t₀ t₁ := by
  obtain ⟨hs0, hs1⟩ := s.2
  constructor
  · nlinarith
  · nlinarith

omit [T2Space Y] in
/-- The integral over an affine segment, computed by a primitive of the whole path. -/
theorem pathIntegral_segMap {a b : Y} {δ : Path a b} {η₂ : Form1 Y} {F : ℝ → ℂ}
    (hF : IsPrimitiveAlong δ η₂ F) {t₀ t₁ : ℝ} (_h₀ : 0 ≤ t₀) (_h₁ : t₁ ≤ 1) :
    pathIntegral (Path.segMap δ t₀ t₁) η₂ = F t₁ - F t₀ := by
  set ψ : ℝ → ℝ := fun u =>
    (1 - ((Set.projIcc (0 : ℝ) 1 zero_le_one u : I) : ℝ)) * t₀
      + ((Set.projIcc (0 : ℝ) 1 zero_le_one u : I) : ℝ) * t₁ with hψ_def
  have hψcont : Continuous ψ := by
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_projIcc)).mul
        continuous_const
    · exact (continuous_subtype_val.comp continuous_projIcc).mul continuous_const
  have hcomp := hF.comp (φ := ψ) (t := Set.univ) hψcont.continuousOn (mapsTo_univ _ _)
  have hKeq : Set.EqOn (δ.extend ∘ ψ) (Path.segMap δ t₀ t₁).extend Set.univ := by
    intro u _
    change δ.extend (ψ u) = (Path.segMap δ t₀ t₁).extend u
    unfold Path.extend IccExtend
    rfl
  have hprim : IsPrimitiveAlong (Path.segMap δ t₀ t₁) η₂ (F ∘ ψ) := hcomp.congr_map hKeq
  rw [hprim.pathIntegral_eq]
  have hψ1 : ψ 1 = t₁ := by
    have hp : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := by
      simp [Set.projIcc]
    change (1 - ((Set.projIcc (0 : ℝ) 1 zero_le_one 1 : I) : ℝ)) * t₀
        + ((Set.projIcc (0 : ℝ) 1 zero_le_one 1 : I) : ℝ) * t₁ = t₁
    rw [hp]
    norm_num
  have hψ0 : ψ 0 = t₀ := by
    have hp : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := by
      simp [Set.projIcc]
    change (1 - ((Set.projIcc (0 : ℝ) 1 zero_le_one 0 : I) : ℝ)) * t₀
        + ((Set.projIcc (0 : ℝ) 1 zero_le_one 0 : I) : ℝ) * t₁ = t₀
    rw [hp]
    norm_num
  rw [Function.comp_apply, Function.comp_apply, hψ0, hψ1]

/-! ### The trace chain -/

/-- A Lebesgue-number subdivision of a loop through regular values into pieces inside
single (regular-centered) trace charts. -/
structure TraceChain (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ c, ∀ x, f x = c)
    {a b : Y} (δ : Path a b) where
  /-- The number of subdivision steps. -/
  n : ℕ
  /-- The subdivision times. -/
  t : ℕ → ℝ
  ht0 : t 0 = 0
  ht1 : ∀ k, n ≤ k → t k = 1
  mono : Monotone t
  /-- The centre of each step's chart. -/
  c : ℕ → Y
  hreg : ∀ k, RS.IsRegularValue f (c k)
  maps : ∀ k, ∀ u ∈ Icc (t k) (t (k + 1)), δ.extend u ∈ (traceChart hf hne (c k)).source

/-- Existence of a trace chain along any path through regular values. -/
theorem exists_traceChain {a b : Y} (δ : Path a b)
    (hδ : ∀ s : I, RS.IsRegularValue f (δ s)) : Nonempty (TraceChain hf hne δ) := by
  have hnhds : ∀ τ : I, ∃ V : Set I, IsOpen V ∧ τ ∈ V ∧ ∃ y : Y, RS.IsRegularValue f y ∧
      ∀ u ∈ V, δ.extend (u : ℝ) ∈ (traceChart hf hne y).source := by
    intro τ
    refine ⟨(fun u : I => δ.extend (u : ℝ)) ⁻¹' (traceChart hf hne (δ τ)).source, ?_, ?_,
      δ τ, hδ τ, fun u hu => hu⟩
    · exact ((δ.continuous_extend.comp continuous_subtype_val).isOpen_preimage _
        (traceChart hf hne (δ τ)).open_source)
    · change δ.extend (τ : ℝ) ∈ (traceChart hf hne (δ τ)).source
      rw [δ.extend_apply τ.2]
      exact mem_traceChart_source_self hf hne (δ τ)
  choose V hVopen hτV y hyreg hmaps using hnhds
  obtain ⟨t, ht0, hmono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hVopen
      (fun τ _ => mem_iUnion.2 ⟨τ, hτV τ⟩)
  choose iOf hiOf using hsub
  refine ⟨⟨n, fun k => (t k : ℝ), by simp [ht0], ?_, ?_, fun k => y (iOf k),
    fun k => hyreg (iOf k), ?_⟩⟩
  · intro k hk
    simp [htn k hk]
  · intro a' b' hab
    exact hmono hab
  · intro k u hu
    have hu' : (t k : ℝ) ≤ u ∧ u ≤ (t (k + 1) : ℝ) := hu
    have hu01 : u ∈ (unitInterval : Set ℝ) :=
      ⟨(t k).2.1.trans hu'.1, hu'.2.trans (t (k + 1)).2.2⟩
    have hmem : (⟨u, hu01⟩ : I) ∈ Icc (t k) (t (k + 1)) := hu'
    have := hmaps (iOf k) _ (hiOf k hmem)
    rwa [show ((⟨u, hu01⟩ : I) : ℝ) = u from rfl] at this

/-! ### Assembly: the loop decomposition -/

variable {hf hne}
variable {a₀ b₀ : Y} {δ : Path a₀ b₀}

theorem TraceChain.t_le (C : TraceChain hf hne δ) (k : ℕ) : C.t k ≤ C.t (k + 1) :=
  C.mono (Nat.le_succ k)

theorem TraceChain.t_nonneg (C : TraceChain hf hne δ) (k : ℕ) : 0 ≤ C.t k := by
  rw [← C.ht0]
  exact C.mono (Nat.zero_le k)

theorem TraceChain.t_le_one (C : TraceChain hf hne δ) (k : ℕ) : C.t k ≤ 1 := by
  rcases le_total C.n k with h | h
  · exact (C.ht1 k h).le
  · calc C.t k ≤ C.t C.n := C.mono h
      _ = 1 := C.ht1 C.n le_rfl

theorem TraceChain.segMap_mem_source (C : TraceChain hf hne δ) (k : ℕ) (s : I) :
    (Path.segMap δ (C.t k) (C.t (k + 1))) s ∈ (traceChart hf hne (C.c k)).source := by
  change δ.extend _ ∈ _
  exact C.maps k _ (Path.segMap_mem_Icc δ (C.t_le k) s)

theorem TraceChain.segMap_mem_V (C : TraceChain hf hne δ) (k : ℕ) (s : I) :
    (Path.segMap δ (C.t k) (C.t (k + 1))) s ∈ (stackAt hf hne (C.c k)).V :=
  (traceChart_source hf hne (C.c k) ▸ C.segMap_mem_source k s).2

theorem TraceChain.segMap_mem_chart_source (C : TraceChain hf hne δ) (k : ℕ) (s : I) :
    (Path.segMap δ (C.t k) (C.t (k + 1))) s ∈ (chartAt ℂ (C.c k)).source :=
  (traceChart_source hf hne (C.c k) ▸ C.segMap_mem_source k s).1

theorem TraceChain.endpoint_mem_V₀ (C : TraceChain hf hne δ) (k : ℕ) :
    δ.extend (C.t k) ∈ (stackAt hf hne (C.c k)).V := by
  have h := C.maps k (C.t k) ⟨le_rfl, C.t_le k⟩
  rw [traceChart_source] at h
  exact h.2

theorem TraceChain.endpoint_mem_V₁ (C : TraceChain hf hne δ) (k : ℕ) :
    δ.extend (C.t (k + 1)) ∈ (stackAt hf hne (C.c k)).V := by
  have h := C.maps k (C.t (k + 1)) ⟨C.t_le k, le_rfl⟩
  rw [traceChart_source] at h
  exact h.2

/-- The `i`-th lifted sheet over the `k`-th piece of the chain. -/
def TraceChain.sheetPath (C : TraceChain hf hne δ) (k : ℕ)
    (i : Fin (stackAt hf hne (C.c k)).n) :
    Path (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))
      (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1)))) :=
  liftSeg (stackAt_mult_eq_one hf hne (C.hreg k) i) (Path.segMap δ (C.t k) (C.t (k + 1)))
    (C.segMap_mem_V k)

/-- The `(k, i)`-th sheet, closed into a based loop by fixed connecting paths. -/
def TraceChain.loop (C : TraceChain hf hne δ) (k : ℕ)
    (i : Fin (stackAt hf hne (C.c k)).n) :
    Path (Classical.arbitrary X) (Classical.arbitrary X) :=
  ((PathConnectedSpace.somePath (Classical.arbitrary X)
      (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))).trans
    (C.sheetPath k i)).trans
    (PathConnectedSpace.somePath (Classical.arbitrary X)
      (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1))))).symm

theorem TraceChain.pathIntegral_sheetPath (C : TraceChain hf hne δ) (k : ℕ)
    (i : Fin (stackAt hf hne (C.c k)).n) (η : Form1 X) :
    pathIntegral (C.sheetPath k i) η
      = pathIntegral (C.loop k i) η
        - pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
            (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))) η
        + pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
            (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1))))) η := by
  unfold TraceChain.loop
  rw [pathIntegral_trans, pathIntegral_trans, pathIntegral_symm]
  ring

/-- **The loop decomposition of the trace integral**: along a loop through regular values, the
integral of `Tr_f η` is the sum of the based-loop periods of `η` over the chain's closed sheets
(loops independent of `η`). -/
theorem pathIntegral_traceForm_eq_sum_loops {y₀ : Y} {δ : Path y₀ y₀}
    (C : TraceChain hf hne δ) (η : Form1 X) :
    pathIntegral δ (traceForm hf hne η)
      = ∑ k ∈ Finset.range C.n, ∑ i, pathIntegral (C.loop k i) η := by
  obtain ⟨F, hF, -⟩ := exists_isPrimitiveAlong δ (traceForm hf hne η)
  set A : ℕ → ℂ := fun k => ∑ᶠ x ∈ f ⁻¹' {δ.extend (C.t k)},
    pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X) x) η with hA_def
  have hpiece : ∀ k, F (C.t (k + 1)) - F (C.t k)
      = (∑ i, pathIntegral (C.loop k i) η) + (A (k + 1) - A k) := by
    intro k
    have h1 : F (C.t (k + 1)) - F (C.t k)
        = pathIntegral (Path.segMap δ (C.t k) (C.t (k + 1))) (traceForm hf hne η) :=
      (pathIntegral_segMap hF (C.t_nonneg k) (C.t_le_one (k + 1))).symm
    have h2 := pathIntegral_traceForm_segment hf hne (C.hreg k)
      (Path.segMap δ (C.t k) (C.t (k + 1))) (C.segMap_mem_V k)
      (C.segMap_mem_chart_source k) η
    have h3 : ∀ i, pathIntegral (C.sheetPath k i) η
        = pathIntegral (C.loop k i) η
          - pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
              (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))) η
          + pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
              (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1))))) η :=
      fun i => C.pathIntegral_sheetPath k i η
    have hA0 : A k = ∑ i, pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
        (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))) η :=
      finsum_mem_fiber_eq_sum_sectionAt
        (fun i => stackAt_mult_eq_one hf hne (C.hreg k) i) (C.endpoint_mem_V₀ k) _
    have hA1 : A (k + 1) = ∑ i, pathIntegral
        (PathConnectedSpace.somePath (Classical.arbitrary X)
          (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1))))) η :=
      finsum_mem_fiber_eq_sum_sectionAt
        (fun i => stackAt_mult_eq_one hf hne (C.hreg k) i) (C.endpoint_mem_V₁ k) _
    calc F (C.t (k + 1)) - F (C.t k)
        = ∑ i, pathIntegral (C.sheetPath k i) η := by rw [h1, h2]; rfl
      _ = ∑ i, (pathIntegral (C.loop k i) η
            - pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
                (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t k)))) η
            + pathIntegral (PathConnectedSpace.somePath (Classical.arbitrary X)
                (sectionAt (stackAt hf hne (C.c k)) i (δ.extend (C.t (k + 1))))) η) :=
          Finset.sum_congr rfl fun i _ => h3 i
      _ = (∑ i, pathIntegral (C.loop k i) η) + (A (k + 1) - A k) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hA0, hA1]
          ring
  have htail : pathIntegral δ (traceForm hf hne η)
      = ∑ k ∈ Finset.range C.n, (F (C.t (k + 1)) - F (C.t k)) := by
    rw [Finset.sum_range_sub (f := fun k => F (C.t k)), C.ht1 C.n le_rfl, C.ht0]
    exact hF.pathIntegral_eq
  have hAeq : A C.n = A 0 := by
    change (∑ᶠ x ∈ f ⁻¹' {δ.extend (C.t C.n)}, _) = ∑ᶠ x ∈ f ⁻¹' {δ.extend (C.t 0)}, _
    rw [C.ht1 C.n le_rfl, C.ht0, Path.extend_one, Path.extend_zero]
  rw [htail, Finset.sum_congr rfl fun k _ => hpiece k, Finset.sum_add_distrib,
    Finset.sum_range_sub (f := A), hAeq]
  ring

/-- **Period membership**: the trace of the basis period vector along a regular-valued loop
lies in the period subgroup of `X` (exact membership, not just closure). -/
theorem periodVector_traceForm_mem {y₀ : Y} (δ : Path y₀ y₀)
    (hδ : ∀ s : I, RS.IsRegularValue f (δ s)) :
    (fun i => pathIntegral δ (traceForm hf hne (RS.basis X i))) ∈ RS.periodSubgroup X := by
  obtain ⟨C⟩ := exists_traceChain hf hne δ hδ
  have hkey : (fun i => pathIntegral δ (traceForm hf hne (RS.basis X i)))
      = ∑ k ∈ Finset.range C.n, ∑ j, RS.periodVector (RS.basis X) (C.loop k j) := by
    funext i
    rw [pathIntegral_traceForm_eq_sum_loops C (RS.basis X i), Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [hkey]
  apply AddSubgroup.sum_mem
  intro k _
  apply AddSubgroup.sum_mem
  intro j _
  exact RS.periodVector_mem_periodSubgroup (C.loop k j)

end RS

end
