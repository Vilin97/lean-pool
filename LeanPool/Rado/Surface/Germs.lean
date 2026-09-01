/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Surface.Harmonic
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Conjugate germs and the étale space

Step 6 of `Rado/PLAN.md`: harmonic conjugates normalized by `Re F = u` exactly
(`IsConjugate`; existence on chart balls from Mathlib's Re-of-holomorphic,
rigidity up to imaginary constants via the open mapping theorem), and the
étale space `ConjEtale u Y` of conjugate germs: sheets over preconnected opens
form a basis, the projection is an open local homeomorphism trivialized over
conjugate neighbourhoods, the space is Hausdorff (identity theorem), the germ
evaluation map is continuous with **discrete fibers** (isolated zeros; a
constant germ would force `u` to be constant), and every connected component
projects onto all of a connected base.
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Conjugate germs and the étale space -/

/-- `F` is a holomorphic conjugate-package for `u` on `V`: holomorphic with
`Re F = u` there. -/
def IsConjugate (u : X → ℝ) (F : X → ℂ) (V : Set X) : Prop :=
  HolomorphicOn F V ∧ ∀ x ∈ V, (F x).re = u x

/-- Existence of conjugates on small connected neighbourhoods of any point of a
harmonic function's domain (Schwarz integral in a chart;
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`). -/
theorem exists_conjugate {u : X → ℝ} {s : Set X} (hu : SurfaceHarmonicOn u s)
    (hs : IsOpen s) {x : X} (hx : x ∈ s) :
    ∃ V F, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧ V ⊆ s ∧ IsConjugate u F V := by
  have he := chartAt_mem_riemannAtlas (X := X) x
  have hmem : chartAt ℂ x x ∈ chartImage (chartAt ℂ x) s :=
    mem_chartImage_of_mem hx (mem_chart_source ℂ x)
  obtain ⟨ρ, hρpos, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage _ hs) _ hmem
  have hharm : HarmonicOnNhd (u ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) ρ) :=
    fun y hy ↦ hu _ he y (hball hy)
  obtain ⟨H, hHan, hHre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  have hsub : ball (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
    fun w hw ↦ chartImage_subset_target _ _ (hball hw)
  refine ⟨(chartAt ℂ x).symm '' ball (chartAt ℂ x x) ρ, H ∘ (chartAt ℂ x), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (chartAt ℂ x).symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hsub)
  · exact ((convex_ball _ _).isPreconnected).image _
      ((chartAt ℂ x).symm.continuousOn.mono (by simpa using hsub))
  · exact ⟨_, mem_ball_self hρpos, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨y, ⟨hys, hysrc⟩, rfl⟩ := hball hw
    rwa [(chartAt ℂ x).left_inv hysrc]
  · -- holomorphy of `H ∘ chart`
    rintro z ⟨w, hw, rfl⟩
    have hzsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).map_target (hsub hw)
    have htrans : AnalyticAt ℂ
        ((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) :=
      transition_analyticAt (chartAt_mem_riemannAtlas _) he ⟨mem_chart_source _ _, hzsrc⟩
    have hfx : ((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w)) = w := by
      simp only [Function.comp_apply,
        (chartAt ℂ ((chartAt ℂ x).symm w)).left_inv (mem_chart_source _ _)]
      exact (chartAt ℂ x).right_inv (hsub hw)
    have hH : AnalyticAt ℂ H (((chartAt ℂ x) ∘ (chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        (chartAt ℂ ((chartAt ℂ x).symm w) ((chartAt ℂ x).symm w))) := by
      rw [hfx]; exact hHan w hw
    exact hH.comp htrans
  · -- the real part is `u`
    rintro z ⟨w, hw, rfl⟩
    have := hHre hw
    simpa [(chartAt ℂ x).right_inv (hsub hw)] using this

/-- Local rigidity: two conjugates near a point agree near that point up to an
imaginary constant; in particular a conjugate germ over a preconnected open `V`
extends to all of `V` once one conjugate exists on `V`. -/
theorem IsConjugate.eventuallyEq_add_const {u : X → ℝ} {F G : X → ℂ} {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hF : IsConjugate u F V) (hG : IsConjugate u G W)
    {y : X} (hyV : y ∈ V) (hyW : y ∈ W) :
    ∃ t : ℝ, F =ᶠ[𝓝 y] fun z ↦ G z + t * I := by
  -- the difference read through the chart at `y`, on a small ball
  set e := chartAt ℂ y with he_def
  have he := chartAt_mem_riemannAtlas (X := X) y
  have hVWo : IsOpen (V ∩ W ∩ e.source) :=
    (hV.inter hW).inter e.open_source
  have hyVW : y ∈ V ∩ W ∩ e.source := ⟨⟨hyV, hyW⟩, mem_chart_source ℂ y⟩
  have himg : IsOpen (e '' (V ∩ W ∩ e.source)) :=
    e.isOpen_image_of_subset_source hVWo inter_subset_right
  obtain ⟨ρ, hρpos, hball⟩ := Metric.isOpen_iff.mp himg (e y) ⟨y, hyVW, rfl⟩
  have hsymm_mem : ∀ w ∈ ball (e y) ρ, e.symm w ∈ V ∩ W ∩ e.source := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hball hw
    rwa [e.left_inv hz.2]
  -- the difference is analytic with vanishing real part on the ball
  have hd : AnalyticOnNhd ℂ (fun w ↦ F (e.symm w) - G (e.symm w)) (ball (e y) ρ) := by
    intro w hw
    have hzV : e.symm w ∈ V ∩ e.source :=
      ⟨(hsymm_mem w hw).1.1, (hsymm_mem w hw).2⟩
    have hzW : e.symm w ∈ W ∩ e.source :=
      ⟨(hsymm_mem w hw).1.2, (hsymm_mem w hw).2⟩
    have hwt : w ∈ e.target := by
      obtain ⟨z, hz, rfl⟩ := hball hw
      exact e.map_source hz.2
    have h1 : AnalyticAt ℂ (F ∘ e.symm) w := by
      have := hF.1.analyticAt_comp_symm he (x := e.symm w) ⟨hzV.1, hzV.2⟩
      rw [← he_def] at this
      rwa [e.right_inv hwt] at this
    have h2 : AnalyticAt ℂ (G ∘ e.symm) w := by
      have := hG.1.analyticAt_comp_symm he (x := e.symm w) ⟨hzW.1, hzW.2⟩
      rw [← he_def] at this
      rwa [e.right_inv hwt] at this
    exact h1.sub h2
  have hre : ∀ w ∈ ball (e y) ρ, (F (e.symm w) - G (e.symm w)).re = 0 := by
    intro w hw
    have hm := hsymm_mem w hw
    simp [Complex.sub_re, hF.2 _ hm.1.1, hG.2 _ hm.1.2]
  -- open mapping: the difference is constant on the ball
  obtain ⟨cst, hcst⟩ := hd.eq_const_of_re_eq_const hre isOpen_ball
    ⟨⟨_, mem_ball_self hρpos⟩, (convex_ball _ _).isPreconnected⟩
  refine ⟨cst.im, ?_⟩
  have hcre : cst.re = 0 := by
    have := hre _ (mem_ball_self hρpos)
    rw [hcst _ (mem_ball_self hρpos)] at this
    exact this
  -- transfer back through the chart
  have hmem : e.source ∩ e ⁻¹' ball (e y) ρ ∈ 𝓝 y := by
    refine (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).mem_nhds
      ⟨mem_chart_source ℂ y, mem_ball_self hρpos⟩
  filter_upwards [hmem] with z hz
  have h1 : F z - G z = cst := by
    have := hcst _ hz.2
    rwa [e.left_inv hz.1] at this
  have h2 : cst = cst.im * I := by
    rw [Complex.ext_iff]
    simp [hcre]
  rw [← sub_eq_iff_eq_add', ← h2] at *
  exact h1

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Adding an imaginary constant preserves conjugacy. -/
theorem IsConjugate.add_const_mul_I {u : X → ℝ} {F : X → ℂ} {V : Set X}
    (hF : IsConjugate u F V) (t : ℝ) : IsConjugate u (fun z ↦ F z + t * I) V := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ by simp [hF.2 x hx]⟩
  exact (hF.1 x hx).add analyticAt_const

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Conjugates restrict to subsets. -/
theorem IsConjugate.mono {u : X → ℝ} {F : X → ℂ} {V W : Set X} (hF : IsConjugate u F V)
    (hWV : W ⊆ V) : IsConjugate u F W :=
  ⟨hF.1.mono hWV, fun x hx ↦ hF.2 x (hWV hx)⟩

/-- Rigidity: two conjugates on a preconnected open set differ by an imaginary
constant. -/
theorem IsConjugate.exists_sub_const {u : X → ℝ} {F G : X → ℂ} {V : Set X}
    (hV : IsOpen V) (hVc : IsPreconnected V) (hF : IsConjugate u F V)
    (hG : IsConjugate u G V) : ∃ t : ℝ, EqOn G (fun z ↦ F z + t * I) V := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun z hz ↦ absurd hz (notMem_empty z)⟩
  obtain ⟨t₀, ht₀⟩ := IsConjugate.eventuallyEq_add_const hV hV hG hF hx₀ hx₀
  exact ⟨t₀, HolomorphicOn.eqOn_of_eventuallyEq hG.1
    (IsConjugate.add_const_mul_I hF t₀).1 hV hVc hx₀ ht₀⟩

/-- A harmonic function that is locally constant near an accumulation of
constancy cannot avoid being constant: on a preconnected open set, if `u` is
locally constant near one point, it is constant. (Via conjugates and the
identity theorem for the chart derivative.) -/
theorem SurfaceHarmonicOn.eqOn_const_of_locallyConstant {u : X → ℝ} {s : Set X}
    (hu : SurfaceHarmonicOn u s) (hs : IsOpen s)
    (hsc : IsPreconnected s) {y : X} (hy : y ∈ s) (hloc : ∀ᶠ z in 𝓝 y, u z = u y) :
    EqOn u (fun _ ↦ u y) s := by
  classical
  -- the locally-constant locus
  set A : Set X := {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, u w = u z} with hA
  have hyA : y ∈ A := ⟨hy, hloc⟩
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzloc⟩
    filter_upwards [hzloc.eventually_nhds, hs.mem_nhds hzs, hzloc] with w hw hws hwz
    exact ⟨hws, by filter_upwards [hw] with v hv; rw [hv, hwz]⟩
  -- closure step: a boundary point of `A` inside `s` lies in `A`, and in fact
  -- `u` is constant on a whole conjugate neighbourhood of it
  have hclosure : ∀ z ∈ s, z ∈ closure A → z ∈ A := by
    intro z hzs hzcl
    obtain ⟨V, F, hVo, hVc, hzV, hVs, hFconj⟩ := exists_conjugate hu hs hzs
    -- pick a point of `A` in `V`
    obtain ⟨a, haV, haA⟩ := mem_closure_iff.mp hzcl V hVo hzV
    -- near `a`, the constant `u a` is a conjugate of `u`
    have hWmem : {w | u w = u a} ∈ 𝓝 a := haA.2
    set W := V ∩ interior {w | u w = u a} with hW
    have hWo : IsOpen W := hVo.inter isOpen_interior
    have haW : a ∈ W := ⟨haV, mem_interior_iff_mem_nhds.mpr hWmem⟩
    have hGconj : IsConjugate u (fun _ ↦ (u a : ℂ)) W := by
      refine ⟨fun x hx ↦ analyticAt_const, fun x hx ↦ ?_⟩
      have := interior_subset hx.2
      simp only [mem_ofPred_eq] at this
      simp [this]
    -- rigidity: `F` is eventually constant at `a`, hence constant on `V`
    obtain ⟨t, ht⟩ := IsConjugate.eventuallyEq_add_const hVo hWo hFconj hGconj haV haW
    have hFconst : EqOn F (fun _ ↦ (u a : ℂ) + t * I) V :=
      HolomorphicOn.eqOn_of_eventuallyEq hFconj.1
        (fun x hx ↦ analyticAt_const) hVo hVc haV ht
    -- so `u` is constant on `V`, and `z ∈ A`
    have huV : ∀ w ∈ V, u w = u a := by
      intro w hw
      have h1 := hFconj.2 w hw
      rw [hFconst hw] at h1
      simpa using h1.symm
    refine ⟨hzs, ?_⟩
    filter_upwards [hVo.mem_nhds hzV] with w hw
    rw [huV w hw, huV z hzV]
  -- `A` is relatively clopen in preconnected `s`, hence `s ⊆ A`
  have hsub : s ⊆ A := by
    have hBopen : IsOpen (s \ closure A) := hs.sdiff isClosed_closure
    have hcover : s ⊆ A ∪ (s \ closure A) := by
      intro z hz
      by_cases hzA : z ∈ closure A
      · exact Or.inl (hclosure z hz hzA)
      · exact Or.inr ⟨hz, hzA⟩
    have hdisj : Disjoint A (s \ closure A) :=
      disjoint_sdiff_right.mono_left subset_closure
    rcases hsc.subset_or_subset hAopen hBopen hdisj hcover with h | h
    · exact h
    · exact absurd (h hy) fun hcon ↦ hcon.2 (subset_closure hyA)
  -- a locally constant function on a preconnected set is constant
  have hCopen : IsOpen {z | z ∈ s ∧ u z = u y} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzs, hzu⟩
    filter_upwards [(hsub hzs).2, hs.mem_nhds hzs] with w hw hws
    exact ⟨hws, by rw [hw, hzu]⟩
  have hDopen : IsOpen {z | z ∈ s ∧ u z ≠ u y} := by
    have : {z | z ∈ s ∧ u z ≠ u y} = s ∩ u ⁻¹' {u y}ᶜ := by ext; simp
    rw [this]
    exact hu.continuousOn.isOpen_inter_preimage hs isOpen_compl_singleton
  have hdisj : Disjoint {z | z ∈ s ∧ u z = u y} {z | z ∈ s ∧ u z ≠ u y} := by
    rw [Set.disjoint_left]
    rintro z ⟨_, h1⟩ ⟨_, h2⟩
    exact h2 h1
  have hcover : s ⊆ {z | z ∈ s ∧ u z = u y} ∪ {z | z ∈ s ∧ u z ≠ u y} := by
    intro z hz
    by_cases h : u z = u y
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  rcases hsc.subset_or_subset hCopen hDopen hdisj hcover with h | h
  · exact fun z hz ↦ (h hz).2
  · exact absurd (h hy).2 (by simp)


variable (u : X → ℝ) (Y : Set X)

/-- The value of a germ at the base point of its filter (well defined because
every neighbourhood of `y` contains `y`). -/
noncomputable def germValue {y : X} (γ : Germ (𝓝 y) ℂ) : ℂ :=
  γ.liftOn (fun f ↦ f y) fun _ _ h ↦ h.self_of_nhds

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
@[simp] theorem germValue_coe {y : X} (F : X → ℂ) :
    germValue (F : Germ (𝓝 y) ℂ) = F y := rfl

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The set of points where two functions have the same germ is open. -/
theorem isOpen_eventuallyEq_nhds {F G : X → ℂ} : IsOpen {x : X | F =ᶠ[𝓝 x] G} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact eventually_eventuallyEq_nhds.mpr hx

/-- The étale space of conjugate germs of `u` over `Y`: pairs of a point
`y ∈ Y` and the germ at `y` of a conjugate of `u` defined on some open
neighbourhood inside `Y`. -/
def ConjEtale : Type _ :=
  {p : Σ y : X, Germ (𝓝 y) ℂ // p.1 ∈ Y ∧
    ∃ V F, IsOpen V ∧ p.1 ∈ V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ p.2 = (F : Germ (𝓝 p.1) ℂ)}

namespace ConjEtale

variable {u Y}

/-- The sheet of a conjugate `F` over `V`. -/
def sheet (V : Set X) (F : X → ℂ) : Set (ConjEtale u Y) :=
  {q | q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ)}

variable (u Y) in
/-- Basic open sets: sheets of conjugates over preconnected opens inside `Y`. -/
def basicSets : Set (Set (ConjEtale u Y)) :=
  {S | ∃ V F, IsOpen V ∧ IsPreconnected V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ S = sheet V F}

instance : TopologicalSpace (ConjEtale u Y) :=
  TopologicalSpace.generateFrom (basicSets u Y)

/-- The projection to the surface. -/
def proj (q : ConjEtale u Y) : X := q.1.1

/-- The evaluation map. -/
noncomputable def eval (q : ConjEtale u Y) : ℂ := germValue q.1.2

section Etale

variable (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Membership in a sheet, unfolded. -/
theorem mem_sheet_iff {V : Set X} {F : X → ℂ} {q : ConjEtale u Y} :
    q ∈ sheet V F ↔ q.1.1 ∈ V ∧ q.1.2 = (F : Germ (𝓝 q.1.1) ℂ) := Iff.rfl

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Basic sets are open. -/
theorem isOpen_of_mem_basicSets {S : Set (ConjEtale u Y)} (hS : S ∈ basicSets u Y) :
    IsOpen S :=
  TopologicalSpace.isOpen_generateFrom_of_mem hS

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The sheets form a topological basis. -/
theorem isTopologicalBasis_basicSets :
    TopologicalSpace.IsTopologicalBasis (basicSets u Y) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  refine ⟨?_, ?_, rfl⟩
  · -- intersections refine
    rintro S₁ ⟨V₁, F₁, hV₁o, _, hV₁Y, hF₁, rfl⟩ S₂ ⟨V₂, F₂, hV₂o, _, hV₂Y, hF₂, rfl⟩
      q ⟨⟨hy₁, hg₁⟩, ⟨hy₂, hg₂⟩⟩
    have hev : F₁ =ᶠ[𝓝 q.1.1] F₂ := Filter.Germ.coe_eq.mp (hg₁.symm.trans hg₂)
    have hOopen : IsOpen {x : X | F₁ =ᶠ[𝓝 x] F₂} := isOpen_eventuallyEq_nhds
    set W := connectedComponentIn (V₁ ∩ V₂ ∩ {x : X | F₁ =ᶠ[𝓝 x] F₂}) q.1.1 with hW
    have hWsub : W ⊆ V₁ ∩ V₂ ∩ {x : X | F₁ =ᶠ[𝓝 x] F₂} := connectedComponentIn_subset _ _
    have hWo : IsOpen W := ((hV₁o.inter hV₂o).inter hOopen).connectedComponentIn
    have hqW : q.1.1 ∈ W := mem_connectedComponentIn ⟨⟨hy₁, hy₂⟩, hev⟩
    refine ⟨sheet W F₁, ⟨W, F₁, hWo, isPreconnected_connectedComponentIn,
      fun z hz ↦ hV₁Y (hWsub hz).1.1, hF₁.mono fun z hz ↦ (hWsub hz).1.1, rfl⟩,
      ⟨hqW, hg₁⟩, ?_⟩
    rintro p ⟨hpW, hpF⟩
    have hp12 := hWsub hpW
    refine ⟨⟨hp12.1.1, hpF⟩, hp12.1.2, ?_⟩
    rw [hpF]
    exact Filter.Germ.coe_eq.mpr hp12.2
  · -- coverage
    rw [sUnion_eq_univ_iff]
    intro q
    obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
    set W := connectedComponentIn V q.1.1 with hW
    have hWsub : W ⊆ V := connectedComponentIn_subset _ _
    exact ⟨sheet W F, ⟨W, F, hVo.connectedComponentIn, isPreconnected_connectedComponentIn,
      hWsub.trans hVY, hF.mono hWsub, rfl⟩, mem_connectedComponentIn hqV, hgerm⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem continuous_proj : Continuous (proj (u := u) (Y := Y)) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [continuous_def]
  intro O hO
  rw [(isTopologicalBasis_basicSets (u := u) (Y := Y)).isOpen_iff]
  intro q hq
  obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
  have hsub : connectedComponentIn (V ∩ O) q.1.1 ⊆ V ∩ O := connectedComponentIn_subset _ _
  refine ⟨sheet (connectedComponentIn (V ∩ O) q.1.1) F,
    ⟨_, F, (hVo.inter hO).connectedComponentIn, isPreconnected_connectedComponentIn,
      fun z hz ↦ hVY (hsub hz).1, hF.mono fun z hz ↦ (hsub hz).1, rfl⟩,
    ⟨mem_connectedComponentIn ⟨hqV, hq⟩, hgerm⟩, ?_⟩
  rintro p ⟨hpW, _⟩
  exact (hsub hpW).2

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem isOpenMap_proj : IsOpenMap (proj (u := u) (Y := Y)) := by
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hqO, rfl⟩
  obtain ⟨S, hSb, hqS, hSO⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).isOpen_iff.mp hO q hqO
  obtain ⟨V, F, hVo, hVc, hVY, hF, rfl⟩ := hSb
  have himg : V ⊆ proj (u := u) (Y := Y) '' O := fun z hz ↦
    ⟨⟨⟨z, (F : Germ (𝓝 z) ℂ)⟩, hVY hz, V, F, hVo, hz, hVY, hF, rfl⟩, hSO ⟨hz, rfl⟩, rfl⟩
  exact Filter.mem_of_superset (hVo.mem_nhds hqS.1) himg

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `proj` restricted to a sheet is injective (germs of a single `F`). -/
theorem injOn_proj_sheet {V : Set X} {F : X → ℂ} :
    InjOn (proj (u := u) (Y := Y)) (sheet V F) := by
  rintro ⟨⟨y, γ⟩, hq⟩ hmem ⟨⟨y', γ'⟩, hq'⟩ hmem' h
  have hyy : y = y' := h
  subst hyy
  obtain ⟨-, hγ⟩ := hmem
  obtain ⟨-, hγ'⟩ := hmem'
  simp only at hγ hγ'
  subst hγ
  subst hγ'
  rfl

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Hausdorffness of the étale space (identity theorem). -/
theorem t2Space [T2Space X] : T2Space (ConjEtale u Y) := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  constructor
  intro q₁ q₂ hne
  by_cases hbase : proj q₁ = proj q₂
  · -- same base point: separate the germs by sheets over a common
    -- preconnected neighbourhood, disjoint by the identity theorem
    obtain ⟨hY₁, V₁, F₁, hV₁o, hq₁V, hV₁Y, hF₁, hg₁⟩ := q₁.2
    obtain ⟨hY₂, V₂, F₂, hV₂o, hq₂V, hV₂Y, hF₂, hg₂⟩ := q₂.2
    set W := connectedComponentIn (V₁ ∩ V₂) (proj q₁) with hWdef
    have hWo : IsOpen W := (hV₁o.inter hV₂o).connectedComponentIn
    have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
    have hWsub : W ⊆ V₁ ∩ V₂ := connectedComponentIn_subset _ _
    have hq₂V₂ : proj q₁ ∈ V₂ := by rw [hbase]; exact hq₂V
    have hyW : proj q₁ ∈ W := mem_connectedComponentIn ⟨hq₁V, hq₂V₂⟩
    have hyW₂ : q₂.1.1 ∈ W := by
      change proj q₂ ∈ W
      rw [← hbase]
      exact hyW
    have hWY : W ⊆ Y := fun z hz ↦ hV₁Y (hWsub hz).1
    have hb₁ : sheet W F₁ ∈ basicSets u Y :=
      ⟨W, F₁, hWo, hWc, hWY, hF₁.mono fun z hz ↦ (hWsub hz).1, rfl⟩
    have hb₂ : sheet W F₂ ∈ basicSets u Y :=
      ⟨W, F₂, hWo, hWc, hWY, hF₂.mono fun z hz ↦ (hWsub hz).2, rfl⟩
    refine ⟨sheet W F₁, sheet W F₂, isOpen_of_mem_basicSets hb₁, isOpen_of_mem_basicSets hb₂,
      ⟨hyW, hg₁⟩, ⟨hyW₂, hg₂⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro p ⟨hpW, hp₁⟩ ⟨-, hp₂⟩
    -- the two conjugates agree near `p`, hence on `W`, hence at the base point
    have hev : F₁ =ᶠ[𝓝 p.1.1] F₂ := Filter.Germ.coe_eq.mp (hp₁.symm.trans hp₂)
    have heqOn : EqOn F₁ F₂ W :=
      HolomorphicOn.eqOn_of_eventuallyEq (hF₁.1.mono fun z hz ↦ (hWsub hz).1)
        (hF₂.1.mono fun z hz ↦ (hWsub hz).2) hWo hWc hpW hev
    have hyev : F₁ =ᶠ[𝓝 (proj q₁)] F₂ := by
      filter_upwards [hWo.mem_nhds hyW] with z hz
      exact heqOn hz
    have hyev₂ : F₁ =ᶠ[𝓝 (proj q₂)] F₂ := by
      rw [← hbase]
      exact hyev
    have hg₂' : q₂.1.2 = (F₁ : Germ (𝓝 q₂.1.1) ℂ) :=
      hg₂.trans (Filter.Germ.coe_eq.mpr hyev₂).symm
    exact absurd (injOn_proj_sheet ⟨hyW, hg₁⟩ ⟨hyW₂, hg₂'⟩ hbase) hne
  · obtain ⟨O₁, O₂, hO₁, hO₂, h₁, h₂, hdisj⟩ := t2_separation hbase
    exact ⟨proj ⁻¹' O₁, proj ⁻¹' O₂, hO₁.preimage continuous_proj,
      hO₂.preimage continuous_proj, h₁, h₂, hdisj.preimage _⟩

/-- Every point of `Y` has a conjugate germ over it. -/
theorem exists_mk (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y) {y : X} (hy : y ∈ Y) :
    ∃ q : ConjEtale u Y, proj q = y := by
  obtain ⟨V, F, hVo, hVc, hyV, hVY, hF⟩ := exists_conjugate hu hY hy
  exact ⟨⟨⟨y, (F : Germ (𝓝 y) ℂ)⟩, hy, V, F, hVo, hyV, hVY, hF, rfl⟩, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Every étale point lies on a basic sheet. -/
private theorem exists_basic_sheet_mem (q : ConjEtale u Y) :
    ∃ V F, IsOpen V ∧ IsPreconnected V ∧ V ⊆ Y ∧ IsConjugate u F V ∧ q ∈ sheet V F := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  obtain ⟨hqY, V, F, hVo, hqV, hVY, hF, hgerm⟩ := q.2
  exact ⟨connectedComponentIn V q.1.1, F, hVo.connectedComponentIn,
    isPreconnected_connectedComponentIn, (connectedComponentIn_subset _ _).trans hVY,
    hF.mono (connectedComponentIn_subset _ _), mem_connectedComponentIn hqV, hgerm⟩

/-- The tautological section of a basic sheet. -/
private def sheetSec {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) : V → ConjEtale u Y := fun z ↦
  ⟨⟨z.1, (F : Germ (𝓝 z.1) ℂ)⟩, hVY z.2, V, F, hVo, z.2, hVY, hF, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem sheetSec_image {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) (O : Set X) :
    sheetSec hVo hVY hF '' (Subtype.val ⁻¹' O) = proj ⁻¹' O ∩ sheet V F := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.2, rfl⟩
  · rintro ⟨hqO, hqV, hqF⟩
    refine ⟨⟨q.1.1, hqV⟩, hqO, ?_⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq hqF.symm)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem continuous_sheetSec {V : Set X} {F : X → ℂ} (hVo : IsOpen V) (hVY : V ⊆ Y)
    (hF : IsConjugate u F V) : Continuous (sheetSec hVo hVY hF) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro S ⟨W, G, hWo, hWc, hWY, hG, rfl⟩
  have heq : sheetSec hVo hVY hF ⁻¹' sheet W G
      = Subtype.val ⁻¹' (W ∩ {x : X | F =ᶠ[𝓝 x] G}) := by
    ext z
    simp only [sheetSec, mem_preimage, sheet, mem_ofPred_eq, mem_inter_iff]
    exact and_congr Iff.rfl Filter.Germ.coe_eq
  rw [heq]
  exact (hWo.inter isOpen_eventuallyEq_nhds).preimage continuous_subtype_val

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem sheetSec_image_mem_nhds {W : Set X} {G : X → ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWY : W ⊆ Y) (hG : IsConjugate u G W) {q : ConjEtale u Y}
    (hq : q ∈ sheet W G) {K : Set X} (hK : K ∈ 𝓝 q.1.1) :
    sheetSec hWo hWY hG '' (Subtype.val ⁻¹' K) ∈ 𝓝 q := by
  rw [sheetSec_image]
  refine Filter.mem_of_superset ?_ (inter_subset_inter_left _ (preimage_mono interior_subset))
  have hopen : IsOpen (proj (u := u) (Y := Y) ⁻¹' interior K ∩ sheet W G) :=
    (isOpen_interior.preimage continuous_proj).inter
      (isOpen_of_mem_basicSets ⟨W, G, hWo, hWc, hWY, hG, rfl⟩)
  exact hopen.mem_nhds ⟨mem_interior_iff_mem_nhds.mpr hK, hq⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The étale space inherits the local properties needed by Poincaré–Volterra:
local compactness, local connectedness, local second countability. -/
theorem locallyCompactSpace :
    LocallyCompactSpace (ConjEtale u Y) := by
  have : LocallyCompactSpace X := Rado.locallyCompactSpace
  constructor
  intro q N hN
  obtain ⟨S, hSb, hqS, hSN⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).mem_nhds_iff.mp hN
  obtain ⟨W, G, hWo, hWc, hWY, hG, rfl⟩ := hSb
  obtain ⟨K, hKn, hKW, hKc⟩ := local_compact_nhds (hWo.mem_nhds hqS.1)
  refine ⟨sheetSec hWo hWY hG '' (Subtype.val ⁻¹' K),
    sheetSec_image_mem_nhds hWo hWc hWY hG hqS hKn, ?_, ?_⟩
  · rw [sheetSec_image]
    exact inter_subset_right.trans hSN
  · have hKcomp : IsCompact (Subtype.val ⁻¹' K : Set W) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_inter_range,
        Subtype.range_coe, inter_eq_self_of_subset_left hKW]
      exact hKc
    exact hKcomp.image (continuous_sheetSec hWo hWY hG)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem locallyConnectedSpace :
    LocallyConnectedSpace (ConjEtale u Y) := by
  have hX : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro q U hU
  obtain ⟨S, hSb, hqS, hSN⟩ :=
    (isTopologicalBasis_basicSets (u := u) (Y := Y)).mem_nhds_iff.mp hU
  obtain ⟨W, G, hWo, hWc, hWY, hG, rfl⟩ := hSb
  obtain ⟨V', hV'n, hV'c, hV'W⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp hX q.1.1 W (hWo.mem_nhds hqS.1)
  refine ⟨sheetSec hWo hWY hG '' (Subtype.val ⁻¹' V'),
    sheetSec_image_mem_nhds hWo hWc hWY hG hqS hV'n, ?_, ?_⟩
  · have := Subtype.preconnectedSpace hV'c
    have hcont : Continuous ((sheetSec hWo hWY hG) ∘ Set.inclusion hV'W) :=
      (continuous_sheetSec hWo hWY hG).comp (continuous_inclusion hV'W)
    have hrange : range ((sheetSec hWo hWY hG) ∘ Set.inclusion hV'W)
        = sheetSec hWo hWY hG '' (Subtype.val ⁻¹' V') := by
      rw [range_comp, Set.range_inclusion]
      rfl
    rw [← hrange]
    exact isPreconnected_range hcont
  · rw [sheetSec_image]
    exact inter_subset_right.trans hSN

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A sheet over a second-countable base is second countable: the restricted
projection is an open embedding into `↥W`. -/
private theorem secondCountable_sheet {W : Set X} {F : X → ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWY : W ⊆ Y) (hF : IsConjugate u F W)
    (hWsc : SecondCountableTopology W) :
    SecondCountableTopology (sheet (u := u) (Y := Y) W F) := by
  have := hWsc
  have hSb : sheet W F ∈ basicSets u Y := ⟨W, F, hWo, hWc, hWY, hF, rfl⟩
  let ρ : {p : ConjEtale u Y // p ∈ sheet W F} → {z : X // z ∈ W} :=
    fun p ↦ ⟨proj p.1, p.2.1⟩
  have hρcont : Continuous ρ :=
    Continuous.subtype_mk (continuous_proj.comp continuous_subtype_val) _
  have hρinj : Function.Injective ρ := by
    intro p₁ p₂ h
    exact Subtype.ext (injOn_proj_sheet p₁.2 p₂.2 (congrArg Subtype.val h))
  have hρopen : IsOpenMap ρ := by
    intro T hT
    obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.mp hT
    have himg : ρ '' (Subtype.val ⁻¹' T')
        = Subtype.val ⁻¹' (proj (u := u) (Y := Y) '' (T' ∩ sheet W F)) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, ⟨hp, p.2⟩, rfl⟩
      · rintro ⟨p, ⟨hpT, hpS⟩, hpz⟩
        exact ⟨⟨p, hpS⟩, hpT, Subtype.ext hpz⟩
    rw [himg]
    exact (isOpenMap_proj _ (hT'.inter (isOpen_of_mem_basicSets hSb))).preimage
      continuous_subtype_val
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hρcont hρinj
    hρopen).isEmbedding.secondCountableTopology

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem locally_secondCountable
    (q : ConjEtale u Y) :
    ∃ U : Set (ConjEtale u Y), q ∈ U ∧ IsOpen U ∧ SecondCountableTopology U := by
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  -- a basic sheet through `q` refined into a second-countable chart piece
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  obtain ⟨U₀, hqU₀, hU₀o, hU₀sc⟩ := Rado.locally_secondCountable (X := X) q.1.1
  set W := connectedComponentIn (V ∩ U₀) q.1.1 with hWdef
  have hWsub : W ⊆ V ∩ U₀ := connectedComponentIn_subset _ _
  have hWo : IsOpen W := (hVo.inter hU₀o).connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWY : W ⊆ Y := fun z hz ↦ hVY (hWsub hz).1
  have hqW : q.1.1 ∈ W := mem_connectedComponentIn ⟨hqV.1, hqU₀⟩
  have hGW : IsConjugate u F W := hF.mono fun z hz ↦ (hWsub hz).1
  have hSb : sheet W F ∈ basicSets u Y := ⟨W, F, hWo, hWc, hWY, hGW, rfl⟩
  -- second countability of `↥W` (hereditary from `↥U₀`)
  have hWsc : SecondCountableTopology W := by
    have := hU₀sc
    exact (Topology.IsEmbedding.inclusion fun z hz ↦ (hWsub hz).2).secondCountableTopology
  exact ⟨sheet W F, ⟨hqW, hqV.2⟩, isOpen_of_mem_basicSets hSb,
    secondCountable_sheet hWo hWc hWY hGW hWsc⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem continuous_eval :
    Continuous (eval (u := u) (Y := Y)) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  have hopen : IsOpen (sheet V F : Set (ConjEtale u Y)) :=
    isOpen_of_mem_basicSets ⟨V, F, hVo, hVc, hVY, hF, rfl⟩
  have hproj : ContinuousAt (proj (u := u) (Y := Y)) q := continuous_proj.continuousAt
  have hFc : ContinuousAt F (proj (u := u) (Y := Y) q) :=
    hF.1.continuousOn.continuousAt (hVo.mem_nhds hqV.1)
  have h1 : ContinuousAt (F ∘ proj (u := u) (Y := Y)) q := hFc.comp hproj
  refine h1.congr ?_
  filter_upwards [hopen.mem_nhds hqV] with p hp
  simp only [Function.comp_apply, eval, hp.2, germValue_coe]
  rfl

/-- Discreteness of the fibers of `eval`: if evaluation were constant near a
germ, `u` would be locally constant near the base point, hence constant on all
of connected `Y` (`SurfaceHarmonicOn.eqOn_const_of_locallyConstant`) —
contradicting nonconstancy. -/
theorem eval_discrete_fibers (hu : SurfaceHarmonicOn u Y) (hY : IsOpen Y)
    (hYc : IsPreconnected Y) {x₀ x₁ : X} (h₀ : x₀ ∈ Y) (h₁ : x₁ ∈ Y)
    (hne : u x₀ ≠ u x₁) (q : ConjEtale u Y) :
    ∃ U ∈ 𝓝 q, ∀ w ∈ U, eval w = eval q → w = q := by
  obtain ⟨V, F, hVo, hVc, hVY, hF, hqV⟩ := exists_basic_sheet_mem q
  set y := q.1.1 with hy_def
  have hyV : y ∈ V := hqV.1
  have hevalq : eval q = F y := by
    rw [hy_def]
    simp only [eval, hqV.2, germValue_coe]
  -- the chart representative of `F` is analytic at the base point
  have hFan : AnalyticAt ℂ (F ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hF.1 y hyV
  rcases hFan.eventually_eq_or_eventually_ne analyticAt_const (g := fun _ ↦ F y) with hcase | hcase
  · -- `F` locally constant near `y` forces `u` locally constant, contradiction
    exfalso
    have htend : Filter.Tendsto (chartAt ℂ y) (𝓝 y) (𝓝 (chartAt ℂ y y)) :=
      (chartAt ℂ y).continuousAt (mem_chart_source ℂ y)
    have hFev : ∀ᶠ w in 𝓝 y, F w = F y := by
      filter_upwards [htend.eventually hcase,
        (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)] with w hw hwsrc
      rwa [Function.comp_apply, (chartAt ℂ y).left_inv hwsrc] at hw
    have huev : ∀ᶠ w in 𝓝 y, u w = u y := by
      filter_upwards [hFev, hVo.mem_nhds hyV] with w hw hwV
      rw [← hF.2 w hwV, ← hF.2 y hyV, hw]
    have hconst := hu.eqOn_const_of_locallyConstant hY hYc (hVY hyV) huev
    exact hne ((hconst h₀).trans (hconst h₁).symm)
  · -- isolated `F y`-points: the sheet is locally injective for `eval`
    have htend : Filter.Tendsto (chartAt ℂ y) (𝓝 y) (𝓝 (chartAt ℂ y y)) :=
      (chartAt ℂ y).continuousAt (mem_chart_source ℂ y)
    -- transfer the punctured-neighbourhood condition through the chart
    have hFev : ∀ᶠ w in 𝓝 y, w ≠ y → F w ≠ F y := by
      have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ y y), z ≠ chartAt ℂ y y →
          (F ∘ (chartAt ℂ y).symm) z ≠ F y := by
        rw [eventually_nhdsWithin_iff] at hcase
        exact hcase.mono fun z hz hne ↦ hz hne
      filter_upwards [htend.eventually h1,
        (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)] with w hw hwsrc hwne
      have hzne : chartAt ℂ y w ≠ chartAt ℂ y y := fun hcon ↦
        hwne ((chartAt ℂ y).injOn hwsrc (mem_chart_source ℂ y) hcon)
      have := hw hzne
      rwa [Function.comp_apply, (chartAt ℂ y).left_inv hwsrc] at this
    obtain ⟨N, hNprop, hNo, hyN⟩ := eventually_nhds_iff.mp hFev
    have hSopen : IsOpen (sheet V F : Set (ConjEtale u Y)) :=
      isOpen_of_mem_basicSets ⟨V, F, hVo, hVc, hVY, hF, rfl⟩
    refine ⟨proj ⁻¹' N ∩ sheet V F,
      ((hNo.preimage continuous_proj).inter hSopen).mem_nhds ⟨hyN, hqV⟩, ?_⟩
    rintro w ⟨hwN, hwS⟩ heval
    have hevalw : eval w = F (proj w) := by
      simp only [eval, proj, hwS.2, germValue_coe]
    have hwy : proj w = y := by
      by_contra hcon
      exact hNprop _ hwN hcon (by rw [← hevalw, heval, hevalq])
    exact injOn_proj_sheet hwS hqV hwy

/-- Over a connected `Y`, every connected component of the étale space projects
onto all of `Y` (openness and closedness of the image of a component, via local
triviality of `proj` over small preconnected chart neighbourhoods). -/
theorem surjOn_proj_connectedComponent (hu : SurfaceHarmonicOn u Y)
    (hY : IsOpen Y) (hYc : IsPreconnected Y) (q₀ : ConjEtale u Y) :
    SurjOn (proj (u := u) (Y := Y)) (connectedComponent q₀) Y := by
  have : LocallyConnectedSpace (ConjEtale u Y) := locallyConnectedSpace
  set S := proj (u := u) (Y := Y) '' connectedComponent q₀ with hS_def
  have hSopen : IsOpen S := isOpenMap_proj _ isOpen_connectedComponent
  -- the image is relatively closed in `Y`: any closure point in `Y` lies on a
  -- sheet over a preconnected trivializing neighbourhood that meets the
  -- component, hence is contained in it
  have key : ∀ y ∈ Y, y ∈ closure S → y ∈ S := by
    intro y hyY hycl
    obtain ⟨V, F, hVo, hVc, hyV, hVY, hF⟩ := exists_conjugate hu hY hyY
    obtain ⟨y', hy'V, hy'S⟩ := mem_closure_iff.mp hycl V hVo hyV
    obtain ⟨q', hq'C, hq'proj⟩ := hy'S
    have hq'V : proj q' ∈ V := by rw [hq'proj]; exact hy'V
    -- local triviality: `q'` lies on a sheet over `V`
    obtain ⟨hq'Y, W, G, hWo, hq'W, hWY, hG, hgerm⟩ := q'.2
    obtain ⟨s, hs⟩ := IsConjugate.eventuallyEq_add_const hWo hVo hG hF hq'W hq'V
    have hFs : IsConjugate u (fun z ↦ F z + s * I) V := hF.add_const_mul_I s
    have hq'sheet : q' ∈ sheet V (fun z ↦ F z + s * I) := by
      refine ⟨hq'V, ?_⟩
      rw [hgerm]
      exact Filter.Germ.coe_eq.mpr hs
    -- the sheet is preconnected (image of the continuous section)
    have hsheet_conn : IsPreconnected (sheet (u := u) (Y := Y) V (fun z ↦ F z + s * I)) := by
      have := Subtype.preconnectedSpace hVc
      have hrange : range (sheetSec hVo hVY hFs) = sheet V (fun z ↦ F z + s * I) := by
        rw [← image_univ]
        have h1 : (univ : Set V) = Subtype.val ⁻¹' V := by
          ext z
          simp
        rw [h1, sheetSec_image]
        ext p
        exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hp.1, hp⟩⟩
      rw [← hrange]
      exact isPreconnected_range (continuous_sheetSec hVo hVY hFs)
    have hsub : sheet (u := u) (Y := Y) V (fun z ↦ F z + s * I) ⊆ connectedComponent q₀ := by
      have h1 := hsheet_conn.subset_connectedComponent hq'sheet
      rwa [← connectedComponent_eq hq'C] at h1
    exact ⟨sheetSec hVo hVY hFs ⟨y, hyV⟩, hsub ⟨hyV, rfl⟩, rfl⟩
  -- clopen argument on the preconnected `Y`
  have hBopen : IsOpen (Y \ closure S) := hY.sdiff isClosed_closure
  have hcover : Y ⊆ S ∪ (Y \ closure S) := by
    intro y hy
    by_cases h : y ∈ closure S
    · exact Or.inl (key y hy h)
    · exact Or.inr ⟨hy, h⟩
  have hdisj : Disjoint S (Y \ closure S) := disjoint_sdiff_right.mono_left subset_closure
  rcases hYc.subset_or_subset hSopen hBopen hdisj hcover with h | h
  · exact fun y hy ↦ h hy
  · exfalso
    have h1 : proj q₀ ∈ Y := q₀.2.1
    have h2 : proj q₀ ∈ S := ⟨q₀, mem_connectedComponent, rfl⟩
    exact (h h1).2 (subset_closure h2)

end Etale

end ConjEtale

end Rado
