/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.OfCoeffs
import LeanPool.JacobianDiffgeo.Forms.Montel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-!
# Finite-dimensionality of the space of holomorphic 1-forms (CC1, design §2.6)

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). On a compact `X` the space
`RS.Form1 X` is finite-dimensional, making `genus := Module.finrank ℂ (Form1 X)` honest.

Route: a **good cover** (finitely many doubly-shrunk chart neighbourhoods `V i ⋐ W i ⋐` chart
sources) gives an injective linear *coefficient embedding* `J : Form1 X →ₗ[ℂ] Π i, C(K i, ℂ)`
into a finite product of sup-normed spaces (`K i` the compact chart image of `closure (V i)`).
The transition rule bounds all coefficients on the larger open `U i ⊇ K i` uniformly over the
unit ball of the image, so the unit ball sits inside a product of **Montel** compacta
(`RS.isCompact_closure_montelFamily`); the unit ball of the image is *closed* by Weierstrass
convergence + reassembly through `RS.Form1.ofCoeffs` over restricted charts, hence compact;
**Riesz** (`FiniteDimensional.of_isCompact_closedBall₀`) finishes.

Main declarations:
* `RS.GoodCover`, `RS.GoodCover.nonempty` — finite doubly-shrunk chart covers exist.
* `RS.GoodCover.J` — the coefficient embedding, `RS.GoodCover.J_injective`.
* `RS.GoodCover.exists_montel_bound` — the uniform coefficient bound.
* `RS.GoodCover.isClosed_ball_inter_range` — the unit ball of the image is closed.
* `instance : FiniteDimensional ℂ (Form1 X)` (compact T2 `X`).
-/

open scoped ContDiff Manifold Bundle Topology
open Set Filter IsManifold

-- Several lemmas about `G.P`/`gext` below are stated in a section carrying
-- `[IsManifold 𝓘(ℂ) ω X]` (needed by other declarations in the same `variable` block) but do not
-- themselves use it; silence the resulting (harmless) unused-variable linter noise.

noncomputable section

namespace RS

/-! ### A generic dense-agreement extension helper -/

/-- Two functions continuous on `t` that agree on a subset `s` with `t ⊆ closure s` agree
on `t`. -/
theorem eqOn_of_eqOn_of_subset_closure {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {f g : α → β} {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s)
    (hf : ContinuousOn f t) (hg : ContinuousOn g t) (h : Set.EqOn f g s) : Set.EqOn f g t := by
  intro z hz
  have hne : (𝓝[s] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hts hz)
  have h1 : Filter.Tendsto f (𝓝[s] z) (𝓝 (f z)) := (hf z hz).mono hst
  have h2 : Filter.Tendsto g (𝓝[s] z) (𝓝 (g z)) := (hg z hz).mono hst
  have h3 : Filter.Tendsto f (𝓝[s] z) (𝓝 (g z)) :=
    Filter.Tendsto.congr'
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun w hw => (h hw).symm) h2
  exact tendsto_nhds_unique h1 h3

/-! ### Good covers -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A **good cover**: finitely many chart-centred pairs of open sets `V i ⋐ W i` with
`closure (W i)` inside the chart source, the `V i` covering `X` (design §2.6 step 1). -/
structure GoodCover (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Number of cover elements. -/
  n : ℕ
  /-- Chart centres. -/
  c : Fin n → X
  /-- Inner cover sets. -/
  V : Fin n → Set X
  /-- Outer cover sets. -/
  W : Fin n → Set X
  isOpen_V : ∀ i, IsOpen (V i)
  isOpen_W : ∀ i, IsOpen (W i)
  closure_V_subset : ∀ i, closure (V i) ⊆ W i
  closure_W_subset : ∀ i, closure (W i) ⊆ (chartAt ℂ (c i)).source
  iUnion_V : ⋃ i, V i = Set.univ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Good covers exist on compact T2 surfaces (double shrinking by local compactness +
finite subcover). -/
theorem GoodCover.nonempty [T2Space X] [CompactSpace X] : Nonempty (GoodCover X) := by
  have h : ∀ x : X, ∃ V : Set X, ∃ W : Set X, IsOpen V ∧ IsOpen W ∧ x ∈ V ∧
      closure V ⊆ W ∧ closure W ⊆ (chartAt ℂ x).source := by
    intro x
    obtain ⟨K₁, hK₁c, hx₁, hK₁s⟩ :=
      exists_compact_subset (chartAt ℂ x).open_source (mem_chart_source ℂ x)
    obtain ⟨K₂, hK₂c, hx₂, hK₂s⟩ := exists_compact_subset isOpen_interior hx₁
    exact ⟨interior K₂, interior K₁, isOpen_interior, isOpen_interior, hx₂,
      (closure_minimal interior_subset hK₂c.isClosed).trans hK₂s,
      (closure_minimal interior_subset hK₁c.isClosed).trans hK₁s⟩
  choose Vf Wf hVo hWo hxV hVW hWs using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Vf hVo
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨⟨t.card, fun i => ↑(t.equivFin.symm i), fun i => Vf ↑(t.equivFin.symm i),
    fun i => Wf ↑(t.equivFin.symm i), fun i => hVo _, fun i => hWo _, fun i => hVW _,
    fun i => hWs _, ?_⟩⟩
  apply Set.eq_univ_of_univ_subset
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
  simpa using hxy

namespace GoodCover

variable (G : GoodCover X)

/-- The chart of the `i`-th cover element. -/
def e (i : Fin G.n) : OpenPartialHomeomorph X ℂ := chartAt ℂ (G.c i)


omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem W_subset_source (i : Fin G.n) : G.W i ⊆ (G.e i).source :=
  subset_closure.trans (G.closure_W_subset i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem closureV_subset_source (i : Fin G.n) : closure (G.V i) ⊆ (G.e i).source :=
  (G.closure_V_subset i).trans (G.W_subset_source i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem V_subset_source (i : Fin G.n) : G.V i ⊆ (G.e i).source :=
  subset_closure.trans (G.closureV_subset_source i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem exists_mem_V (x : X) : ∃ i, x ∈ G.V i :=
  Set.mem_iUnion.mp (G.iUnion_V ▸ Set.mem_univ x)

/-- Open chart image of the inner set. -/
def O (i : Fin G.n) : Set ℂ := G.e i '' G.V i

/-- Compact chart image of the closed inner set: the set on which coefficients are compared. -/
def K (i : Fin G.n) : Set ℂ := G.e i '' closure (G.V i)

/-- Open chart image of the outer set: the Montel domain. -/
def U (i : Fin G.n) : Set ℂ := G.e i '' G.W i

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem isOpen_O (i : Fin G.n) : IsOpen (G.O i) :=
  (G.e i).isOpen_image_of_subset_source (G.isOpen_V i) (G.V_subset_source i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem isOpen_U (i : Fin G.n) : IsOpen (G.U i) :=
  (G.e i).isOpen_image_of_subset_source (G.isOpen_W i) (G.W_subset_source i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem isCompact_K [CompactSpace X] (i : Fin G.n) : IsCompact (G.K i) :=
  isClosed_closure.isCompact.image_of_continuousOn
    ((G.e i).continuousOn.mono (G.closureV_subset_source i))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem O_subset_K (i : Fin G.n) : G.O i ⊆ G.K i := Set.image_mono subset_closure

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem K_subset_U (i : Fin G.n) : G.K i ⊆ G.U i := Set.image_mono (G.closure_V_subset i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem O_subset_target (i : Fin G.n) : G.O i ⊆ (G.e i).target := by
  rintro _ ⟨p, hp, rfl⟩
  exact (G.e i).map_source (G.V_subset_source i hp)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem K_subset_target (i : Fin G.n) : G.K i ⊆ (G.e i).target := by
  rintro _ ⟨p, hp, rfl⟩
  exact (G.e i).map_source (G.closureV_subset_source i hp)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem U_subset_target (i : Fin G.n) : G.U i ⊆ (G.e i).target := by
  rintro _ ⟨p, hp, rfl⟩
  exact (G.e i).map_source (G.W_subset_source i hp)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem K_subset_closure_O (i : Fin G.n) : G.K i ⊆ closure (G.O i) :=
  ((G.e i).continuousOn.mono (G.closureV_subset_source i)).image_closure

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem symm_mem_W {i : Fin G.n} {z : ℂ} (hz : z ∈ G.U i) : (G.e i).symm z ∈ G.W i := by
  obtain ⟨p, hp, rfl⟩ := hz
  rwa [(G.e i).left_inv (G.W_subset_source i hp)]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_K_of_mem_V {i : Fin G.n} {x : X} (hx : x ∈ G.V i) : G.e i x ∈ G.K i :=
  Set.mem_image_of_mem _ (subset_closure hx)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem e_mem_maximalAtlas [IsManifold 𝓘(ℂ) ω X] (i : Fin G.n) :
    G.e i ∈ maximalAtlas 𝓘(ℂ) ω X :=
  chart_mem_maximalAtlas (G.c i)

/-! #### Restricted charts -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem restr_source_eq (i : Fin G.n) :
    ((G.e i).restr (G.V i)).source = (G.e i).source ∩ G.V i := by
  rw [OpenPartialHomeomorph.restr_source, (G.isOpen_V i).interior_eq]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_restr_source {i : Fin G.n} {x : X} (hx : x ∈ G.V i) :
    x ∈ ((G.e i).restr (G.V i)).source := by
  rw [G.restr_source_eq i]
  exact ⟨G.V_subset_source i hx, hx⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem restr_target_eq (i : Fin G.n) : ((G.e i).restr (G.V i)).target = G.O i := by
  rw [OpenPartialHomeomorph.restr_target, (G.isOpen_V i).interior_eq]
  ext z
  constructor
  · rintro ⟨hzt, hzs⟩
    exact ⟨(G.e i).symm z, hzs, (G.e i).right_inv hzt⟩
  · rintro ⟨p, hp, rfl⟩
    have hps : p ∈ (G.e i).source := G.V_subset_source i hp
    exact ⟨(G.e i).map_source hps, by
      rw [Set.mem_preimage, (G.e i).left_inv hps]; exact hp⟩

/-! ### The coefficient embedding `J` -/

instance instCompactSpaceK [CompactSpace X] (i : Fin G.n) : CompactSpace (G.K i) :=
  isCompact_iff_compactSpace.mp (G.isCompact_K i)

/-- The target of the coefficient embedding: a finite product of sup-normed spaces of
continuous functions on the compact sets `K i`. -/
abbrev P : Type _ := ∀ i : Fin G.n, C(G.K i, ℂ)


/-- The coefficient embedding: a holomorphic 1-form goes to the tuple of restrictions of its
chart coefficients to the compacta `K i`. The norm `‖J η‖ = max_i sup_{K i} ‖coeffIn (e i) η‖`
is exactly CC1's prescribed norm — it lives on `P`, never as an instance on `Form1 X`. -/
def J : Form1 X →ₗ[ℂ] G.P where
  toFun η i :=
    ⟨(G.K i).domRestrict (coeffIn (G.e i) η),
      (((η.analyticOnNhd_coeffIn (G.e_mem_maximalAtlas i)).continuousOn).mono
        (G.K_subset_target i)).domRestrict⟩
  map_add' η η' := by
    funext i
    ext z
    exact coeffIn_add (G.e i) η η' z
  map_smul' a η := by
    funext i
    ext z
    exact coeffIn_smul (G.e i) a η z

@[simp]
theorem J_apply (η : Form1 X) (i : Fin G.n) (z : G.K i) :
    G.J η i z = coeffIn (G.e i) η z := rfl

theorem norm_coeffIn_le_of_mem_K [CompactSpace X] (η : Form1 X) {i : Fin G.n} {z : ℂ}
    (hz : z ∈ G.K i) : ‖coeffIn (G.e i) η z‖ ≤ ‖G.J η‖ :=
  calc ‖coeffIn (G.e i) η z‖ = ‖G.J η i ⟨z, hz⟩‖ := rfl
    _ ≤ ‖G.J η i‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖G.J η‖ := norm_le_pi_norm _ i

theorem J_injective : Function.Injective G.J := by
  rw [injective_iff_map_eq_zero]
  intro η hη
  refine Form1.ext_coeffAt fun x => ?_
  rw [coeffAt_zero]
  obtain ⟨i, hi⟩ := G.exists_mem_V x
  have hxs : x ∈ (G.e i).source := G.V_subset_source i hi
  have hz : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' ((G.e i).source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hxs, mem_chart_source ℂ x⟩, rfl⟩
  have h := coeffIn_trans (G.e_mem_maximalAtlas i) (chart_mem_maximalAtlas x) η hz
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h
  have hK : G.e i x ∈ G.K i := G.mem_K_of_mem_V hi
  have hzero : coeffIn (G.e i) η (G.e i x) = 0 := by
    have : G.J η i ⟨G.e i x, hK⟩ = 0 := by rw [hη]; rfl
    exact this
  rw [coeffAt, h, hzero, mul_zero]

/-! ### The uniform Montel bound -/

/-- Uniform bound (design §2.6 step 4): coefficients of unit-ball forms are uniformly bounded on
the Montel domains `U i` — the transition-derivative suprema over the compact overlap pieces
transfer the `K j`-bounds outward. -/
theorem exists_montel_bound [CompactSpace X] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : Form1 X, ‖G.J η‖ ≤ 1 →
      ∀ i, ∀ z ∈ G.U i, ‖coeffIn (G.e i) η z‖ ≤ C := by
  -- bound the transition derivatives on the compact overlap pieces
  have hbd : ∀ i j : Fin G.n, ∃ Cij : ℝ,
      ∀ z ∈ G.e i '' (closure (G.W i) ∩ closure (G.V j)),
        ‖deriv (⇑(G.e j) ∘ ⇑(G.e i).symm) z‖ ≤ Cij := by
    intro i j
    have hTc : IsCompact (G.e i '' (closure (G.W i) ∩ closure (G.V j))) :=
      ((isClosed_closure.inter isClosed_closure).isCompact).image_of_continuousOn
        ((G.e i).continuousOn.mono (inter_subset_left.trans (G.closure_W_subset i)))
    have hcont : ContinuousOn (deriv (⇑(G.e j) ∘ ⇑(G.e i).symm))
        (G.e i '' (closure (G.W i) ∩ closure (G.V j))) := by
      rintro _ ⟨p, hp, rfl⟩
      have hps : p ∈ (G.e i).source := G.closure_W_subset i hp.1
      have h1 : AnalyticAt ℂ (⇑(G.e j) ∘ ⇑(G.e i).symm) (G.e i p) := by
        refine analyticAt_trans (G.e_mem_maximalAtlas j) (G.e_mem_maximalAtlas i)
          ((G.e i).map_source hps) ?_
        rw [(G.e i).left_inv hps]
        exact G.closureV_subset_source j hp.2
      exact h1.deriv.continuousAt.continuousWithinAt
    exact hTc.exists_bound_of_continuousOn hcont
  choose Cb hCb using hbd
  set M : ℝ := ∑ p : Fin G.n × Fin G.n, max (Cb p.1 p.2) 0 with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => le_max_right _ _
  refine ⟨M, hM0, ?_⟩
  intro η hη i z hz
  -- the base point lies in some inner set `V j`
  obtain ⟨j, hj⟩ := G.exists_mem_V ((G.e i).symm z)
  have hpW : (G.e i).symm z ∈ G.W i := G.symm_mem_W hz
  have hpsi : (G.e i).symm z ∈ (G.e i).source := G.W_subset_source i hpW
  have hpsj : (G.e i).symm z ∈ (G.e j).source := G.V_subset_source j hj
  -- transition to chart `j`
  have hzim : z ∈ ⇑(G.e i) '' ((G.e j).source ∩ (G.e i).source) :=
    ⟨(G.e i).symm z, ⟨hpsj, hpsi⟩, (G.e i).right_inv (G.U_subset_target i hz)⟩
  have htrans := coeffIn_trans (G.e_mem_maximalAtlas j) (G.e_mem_maximalAtlas i) η hzim
  rw [htrans, norm_mul]
  -- bound the transition derivative
  have hzT : z ∈ G.e i '' (closure (G.W i) ∩ closure (G.V j)) :=
    ⟨(G.e i).symm z, ⟨subset_closure hpW, subset_closure hj⟩,
      (G.e i).right_inv (G.U_subset_target i hz)⟩
  have h1 : ‖deriv (⇑(G.e j) ∘ ⇑(G.e i).symm) z‖ ≤ M :=
    (hCb i j z hzT).trans <| (le_max_left _ _).trans <|
      Finset.single_le_sum (f := fun p : Fin G.n × Fin G.n => max (Cb p.1 p.2) 0)
        (fun p _ => le_max_right _ _) (Finset.mem_univ (i, j))
  -- bound the transported coefficient
  have h2 : ‖coeffIn (G.e j) η (G.e j ((G.e i).symm z))‖ ≤ 1 :=
    (G.norm_coeffIn_le_of_mem_K η (G.mem_K_of_mem_V hj)).trans hη
  calc ‖deriv (⇑(G.e j) ∘ ⇑(G.e i).symm) z‖ * ‖coeffIn (G.e j) η (G.e j ((G.e i).symm z))‖
      ≤ M * 1 := mul_le_mul h1 h2 (norm_nonneg _) hM0
    _ = M := mul_one M

/-- Unit-ball coefficient tuples lie in the Montel families. -/
theorem J_mem_montelFamily [CompactSpace X] {C : ℝ}
    (hC : ∀ η : Form1 X, ‖G.J η‖ ≤ 1 → ∀ i, ∀ z ∈ G.U i, ‖coeffIn (G.e i) η z‖ ≤ C)
    {η : Form1 X} (hη : ‖G.J η‖ ≤ 1) (i : Fin G.n) :
    G.J η i ∈ montelFamily (G.U i) (G.K i) C :=
  ⟨coeffIn (G.e i) η,
    ((η.analyticOnNhd_coeffIn (G.e_mem_maximalAtlas i)).mono
      (G.U_subset_target i)).differentiableOn,
    fun z hz => hC η hη i z hz, fun _ => rfl⟩

/-! ### Closedness of the unit ball of the image -/

open scoped Classical in
/-- The (junk-extended) limit coefficient function on `K i` of a convergent tuple. -/
def gext (f : G.P) (i : Fin G.n) : ℂ → ℂ :=
  fun z => if h : z ∈ G.K i then f i ⟨z, h⟩ else 0

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem gext_apply (f : G.P) {i : Fin G.n} {z : ℂ} (hz : z ∈ G.K i) :
    G.gext f i z = f i ⟨z, hz⟩ := dite_eq_left hz

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem continuousOn_gext (f : G.P) (i : Fin G.n) :
    ContinuousOn (G.gext f i) (G.K i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (G.K i).domRestrict (G.gext f i) = ⇑(f i) := funext fun z => G.gext_apply f z.2
  rw [this]
  exact (f i).continuous

/-- Convergence in `P` gives uniform convergence of the coefficient functions on each `K i`. -/
theorem tendstoUniformlyOn_coeffIn [CompactSpace X] {η : ℕ → Form1 X} {f : G.P}
    (hlim : Tendsto (fun m => G.J (η m)) atTop (𝓝 f)) (i : Fin G.n) :
    TendstoUniformlyOn (fun m z => coeffIn (G.e i) (η m) z) (G.gext f i) atTop (G.K i) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hi : Tendsto (fun m => G.J (η m) i) atTop (𝓝 (f i)) := tendsto_pi_nhds.mp hlim i
  filter_upwards [Metric.tendsto_nhds.mp hi ε hε] with m hm z hz
  calc dist (G.gext f i z) (coeffIn (G.e i) (η m) z)
      = dist (f i ⟨z, hz⟩) (G.J (η m) i ⟨z, hz⟩) := by rw [G.gext_apply f hz]; rfl
    _ ≤ dist (f i) (G.J (η m) i) := ContinuousMap.dist_apply_le_dist _
    _ < ε := by rwa [dist_comm] at hm

/-- Weierstrass: the limit coefficient functions are analytic on the open sets `O i`. -/
theorem analyticOnNhd_gext [CompactSpace X] {η : ℕ → Form1 X} {f : G.P}
    (hlim : Tendsto (fun m => G.J (η m)) atTop (𝓝 f)) (i : Fin G.n) :
    AnalyticOnNhd ℂ (G.gext f i) (G.O i) := by
  have hloc : TendstoLocallyUniformlyOn (fun m z => coeffIn (G.e i) (η m) z) (G.gext f i)
      atTop (G.O i) :=
    ((G.tendstoUniformlyOn_coeffIn hlim i).mono (G.O_subset_K i)).tendstoLocallyUniformlyOn
  have hdiff : DifferentiableOn ℂ (G.gext f i) (G.O i) :=
    hloc.differentiableOn
      (Filter.Eventually.of_forall fun m =>
        (((η m).analyticOnNhd_coeffIn (G.e_mem_maximalAtlas i)).mono
          (G.O_subset_target i)).differentiableOn)
      (G.isOpen_O i)
  exact hdiff.analyticOnNhd (G.isOpen_O i)

/-- The limit coefficient functions satisfy the transition compatibility (pointwise limits of
the stagewise `coeffIn_trans` identities). -/
theorem gext_compat [CompactSpace X] {η : ℕ → Form1 X} {f : G.P}
    (hlim : Tendsto (fun m => G.J (η m)) atTop (𝓝 f)) (i j : Fin G.n) {x : X}
    (hxi : x ∈ G.V i) (hxj : x ∈ G.V j) :
    G.gext f j (G.e j x) =
      deriv (⇑(G.e i) ∘ ⇑(G.e j).symm) (G.e j x) * G.gext f i (G.e i x) := by
  have hxsi : x ∈ (G.e i).source := G.V_subset_source i hxi
  have hxsj : x ∈ (G.e j).source := G.V_subset_source j hxj
  have hm : ∀ m, coeffIn (G.e j) (η m) (G.e j x) =
      deriv (⇑(G.e i) ∘ ⇑(G.e j).symm) (G.e j x) * coeffIn (G.e i) (η m) (G.e i x) := by
    intro m
    have hz : G.e j x ∈ ⇑(G.e j) '' ((G.e i).source ∩ (G.e j).source) :=
      ⟨x, ⟨hxsi, hxsj⟩, rfl⟩
    have h := coeffIn_trans (G.e_mem_maximalAtlas i) (G.e_mem_maximalAtlas j) (η m) hz
    rwa [(G.e j).left_inv hxsj] at h
  have h1 : Tendsto (fun m => coeffIn (G.e j) (η m) (G.e j x)) atTop
      (𝓝 (G.gext f j (G.e j x))) :=
    (G.tendstoUniformlyOn_coeffIn hlim j).tendsto_at (G.mem_K_of_mem_V hxj)
  have h2 : Tendsto
      (fun m => deriv (⇑(G.e i) ∘ ⇑(G.e j).symm) (G.e j x) * coeffIn (G.e i) (η m) (G.e i x))
      atTop (𝓝 (deriv (⇑(G.e i) ∘ ⇑(G.e j).symm) (G.e j x) * G.gext f i (G.e i x))) :=
    tendsto_const_nhds.mul
      ((G.tendstoUniformlyOn_coeffIn hlim i).tendsto_at (G.mem_K_of_mem_V hxi))
  exact tendsto_nhds_unique ((tendsto_congr hm).mp h1) h2

/-- **Closedness** (design §2.6 step 5): the unit ball of the range of `J` is closed in `P` —
uniform limits of coefficient tuples are reassembled into a holomorphic 1-form via
`Form1.ofCoeffs` over the restricted charts. -/
theorem isClosed_ball_inter_range [CompactSpace X] :
    IsClosed (Metric.closedBall (0 : G.P) 1 ∩ Set.range G.J) := by
  rw [← isSeqClosed_iff_isClosed]
  intro F f hF hlim
  choose η hη using fun m => (hF m).2
  have hlim' : Tendsto (fun m => G.J (η m)) atTop (𝓝 f) := by
    refine hlim.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact (hη m).symm
  -- the limit coefficient data over the restricted charts
  obtain ⟨D, hDchart, hDcoeff⟩ : ∃ D : Form1CoeffData X (Fin G.n),
      (∀ i, D.chart i = (G.e i).restr (G.V i)) ∧ ∀ i, D.coeff i = G.gext f i := by
    refine ⟨⟨fun i => (G.e i).restr (G.V i),
      fun i => restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ)) (G.e_mem_maximalAtlas i)
        (G.isOpen_V i),
      fun x => ?_, G.gext f, fun i => ?_, fun i j x hx => ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨i, hi⟩ := G.exists_mem_V x
      exact ⟨i, G.mem_restr_source hi⟩
    · rw [G.restr_target_eq i]
      exact G.analyticOnNhd_gext hlim' i
    · -- compatibility, inherited in the limit
      rw [G.restr_source_eq i, G.restr_source_eq j] at hx
      exact G.gext_compat hlim' i j hx.1.2 hx.2.2
  refine ⟨Metric.isClosed_closedBall.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun m => (hF m).1), Form1.ofCoeffs D, ?_⟩
  -- the reassembled form has coefficient tuple `f`
  funext i
  ext z
  change coeffIn (G.e i) (Form1.ofCoeffs D) ↑z = f i z
  have heqO : Set.EqOn (coeffIn (G.e i) (Form1.ofCoeffs D)) (G.gext f i) (G.O i) := by
    intro w hw
    have hw' : w ∈ (D.chart i).target := by
      rw [hDchart i, G.restr_target_eq i]
      exact hw
    have h := Form1.coeffIn_ofCoeffs D i hw'
    rw [hDchart i, coeffIn_restr] at h
    rw [h, hDcoeff i]
  have heqK : Set.EqOn (coeffIn (G.e i) (Form1.ofCoeffs D)) (G.gext f i) (G.K i) :=
    eqOn_of_eqOn_of_subset_closure (G.O_subset_K i) (G.K_subset_closure_O i)
      ((((Form1.ofCoeffs D).analyticOnNhd_coeffIn (G.e_mem_maximalAtlas i)).continuousOn).mono
        (G.K_subset_target i))
      (G.continuousOn_gext f i) heqO
  rw [heqK z.2]
  exact G.gext_apply f z.2

/-- **Compactness** (Montel + closedness): the unit ball of the range of `J` is compact. -/
theorem isCompact_ball_inter_range [CompactSpace X] :
    IsCompact (Metric.closedBall (0 : G.P) 1 ∩ Set.range G.J) := by
  obtain ⟨C, -, hC⟩ := G.exists_montel_bound
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun i =>
      isCompact_closure_montelFamily (G.isOpen_U i) (G.isCompact_K i) (G.K_subset_U i) C)
    (G.isClosed_ball_inter_range) ?_
  rintro p ⟨hp1, η, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  exact subset_closure
    (G.J_mem_montelFamily hC (by rwa [Metric.mem_closedBall, dist_zero_right] at hp1) i)

end GoodCover

/-! ### Riesz and the instance -/


/-- **Finite-dimensionality of the space of holomorphic 1-forms** on a compact Riemann surface
(design §2.6 step 6): the coefficient embedding has compact unit ball, so its range is
finite-dimensional by Riesz, and `J` is injective. This is what makes `genus` honest. -/
instance [T2Space X] [CompactSpace X] : FiniteDimensional ℂ (Form1 X) := by
  obtain ⟨G⟩ := GoodCover.nonempty (X := X)
  have hcomp : IsCompact (Metric.closedBall (0 : LinearMap.range G.J) 1) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_closedBall]
    change IsCompact (Metric.closedBall (0 : G.P) 1 ∩ Set.range G.J)
    exact G.isCompact_ball_inter_range
  let hfd : FiniteDimensional ℂ (LinearMap.range G.J) :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hcomp
  exact (LinearEquiv.ofInjective G.J G.J_injective).symm.finiteDimensional

end RS

end
