/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Surface.Barriers
import LeanPool.Rado.Surface.Germs
import LeanPool.Rado.Topology.PoincareVolterra

/-!
# Assembly: Radó's theorem

Step 8 of `Rado/PLAN.md`: normalize a chart to contain the standard
configuration (`exists_config_chart`), run Perron + barriers to get a
nonconstant harmonic function on the connected open `configY e`, apply the
Poincaré–Volterra lemma to the evaluation map on a connected component of the
étale space of conjugate germs, descend along the open covering projection
(`secondCountable_configY`), and cover `X` by that set together with a chart
ball (`secondCountableTopology_of_riemannSurface`).
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Assembly -/

section Assembly

variable [T2Space X] [ConnectedSpace X]

omit [T2Space X] [ConnectedSpace X] in
/-- Some maximal-atlas chart has target containing the standard configuration
ball (affine renormalization of any chart,
`Rado.affine_trans_mem_riemannAtlas`). -/
theorem exists_config_chart [Nonempty X] :
    ∃ e ∈ riemannAtlas X, ball (0 : ℂ) 8 ⊆ e.target := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have he₀ := chartAt_mem_riemannAtlas x₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (chartAt ℂ x₀).open_target _
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have hρC : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have ha : (8 / (ρ:ℂ)) ≠ 0 := div_ne_zero (by norm_num) hρC
  obtain ⟨e', he', hsrc, hval⟩ := affine_trans_mem_riemannAtlas he₀ (a := 8/(ρ:ℂ))
    (b := -(8/(ρ:ℂ)) * (chartAt ℂ x₀ x₀)) ha
  refine ⟨e', he', ?_⟩
  intro w hw
  set z := chartAt ℂ x₀ x₀ + ((ρ:ℂ)/8) * w with hz
  have hzball : z ∈ ball (chartAt ℂ x₀ x₀) ρ := by
    rw [mem_ball, dist_eq_norm]
    have hzz : z - chartAt ℂ x₀ x₀ = ((ρ:ℂ)/8) * w := by rw [hz]; ring
    rw [hzz, norm_mul]
    have h1 : ‖((ρ:ℂ)/8)‖ = ρ/8 := by
      rw [norm_div]
      simp [abs_of_pos hρ]
    rw [h1]
    have hw8 : ‖w‖ < 8 := by rwa [mem_ball, dist_zero_right] at hw
    calc ρ/8 * ‖w‖ < ρ/8 * 8 := by
          exact mul_lt_mul_of_pos_left hw8 (by positivity)
      _ = ρ := by field_simp
  have hzt : z ∈ (chartAt ℂ x₀).target := hball hzball
  have hxs : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source := (chartAt ℂ x₀).map_target hzt
  have hval' := hval _ hxs
  rw [(chartAt ℂ x₀).right_inv hzt] at hval'
  have hwz : e' ((chartAt ℂ x₀).symm z) = w := by
    rw [hval', hz]
    field_simp
    ring
  have hmem : (chartAt ℂ x₀).symm z ∈ e'.source := by rw [hsrc]; exact hxs
  rw [← hwz]
  exact e'.map_source hmem

/-- Transfer of local second countability to an open subspace. -/
theorem locally_secondCountable_subtype {Z : Type*} [TopologicalSpace Z] {C : Set Z}
    (h : ∀ z ∈ C, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U)
    (q : C) : ∃ W : Set C, q ∈ W ∧ IsOpen W ∧ SecondCountableTopology W := by
  obtain ⟨U, hqU, hUo, hUsc⟩ := h q.1 q.2
  refine ⟨Subtype.val ⁻¹' U, hqU, hUo.preimage continuous_subtype_val, ?_⟩
  have := hUsc
  exact (Topology.IsEmbedding.subtypeVal.restrictPreimage U).secondCountableTopology

/-- The heart of the proof: `Y = configY e` is second countable, via Perron,
the étale space of conjugate germs, and Poincaré–Volterra. -/
theorem secondCountable_configY {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ riemannAtlas X) (hb : ball (0 : ℂ) 8 ⊆ e.target) :
    SecondCountableTopology (configY e) := by
  classical
  set Y : Set X := configY e with hY_def
  have hYo : IsOpen Y := isOpen_configY hb
  have hYc : IsPreconnected Y := (isConnected_configY hb).isPreconnected
  set u : X → ℝ := perronSup (configFamily e) with hu_def
  have hu : SurfaceHarmonicOn u Y :=
    (isPerronFamily_configFamily hb).surfaceHarmonicOn_perronSup hYo
  -- the two witness points and nonconstancy of the Perron envelope
  obtain ⟨hwp, hwm⟩ := witness_mem_configY hb
  have hne : u (e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4)))
      ≠ u (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := by
    have h1 := perronSup_le_witness he hb
    have h2 := perronSup_ge_witness he hb
    rw [← hu_def] at h1 h2
    intro hcon
    rw [hcon] at h1
    linarith
  -- ambient instances
  have : LocallyCompactSpace X := Rado.locallyCompactSpace
  have : LocallyConnectedSpace X := Rado.locallyConnectedSpace
  have : T2Space (ConjEtale u Y) := ConjEtale.t2Space
  have : LocallyCompactSpace (ConjEtale u Y) := ConjEtale.locallyCompactSpace
  have : LocallyConnectedSpace (ConjEtale u Y) := ConjEtale.locallyConnectedSpace
  -- a germ over the witness point and its connected component
  obtain ⟨q₀, hq₀⟩ := ConjEtale.exists_mk hu hYo hwm
  set C : Set (ConjEtale u Y) := connectedComponent q₀ with hC_def
  have hCopen : IsOpen C := isOpen_connectedComponent
  have : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  have : LocallyCompactSpace C := hCopen.locallyCompactSpace
  have : LocallyConnectedSpace C := hCopen.locallyConnectedSpace
  -- Poincaré–Volterra for the evaluation on the component
  have hCsc : SecondCountableTopology C := by
    refine poincare_volterra
      (locally_secondCountable_subtype fun z _ ↦
        ConjEtale.locally_secondCountable z)
      (f := fun q : C ↦ ConjEtale.eval q.1)
      (ConjEtale.continuous_eval.comp continuous_subtype_val) ?_
    intro q
    obtain ⟨U, hU, hUdisc⟩ := ConjEtale.eval_discrete_fibers hu hYo hYc hwm hwp hne q.1
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro w hw heval
    exact Subtype.ext (hUdisc w.1 hw heval)
  -- descend along the restricted projection
  have hCY : ∀ q : C, ConjEtale.proj q.1 ∈ Y := fun q ↦ q.1.2.1
  set g : C → Y := fun q ↦ ⟨ConjEtale.proj q.1, hCY q⟩ with hg_def
  have hgcont : Continuous g :=
    Continuous.subtype_mk
      ((ConjEtale.continuous_proj).comp continuous_subtype_val) hCY
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨q, hqC, hqy⟩ := ConjEtale.surjOn_proj_connectedComponent hu hYo hYc q₀ y.2
    exact ⟨⟨q, hqC⟩, Subtype.ext hqy⟩
  have hgopen : IsOpenMap g := by
    intro T hT
    obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.mp hT
    have himg : g '' (Subtype.val ⁻¹' T')
        = Subtype.val ⁻¹' (ConjEtale.proj (u := u) (Y := Y) '' (T' ∩ C)) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.1, ⟨hq, q.2⟩, rfl⟩
      · rintro ⟨q, ⟨hqT, hqC⟩, hqy⟩
        exact ⟨⟨q, hqC⟩, hqT, Subtype.ext hqy⟩
    rw [himg]
    exact (ConjEtale.isOpenMap_proj _ (hT'.inter hCopen)).preimage continuous_subtype_val
  exact (hgopen.isQuotientMap hgcont hgsurj).secondCountableTopology hgopen

/-- **Radó's theorem**, instance form: a connected Hausdorff Riemann surface is
second countable. `X = configY e ∪ (chart ball)`, both open and second
countable. -/
theorem secondCountableTopology_of_riemannSurface : SecondCountableTopology X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · -- the empty surface: empty cover
    refine Rado.secondCountableTopology_of_countable_setCover (𝒰 := ∅) countable_empty
      (fun U hU ↦ absurd hU (notMem_empty U))
      (fun U hU ↦ absurd hU (notMem_empty U)) ?_
    rw [sUnion_empty]
    exact (univ_eq_empty_iff.mpr hX).symm
  · obtain ⟨e, he, hb⟩ := exists_config_chart (X := X)
    have hopen₂ : IsOpen (e.symm '' ball (0 : ℂ) 8 : Set X) :=
      e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hb)
    have hsc₂ : SecondCountableTopology (e.symm '' ball (0 : ℂ) 8 : Set X) := by
      have := e.secondCountableTopology_source
      have hsub : (e.symm '' ball (0 : ℂ) 8 : Set X) ⊆ e.source := by
        rintro x ⟨w, hw, rfl⟩
        exact e.map_target (hb hw)
      exact (Topology.IsEmbedding.inclusion hsub).secondCountableTopology
    refine Rado.secondCountableTopology_of_countable_setCover
      (𝒰 := {configY e, e.symm '' ball (0 : ℂ) 8}) ((countable_singleton _).insert _)
      ?_ ?_ ?_
    · rintro U (rfl | rfl)
      · exact isOpen_configY hb
      · exact hopen₂
    · rintro U (rfl | rfl)
      · exact secondCountable_configY he hb
      · exact hsc₂
    · rw [sUnion_insert, sUnion_singleton, eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1
      · right
        rcases hx with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
        · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
        · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
      · exact Or.inl ⟨mem_univ _, hx⟩

end Assembly

end Rado
