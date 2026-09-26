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

public import LeanPool.PoincareGeometry.AlmostSchur.ArbitraryWeakPoissonJets
public import LeanPool.PoincareGeometry.AlmostSchur.SmoothWeakPoisson
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurBound
public import LeanPool.PoincareGeometry.AlmostSchur.DensityComparison
public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureSmooth
public import Mathlib.Topology.Compactness.Lindelof

/-!
# The complete weak-to-classical almost-Schur assembly

The local jet theorem is now connected to the actual Riemannian volume.  A
chart restriction is mapped to a positive metric-density measure, hence is
absolutely continuous with respect to Euclidean volume.  Nested compact balls
and a smooth plateau then produce a smooth representative on a neighborhood of
each point; a countable Lindelöf subcover glues these representatives.

The intermediate assembly takes smooth coordinate forcing explicitly.
`smooth_coordinate_forcing` below derives that regularity from the smooth
metric and scalar-curvature regularity theorem. Consequently
`almostSchur_bound_complete` has no additional forcing-regularity hypothesis.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]
  [PreconnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => leviCivitaConnection (I := I) (M := M)

local instance finalMeasurableSpace : MeasurableSpace E := borel E
local instance finalBorelSpace : BorelSpace E := ⟨rfl⟩
local instance finalOpensMeasurableSpace : OpensMeasurableSpace E := by
  infer_instance
local instance finalMeasurableAdd : MeasurableAdd E := by
  infer_instance

local instance finalMetricZero :
    IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance finalContinuousMetric : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance finalMetricTwo :
    IsContMDiffRiemannianBundle I (↑(2 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

local instance finalMetricThree :
    IsContMDiffRiemannianBundle I (↑(3 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))

local instance finalFiberFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

local instance finalFiniteMeasure :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-! ## Coordinate measure transport -/

theorem chart_restrict_map_absolutelyContinuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (c : M) {O : Set E} {U : Set M}
    (hO : IsOpen O) (hOt : O ⊆ (extChartAt I c).target)
    (hU : U = (extChartAt I c).source ∩ (extChartAt I c) ⁻¹' O) :
    AEMeasurable (extChartAt I c)
        ((riemannianVolume (I := I) (M := M)).restrict U) ∧
      Measure.map (extChartAt I c)
          ((riemannianVolume (I := I) (M := M)).restrict U) ≪ volume.restrict O := by
  let φ := extChartAt I c
  have hs : MeasurableSet φ.source :=
    (isOpen_extChartAt_source (I := I) c).measurableSet
  have hφs : AEMeasurable φ
      ((riemannianVolume (I := I) (M := M)).restrict φ.source) :=
    aemeasurable_restrict_of_measurable_subtype hs
      (continuousOn_extChartAt (I := I) c).domRestrict.measurable
  have hUsub : U ⊆ φ.source := by
    rw [hU]
    exact inter_subset_left
  have hφU : AEMeasurable φ
      ((riemannianVolume (I := I) (M := M)).restrict U) := hφs.mono_set hUsub
  have hmap : Measure.map φ
        ((riemannianVolume (I := I) (M := M)).restrict U) =
      (Measure.map φ
        ((riemannianVolume (I := I) (M := M)).restrict φ.source)).restrict O := by
    rw [Measure.restrict_map_of_aemeasurable hφs hO.measurableSet]
    congr 1
    rw [Measure.restrict_restrict₀
      (hφs.nullMeasurableSet_preimage hO.measurableSet), hU]
    rw [inter_comm]
  have hmap' : Measure.map φ
        ((riemannianVolume (I := I) (M := M)).restrict U) =
      (volume.withDensity (fun z => ENNReal.ofReal
        (matrixDensity (coordinateMetric (I := I) b.toBasis c z)))).restrict O := by
    calc
      Measure.map φ
          ((riemannianVolume (I := I) (M := M)).restrict U) =
          (Measure.map φ
            ((riemannianVolume (I := I) (M := M)).restrict φ.source)).restrict O := hmap
      _ = ((b.toBasis.addHaar.withDensity (fun z => ENNReal.ofReal
          (matrixDensity (coordinateMetric (I := I) b.toBasis c z)))).restrict φ.target).restrict O := by
        rw [map_riemannianVolume_restrict_chart b.toBasis c]
      _ = (volume.withDensity (fun z => ENNReal.ofReal
          (matrixDensity (coordinateMetric (I := I) b.toBasis c z)))).restrict O := by
        rw [Measure.restrict_restrict hO.measurableSet,
          inter_eq_left.mpr hOt, b.addHaar_eq_volume]
  exact ⟨hφU, hmap'.symm ▸
    (withDensity_absolutelyContinuous volume _).restrict O⟩

/-! ## One smooth local representative -/

theorem exists_local_smooth_weakPoisson_representative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (c : M)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (u : M → ℝ)
    (huf : u =ᵐ[riemannianVolume (I := I) (M := M)] (f : M → ℝ))
    (hcoord : ContDiffOn ℝ ∞
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        u ((extChartAt I c).symm z)) (extChartAt I c).target) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧
      ∃ q : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ q V ∧
        q =ᵐ[(riemannianVolume (I := I) (M := M)).restrict V]
          energyCompletionToL2 (weakPoissonSolution f) := by
  let φ := extChartAt I c
  obtain ⟨d, hd, hdT⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target c)
    (φ c) (φ.map_source (mem_extChartAt_source c))
  have hdpos : 0 < d := hd
  let r : ℕ → ℝ := fun m => d / 8 + d / (16 * ((m : ℝ) + 1))
  let Kbig : Set E := closedBall (φ c) (d / 2)
  let K : ℕ → Set E := fun m => closedBall (φ c) (r m)
  let Sreg : Set E := closedBall (φ c) (d / 8)
  let Sinner : Set E := closedBall (φ c) (d / 16)
  have hKbig : IsCompact Kbig := isCompact_closedBall _ _
  have hKbig_target : Kbig ⊆ φ.target := by
    exact (closedBall_subset_ball (by linarith : d / 2 < d)).trans hdT
  have hconvbig : Convex ℝ Kbig := convex_closedBall _ _
  have hK0big : K 0 ⊆ interior Kbig := by
    exact (closedBall_subset_ball (by
      dsimp [K, Kbig, r]
      have : 0 < d := hdpos
      norm_num
      linarith)).trans
      ball_subset_interior_closedBall
  have hK : ∀ m, IsCompact (K m) := fun m => isCompact_closedBall _ _
  have hconv : ∀ m, Convex ℝ (K m) := fun m => convex_closedBall _ _
  have hstep : ∀ m, K (m + 1) ⊆ interior (K m) := by
    intro m
    dsimp [K, r]
    have hden : (m : ℝ) + 1 < (m : ℝ) + 2 := by linarith
    have hfrac : d / (16 * ((m : ℝ) + 2)) < d / (16 * ((m : ℝ) + 1)) := by
      apply (div_lt_div_iff_of_pos_left (by positivity) (by positivity) (by positivity)).2
      nlinarith [hden]
    have hmcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by
      push_cast
      ring
    rw [hmcast]
    have hfrac' : d / 8 + d / (16 * ((m : ℝ) + 2)) <
        d / 8 + d / (16 * ((m : ℝ) + 1)) :=
      by simpa [add_comm] using add_lt_add_left hfrac (d / 8)
    exact (closedBall_subset_ball hfrac').trans
      (ball_subset_interior_closedBall (x := φ c)
        (ε := d / 8 + d / (16 * ((m : ℝ) + 1))))
  have hSreg : IsCompact Sreg := isCompact_closedBall _ _
  have hSall : ∀ m, Sreg ⊆ interior (K m) := by
    intro m
    change closedBall (φ c) (d / 8) ⊆ interior (closedBall (φ c) (r m))
    exact (closedBall_subset_ball (by
      change d / 8 < d / 8 + d / (16 * ((m : ℝ) + 1))
      have : 0 < d / (16 * ((m : ℝ) + 1)) := by positivity
      linarith)).trans ball_subset_interior_closedBall
  have hSinner : IsCompact Sinner := isCompact_closedBall _ _
  have hSinner_reg : Sinner ⊆ interior Sreg := by
    change closedBall (φ c) (d / 16) ⊆ interior (closedBall (φ c) (d / 8))
    exact (closedBall_subset_ball (by
      linarith [hdpos])).trans ball_subset_interior_closedBall
  have hKtarget : K 0 ⊆ φ.target := hK0big.trans (interior_subset.trans hKbig_target)
  let Fc : E → ℝ := fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
    u (φ.symm z)
  have hFc : ContDiffOn ℝ ∞ Fc φ.target := by simpa [Fc, φ] using hcoord
  have hFc_ae : Fc =ᵐ[volume.restrict Kbig]
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        f (φ.symm z)) := by
    have hcomp := ae_eq_comp_chart_symm huf c hKbig hKbig_target
    filter_upwards [hcomp] with z hz
    change u (φ.symm z) = f (φ.symm z) at hz
    change matrixDensity (coordinateMetric (I := I) b.toBasis c z) * u (φ.symm z) =
      matrixDensity (coordinateMetric (I := I) b.toBasis c z) * f (φ.symm z)
    rw [hz]
  have hJall := exists_weakPoisson_all_order_jets_on_nested_compacts
    (E := E) (ι := ι) (I := I) (M := M) (Kbig := Kbig) (K := K) (S := Sreg)
    b c hKbig hKbig_target hconvbig hK0big hK hconv hstep hSreg hSall f hf Fc
    hFc hFc_ae
  obtain ⟨v, hJ⟩ := hJall
  obtain ⟨χ, O, ε, hχ, hcχ, hsχ, _, hO, hSO, hOW, hχ1, _, _⟩ :=
    exists_smooth_compact_plateau hSinner isOpen_interior hSinner_reg
  let U := φ.source ∩ φ ⁻¹' O
  have hU : IsOpen U := by
    exact (continuousOn_extChartAt (I := I) c).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) c) hO
  have hcU : c ∈ U := by
    refine ⟨mem_extChartAt_source c, ?_⟩
    exact hSO (mem_closedBall_self (by positivity))
  have hOreg : O ⊆ Sreg := hOW.trans interior_subset
  have hOinner : O ⊆ interior (K 0) := hOreg.trans (hSall 0)
  have hOt : O ⊆ φ.target := hOinner.trans
    (interior_subset.trans hKtarget)
  obtain ⟨hφU, hmapU⟩ := chart_restrict_map_absolutelyContinuous
    (I := I) (M := M) b c hO hOt rfl
  let J : ∀ n : ℕ, LocalL2DerivativeJet (fun i => b i) Sreg n :=
    fun n => (hJ n).choose
  have hJroot : ∀ n, (J n).value [] = v := by
    intro n
    exact (hJ n).choose_spec.2.1
  have hJae : (J 0).value [] =ᵐ[volume.restrict Sreg]
      (fun z => energyCompletionToL2 (weakPoissonSolution f) (φ.symm z)) :=
    (hJ 0).choose_spec.2.2
  have hJroot_fun : ((J 0).value [] : E → ℝ) = (v : E → ℝ) :=
    congrArg (fun q : Lp ℝ 2 (volume : Measure E) => (q : E → ℝ)) (hJroot 0)
  have hOSreg : O ⊆ Sreg := hOW.trans interior_subset
  have hrootO : (v : E → ℝ) =ᵐ[volume.restrict O]
      (fun z => energyCompletionToL2 (weakPoissonSolution f) (φ.symm z)) := by
    rw [← hJroot_fun]
    exact ae_restrict_of_ae_restrict_of_subset hOSreg hJae
  have hvu : (fun x => v (φ x)) =ᵐ[
      (riemannianVolume (I := I) (M := M)).restrict U]
      energyCompletionToL2 (weakPoissonSolution f) := by
    have hc := ae_eq_comp' hφU hrootO hmapU
    filter_upwards [hc, ae_restrict_mem hU.measurableSet] with x hx hxU
    change v (φ x) = energyCompletionToL2 (weakPoissonSolution f) (φ.symm (φ x)) at hx
    rw [φ.left_inv hxU.1] at hx
    exact hx
  obtain ⟨q, hq, hqa⟩ := local_smooth_representative_of_all_jets
    (I := I) (M := M) b c J v hJroot hχ hcχ hsχ hO hχ1
    inter_subset_left hφU hmapU
    (energyCompletionToL2 (weakPoissonSolution f)) hvu
  exact ⟨U, hU, hcU, q, hq, hqa⟩

/-! ## Compact global assembly -/

/-- The complete almost-Schur estimate from smooth coordinate forcing.

The hypothesis `hcoord` is the explicit regularity boundary of this file: it
states that the centered scalar-curvature forcing, after multiplication by the
chart density, is smooth in every exterior chart.  The local jet theorem then
supplies a smooth representative of the weak solution on a neighborhood of
every point, and compactness reduces the resulting cover to a finite (hence
countable) one. -/
theorem almostSchur_bound_of_smooth_coordinate_forcing
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    (hcoord : ∀ c : M, ContDiffOn ℝ ∞
      (fun z => matrixDensity
          (coordinateMetric (I := I) (stdOrthonormalBasis ℝ E).toBasis c z) *
        centeredScalarCurvature (I := I) (M := M)
          ((extChartAt I c).symm z)) (extChartAt I c).target)
    (hd : 2 < (Module.finrank ℝ E : ℝ)) :
    (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
      riemannianMean (I := I)
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
      ∂riemannianVolume (I := I)) ≤
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I)) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  let u : M → ℝ := centeredScalarCurvature (I := I) (M := M)
  let hmem : MemLp u 2 (riemannianVolume (I := I) (M := M)) := by
    simpa [u] using
      (memLp_centeredScalarCurvature (I := I) (M := M))
  let f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)) :=
    MemLp.toLp u hmem
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) 1
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur := by
    intro x
    exact contMDiffAt_scalarCurvature_one
      (leviCivitaConnection (I := I) (M := M))
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion x
  have hf : (∫ x, f x ∂riemannianVolume (I := I) (M := M)) = 0 := by
    rw [integral_congr_ae hmem.coeFn_toLp]
    simpa [u, centeredScalarCurvature] using
      integral_sub_riemannianMean
        ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur)
        hscalar
  have huf : u =ᵐ[riemannianVolume (I := I) (M := M)] (f : M → ℝ) :=
    hmem.coeFn_toLp.symm
  have hlocal : ∀ c : M, ∃ V : Set M, IsOpen V ∧ c ∈ V ∧
      ∃ q : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ q V ∧
        q =ᵐ[(riemannianVolume (I := I) (M := M)).restrict V]
          energyCompletionToL2 (weakPoissonSolution f) := by
    intro c
    exact exists_local_smooth_weakPoisson_representative
      (I := I) (M := M) b c f hf u huf (by
        simpa [b, u] using hcoord c)
  choose V hVopen hcV q hq hqa using hlocal
  have hVcover : (Set.univ : Set M) ⊆ ⋃ c : M, V c := by
    intro x _
    exact mem_iUnion.2 ⟨x, hcV x⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
      V hVopen hVcover
  let ι : Type _ := (t : Set M)
  let U : ι → Set M := fun i => V i.1
  let Q : ι → M → ℝ := fun i => q i.1
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    exact hVopen i.1
  have hQ : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (Q i) (U i) := by
    intro i
    exact hq i.1
  have hUcover : ∀ x, ∃ i : ι, x ∈ U i := by
    intro x
    have hx : x ∈ ⋃ c ∈ t, V c := ht (mem_univ x)
    rcases mem_iUnion₂.1 hx with ⟨c, hct, hxc⟩
    exact ⟨⟨c, hct⟩, hxc⟩
  have hQae : ∀ i, Q i =ᵐ[
      (riemannianVolume (I := I) (M := M)).restrict (U i)]
      energyCompletionToL2 (weakPoissonSolution
        (MemLp.toLp
          (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M)))) := by
    intro i
    have hsame : f =
        MemLp.toLp
          (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M)) := by
      change MemLp.toLp u hmem = _
      exact MemLp.toLp_congr hmem
        (memLp_centeredScalarCurvature (I := I) (M := M)) (by
          filter_upwards [] with x
          rfl)
    rw [← hsame]
    exact hqa i.1
  exact almostSchur_bound_of_local_smooth_representatives
    (I := I) (M := M) hRic U hU hUcover Q hQ hQae hd

/-! ## The smooth coordinate forcing is intrinsic -/

/-- A smooth metric has smooth coordinate density, and the preceding
curvature regularity theorem gives smooth scalar curvature.  Consequently the
coordinate forcing used by the local elliptic bootstrap is not an additional
hypothesis. -/
theorem smooth_coordinate_forcing
    (c : M) :
    ContDiffOn ℝ ∞
      (fun z => matrixDensity
          (coordinateMetric (I := I) (stdOrthonormalBasis ℝ E).toBasis c z) *
        centeredScalarCurvature (I := I) (M := M)
          ((extChartAt I c).symm z)) (extChartAt I c).target := by
  let cov := leviCivitaConnection (I := I) (M := M)
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ cov.scalarCurvatureAlmostSchur :=
    contMDiffAt_scalarCurvature_infty (I := I) cov
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
  have hcenter : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (centeredScalarCurvature (I := I) (M := M)) := by
    change ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x ↦ (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
        riemannianMean (I := I)
          (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur)
    simpa [cov] using
      hscalar.sub (contMDiff_const (c := riemannianMean (I := I) cov.scalarCurvatureAlmostSchur))
  have hcenter_chart : ContDiffOn ℝ ∞
      (fun z => centeredScalarCurvature (I := I) (M := M)
        ((extChartAt I c).symm z)) (extChartAt I c).target := by
    apply ContMDiffOn.contDiffOn
    exact hcenter.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)
  have hdensity : ContDiffOn ℝ ∞
      (fun z => matrixDensity
        (coordinateMetric (I := I) (stdOrthonormalBasis ℝ E).toBasis c z))
      (extChartAt I c).target :=
    contDiffOn_coordinateDensity_of_order (I := I) (∞ : ℕ∞ω)
      (stdOrthonormalBasis ℝ E).toBasis c
  simpa only [Function.comp_apply] using hdensity.mul hcenter_chart

/-- The complete De Lellis--Topping almost-Schur inequality under the stated
geometric hypotheses. -/
theorem almostSchur_bound_complete
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    (hd : 2 < (Module.finrank ℝ E : ℝ)) :
    (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
      riemannianMean (I := I)
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
      ∂riemannianVolume (I := I)) ≤
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I)) := by
  exact almostSchur_bound_of_smooth_coordinate_forcing
    (I := I) (M := M) hRic (fun c => smooth_coordinate_forcing (I := I) (M := M) c) hd

end AlmostSchur
