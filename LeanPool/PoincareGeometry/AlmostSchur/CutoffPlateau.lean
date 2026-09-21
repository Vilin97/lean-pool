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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCutoffGraph
public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientWeakDerivative
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.MetricSpace.Thickening

/-! # Smooth compact plateaus and support-safe quotient agreement

Compact inner supports have a uniform translation margin inside an open
plateau. All quotient identities below use only interior endpoints.
-/

@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A compact support inside an open set has one margin for both signs of every
translation vector. The bound uses the displacement `|h| * ‖v‖`. -/
theorem exists_uniform_translation_margin {S O : Set E} (hS : IsCompact S)
    (hO : IsOpen O) (hSO : S ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (v : E) (h : ℝ), |h| * ‖v‖ < ε →
      (∀ z ∈ S, z + h • v ∈ O ∧ z - h • v ∈ O) ∧
      (fun z => z + h • v) ⁻¹' S ⊆ O ∧
      (fun z => z + (-h) • v) ⁻¹' S ⊆ O := by
  obtain ⟨ε, hε, he⟩ := hS.exists_thickening_subset_open hO hSO
  have hnear (z : E) (hz : z ∈ S) (a : E) (ha : ‖a‖ < ε) : z + a ∈ O := by
    apply he
    apply mem_thickening_iff.mpr
    exact ⟨z, hz, by simpa [dist_eq_norm] using ha⟩
  refine ⟨ε, hε, ?_⟩
  intro v h hh
  have ha : ‖h • v‖ < ε := by simpa [norm_smul, Real.norm_eq_abs] using hh
  have hn : ‖-(h • v)‖ < ε := by simpa using ha
  refine ⟨fun z hz => ⟨hnear z hz _ ha, by simpa [sub_eq_add_neg] using hnear z hz _ hn⟩, ?_, ?_⟩
  · intro z hz
    simpa using hnear (z + h • v) hz (-(h • v)) hn
  · intro z hz
    simpa [neg_smul] using hnear (z + (-h) • v) hz (h • v) ha

/-- A genuine smooth compact cutoff inside W is identically one on an open
neighborhood of S containing all sufficiently small translations of S. -/
theorem exists_smooth_compact_plateau {S W : Set E} (hS : IsCompact S)
    (hW : IsOpen W) (hSW : S ⊆ W) :
    ∃ (χ : E → ℝ) (O : Set E) (ε : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ W ∧
      (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧ IsOpen O ∧ S ⊆ O ∧ O ⊆ W ∧
      EqOn χ (fun _ => 1) O ∧ 0 < ε ∧
      ∀ (v : E) (h : ℝ), |h| * ‖v‖ < ε →
        (∀ z ∈ S, z + h • v ∈ O ∧ z - h • v ∈ O) ∧
        (fun z => z + h • v) ⁻¹' S ⊆ O ∧
        (fun z => z + (-h) • v) ⁻¹' S ⊆ O := by
  obtain ⟨L, hL, hSL, hLW⟩ := exists_compact_between hS hW hSW
  obtain ⟨χ, hχ1, hχ0, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, E)) hS.isClosed hSL (n := (⊤ : ℕ∞))
  obtain ⟨O, hO, hSO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  have hsχ : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  obtain ⟨ε, hε, he⟩ := exists_uniform_translation_margin hS (hO.inter hW)
    (subset_inter hSO hSW)
  refine ⟨χ, O ∩ W, ε, χ.contMDiff.contDiff, hL.of_isClosed_subset (isClosed_tsupport _) hsχ,
    hsχ.trans hLW, hχrange, hO.inter hW, subset_inter hSO hSW, inter_subset_right,
    fun z hz => hOχ hz.1, hε, he⟩

/-- Choosing S as the support of the inner cutoff covers both that support and
the support of its full derivative, with the same uniform translation margin. -/
theorem exists_smooth_plateau_for_cutoff (η : E → ℝ) (hcη : HasCompactSupport η)
    {W : Set E} (hW : IsOpen W) (hηW : tsupport η ⊆ W) :
    ∃ (χ : E → ℝ) (O : Set E) (ε : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ W ∧
      (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧ IsOpen O ∧ tsupport η ⊆ O ∧ O ⊆ W ∧
      EqOn χ (fun _ => 1) O ∧ 0 < ε ∧
      ∀ (v : E) (h : ℝ), |h| * ‖v‖ < ε →
        (∀ z ∈ tsupport η ∪ tsupport (fderiv ℝ η), z + h • v ∈ O ∧ z - h • v ∈ O) ∧
        (fun z => z + h • v) ⁻¹' tsupport η ⊆ O ∧
        (fun z => z + (-h) • v) ⁻¹' tsupport η ⊆ O := by
  obtain ⟨χ, O, ε, hχ, hcχ, hsχ, hr, hO, hηO, hOW, hχ1, hε, he⟩ :=
    exists_smooth_compact_plateau hcη hW hηW
  refine ⟨χ, O, ε, hχ, hcχ, hsχ, hr, hO, hηO, hOW, hχ1, hε, ?_⟩
  intro v h hh
  obtain ⟨he, hp, hn⟩ := he v h hh
  refine ⟨?_, hp, hn⟩
  intro z hz
  exact he z (hz.elim id (fun hz => tsupport_fderiv_subset ℝ hz))

omit [FiniteDimensional ℝ E] in
/-- The derivative vanishes everywhere inside an open constant plateau. -/
theorem fderiv_eq_zero_on_plateau {χ : E → ℝ} {O : Set E}
    (hO : IsOpen O) (hχ : EqOn χ (fun _ => 1) O) {z : E} (hz : z ∈ O) :
    fderiv ℝ χ z = 0 := by
  have he : χ =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact hχ hy
  simpa using he.fderiv_eq

variable [MeasurableSpace E] [BorelSpace E]

/-- Local AE agreement transfers to actual quotients whenever both endpoints
remain in the agreement region. No derivative of a zero extension is used. -/
theorem differenceQuotient_ae_eq_of_local_agreement
    (q : Lp ℝ 2 (volume : Measure E)) (f : E → ℝ) {S O : Set E}
    (hq : ∀ᵐ z ∂(volume : Measure E), z ∈ O → q z = f z)
    (hSO : S ⊆ O) (v : E) (h : ℝ) (hshift : ∀ z ∈ S, z + h • v ∈ O) :
    ∀ᵐ z ∂(volume : Measure E), z ∈ S →
      directionalDifferenceQuotient q v h z = h⁻¹ * (f (z + h • v) - f z) := by
  have ht := (measurePreserving_add_right (volume : Measure E) (h • v)).quasiMeasurePreserving.ae hq
  filter_upwards [directionalDifferenceQuotient_ae_eq q v h, hq, ht] with z hz hq ht
  intro hs
  rw [hz, hq (hSO hs), ht (hshift z hs)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The same inner support covers every directional derivative of the inner cutoff. -/
theorem cutoff_derivative_support_subset_plateau {η : E → ℝ} {O : Set E}
    (hη : tsupport η ⊆ O) (v : E) :
    tsupport (fun z => fderiv ℝ η z v) ⊆ O :=
  (tsupport_fderiv_apply_subset ℝ v).trans hη

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- The actual localized energy graph agrees with uncut coordinate data on a
plateau. Its quotients therefore agree wherever both endpoints remain there. -/
theorem exists_energyCutoffGraph_plateau {ι : Type*} (b : ι → E)
    (c : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (χ : E → ℝ) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ K) {O : Set E} (hO : IsOpen O)
    (hχ1 : EqOn χ (fun _ => 1) O) :
    ∃ P : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (volume : Measure E),
    ∃ Q : ι → EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (volume : Measure E),
      (∀ u, (P u, fun i => Q i u) ∈ closure (c1SupportedTestGraph b (tsupport χ))) ∧
      (∀ u, ∀ᵐ z ∂(volume : Measure E), z ∈ O →
        P u z = energyCompletionToL2 u ((extChartAt I c).symm z)) ∧
      (∀ u i, ∀ᵐ z ∂(volume : Measure E), z ∈ O →
        Q i u z = energyChartDerivative c hK hKt (b i) u z) ∧
      ∀ (S : Set E), S ⊆ O → ∀ (v : E) (h : ℝ), (∀ z ∈ S, z + h • v ∈ O) →
        (∀ u, ∀ᵐ z ∂(volume : Measure E), z ∈ S →
          directionalDifferenceQuotient (P u) v h z = h⁻¹ *
            (energyCompletionToL2 u ((extChartAt I c).symm (z + h • v)) -
              energyCompletionToL2 u ((extChartAt I c).symm z))) ∧
        (∀ u i, ∀ᵐ z ∂(volume : Measure E), z ∈ S →
          directionalDifferenceQuotient (Q i u) v h z = h⁻¹ *
            (energyChartDerivative c hK hKt (b i) u (z + h • v) -
              energyChartDerivative c hK hKt (b i) u z)) := by
  obtain ⟨P, Q, hP, hQ, hg⟩ := exists_energyCutoffGraph (I := I) b c hK hKt χ hχ hcχ hχK
  have hp (u) : ∀ᵐ z ∂(volume : Measure E), z ∈ O →
      P u z = energyCompletionToL2 u ((extChartAt I c).symm z) := by
    filter_upwards [hP u] with z hz
    intro ho
    simpa only [chartCutoff, hχ1 ho, one_mul] using hz
  have hq (u) (i) : ∀ᵐ z ∂(volume : Measure E), z ∈ O →
      Q i u z = energyChartDerivative c hK hKt (b i) u z := by
    filter_upwards [hQ u i] with z hz
    intro ho
    simpa only [hχ1 ho, fderiv_eq_zero_on_plateau hO hχ1 ho,
      zero_apply, zero_mul, one_mul, zero_add] using hz
  refine ⟨P, Q, hg, hp, hq, ?_⟩
  intro S hSO v h hshift
  exact ⟨fun u => differenceQuotient_ae_eq_of_local_agreement (P u) _ (hp u) hSO v h hshift,
    fun u i => differenceQuotient_ae_eq_of_local_agreement (Q i u) _ (hq u i) hSO v h hshift⟩

end AlmostSchur
