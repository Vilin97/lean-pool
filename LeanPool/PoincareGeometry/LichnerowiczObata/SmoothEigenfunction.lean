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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ManifoldReactionJets

/-!
# Smooth representatives of weak eigenfunctions

The nested-ball and chart-transport assembly is adapted from
AlmostSchur/AlmostSchurFinal.lean at immutable commit
3faf25aefc27842a77c37ca178e8a40a20bb20c7 of
Arthur742Ramos/lean-poincare-formalization-plan. Here the equation's forcing
is proportional to its weak solution. Smoothness comes from the reaction
bootstrap, not from an assumed smooth forcing.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter Metric AlmostSchur
open scoped Manifold ContDiff Topology BigOperators

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

theorem exists_local_smooth_reaction_representative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (c : M)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (μ : ℝ)
    (hrelation : (f : M → ℝ) =ᵐ[riemannianVolume (I := I) (M := M)]
      (fun x => -μ * energyCompletionToL2 (weakPoissonSolution f) x)) :
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
  let Fc : E → ℝ := fun z => -μ * matrixDensity (coordinateMetric (I := I) b.toBasis c z)
  have hFc : ContDiffOn ℝ ∞ Fc φ.target := by
    exact contDiffOn_const.mul (contDiffOn_coordinateDensity_of_order (I := I) ∞ b.toBasis c)
  have hFc_ae : (fun z => Fc z * energyCompletionToL2 (weakPoissonSolution f) (φ.symm z))
      =ᵐ[volume.restrict Kbig]
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        f (φ.symm z)) := by
    have hcomp := ae_eq_comp_chart_symm hrelation c hKbig hKbig_target
    filter_upwards [hcomp] with z hz
    change f (φ.symm z) = -μ * energyCompletionToL2 (weakPoissonSolution f) (φ.symm z) at hz
    rw [hz]
    dsimp only [Fc]
    ring
  have hJall := exists_reaction_all_order_jets_on_nested_compacts
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

/-- Local reaction regularity glues to a global smooth representative. -/
theorem exists_smooth_reaction_representative
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (μ : ℝ)
    (hrelation : (f : M → ℝ) =ᵐ[riemannianVolume (I := I) (M := M)]
      (fun x => -μ * energyCompletionToL2 (weakPoissonSolution f) x)) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      g =ᵐ[riemannianVolume (I := I)] energyCompletionToL2 (weakPoissonSolution f) := by
  classical
  have hlocal := fun c : M => exists_local_smooth_reaction_representative
    (I := I) (stdOrthonormalBasis ℝ E) c f hf μ hrelation
  choose V hV hcV q hq hqa using hlocal
  have hcover : (Set.univ : Set M) ⊆ ⋃ c : M, V c := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hcV x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  have hsubcover : ∀ x, ∃ i : (t : Set M), x ∈ V i.1 := by
    intro x
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact ⟨⟨c, hc⟩, hxc⟩
  obtain ⟨g, hg, hga, _⟩ := exists_smooth_representative_of_open_cover (I := I)
    (energyCompletionToL2 (weakPoissonSolution f))
    (fun i : (t : Set M) => V i.1) (fun i => hV i.1) hsubcover
    (fun i => q i.1) (fun i => hq i.1) (fun i => hqa i.1)
  exact ⟨g, hg, hga⟩

local notation "W" => (EnergyCompletion (I := I) (M := M))
local notation "J" => (energyCompletionToL2 (I := I) (M := M))
local notation "ν" => (riemannianVolume (I := I) (M := M))
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Every variational eigenvector has a smooth representative satisfying the
actual pointwise Laplace--Beltrami eigen-equation. -/
theorem exists_smooth_variational_eigenfunction {μ : ℝ} {u : W}
    (hvar : ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v)) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      g =ᵐ[ν] J u ∧ ∀ x, laplacian LC g x = -μ * g x := by
  let f : Lp ℝ 2 ν := -μ • J u
  have hue : u = weakPoissonSolution f := variational_eq_weakPoisson hvar
  have hfa : (f : M → ℝ) =ᵐ[ν] (fun x => -μ * J u x) := by
    filter_upwards [Lp.coeFn_smul (-μ) (J u)] with x hx
    exact hx
  have hf : (∫ x, f x ∂ν) = 0 := by
    rw [integral_congr_ae hfa, integral_const_mul, integral_energyCompletionToL2, mul_zero]
  have hrelation : (f : M → ℝ) =ᵐ[ν]
      (fun x => -μ * energyCompletionToL2 (weakPoissonSolution f) x) := by
    simpa only [← hue] using hfa
  obtain ⟨g, hg, hga⟩ := exists_smooth_reaction_representative f hf μ hrelation
  have hgu : g =ᵐ[ν] J u := by simpa only [← hue] using hga
  have hforcing : (fun x => -μ * g x) =ᵐ[ν] f := by
    filter_upwards [hgu, hfa] with x hx hf'
    rw [hx, hf']
  have heq := laplacian_smooth_weakPoisson_representative LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion f hf
    g (fun x => -μ * g x) (hg.of_le (by decide))
    (continuous_const.mul hg.continuous) hga hforcing
  exact ⟨g, hg, hgu, fun x => congrFun heq x⟩

end LichnerowiczObata
