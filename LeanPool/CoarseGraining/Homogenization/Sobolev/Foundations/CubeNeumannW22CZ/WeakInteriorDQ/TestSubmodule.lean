/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Order.Filter.Finite

/-! # Test Submodule -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

/-- Monotonicity of concentric closed cube dilations. -/
theorem scaledClosedCubeSet_mono {d : ℕ} (Q : TriadicCube d) {ρ σ : ℝ}
    (hρσ : ρ ≤ σ) :
    scaledClosedCubeSet Q ρ ⊆ scaledClosedCubeSet Q σ := by
  intro x hx k
  exact (hx k).trans (mul_le_mul_of_nonneg_right hρσ (cubeRadius_nonneg Q))

/-- The open concentric subcube is contained in the corresponding closed
concentric subcube. -/
theorem scaledOpenCubeSet_subset_scaledClosedCubeSet {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) :
    scaledOpenCubeSet Q ρ ⊆ scaledClosedCubeSet Q ρ := by
  intro x hx i
  exact le_of_lt (hx i)

/-- Open concentric subcubes are open subsets of the ambient Euclidean space. -/
theorem isOpen_scaledOpenCubeSet {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) :
    IsOpen (scaledOpenCubeSet Q ρ) := by
  unfold scaledOpenCubeSet
  rw [show {x : Vec d | ∀ i, |x i - cubeCenter Q i| < ρ * cubeRadius Q} =
      ⋂ i : Fin d, {x : Vec d | |x i - cubeCenter Q i| < ρ * cubeRadius Q} by
    ext x
    simp]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Iio.preimage
      ((continuous_abs.comp ((continuous_apply i).sub continuous_const)))

/-- Nonnegative scaled open subcubes have finite Lebesgue measure. -/
theorem volume_scaledOpenCubeSet_ne_top_of_nonneg {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    MeasureTheory.volume (scaledOpenCubeSet Q ρ) ≠ ⊤ := by
  have hle :
      MeasureTheory.volume (scaledOpenCubeSet Q ρ) ≤
        MeasureTheory.volume (scaledClosedCubeSet Q ρ) :=
    MeasureTheory.measure_mono (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ)
  exact ne_top_of_le_ne_top (isCompact_scaledClosedCubeSet Q hρ).measure_ne_top hle

/-- A small coordinate shift of a point in a smaller concentric closed cube
remains in a larger concentric closed cube. -/
theorem euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
    {d : ℕ} (Q : TriadicCube d) {ρ σ step : ℝ} (hρσ : ρ ≤ σ)
    (hstep : |step| ≤ (σ - ρ) * cubeRadius Q) (i : Fin d) {x : Vec d}
    (hx : x ∈ scaledClosedCubeSet Q ρ) :
    euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ := by
  intro k
  by_cases hki : k = i
  · subst k
    calc
      |euclideanCoordShift step i x i - cubeCenter Q i| =
          |(x i - cubeCenter Q i) + step| := by
            simp [euclideanCoordShift, basisVec]
            ring_nf
      _ ≤ |x i - cubeCenter Q i| + |step| := abs_add_le _ _
      _ ≤ ρ * cubeRadius Q + (σ - ρ) * cubeRadius Q := add_le_add (hx i) hstep
      _ = σ * cubeRadius Q := by ring
  · calc
      |euclideanCoordShift step i x k - cubeCenter Q k| =
          |x k - cubeCenter Q k| := by
            simp [euclideanCoordShift, basisVec, hki]
      _ ≤ ρ * cubeRadius Q := hx k
      _ ≤ σ * cubeRadius Q := mul_le_mul_of_nonneg_right hρσ (cubeRadius_nonneg Q)

/-- A concentric closed subcube with relative radius strictly below one lies in
the open triadic cube. -/
theorem scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
    {d : ℕ} (Q : TriadicCube d) {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1) :
    scaledClosedCubeSet Q ρ ⊆ openCubeSet Q := by
  intro x hx
  rw [← ball_cubeCenter_eq_openCubeSet]
  have hxball :
      x ∈ Metric.closedBall (cubeCenter Q) (ρ * cubeRadius Q) :=
    scaledClosedCubeSet_subset_metricClosedBall Q hρ_nonneg hx
  have hrad_lt : ρ * cubeRadius Q < cubeRadius Q := by
    have hrad_pos : 0 < cubeRadius Q := cubeRadius_pos Q
    nlinarith
  exact Metric.closedBall_subset_ball hrad_lt hxball

namespace QuantitativeCubeCutoff

/-- The topological support of a quantitative cube cutoff is contained in its
outer closed subcube. -/
theorem tsupport_subset_scaledClosedCubeSet_of_support_subset
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    tsupport (η : Vec d → ℝ) ⊆ scaledClosedCubeSet Q ρ₂ := by
  have hsupp :
      Function.support (η : Vec d → ℝ) ⊆ scaledClosedCubeSet Q ρ₂ := by
    intro x hx i
    exact le_of_lt (η.support_subset hx i)
  simpa [tsupport] using closure_minimal hsupp (isClosed_scaledClosedCubeSet Q ρ₂)

/-- A quantitative cube cutoff whose outer radius is strictly less than one is
supported inside the open triadic cube. -/
theorem tsupport_subset_openCubeSet_of_nonneg_of_lt_one
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hρ₂_nonneg : 0 ≤ ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    tsupport (η : Vec d → ℝ) ⊆ openCubeSet Q :=
  (η.tsupport_subset_scaledClosedCubeSet_of_support_subset).trans
    (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hρ₂_nonneg hρ₂_lt_one)

end QuantitativeCubeCutoff

/-- If a real scalar lies between zero and one, cutting a vector by that scalar
cannot increase the pointwise norm of the removed tail. -/
private theorem norm_sub_smul_le_norm_of_nonneg_of_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) (v : E) :
    ‖v - c • v‖ ≤ ‖v‖ := by
  have hnorm_factor : ‖(1 - c : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
    linarith
  calc
    ‖v - c • v‖ = ‖(1 - c) • v‖ := by
      congr 1
      simp [sub_smul]
    _ = ‖(1 - c : ℝ)‖ * ‖v‖ := norm_smul (1 - c) v
    _ ≤ 1 * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right hnorm_factor (norm_nonneg v)
    _ = ‖v‖ := by simp

/-- Mathlib's global smooth compact-support density specialized to scalar
`L²` fields on a restricted Lebesgue domain. -/
theorem dense_smoothCompactScalarL2 {d : ℕ} {U : Set (Vec d)} :
    Dense {f : ScalarL2 U |
      ∃ g : Vec d → ℝ,
      ∃ hgL2 : MemScalarL2 U g,
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g} := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hDenseAE :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (E := Vec d) (F := ℝ) (μ := volumeMeasureOn U)
      (p := (2 : ENNReal)) ENNReal.ofNat_ne_top
  refine hDenseAE.mono ?_
  intro f hf
  rcases hf with ⟨g, hfg, hg_compact, hg_cont⟩
  let hgL2 : MemScalarL2 U g := (MeasureTheory.Lp.memLp f).ae_eq hfg
  refine ⟨g, hgL2, ?_, by simpa using hg_cont, hg_compact⟩
  calc
    f = (MeasureTheory.Lp.memLp f).toLp (fun x => f x) :=
      (MeasureTheory.Lp.toLp_coeFn f (MeasureTheory.Lp.memLp f)).symm
    _ = hgL2.toLp g :=
      MeasureTheory.MemLp.toLp_congr (MeasureTheory.Lp.memLp f) hgL2 hfg

/-- Localize a smooth scalar `L²` field to an open finite-measure set without
changing it much in `L²`.  This turns Mathlib's ambient compactly supported
smooth probes into probes whose topological support is contained in `U`. -/
theorem exists_contDiff_scalarL2_tsupport_subset_eLpNorm_sub_le
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤)
    {g : Vec d → ℝ} (hgL2 : MemScalarL2 U g)
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Vec d → ℝ,
      ∃ _hφL2 : MemScalarL2 U φ,
        MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U) ≤ ENNReal.ofReal ε ∧
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    hgL2.eLpNorm_indicator_le (p := (2 : ENNReal)) (by norm_num)
      ENNReal.ofNat_ne_top hε
  obtain ⟨K, hKU, hK_compact, hK_closed, hμK⟩ :=
    hUopen.measurableSet.exists_isCompact_isClosed_sdiff_lt (μ := MeasureTheory.volume)
      hUfinite ((ENNReal.ofReal_pos.mpr hδpos).ne')
  rcases exists_compact_closed_between hK_compact hUopen hKU with
    ⟨L, hL_compact, hL_closed, hKL, hLU⟩
  obtain ⟨η, hη_one, hη_zero, hη_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤) (I := 𝓘(ℝ, Vec d))
      hK_closed hKL
  let φ : Vec d → ℝ := fun x => η x • g x
  have hη_cont : ContDiff ℝ (⊤ : ℕ∞) η := η.contMDiff.contDiff
  have hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ := by
    simpa [φ] using! hη_cont.smul hg_cont
  have hφ_support : Function.support φ ⊆ L := by
    intro x hx
    by_contra hxL
    have hz : η x = 0 := hη_zero x hxL
    exact hx (by simp [φ, hz])
  have hφ_compact : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hL_compact hφ_support
  have hφ_tsupport : tsupport φ ⊆ U := by
    have hφ_tsupport_L : tsupport φ ⊆ L := by
      simpa [tsupport] using closure_minimal hφ_support hL_closed
    exact hφ_tsupport_L.trans hLU
  have hφL2 : MemScalarL2 U φ :=
    hφ_cont.continuous.memLp_of_hasCompactSupport hφ_compact
  refine ⟨φ, hφL2, ?_, hφ_cont, hφ_compact, hφ_tsupport⟩
  have hμsmall : volumeMeasureOn U (U \ K) ≤ ENNReal.ofReal δ := by
    unfold volumeMeasureOn
    rw [MeasureTheory.Measure.restrict_apply (hUopen.measurableSet.diff hK_closed.measurableSet)]
    simpa [Set.inter_eq_self_of_subset_left (Set.sdiff_subset : U \ K ⊆ U)] using hμK.le
  have hindicator := hδ (U \ K) (hUopen.measurableSet.diff hK_closed.measurableSet) hμsmall
  calc
    MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U)
        ≤ MeasureTheory.eLpNorm ((U \ K).indicator g) 2 (volumeMeasureOn U) := by
          refine MeasureTheory.eLpNorm_mono_ae ?_
          have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
            simpa [volumeMeasureOn] using MeasureTheory.ae_restrict_mem hUopen.measurableSet
          filter_upwards [hmem] with x hxU
          by_cases hxK : x ∈ K
          · have hφx : φ x = g x := by
              have hηx : η x = 1 := hη_one.self_of_nhdsSet x hxK
              simp [φ, hηx]
            simp [hφx, hxK]
          · have hxDiff : x ∈ U \ K := ⟨hxU, hxK⟩
            rw [Set.indicator_of_mem hxDiff]
            have hη01 := hη_range x
            exact norm_sub_smul_le_norm_of_nonneg_of_le_one
              (η x) hη01.1 hη01.2 (g x)
    _ ≤ ENNReal.ofReal ε := hindicator

/-- Smooth compactly supported scalar probes with support contained in an open
finite-measure set are dense in `L²(U)`. -/
theorem dense_smoothCompactSupportScalarL2_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    Dense {f : ScalarL2 U |
      ∃ g : Vec d → ℝ,
      ∃ hgL2 : MemScalarL2 U g,
        f = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
          tsupport g ⊆ U} := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨g, hg_compact, hg_cont, hg_err⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      ENNReal.ofNat_ne_top (by norm_num : (1 : ENNReal) ≤ 2)
      (MeasureTheory.Lp.memLp f) hε2
  have hgL2 : MemScalarL2 U g :=
    hg_cont.continuous.memLp_of_hasCompactSupport hg_compact
  obtain ⟨φ, hφL2, hφ_err, hφ_cont, hφ_compact, hφ_support⟩ :=
    exists_contDiff_scalarL2_tsupport_subset_eLpNorm_sub_le
      hUopen hUfinite hgL2 hg_cont hε2
  refine ⟨hφL2.toLp φ, ?_, ?_⟩
  · exact ⟨φ, hφL2, rfl, hφ_cont, hφ_compact, hφ_support⟩
  · have hnorm :
        MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U) ≤
          ENNReal.ofReal ε := by
      calc
        MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U)
            = MeasureTheory.eLpNorm ((fun x => f x) - φ) 2 (volumeMeasureOn U) := by
              apply MeasureTheory.eLpNorm_congr_ae
              filter_upwards [hφL2.coeFn_toLp] with x hx
              simp [Pi.sub_apply, hx]
        _ = MeasureTheory.eLpNorm (((fun x => f x) - g) + (g - φ)) 2
              (volumeMeasureOn U) := by
              congr 1
              funext x
              simp [Pi.sub_apply]
        _ ≤ MeasureTheory.eLpNorm ((fun x => f x) - g) 2 (volumeMeasureOn U) +
              MeasureTheory.eLpNorm (g - φ) 2 (volumeMeasureOn U) := by
              refine MeasureTheory.eLpNorm_add_le ?_ ?_ (by norm_num : (1 : ENNReal) ≤ 2)
              · exact (MeasureTheory.Lp.aestronglyMeasurable f).sub hgL2.aestronglyMeasurable
              · exact hgL2.aestronglyMeasurable.sub hφL2.aestronglyMeasurable
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hg_err hφ_err
        _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
    rw [Metric.mem_closedBall, dist_comm, MeasureTheory.Lp.dist_def]
    exact ENNReal.toReal_le_of_le_ofReal
      (a := MeasureTheory.eLpNorm (fun x => f x - hφL2.toLp φ x) 2 (volumeMeasureOn U))
      (b := ε) hε.le hnorm

/-- The existing `H1WeakTestFunction` carrier realizes the local smooth scalar
probe density as a dense range in `ScalarL2`. -/
theorem denseRange_h1WeakTestFunction_toScalarL2
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    DenseRange (fun φ : H1WeakTestFunction U => φ.toScalarL2) := by
  refine (dense_smoothCompactSupportScalarL2_tsupport_subset hUopen hUfinite).mono ?_
  intro f hf
  rcases hf with ⟨g, hgL2, hfg, hg_cont, hg_compact, hg_support⟩
  let φ : H1WeakTestFunction U :=
    ⟨g, hg_cont, hg_compact, hg_support⟩
  refine ⟨φ, ?_⟩
  have htoLp : φ.toScalarL2 = hgL2.toLp g := by
    simp [φ, H1WeakTestFunction.toScalarL2, Homogenization.toScalarL2]
  change φ.toScalarL2 = f
  rw [htoLp, ← hfg]

namespace H1WeakTestFunction

/-- Pointwise sum of two smooth weak tests on the same support set. -/
noncomputable def add {d : ℕ} {U : Set (Vec d)}
    (φ ψ : H1WeakTestFunction U) : H1WeakTestFunction U :=
  { toFun := fun z => φ z + ψ z
    smooth := φ.smooth.add ψ.smooth
    compactSupport := φ.compactSupport.add ψ.compactSupport
    support_subset := by
      exact
        (tsupport_add (φ : Vec d → ℝ) (ψ : Vec d → ℝ)).trans
          (Set.union_subset φ.support_subset ψ.support_subset) }

/-- `ScalarL2` class of a pointwise sum of smooth weak tests. -/
theorem toScalarL2_add {d : ℕ} {U : Set (Vec d)}
    (φ ψ : H1WeakTestFunction U) :
    (φ.add ψ).toScalarL2 = φ.toScalarL2 + ψ.toScalarL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [(φ.add ψ).coeFn_toScalarL2, φ.coeFn_toScalarL2, ψ.coeFn_toScalarL2,
        MeasureTheory.Lp.coeFn_add φ.toScalarL2 ψ.toScalarL2]
    with z hθ hφ hψ hadd
  calc
    (φ.add ψ).toScalarL2 z = (φ.add ψ) z := hθ
    _ = φ z + ψ z := rfl
    _ = φ.toScalarL2 z + ψ.toScalarL2 z := by rw [← hφ, ← hψ]
    _ = (φ.toScalarL2 + ψ.toScalarL2) z := by
      rw [hadd]
      rfl

/-- Pointwise scalar multiple of a smooth weak test. -/
noncomputable def smul {d : ℕ} {U : Set (Vec d)}
    (c : ℝ) (φ : H1WeakTestFunction U) : H1WeakTestFunction U :=
  { toFun := fun z => c • φ z
    smooth := by
      simpa using φ.smooth.const_smul c
    compactSupport := by
      simpa using! φ.compactSupport.smul_left (f := fun _ : Vec d => c)
    support_subset := by
      exact
        (tsupport_smul_subset_right (fun _ : Vec d => c) (φ : Vec d → ℝ)).trans
          φ.support_subset }

/-- `ScalarL2` class of a pointwise scalar multiple of a smooth weak test. -/
theorem toScalarL2_smul {d : ℕ} {U : Set (Vec d)}
    (c : ℝ) (φ : H1WeakTestFunction U) :
    (φ.smul c).toScalarL2 = c • φ.toScalarL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [(φ.smul c).coeFn_toScalarL2, φ.coeFn_toScalarL2,
        MeasureTheory.Lp.coeFn_smul c φ.toScalarL2]
    with z hθ hφ hsmul
  calc
    (φ.smul c).toScalarL2 z = (φ.smul c) z := hθ
    _ = c • φ z := rfl
    _ = c • φ.toScalarL2 z := by rw [← hφ]
    _ = (c • φ.toScalarL2) z := by
      rw [hsmul]
      rfl

end H1WeakTestFunction

/-- The scalar `L²` classes represented by smooth compactly supported weak
tests form a submodule of `ScalarL2`. -/
noncomputable def h1WeakTestScalarL2Submodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (ScalarL2 U) where
  carrier := Set.range (fun φ : H1WeakTestFunction U => φ.toScalarL2)
  zero_mem' := by
    let φ : H1WeakTestFunction U :=
      { toFun := 0
        smooth := contDiff_const
        compactSupport := (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
        support_subset := by simp }
    refine ⟨φ, ?_⟩
    simp [φ, H1WeakTestFunction.toScalarL2, Homogenization.toScalarL2]
  add_mem' := by
    rintro x y ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    let θ : H1WeakTestFunction U :=
      { toFun := fun z => φ z + ψ z
        smooth := φ.smooth.add ψ.smooth
        compactSupport := φ.compactSupport.add ψ.compactSupport
        support_subset := by
          exact
            (tsupport_add (φ : Vec d → ℝ) (ψ : Vec d → ℝ)).trans
              (Set.union_subset φ.support_subset ψ.support_subset) }
    refine ⟨θ, ?_⟩
    change θ.toScalarL2 = φ.toScalarL2 + ψ.toScalarL2
    apply MeasureTheory.Lp.ext
    filter_upwards
        [θ.coeFn_toScalarL2, φ.coeFn_toScalarL2, ψ.coeFn_toScalarL2,
          MeasureTheory.Lp.coeFn_add φ.toScalarL2 ψ.toScalarL2]
      with z hθ hφ hψ hadd
    calc
      θ.toScalarL2 z = θ z := hθ
      _ = φ z + ψ z := rfl
      _ = φ.toScalarL2 z + ψ.toScalarL2 z := by rw [← hφ, ← hψ]
      _ = (φ.toScalarL2 + ψ.toScalarL2) z := by
        rw [hadd]
        rfl
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨φ, rfl⟩
    let θ : H1WeakTestFunction U :=
      { toFun := fun z => c • φ z
        smooth := by
          simpa using φ.smooth.const_smul c
        compactSupport := by
          simpa using! φ.compactSupport.smul_left (f := fun _ : Vec d => c)
        support_subset := by
          exact
            (tsupport_smul_subset_right (fun _ : Vec d => c) (φ : Vec d → ℝ)).trans
              φ.support_subset }
    refine ⟨θ, ?_⟩
    change θ.toScalarL2 = c • φ.toScalarL2
    apply MeasureTheory.Lp.ext
    filter_upwards
        [θ.coeFn_toScalarL2, φ.coeFn_toScalarL2,
          MeasureTheory.Lp.coeFn_smul c φ.toScalarL2]
      with z hθ hφ hsmul
    calc
      θ.toScalarL2 z = θ z := hθ
      _ = c • φ z := rfl
      _ = c • φ.toScalarL2 z := by rw [← hφ]
      _ = (c • φ.toScalarL2) z := by
        rw [hsmul]
        rfl

private theorem exists_h1WeakTestScalarL2Representative
    {d : ℕ} {U : Set (Vec d)}
    (x : h1WeakTestScalarL2Submodule (d := d) U) :
    ∃ φ : H1WeakTestFunction U, φ.toScalarL2 = (x : ScalarL2 U) := by
  rcases x with ⟨y, hy⟩
  change ∃ φ : H1WeakTestFunction U, φ.toScalarL2 = y
  change y ∈ Set.range (fun φ : H1WeakTestFunction U => φ.toScalarL2) at hy
  simpa [Set.mem_range] using hy

/-- A chosen smooth weak-test representative of a point in the smooth-test
`ScalarL2` submodule. -/
noncomputable def h1WeakTestScalarL2Representative
    {d : ℕ} {U : Set (Vec d)}
    (x : h1WeakTestScalarL2Submodule (d := d) U) : H1WeakTestFunction U :=
  Classical.choose (exists_h1WeakTestScalarL2Representative x)

/-- The chosen representative realizes the original submodule point. -/
theorem h1WeakTestScalarL2Representative_toScalarL2
    {d : ℕ} {U : Set (Vec d)}
    (x : h1WeakTestScalarL2Submodule (d := d) U) :
    (h1WeakTestScalarL2Representative x).toScalarL2 = (x : ScalarL2 U) :=
  Classical.choose_spec (exists_h1WeakTestScalarL2Representative x)

/-- The smooth weak-test submodule is dense in scalar `L²` on an open
finite-measure set. -/
theorem dense_h1WeakTestScalarL2Submodule
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) :
    Dense (h1WeakTestScalarL2Submodule (d := d) U : Set (ScalarL2 U)) := by
  simpa [h1WeakTestScalarL2Submodule] using!
    denseRange_h1WeakTestFunction_toScalarL2 hUopen hUfinite

/-- Equality of scalar `L²` classes forces zero squared distance for any
chosen representatives. -/
theorem integral_norm_sq_sub_eq_zero_of_toScalarL2_eq
    {d : ℕ} {U : Set (Vec d)} {F G : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hG : MemScalarL2 U G)
    (hFG : toScalarL2 hF = toScalarL2 hG) :
    ∫ x in U, ‖F x - G x‖ ^ (2 : ℝ) ∂MeasureTheory.volume = 0 := by
  have hFG_ae : F =ᵐ[volumeMeasureOn U] G := by
    simpa [toScalarL2] using
      (MeasureTheory.MemLp.toLp_eq_toLp_iff hF hG).1 hFG
  have hzero :
      (fun x => ‖F x - G x‖ ^ (2 : ℝ)) =ᵐ[volumeMeasureOn U] 0 := by
    filter_upwards [hFG_ae] with x hx
    rw [hx, sub_self, norm_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    rfl
  simpa [volumeMeasureOn] using
    MeasureTheory.integral_eq_zero_of_ae
      (μ := MeasureTheory.volume.restrict U) hzero

/-- The square-root integral norm of a scalar representative agrees with the
norm of its `ScalarL2` class. -/
theorem integral_norm_sq_rpow_half_eq_norm_toScalarL2
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → ℝ}
    (hF : MemScalarL2 U F) :
    (∫ x in U, ‖F x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
      ‖toScalarL2 hF‖ := by
  let A : ℝ := ∫ x in U, ‖F x‖ ^ (2 : ℝ) ∂MeasureTheory.volume
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with x
    exact (show (0 : ℝ) ≤ ‖F x‖ ^ (2 : ℝ) from
      Real.rpow_nonneg (norm_nonneg _) _)
  have hroot_sq : (A ^ (1 / (2 : ℝ))) ^ 2 = A := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hA_nonneg
  have hnorm_sq : ‖toScalarL2 hF‖ ^ 2 = A := by
    rw [toScalarL2, MeasureTheory.Lp.norm_toLp]
    have hsq := toReal_eLpNorm_two_sq_eq_integral_sq hF
    rw [hsq]
    dsimp [A]
    congr 1 with x
    simp [sq_abs]
  have hroot_nonneg : 0 ≤ A ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg hA_nonneg _
  have hnorm_nonneg : 0 ≤ ‖toScalarL2 hF‖ := norm_nonneg _
  nlinarith

/-- The previous norm identification specialized to smooth weak tests. -/
theorem integral_norm_sq_rpow_half_eq_norm_h1WeakTestFunction_toScalarL2
    {d : ℕ} {U : Set (Vec d)} (φ : H1WeakTestFunction U) :
    (∫ x in U, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
      ‖φ.toScalarL2‖ := by
  have hφ_mem : MemScalarL2 U φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict U
  have hφ_l2 : toScalarL2 hφ_mem = φ.toScalarL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toScalarL2 hφ_mem, φ.coeFn_toScalarL2] with x hleft hright
    rw [hleft, hright]
  calc
    (∫ x in U, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
        ‖toScalarL2 hφ_mem‖ :=
      integral_norm_sq_rpow_half_eq_norm_toScalarL2 hφ_mem
    _ = ‖φ.toScalarL2‖ := by rw [hφ_l2]

/-- Equality of the `ScalarL2` classes attached to two smooth weak tests
forces zero squared distance between their pointwise representatives. -/
theorem integral_norm_sq_sub_eq_zero_of_h1WeakTestFunction_toScalarL2_eq
    {d : ℕ} {U : Set (Vec d)} (φ ψ : H1WeakTestFunction U)
    (hφψ : φ.toScalarL2 = ψ.toScalarL2) :
    ∫ x in U, ‖φ x - ψ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume = 0 := by
  have hφ_mem : MemScalarL2 U φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict U
  have hψ_mem : MemScalarL2 U ψ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (ψ.smooth.continuous.memLp_of_hasCompactSupport ψ.compactSupport).restrict U
  have hφ_l2 : toScalarL2 hφ_mem = φ.toScalarL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toScalarL2 hφ_mem, φ.coeFn_toScalarL2] with x hleft hright
    rw [hleft, hright]
  have hψ_l2 : toScalarL2 hψ_mem = ψ.toScalarL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toScalarL2 hψ_mem, ψ.coeFn_toScalarL2] with x hleft hright
    rw [hleft, hright]
  exact
    integral_norm_sq_sub_eq_zero_of_toScalarL2_eq hφ_mem hψ_mem
      (by rw [hφ_l2, hψ_l2, hφψ])

/-- Extend a linear functional from the smooth weak-test submodule to all of
scalar `L²` using `LinearMap.extendOfNorm`.  The norm estimate is supplied in
the accompanying agreement and bound lemmas. -/
noncomputable def extendH1WeakTestScalarL2Functional
    {d : ℕ} {U : Set (Vec d)}
    (ℓ : h1WeakTestScalarL2Submodule (d := d) U →ₗ[ℝ] ℝ) :
    ScalarL2 U →L[ℝ] ℝ :=
  LinearMap.extendOfNorm ℓ (h1WeakTestScalarL2Submodule (d := d) U).subtype

/-- The dense-submodule extension agrees with the original functional on
smooth weak-test classes. -/
theorem extendH1WeakTestScalarL2Functional_apply_subtype
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) (C : ℝ)
    (ℓ : h1WeakTestScalarL2Submodule (d := d) U →ₗ[ℝ] ℝ)
    (hℓ : ∀ x, ‖ℓ x‖ ≤ C * ‖((h1WeakTestScalarL2Submodule (d := d) U).subtype x)‖)
    (x : h1WeakTestScalarL2Submodule (d := d) U) :
    extendH1WeakTestScalarL2Functional (d := d) (U := U) ℓ
        ((h1WeakTestScalarL2Submodule (d := d) U).subtype x) =
      ℓ x := by
  have hdense :
      DenseRange ((h1WeakTestScalarL2Submodule (d := d) U).subtype) := by
    simpa [Submodule.subtype] using
      (dense_h1WeakTestScalarL2Submodule (d := d) hUopen hUfinite).denseRange_val
  change
    (LinearMap.extendOfNorm ℓ ((h1WeakTestScalarL2Submodule (d := d) U).subtype))
        ((h1WeakTestScalarL2Submodule (d := d) U).subtype x) =
      ℓ x
  exact LinearMap.extendOfNorm_eq
    (f := ℓ) (e := (h1WeakTestScalarL2Submodule (d := d) U).subtype)
    hdense ⟨C, hℓ⟩ x

/-- The extended functional keeps the same operator bound supplied on the
dense smooth-test submodule. -/
theorem norm_extendH1WeakTestScalarL2Functional_apply_le
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : MeasureTheory.volume U ≠ ⊤) (C : ℝ)
    (ℓ : h1WeakTestScalarL2Submodule (d := d) U →ₗ[ℝ] ℝ)
    (hℓ : ∀ x, ‖ℓ x‖ ≤ C * ‖((h1WeakTestScalarL2Submodule (d := d) U).subtype x)‖)
    (x : ScalarL2 U) :
    ‖extendH1WeakTestScalarL2Functional (d := d) (U := U) ℓ x‖ ≤
      C * ‖x‖ := by
  have hdense :
      DenseRange ((h1WeakTestScalarL2Submodule (d := d) U).subtype) := by
    simpa [Submodule.subtype] using
      (dense_h1WeakTestScalarL2Submodule (d := d) hUopen hUfinite).denseRange_val
  change
    ‖(LinearMap.extendOfNorm ℓ ((h1WeakTestScalarL2Submodule (d := d) U).subtype))
        x‖ ≤
      C * ‖x‖
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := ℓ) (e := (h1WeakTestScalarL2Submodule (d := d) U).subtype)
    hdense C hℓ x

end

end Homogenization
