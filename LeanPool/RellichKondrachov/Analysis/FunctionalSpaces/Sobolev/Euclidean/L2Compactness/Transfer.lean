/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTransfer : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessTransfer : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessTransfer : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

private lemma dist_smoothL2_le_mul_dist_smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
      dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
        (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict (Kψ (K := K) (ψ := ψ)))) ^
            ((2 : ℝ≥0∞).toReal⁻¹) *
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
              (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < ∞ :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  haveI : Fact ((volume : Measure E) s < ∞) := ⟨hs_lt_top⟩
  haveI : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  intro u v
  set Su :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  set Sv :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
  set Bu :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
  set Bv :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
  have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
  -- Work on `F := Su - Sv` and restrict to the finite-measure set `s`.
  let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
  let g : E → ℝ := fun x => (F : E → ℝ) x
  have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
  have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
  let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
  -- Show `Fs` is pointwise bounded by `‖Bu - Bv‖` on `μs`.
  have hF_ae :
      (g =ᵐ[μs] fun x : E =>
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x) := by
    have hsub :
        (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
      simpa [F, g, Su, Sv] using
        (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
    have hu :
        (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
    have hv :
        (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
    have hF :
        (F : E → ℝ) =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
      have h := hsub.trans (hu.sub hv)
      filter_upwards [h] with x hx
      simpa [Pi.sub_apply] using hx
    exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
  have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
    simpa [Fs, g] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
  have hbound :
      ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
    have hpoint :
        ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
          ‖Bu - Bv‖ := by
      intro x hx
      let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
      have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
        simp [Bu, x']
      have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
        simp [Bv, x']
      have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
        (Bu - Bv).norm_coe_le_norm x'
      simpa [hBu, hBv] using this
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
        hFs_ae, hF_ae] with x hx hFs hF
    have := hpoint x hx
    -- rewrite through the AE equalities
    simpa [hFs, hF] using this
  have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
    have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
      (f := Fs) (hC := hBuBv) hbound)
    simpa [mS] using this
  -- Relate the `L²` norm on `volume` to the restricted norm on `μs` using extension-by-zero.
  have hsupport :
      ∀ x : E, x ∉ s →
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x = 0 := by
    intro x hx
    have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
    have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
    have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
      simpa [Function.support] using this
    have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
      simpa [Function.support] using this
    simp [hu0, hv0]
  have hF0 :
      ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
    have hF_ae_full :
        (g =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x -
              smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        have h := hsub.trans (hu.sub hv)
        filter_upwards [h] with x hx
        simpa [Pi.sub_apply] using hx
      simpa [g] using hF
    filter_upwards [hF_ae_full] with x hx
    intro hxnot
    have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
      hsupport x hxnot
    simpa [hx] using this
  have hF_ind :
      (s.indicator g =ᵐ[(volume : Measure E)] g) := by
    filter_upwards [hF0] with x hx
    by_cases hxmem : x ∈ s
    · simp [g, hxmem]
    · have : g x = 0 := hx hxmem
      simp [g, hxmem, this]
  -- Conclude `‖F‖ = ‖Fs‖` using `extendByZeroₗᵢ` and the indicator identity.
  let Fext :
      MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
    (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
      (s := s) hs) Fs
  have hFext_ae :
      ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
          E → ℝ) =ᵐ[(volume : Measure E)]
        s.indicator fun x : E => (Fs : E → ℝ) x := by
    simpa [Fext] using
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
        (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
        (s := s) hs Fs)
  have hFs_on :
      ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
    -- rewrite the AE equality `Fs = g` on the restricted measure as an implication on `volume`
    have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
    simpa [g] using this
  have hindicator :
      (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
    filter_upwards [hFs_on] with x hx
    by_cases hxmem : x ∈ s
    · simp [hxmem, hx hxmem]
    · simp [hxmem]
  have hFext_ae' :
      (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
    exact hFext_ae.trans (hindicator.trans hF_ind)
  have hFext_eq : Fext = F := by
    refine MeasureTheory.Lp.ext ?_
    simpa [g, F] using hFext_ae'
  have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
    -- use `‖F‖ = ‖Fs‖` via the isometry.
    have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
      simp [Fext]
    -- `Fext = F` and `Fs` is bounded.
    have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
      simpa [hnorm_ext] using hnorm_Fs
    simpa [hFext_eq] using this
  -- Convert to the `dist` statement.
  simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using hnorm_F

theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < ∞ :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  haveI : Fact ((volume : Measure E) s < ∞) := ⟨hs_lt_top⟩
  haveI : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :=
    dist_smoothL2_le_mul_dist_smoothBCF (K := K) (ψ := ψ) hK hKm hψc hψcs
  have hTB_B : TotallyBounded B := by
    -- Use a finite `BCF` ε-net for `A` with centers in the image, then transfer to `L²`.
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    · let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have hmS0' :
            (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict s) : ℝ) ^
              ((2 : ℝ≥0∞).toReal⁻¹) = 0 := hmS0
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          have hle' := hle
          simp only [s] at hmS0'
          rw [hmS0', zero_mul] at hle'
          simpa [c] using hle'
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      -- membership in the open ball follows from `dist = 0` and `ε > 0`
      simpa [Metric.mem_ball, hdist0] using hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let δ : ℝ := ε / mS
      have hδpos : 0 < δ := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := δ) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x δ :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < δ := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < δ := by
          simpa [hf_eq] using hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * δ := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * δ = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * δ = mS * (ε / mS) := by simp [δ]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa using (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      -- show the chosen center lies in `tL2`
      exact ⟨f', rfl⟩
  -- Compactness follows from total boundedness + completeness of `L²`.
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
