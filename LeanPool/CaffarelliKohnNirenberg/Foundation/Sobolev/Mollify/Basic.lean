/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# ContDiffBump mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The custom convex-approximation chain was not used here: Mathlib
v4.34 already provides normalized `ContDiffBump` kernels, convolution
regularity, and approximate-identity convergence. This direct port keeps the
kernel and convolution API independent of the sibling geometry layer.
-/

@[expose] public section

open scoped Convolution Topology

namespace CKN

/-- A smooth bump centered at zero with outer radius `ε`. -/
noncomputable def standardMollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump (0 : Vec d) :=
  { rIn := ε / 2
    rOut := ε
    rIn_pos := half_pos hε
    rIn_lt_rOut := half_lt_self hε }

/-- The normalized scalar kernel associated with `standardMollifier`. -/
noncomputable def mollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) : Vec d → ℝ :=
  (standardMollifier ε hε).normed MeasureTheory.volume

theorem mollifier_nonneg {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    0 ≤ mollifier (d := d) ε hε x := by
  exact (standardMollifier (d := d) ε hε).nonneg_normed x

theorem mollifier_integral_one {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Vec d, mollifier (d := d) ε hε x ∂MeasureTheory.volume = 1 := by
  exact (standardMollifier (d := d) ε hε).integral_normed

theorem mollifier_hasCompactSupport {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).hasCompactSupport_normed

theorem mollifier_contDiff {d : ℕ} {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).contDiff_normed

theorem mollifier_locallyIntegrable {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    MeasureTheory.LocallyIntegrable (mollifier (d := d) ε hε)
      MeasureTheory.volume := by
  exact (mollifier_contDiff (d := d) hε (n := 0)).continuous.locallyIntegrable

/-- Convolution of `u` with the normalized radius-`ε` kernel. -/
noncomputable def mollify {d : ℕ} (u : Vec d → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Vec d → ℝ :=
  MeasureTheory.convolution (mollifier (d := d) ε hε) u
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

theorem mollify_contDiff {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    ContDiff ℝ n (mollify u ε hε) := by
  exact (mollifier_hasCompactSupport (d := d) hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_contDiff (d := d) hε) hu

theorem mollify_continuous {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    Continuous (mollify u ε hε) := by
  exact (mollify_contDiff hε hu (n := 0)).continuous

theorem mollify_tendsto_of_continuous {ι : Type*} {l : Filter ι}
    {d : ℕ} {u : Vec d → ℝ} {ε : ι → ℝ}
    (hε : Filter.Tendsto ε l (nhds 0))
    (hε_pos : ∀ i, 0 < ε i) (hu : Continuous u) (x : Vec d) :
    Filter.Tendsto (fun i => mollify u (ε i) (hε_pos i) x) l (nhds (u x)) := by
  let φ : ι → ContDiffBump (0 : Vec d) :=
    fun i => standardMollifier (ε i) (hε_pos i)
  have hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0) := by
    simpa [φ, standardMollifier] using hε
  simpa [φ, mollify, mollifier] using
    (ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := MeasureTheory.volume) hφ hu x)

end CKN
