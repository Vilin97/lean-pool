/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia.Iteration
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia.LevelRecursion
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia.Admissibility
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.Basic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.MatchedTrace
public import LeanPool.CoarseGraining.Homogenization.Sobolev.MatchedPair
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding

/-!
# The generic one-sided De Giorgi core

The purely analytic heart of the coupled Stampacchia estimate on an axis cube
`U = axisCube z L`.  Given two `H¹` functions `w₁, w₂` sharing a boundary trace,
a median `m₀` with the one-sided median inequality, and the level-energy estimate
in `F4`-RHS shape, the essential supremum of `w₁ − m₀` over `U` is bounded by
`C_d · L · E₀`.

The proof combines the truncation toolbox (`D1`, `D4`), the matched-pair Sobolev
inequality (`F4`), Chebyshev (`real_chebyshev_level`), the squared level recursion
(`sq_level_recursion_of_le`), the admissibility algebra (`deGiorgi_admissible`)
and the iteration engine (`deGiorgi_levelVolume_tendsto_zero`).
-/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **Generic one-sided De Giorgi core.**

There is a dimensional constant `Cd ≥ 0` such that: for every axis cube
`U = axisCube z L` of side `L > 0`, every pair `w₁ w₂ : H1Function U` with
measurable representatives sharing a trace (`w₁ − w₂ ∈ H¹₀`), every median level
`m₀` obeying the one-sided median inequality, and every level-energy bound with
constant `E₀ ≥ 0` in `F4`-RHS shape, one has `w₁ ≤ m₀ + Cd·L·E₀` almost
everywhere on `U`. -/
theorem deGiorgi_one_sided_core {d : ℕ} (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L →
        ∀ (w₁ w₂ : H1Function (axisCube z L)),
          Measurable w₁.toFun → Measurable w₂.toFun →
          MemH10 (axisCube z L) (fun x => w₁.toFun x - w₂.toFun x) →
          ∀ (m₀ E₀ : ℝ), 0 ≤ E₀ →
          MeasureTheory.volume {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x}
              + MeasureTheory.volume {x | x ∈ axisCube z L ∧ m₀ < w₂.toFun x}
              ≤ MeasureTheory.volume (axisCube z L) →
          (∀ k : ℝ, 0 ≤ k →
            (∑ i : Fin d, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
                  (fun x => w₁.grad x i)) 2 (volumeMeasureOn (axisCube z L))).toReal)
              + (∑ i : Fin d, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
                  (fun x => w₂.grad x i)) 2 (volumeMeasureOn (axisCube z L))).toReal)
              ≤ E₀ * Real.sqrt
                  ((MeasureTheory.volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
                    + (MeasureTheory.volume
                        {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) →
          ∀ᵐ x ∂(volumeMeasureOn (axisCube z L)), w₁.toFun x ≤ m₀ + Cd * L * E₀ := by
  classical
  have : NeZero d := ⟨by omega⟩
  -- Sobolev constants (dimensional).
  obtain ⟨C_F, hC_F0, hF⟩ := matchedPair_sobolev hd
  obtain ⟨CE, hCEpos, hEmb⟩ := cube_sobolev_embedding hd
  -- Exponent bookkeeping.
  set p : ℝ≥0∞ := (twoStar d : ℝ≥0∞) with hp_def
  have hdR : (2 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 2 < d)
  have hd2pos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hp_ne_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.coe_ne_top
  have h2led : (2 : ℝ≥0) ≤ (d : ℝ≥0) := by exact_mod_cast (by omega : 2 ≤ d)
  have hq_val : p.toReal = 2 * (d : ℝ) / ((d : ℝ) - 2) := by
    rw [hp_def, ENNReal.coe_toReal, twoStar, NNReal.coe_div, NNReal.coe_sub h2led,
      NNReal.coe_mul]
    norm_num
  have hq_pos : 0 < p.toReal := by rw [hq_val]; positivity
  have hp_ne_zero : p ≠ 0 := fun h => by rw [h] at hq_pos; simp at hq_pos
  -- Real exponents `α = q/2`, `β = α − 1`, `γ = 2/q`, `B = 4^α`.
  set q : ℝ := p.toReal with hq_def
  have hqne : q ≠ 0 := hq_pos.ne'
  set α : ℝ := q / 2 with hα_def
  set β : ℝ := α - 1 with hβ_def
  set γ : ℝ := 2 / q with hγ_def
  set B : ℝ := (4 : ℝ) ^ α with hB_def
  have hq2 : 2 < q := by rw [hq_val, lt_div_iff₀ hd2pos]; linarith
  have hα1 : 1 < α := by rw [hα_def]; linarith
  have hαpos : 0 < α := lt_trans one_pos hα1
  have hβpos : 0 < β := by rw [hβ_def]; linarith
  have hγα : γ * α = 1 := by
    rw [hγ_def, hα_def]; field_simp
  have hdβ : (d : ℝ) * β = 2 * α := by
    rw [hβ_def, hα_def, hq_val]; field_simp; ring
  have hBpos : 0 < B := by rw [hB_def]; exact Real.rpow_pos_of_pos (by norm_num) _
  -- The final dimensional constant.
  set Cd : ℝ := C_F * B ^ (1 / (2 * β)) + 1 with hCd_def
  have hCd_pos : 0 < Cd := by
    rw [hCd_def]
    have : 0 ≤ C_F * B ^ (1 / (2 * β)) :=
      mul_nonneg hC_F0 (Real.rpow_nonneg hBpos.le _)
    linarith
  refine ⟨Cd, hCd_pos.le, ?_⟩
  intro z L hL w₁ w₂ hw₁meas hw₂meas hmatch m₀ E₀ hE₀ hmedian hlevel
  -- Domain facts (spelled out to keep defeq with `hF`/`hmatch`).
  have hUdom : IsOpenBoundedConvexDomain (axisCube z L) :=
    isOpenBoundedConvexDomain_axisCube z L
  have hUmeas : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have hμfinI : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) :=
    hUdom.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hab : (z : Vec d) ≤ fun i => z i + L := fun i => le_add_of_nonneg_right hL.le
  have hVolU_top : volume (axisCube z L) ≠ ⊤ := by
    rw [axisCube, Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hVolU_toReal : (volume (axisCube z L)).toReal = L ^ d := by
    rw [axisCube, Real.volume_pi_Ioo_toReal hab,
      show (fun i => (z i + L) - z i) = (fun _ : Fin d => L) from by funext i; ring,
      Finset.prod_const]
    simp
  have hSub_top : ∀ (S : Set (Vec d)), S ⊆ axisCube z L → volume S ≠ ⊤ :=
    fun S hSU => ne_top_of_le_ne_top hVolU_top (measure_mono hSU)
  have hμvol : ∀ S : Set (Vec d), S ⊆ axisCube z L →
      (volumeMeasureOn (axisCube z L)) S = volume S := by
    intro S hSU
    show (volume.restrict (axisCube z L)) S = volume S
    rw [Measure.restrict_apply' hUmeas, Set.inter_eq_left.mpr hSU]
  -- Finiteness of the critical-exponent norm via the Sobolev embedding (E1).
  have hfin_2star : ∀ (u : H1Function (axisCube z L)),
      eLpNorm u.toFun p (volumeMeasureOn (axisCube z L)) ≠ ⊤ := by
    intro u
    have hEu := hEmb z L hL u
    have hgrad_ne : ∀ i : Fin d,
        eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      fun i => (u.gradMemL2 i).eLpNorm_lt_top.ne
    have hval_ne : eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      u.memL2.eLpNorm_lt_top.ne
    have hRHS_ne :
        (CE : ℝ≥0∞) * ((∑ i : Fin d,
            eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)))
            + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.2
          ⟨(ENNReal.sum_lt_top.2 fun i _ => (hgrad_ne i).lt_top).ne,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hval_ne⟩)
    exact (lt_of_le_of_lt hEu hRHS_ne.lt_top).ne
  -- The truncation package: `F4` gives the Sobolev level bound for each `k ≥ 0`.
  have htrunc : ∀ k : ℝ, 0 ≤ k → ∃ (fk gk : H1Function (axisCube z L)),
      fk.toFun = (fun x => max (w₁.toFun x - (m₀ + k)) 0) ∧
      gk.toFun = (fun x => max (w₂.toFun x - (m₀ + k)) 0) ∧
      (eLpNorm fk.toFun p (volumeMeasureOn (axisCube z L))).toReal
          + (eLpNorm gk.toFun p (volumeMeasureOn (axisCube z L))).toReal
        ≤ C_F * E₀ * Real.sqrt
            ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
              + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
    intro k hk
    obtain ⟨fk, hfk_tf, hfk_grad⟩ := exists_h1_max_sub_const hUdom w₁ (m₀ + k)
    obtain ⟨gk, hgk_tf, hgk_grad⟩ := exists_h1_max_sub_const hUdom w₂ (m₀ + k)
    refine ⟨fk, gk, hfk_tf, hgk_tf, ?_⟩
    have hfk_meas : Measurable fk.toFun := by
      rw [hfk_tf]; exact (hw₁meas.sub measurable_const).max measurable_const
    have hgk_meas : Measurable gk.toFun := by
      rw [hgk_tf]; exact (hw₂meas.sub measurable_const).max measurable_const
    have hmatch_fg : MemH10 (axisCube z L) (fun x => fk.toFun x - gk.toFun x) := by
      have hfun_eq : (fun x => fk.toFun x - gk.toFun x)
          = (fun x => max (w₁.toFun x - (m₀ + k)) 0 - max (w₂.toFun x - (m₀ + k)) 0) := by
        funext x; rw [hfk_tf, hgk_tf]
      rw [hfun_eq]; exact memH10_max_sub_matched hUdom w₁ w₂ hmatch (m₀ + k)
    have hmaxne : ∀ (w : ℝ), (max (w - (m₀ + k)) 0 ≠ 0) ↔ m₀ + k < w := by
      intro w; rw [ne_eq, max_eq_right_iff, not_le]; constructor <;> intro h <;> linarith
    have hset1 : {x | x ∈ axisCube z L ∧ fk.toFun x ≠ 0}
        = {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x} := by
      ext x; simp only [Set.mem_ofPred_eq, hfk_tf]
      exact and_congr_right fun _ => hmaxne (w₁.toFun x)
    have hset2 : {x | x ∈ axisCube z L ∧ gk.toFun x ≠ 0}
        = {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x} := by
      ext x; simp only [Set.mem_ofPred_eq, hgk_tf]
      exact and_congr_right fun _ => hmaxne (w₂.toFun x)
    have hzero : volume {x | x ∈ axisCube z L ∧ fk.toFun x ≠ 0}
        + volume {x | x ∈ axisCube z L ∧ gk.toFun x ≠ 0} ≤ volume (axisCube z L) := by
      rw [hset1, hset2]
      refine le_trans (add_le_add (measure_mono ?_) (measure_mono ?_)) hmedian
      · intro x hx; exact ⟨hx.1, by have := hx.2; linarith⟩
      · intro x hx; exact ⟨hx.1, by have := hx.2; linarith⟩
    have hF4 := hF z L hL fk gk hfk_meas hgk_meas hmatch_fg hzero
    have hcongr1 :
        (∑ i : Fin d, (eLpNorm (fun x => fk.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
        = ∑ i : Fin d, (eLpNorm
            ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator (fun x => w₁.grad x i))
            2 (volumeMeasureOn (axisCube z L))).toReal := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [hfk_grad, ae_restrict_mem hUmeas] with x hgx hxU
      show fk.grad x i
        = {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator (fun x => w₁.grad x i) x
      rw [hgx]
      by_cases hc : m₀ + k < w₁.toFun x
      · rw [Set.indicator_of_mem (show x ∈ {y | m₀ + k < w₁.toFun y} from hc),
          Set.indicator_of_mem
            (show x ∈ {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x} from ⟨hxU, hc⟩)]
      · rw [Set.indicator_of_notMem (show x ∉ {y | m₀ + k < w₁.toFun y} from hc),
          Set.indicator_of_notMem
            (show x ∉ {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x} from fun h => hc h.2)]
        rfl
    have hcongr2 :
        (∑ i : Fin d, (eLpNorm (fun x => gk.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
        = ∑ i : Fin d, (eLpNorm
            ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator (fun x => w₂.grad x i))
            2 (volumeMeasureOn (axisCube z L))).toReal := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [hgk_grad, ae_restrict_mem hUmeas] with x hgx hxU
      show gk.grad x i
        = {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator (fun x => w₂.grad x i) x
      rw [hgx]
      by_cases hc : m₀ + k < w₂.toFun x
      · rw [Set.indicator_of_mem (show x ∈ {y | m₀ + k < w₂.toFun y} from hc),
          Set.indicator_of_mem
            (show x ∈ {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x} from ⟨hxU, hc⟩)]
      · rw [Set.indicator_of_notMem (show x ∉ {y | m₀ + k < w₂.toFun y} from hc),
          Set.indicator_of_notMem
            (show x ∉ {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x} from fun h => hc h.2)]
        rfl
    rw [hcongr1, hcongr2] at hF4
    calc (eLpNorm fk.toFun p (volumeMeasureOn (axisCube z L))).toReal
            + (eLpNorm gk.toFun p (volumeMeasureOn (axisCube z L))).toReal
        ≤ C_F * ((∑ i : Fin d, (eLpNorm
              ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator (fun x => w₁.grad x i))
              2 (volumeMeasureOn (axisCube z L))).toReal)
            + ∑ i : Fin d, (eLpNorm
              ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator (fun x => w₂.grad x i))
              2 (volumeMeasureOn (axisCube z L))).toReal) := hF4
      _ ≤ C_F * (E₀ * Real.sqrt
              ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
                + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) :=
          mul_le_mul_of_nonneg_left (hlevel k hk) hC_F0
      _ = C_F * E₀ * Real.sqrt
              ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
                + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by ring
  -- Chebyshev exponent facts.
  have hr0 : (0 : ℝ) ≤ 1 / q := by positivity
  have hr1 : (1 : ℝ) / q ≤ 1 := by rw [div_le_one hq_pos]; linarith
  -- The geometric level recursion for the combined level volume.
  have hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l - k) ^ 2 * ((volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal
          + (volume {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^ γ
        ≤ (C_F ^ 2 * E₀ ^ 2) * ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
          + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
    intro k l hk hkl
    obtain ⟨fk, gk, hfk_tf, hgk_tf, hSob⟩ := htrunc k hk
    have hεnn : (0 : ℝ) ≤ l - k := by linarith
    have hfk_meas : Measurable fk.toFun := by
      rw [hfk_tf]; exact (hw₁meas.sub measurable_const).max measurable_const
    have hgk_meas : Measurable gk.toFun := by
      rw [hgk_tf]; exact (hw₂meas.sub measurable_const).max measurable_const
    have hSsub1 : ∀ x ∈ {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}, (l - k) ≤ fk.toFun x := by
      intro x hx; rw [hfk_tf]; have hxlt : m₀ + l < w₁.toFun x := hx.2
      rw [le_max_iff]; left; linarith
    have hSsub2 : ∀ x ∈ {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}, (l - k) ≤ gk.toFun x := by
      intro x hx; rw [hgk_tf]; have hxlt : m₀ + l < w₂.toFun x := hx.2
      rw [le_max_iff]; left; linarith
    have hcheb1 := real_chebyshev_level hp_ne_zero hp_ne_top hfk_meas.aestronglyMeasurable
      (hfin_2star fk) hεnn hSsub1
    have hcheb2 := real_chebyshev_level hp_ne_zero hp_ne_top hgk_meas.aestronglyMeasurable
      (hfin_2star gk) hεnn hSsub2
    rw [hμvol _ (fun x hx => hx.1), ← hq_def] at hcheb1
    rw [hμvol _ (fun x hx => hx.1), ← hq_def] at hcheb2
    have hkey := sq_level_recursion_of_le (ε := l - k) (r := 1 / q)
      (a := (volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal)
      (b := (volume {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) hεnn hr0 hr1
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hcheb1 hcheb2 hSob (by positivity)
    have hexp : (2 : ℝ) * (1 / q) = γ := by rw [hγ_def]; ring
    have hRsq : (C_F * E₀ * Real.sqrt
          ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
            + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) ^ 2
        = (C_F ^ 2 * E₀ ^ 2) * ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
            + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    calc (l - k) ^ 2 * ((volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal
            + (volume {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^ γ
        = (l - k) ^ 2 * ((volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal
            + (volume {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^ (2 * (1 / q)) := by
          rw [← hexp]
      _ ≤ (C_F * E₀ * Real.sqrt
              ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
                + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) ^ 2 := hkey
      _ = (C_F ^ 2 * E₀ ^ 2) * ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
            + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := hRsq
  -- Split on `E₀ = 0`.
  rcases eq_or_lt_of_le hE₀ with hE0 | hE0pos
  · -- `E₀ = 0`: the level energy vanishes, so `w₁ ≤ m₀` a.e.
    obtain ⟨f0, g0, hf0_tf, hg0_tf, hSob0⟩ := htrunc 0 le_rfl
    have hf0nn : 0 ≤ (eLpNorm f0.toFun p (volumeMeasureOn (axisCube z L))).toReal :=
      ENNReal.toReal_nonneg
    have hg0nn : 0 ≤ (eLpNorm g0.toFun p (volumeMeasureOn (axisCube z L))).toReal :=
      ENNReal.toReal_nonneg
    have hzeroRHS : C_F * E₀ * Real.sqrt
        ((volume {x | x ∈ axisCube z L ∧ m₀ + 0 < w₁.toFun x}).toReal
          + (volume {x | x ∈ axisCube z L ∧ m₀ + 0 < w₂.toFun x}).toReal) = 0 := by
      rw [← hE0]; ring
    rw [hzeroRHS] at hSob0
    have hf0z : (eLpNorm f0.toFun p (volumeMeasureOn (axisCube z L))).toReal = 0 :=
      le_antisymm (by linarith) hf0nn
    have hf0eLp : eLpNorm f0.toFun p (volumeMeasureOn (axisCube z L)) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hf0z |>.resolve_right (hfin_2star f0)
    have hf0ae : f0.toFun =ᵐ[volumeMeasureOn (axisCube z L)] 0 :=
      (eLpNorm_eq_zero_iff f0.memL2.1 hp_ne_zero).mp hf0eLp
    filter_upwards [hf0ae] with x hx
    simp only [Pi.zero_apply] at hx
    rw [hf0_tf] at hx
    have hxmax : max (w₁.toFun x - (m₀ + 0)) 0 = 0 := hx
    have hle0 : w₁.toFun x - (m₀ + 0) ≤ 0 := by
      by_contra h; push Not at h; rw [max_eq_left h.le] at hxmax; linarith
    rw [← hE0]; simp only [mul_zero, add_zero]; linarith
  · -- `0 < E₀`: run the iteration engine.
    set K : ℝ := Cd * L * E₀ with hK_def
    have hK_pos : 0 < K := by rw [hK_def]; positivity
    have hLd_pos : 0 < (volume (axisCube z L)).toReal := by rw [hVolU_toReal]; positivity
    have ha0 : (volume {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K 0 < w₁.toFun x}).toReal
          + (volume {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K 0 < w₂.toFun x}).toReal
        ≤ (volume (axisCube z L)).toReal := by
      rw [deGiorgiLevel_zero]
      have hmed' :
          volume {x | x ∈ axisCube z L ∧ m₀ + (0 : ℝ) < w₁.toFun x}
            + volume {x | x ∈ axisCube z L ∧ m₀ + (0 : ℝ) < w₂.toFun x}
            ≤ volume (axisCube z L) := by
        rw [show (fun x => x ∈ axisCube z L ∧ m₀ + (0 : ℝ) < w₁.toFun x)
              = (fun x => x ∈ axisCube z L ∧ m₀ < w₁.toFun x) from by funext x; rw [add_zero],
          show (fun x => x ∈ axisCube z L ∧ m₀ + (0 : ℝ) < w₂.toFun x)
              = (fun x => x ∈ axisCube z L ∧ m₀ < w₂.toFun x) from by funext x; rw [add_zero]]
        exact hmedian
      have hmono := ENNReal.toReal_mono hVolU_top hmed'
      rwa [ENNReal.toReal_add (hSub_top _ (fun x hx => hx.1)) (hSub_top _ (fun x hx => hx.1))]
        at hmono
    have hchoice : C_F * ((4 : ℝ) ^ α) ^ (1 / (2 * β)) ≤ Cd := by
      rw [hCd_def, ← hB_def]; linarith
    have hKcond :
        ((C_F ^ 2 * E₀ ^ 2) / K ^ 2) ^ α * B * ((volume (axisCube z L)).toReal) ^ β
          ≤ B ^ (-(1 / β)) := by
      rw [hVolU_toReal, hK_def, hB_def]
      exact deGiorgi_admissible hαpos hβpos hβ_def hdβ hC_F0 hE0pos hL hCd_pos hchoice
    have hlimit := deGiorgi_levelVolume_tendsto_zero
      (a := fun k => (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal
        + (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)
      (Ld := (volume (axisCube z L)).toReal) (Crec := C_F ^ 2 * E₀ ^ 2) (K := K)
      (α := α) (β := β) (γ := γ) (B := B)
      (hnn := fun k => by positivity) (hLd := hLd_pos) (hCrec := by positivity)
      (hK := hK_pos) (hα1 := hα1) (hβ := hβ_def) (hγα := hγα) (hB := hB_def)
      (ha0 := ha0) (hrec := hrec) (hKcond := hKcond)
    set T : Set (Vec d) := {x | x ∈ axisCube z L ∧ m₀ + K < w₁.toFun x} with hT_def
    have hT_top : volume T ≠ ⊤ := hSub_top _ (fun x hx => hx.1)
    have hT0 : volume T = 0 := by
      refine measure_eq_zero_of_toReal_tendsto hT_top ?_ hlimit
      intro n
      have hTsub : T ⊆ {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K n < w₁.toFun x} := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        have hlt : deGiorgiLevel K n < K := deGiorgiLevel_lt hK_pos n
        have := hx.2; linarith
      have h1 : (volume T).toReal
          ≤ (volume {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K n < w₁.toFun x}).toReal :=
        ENNReal.toReal_mono (hSub_top _ (fun x hx => hx.1)) (measure_mono hTsub)
      have h2 : (0 : ℝ)
          ≤ (volume {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K n < w₂.toFun x}).toReal :=
        ENNReal.toReal_nonneg
      linarith
    refine (MeasureTheory.ae_iff).mpr ?_
    have hset : {x | ¬ (w₁.toFun x ≤ m₀ + Cd * L * E₀)} = {x | m₀ + K < w₁.toFun x} := by
      ext x; rw [hK_def]; simp only [Set.mem_ofPred_eq, not_le]
    rw [hset]
    show (volume.restrict (axisCube z L)) {x | m₀ + K < w₁.toFun x} = 0
    rw [Measure.restrict_apply' hUmeas]
    have hTeq : {x | m₀ + K < w₁.toFun x} ∩ axisCube z L = T := by
      rw [hT_def]; ext x; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hTeq]; exact hT0
