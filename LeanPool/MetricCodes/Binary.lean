/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Foundations

/-!
# Binary-code asymptotics

Asymptotic Johnson-scheme estimates and the binary-code variational bound.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Johnson

section


open Filter Topology
open scoped Topology

namespace Asymptotics

/-- The shell weight used in the Johnson-code argument. -/
def shellWeight (a : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree a n

/-- The support degree used in the Johnson-code argument. -/
def supportDegree (b : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree b n

/-- The complement degree used in the Johnson-code argument. -/
def complementDegree (g : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree g n

/-- The terminal degree used in the Johnson-code argument. -/
def terminalDegree (u : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree u n

theorem tendsto_shellWeight_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (shellWeight a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa only [shellWeight] using MetricCodes.Hamming.tendsto_longitudinal_ratio ha

theorem tendsto_supportDegree_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (supportDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa only [supportDegree] using MetricCodes.Hamming.tendsto_longitudinal_ratio hb

theorem tendsto_complementDegree_ratio {g : ℝ} (hg : 0 ≤ g) :
    Tendsto (fun n : ℕ => (complementDegree g n : ℝ) / (n : ℝ))
      atTop (nhds g) := by
  simpa only [complementDegree] using MetricCodes.Hamming.tendsto_longitudinal_ratio hg

theorem tendsto_terminalDegree_ratio {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (terminalDegree u n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa only [terminalDegree] using MetricCodes.Hamming.tendsto_longitudinal_ratio hu

theorem tendsto_dimension_ratio :
    Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds (1 : ℝ)) := by
  refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  simp only [ne_eq, Nat.cast_eq_zero, hn, not_false_eq_true, div_self]

theorem tendsto_add_degree_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b)) :
    Tendsto
      (fun n : ℕ => ((f n + g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  refine (hf.add hg).congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring

theorem eventually_degree_lt_of_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, f n < g n := by
  have hnegative : a - b < 0 := sub_neg.mpr hab
  have hratio :=
    (hf.sub hg).eventually (gt_mem_nhds hnegative)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)]
    with n hdiff hn
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hquot : (f n : ℝ) / (n : ℝ) <
      (g n : ℝ) / (n : ℝ) := by
    linarith
  have hreal : (f n : ℝ) < (g n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnreal).mp hquot
  exact_mod_cast hreal

theorem tendsto_atTop_of_ratio_pos
    {f : ℕ → ℕ} {a : ℝ}
    (ha : 0 < a)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a)) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  have hratio := hf.eventually (Ioi_mem_nhds (half_lt_self ha))
  have hgrowth :
      Tendsto (fun n : ℕ => (a / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos ha)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hratio' hlarge' hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfreal : (a / 2) * (n : ℝ) < (f n : ℝ) :=
    (lt_div_iff₀ hnreal).mp hratio'
  exact_mod_cast hlarge'.trans hfreal.le

theorem tendsto_sub_degree_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hgf : ∀ᶠ n : ℕ in atTop, g n ≤ f n) :
    Tendsto
      (fun n : ℕ => ((f n - g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a - b)) := by
  refine (hf.sub hg).congr' ?_
  filter_upwards [hgf] with n hn
  rw [Nat.cast_sub hn]
  ring

theorem scaled_binomialEntropy_identity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (a * Real.log a - b * Real.log b -
      (a - b) * Real.log (a - b)) / Real.log 2 =
      a * MetricCodes.binaryEntropy (b / a) := by
  have hab : 0 < a - b := sub_pos.mpr hba
  have hratio : 0 < b / a := div_pos hb ha
  have hcomp : 0 < 1 - b / a := by
    apply sub_pos.mpr
    exact (div_lt_one ha).mpr hba
  have hblog :
      Real.log b = Real.log a + Real.log (b / a) := by
    calc
      Real.log b = Real.log (a * (b / a)) := by
        congr 1
        field_simp
      _ = Real.log a + Real.log (b / a) :=
        Real.log_mul ha.ne' hratio.ne'
  have hcomplog :
      Real.log (a - b) =
        Real.log a + Real.log (1 - b / a) := by
    calc
      Real.log (a - b) = Real.log (a * (1 - b / a)) := by
        congr 1
        field_simp
      _ = Real.log a + Real.log (1 - b / a) :=
        Real.log_mul ha.ne' hcomp.ne'
  rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
    Real.binEntropy, Real.log_inv, Real.log_inv,
    hblog, hcomplog]
  field_simp [ha.ne']; ring

theorem tendsto_logb_choose_of_ratio
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have ha : 0 < a := lt_trans hb hba
  have hcomplement := tendsto_sub_degree_ratio hN hK hKN
  have hKgrowth := tendsto_atTop_of_ratio_pos hb hK
  have hcomplementgrowth :=
    tendsto_atTop_of_ratio_pos (sub_pos.mpr hba) hcomplement
  have hstirling := SpherePacking.tendsto_log_add_choose_div
    K (fun n : ℕ => N n - K n) b (a - b)
    hKgrowth hcomplementgrowth hK hcomplement
    hb (sub_pos.mpr hba)
  have hsum : b + (a - b) = a := by ring
  simp only [hsum] at hstirling
  have hbase := hstirling.div_const (Real.log 2)
  rw [scaled_binomialEntropy_identity ha hb hba] at hbase
  refine hbase.congr' ?_
  filter_upwards [hKN] with n hn
  have hinteger : K n + (N n - K n) = N n := by omega
  rw [hinteger]
  unfold Real.logb
  ring

theorem tendsto_logb_succ_of_le_dimension
    {N : ℕ → ℕ}
    (hN : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := MetricCodes.Hamming.tendsto_logb_succ_div
  have hnonnegative :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      exact_mod_cast (show 1 ≤ N n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hbounded :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [hN, eventually_gt_atTop (0 : ℕ)]
      with n hNn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast (show 0 < N n + 1 by omega)
    · exact_mod_cast (show N n + 1 ≤ n + 1 by omega)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hzero hupper hnonnegative hbounded

theorem tendsto_logb_booleanHarmonicDimension_of_ratio
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hhalf : ∀ᶠ n : ℕ in atTop, 2 * K n ≤ N n)
    (hNle : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n :=
    hhalf.mono (fun _ hn => by omega)
  have hchoose :=
    tendsto_logb_choose_of_ratio hN hK hb hba hKN
  have hpoly := tendsto_logb_succ_of_le_dimension hNle
  have hlowerlimit :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    have hchoosepos : 0 < ((N n).choose (K n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : K n ≤ N n)
    have hlog :
        Real.logb 2 ((N n).choose (K n) : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 2) hchoosepos
      have hcomparison :=
        MetricCodes.Hamming.choose_le_mul_hammingFibreDimension hhalf'
      change
        ((N n).choose (K n) : ℝ) ≤
          ((N n + 1 : ℕ) : ℝ) *
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ)
      exact_mod_cast hcomparison
    calc
      Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 ((N n).choose (K n) : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).mpr
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) ≤
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hfibre
    have hcomparison :=
      MetricCodes.Hamming.hammingFibreDimension_le_choose (N n) (K n)
    exact_mod_cast hcomparison
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlimit hchoose hlower hupper

theorem eventually_admissibleDegrees
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      MetricCodes.Johnson.AdmissibleDegrees n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n)
        (terminalDegree u n) := by
  have ha := h.weight_pos
  have hu := h.degree_pos
  have hw := tendsto_shellWeight_ratio ha.le
  have hp := tendsto_supportDegree_ratio h.support_nonneg
  have hq := tendsto_complementDegree_ratio h.complement_nonneg
  have hL := tendsto_terminalDegree_ratio hu.le
  have hn := tendsto_dimension_ratio
  have hww := tendsto_add_degree_ratio hw hw
  have hpp := tendsto_add_degree_ratio hp hp
  have hqq := tendsto_add_degree_ratio hq hq
  have hpq := tendsto_add_degree_ratio hp hq
  have hLp := tendsto_add_degree_ratio hL hp
  have hwq := tendsto_add_degree_ratio hw hq
  have hLw := tendsto_add_degree_ratio hL hw
  have hLwq := tendsto_add_degree_ratio hLw hq
  have hnp := tendsto_add_degree_ratio hn hp
  have hweight_positive :
      ∀ᶠ n : ℕ in atTop, 0 < shellWeight a n := by
    have hgrowth : Tendsto (shellWeight a) atTop atTop := by
      change Tendsto
        (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
      exact tendsto_nat_floor_mul_atTop a ha
    exact hgrowth.eventually (eventually_gt_atTop (0 : ℕ))
  have hweight_lt := eventually_degree_lt_of_ratio hw hn
    (by linarith [h.weight_lt_half])
  have hweight_half := eventually_degree_lt_of_ratio hww hn
    (by linarith [h.weight_lt_half])
  have hsupport_half := eventually_degree_lt_of_ratio hpp hw
    (by linarith [h.support_lt_half])
  have hcomplement_half := eventually_degree_lt_of_ratio
    (tendsto_add_degree_ratio hqq hw) hn
    (by linarith [h.complement_lt_half])
  have hfirst := eventually_degree_lt_of_ratio hpq hL
    h.first_lt_degree
  have hterminal_weight := eventually_degree_lt_of_ratio hL hw
    h.degree_lt_weight
  have hterminal_left := eventually_degree_lt_of_ratio hLp hwq
    (by linarith [h.degree_lt_left])
  have hterminal_right := eventually_degree_lt_of_ratio hLwq hnp
    (by linarith [h.degree_lt_right])
  filter_upwards [hweight_positive, hweight_lt, hweight_half,
    hsupport_half, hcomplement_half, hfirst,
    hterminal_weight, hterminal_left, hterminal_right]
    with n hpos hlt hhalf hsupport hcomplement
      hfirst' hweight' hleft hright
  refine {
    weight_pos := hpos
    weight_lt := hlt
    weight_half := by omega
    support_half := by omega
    complement_half := by omega
    first_le := by omega
    last_le := ?_
  }
  unfold MetricCodes.johnsonLastDegree
  apply le_min
  · omega
  · apply le_min <;> omega

theorem tendsto_complementShellWeight_ratio
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa only [shellWeight] using MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'

theorem tendsto_logb_supportHarmonicDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (shellWeight a n) (supportDegree b n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  by_cases hbzero : b = 0
  · subst b
    simp only [booleanHarmonicDimension, supportDegree, Hamming.longitudinalDegree, zero_mul,
      Nat.floor_zero, Nat.cast_one, Real.logb_one, zero_div, binaryEntropy_zero, mul_zero,
      tendsto_const_nhds_iff]
  · have hb : 0 < b := lt_of_le_of_ne h.support_nonneg
      (Ne.symm hbzero)
    have hba : b < a := by
      nlinarith [h.support_lt_half, h.weight_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * supportDegree b n ≤ shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.support_half)
    have hN : ∀ᶠ n : ℕ in atTop, shellWeight a n ≤ n := by
      apply Eventually.of_forall
      intro n
      exact MetricCodes.Hamming.longitudinalDegree_le_dimension
        (by linarith [h.weight_lt_half]) n
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_shellWeight_ratio h.weight_pos.le)
      (tendsto_supportDegree_ratio h.support_nonneg)
      hb hba hhalf hN

theorem tendsto_logb_complementHarmonicDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (n - shellWeight a n) (complementDegree g n) : ℝ) /
            (n : ℝ))
      atTop (nhds
        ((1 - a) * MetricCodes.binaryEntropy (g / (1 - a)))) := by
  by_cases hgzero : g = 0
  · subst g
    simp only [booleanHarmonicDimension, complementDegree, Hamming.longitudinalDegree, zero_mul,
      Nat.floor_zero, Nat.cast_one, Real.logb_one, zero_div, binaryEntropy_zero, mul_zero,
      tendsto_const_nhds_iff]
  · have hg : 0 < g := lt_of_le_of_ne h.complement_nonneg
      (Ne.symm hgzero)
    have hga : g < 1 - a := by
      nlinarith [h.complement_lt_half, h.weight_complement_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * complementDegree g n ≤ n - shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.complement_half)
    have hN :
        ∀ᶠ n : ℕ in atTop, n - shellWeight a n ≤ n :=
      Eventually.of_forall (fun n => Nat.sub_le n _)
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_complementShellWeight_ratio
        h.weight_pos.le (by linarith [h.weight_lt_half]))
      (tendsto_complementDegree_ratio h.complement_nonneg)
      hg hga hhalf hN

theorem tendsto_logb_johnsonFibreDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonFibreDimension n
            (shellWeight a n)
            (supportDegree b n)
            (complementDegree g n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.rankPenalty a b g)) := by
  have hsupport := tendsto_logb_supportHarmonicDimension h
  have hcomplement := tendsto_logb_complementHarmonicDimension h
  have hsum := hsupport.add hcomplement
  change
    Tendsto _ atTop
      (nhds
        (a * MetricCodes.binaryEntropy (b / a) +
          (1 - a) * MetricCodes.binaryEntropy (g / (1 - a))))
  refine hsum.congr' ?_
  filter_upwards [eventually_admissibleDegrees h]
    with n hn
  have hsupportpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (shellWeight a n) (supportDegree b n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.support_half
  have hcomplementpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (n - shellWeight a n) (complementDegree g n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.complement_half
  unfold MetricCodes.johnsonFibreDimension
  push_cast
  rw [Real.logb_mul hsupportpos.ne' hcomplementpos.ne']
  ring

theorem terminalHarmonic_le_johnsonAmbientDimension
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.booleanHarmonicDimension n L ≤
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  unfold MetricCodes.johnsonAmbientDimension
  have hmem : L ∈ Finset.Icc (p + q) L := by
    simp only [Finset.mem_Icc, h.first_le, Std.le_refl, and_self]
  exact Finset.single_le_sum
    (s := Finset.Icc (p + q) L)
    (f := fun j => MetricCodes.booleanHarmonicDimension n j)
    (fun _ _ => Nat.zero_le _) hmem

theorem johnsonAmbientDimension_le_terminalChoose
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L ≤ n.choose L := by
  rw [MetricCodes.Johnson.ambientDimension_eq h]
  exact Nat.sub_le _ _

theorem tendsto_logb_johnsonAmbientDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonAmbientDimension n
            (supportDegree b n + complementDegree g n)
            (terminalDegree u n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy u)) := by
  have hu := h.degree_pos
  have huhalf : u ≤ (1 : ℝ) / 2 := by
    linarith [h.degree_lt_weight, h.weight_lt_half]
  have huone : u < 1 := by linarith
  have hterminal :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa only [terminalDegree, Hamming.longitudinalDegree, hammingFibreDimension,
      Hamming.transverseDegree] using
      MetricCodes.Hamming.tendsto_logb_hammingFibreDimension hu huhalf
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa only [terminalDegree] using MetricCodes.Hamming.tendsto_logb_choose_longitudinal hu huone
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) htermpos
    exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    have hambientpos :
        0 < (MetricCodes.johnsonAmbientDimension n
          (supportDegree b n + complementDegree g n)
          (terminalDegree u n) : ℝ) := by
      have hle := terminalHarmonic_le_johnsonAmbientDimension hn
      exact lt_of_lt_of_le htermpos (by exact_mod_cast hle)
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hambientpos
    exact_mod_cast johnsonAmbientDimension_le_terminalChoose hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hterminal hchoose hlower hupper

/-- The window fibre quotient used in the Johnson-code argument. -/
def windowFibreQuotient (a b g u : ℝ) (n : ℕ) : ℝ :=
  (MetricCodes.johnsonAmbientDimension n
    (supportDegree b n + complementDegree g n)
    (terminalDegree u n) : ℝ) /
      (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ)

theorem eventually_windowFibreQuotient_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop, 0 < windowFibreQuotient a b g u n := by
  filter_upwards [eventually_admissibleDegrees h] with n hn
  have htermhalf : 2 * terminalDegree u n ≤ n := by
    have hhalf := hn.terminal_le_half
    omega
  have htermpos :
      0 < (MetricCodes.booleanHarmonicDimension n
        (terminalDegree u n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      htermhalf
  have hambientpos :
      0 < (MetricCodes.johnsonAmbientDimension n
        (supportDegree b n + complementDegree g n)
        (terminalDegree u n) : ℝ) := by
    exact lt_of_lt_of_le htermpos
      (by exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn)
  have hfibrepos :
      0 < (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ) := by
    exact_mod_cast hn.fibreDimension_pos
  exact div_pos hambientpos hfibrepos

theorem tendsto_logb_windowFibreQuotient
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (windowFibreQuotient a b g u n) / (n : ℝ))
      atTop
      (nhds (MetricCodes.binaryEntropy u -
        MetricCodes.Johnson.rankPenalty a b g)) := by
  have hnum := tendsto_logb_johnsonAmbientDimension h
  have hden := tendsto_logb_johnsonFibreDimension h
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_admissibleDegrees h] with n hn
  have htermhalf : 2 * terminalDegree u n ≤ n := by
    have hhalf := hn.terminal_le_half
    omega
  have htermpos :
      0 < (MetricCodes.booleanHarmonicDimension n
        (terminalDegree u n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      htermhalf
  have hambientpos :
      0 < (MetricCodes.johnsonAmbientDimension n
        (supportDegree b n + complementDegree g n)
        (terminalDegree u n) : ℝ) := by
    exact lt_of_lt_of_le htermpos
      (by exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn)
  have hfibrepos :
      0 < (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ) := by
    exact_mod_cast hn.fibreDimension_pos
  unfold windowFibreQuotient
  rw [Real.logb_div hambientpos.ne' hfibrepos.ne']
  ring

/-- The bassalygo factor used in the Johnson-code argument. -/
def bassalygoFactor (a : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / (n.choose (shellWeight a n) : ℝ)

theorem tendsto_logb_shellChoose
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  simpa only [shellWeight] using
    MetricCodes.Hamming.tendsto_logb_choose_longitudinal h.weight_pos (by linarith
      [h.weight_lt_half])

theorem tendsto_logb_bassalygoFactor
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (bassalygoFactor a n) / (n : ℝ))
      atTop (nhds (1 - MetricCodes.binaryEntropy a)) := by
  have hpower :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ))
        atTop (nhds (1 : ℝ)) := by
    refine tendsto_dimension_ratio.congr'
      (Eventually.of_forall fun n => ?_)
    change
      (n : ℝ) / (n : ℝ) =
        Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    simp only [mul_one]
  have hchoose := tendsto_logb_shellChoose h
  have hdiff := hpower.sub hchoose
  refine hdiff.congr' (Eventually.of_forall fun n => ?_)
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoFactor
  change
    Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ) -
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ) =
      Real.logb 2
        (((2 : ℝ) ^ n) / (n.choose (shellWeight a n) : ℝ)) /
          (n : ℝ)
  rw [Real.logb_div (by positivity) hchoosepos.ne']
  ring

/-- The bassalygo window fibre quotient used in the Johnson-code argument. -/
def bassalygoWindowFibreQuotient
    (a b g u : ℝ) (n : ℕ) : ℝ :=
  bassalygoFactor a n * windowFibreQuotient a b g u n

theorem eventually_bassalygoWindowFibreQuotient_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      0 < bassalygoWindowFibreQuotient a b g u n := by
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquot
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoWindowFibreQuotient bassalygoFactor
  exact mul_pos (div_pos (by positivity) hchoosepos) hquot

theorem tendsto_logb_bassalygoWindowFibreQuotient
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (bassalygoWindowFibreQuotient a b g u n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hfactor := tendsto_logb_bassalygoFactor h
  have hquotient := tendsto_logb_windowFibreQuotient h
  have hsum := hfactor.add hquotient
  have hlimit :
      (1 - MetricCodes.binaryEntropy a) +
          (MetricCodes.binaryEntropy u -
            MetricCodes.Johnson.rankPenalty a b g) =
        MetricCodes.Johnson.shellRate a b g u := by
    unfold MetricCodes.Johnson.shellRate
    ring
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquotpos
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  have hfactorpos : 0 < bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_pos (by positivity) hchoosepos
  unfold bassalygoWindowFibreQuotient
  rw [Real.logb_mul hfactorpos.ne' hquotpos.ne']
  ring

theorem tendsto_logb_const_mul_bassalygoWindowFibreQuotient
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (C * bassalygoWindowFibreQuotient a b g u n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hconstant :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquotient := tendsto_logb_bassalygoWindowFibreQuotient h
  have hsum := hconstant.add hquotient
  have hsum' :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2
              (bassalygoWindowFibreQuotient a b g u n) /
                (n : ℝ))
        atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
    simpa only [zero_add] using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_bassalygoWindowFibreQuotient_pos h]
    with n hn
  rw [Real.logb_mul hC.ne' hn.ne']
  ring

theorem centered_diagonal_limit_algebra
    {a m sigma eta z : ℝ}
    (hz : z ≠ 0)
    (hm : 1 - m ^ 2 ≠ 0)
    (hcenter : 1 - m ^ 2 = 4 * a * (1 - a)) :
    (m * sigma * eta / (4 * z ^ 2) - (m / 2) ^ 2) /
        (a * (1 - a)) =
      m * (sigma * eta - m * z ^ 2) /
        (z ^ 2 * (1 - m ^ 2)) := by
  have hprod : a * (1 - a) ≠ 0 := by
    intro hzero
    apply hm
    rw [hcenter]
    calc
      4 * a * (1 - a) = 4 * (a * (1 - a)) := by ring
      _ = 0 := by rw [hzero]; ring
  have ha : a ≠ 0 := by
    intro hzero
    apply hprod
    simp only [hzero, sub_zero, mul_one]
  have ha' : 1 - a ≠ 0 := by
    intro hzero
    apply hprod
    rw [hzero]
    ring
  rw [hcenter]
  field_simp [hz, ha, ha']; ring

theorem tendsto_threshold_ceil
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))))
      atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementShellWeight_ratio
    h.weight_pos.le (by linarith [h.weight_lt_half])
  have hd := MetricCodes.Hamming.tendsto_ceil_distance_ratio
    h.distance_pos.le
  have hden :=
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hw).mul hc
  have hdenpos : 0 < 2 * a * (1 - a) := by
    have ha := h.weight_pos
    have hc' := h.weight_complement_pos
    positivity
  have hdivision := hd.div hden hdenpos.ne'
  have hnormalized :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hdivision
  have hnormalized' :
      Tendsto
        (fun n : ℕ =>
          1 -
            (((Nat.ceil (d * (n : ℝ)) : ℕ) : ℝ) /
              (n : ℝ)) /
              (2 * ((shellWeight a n : ℝ) / (n : ℝ)) *
                (((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))))
        atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
    simpa only [asymptoticThreshold, Pi.div_apply] using hnormalized
  refine hnormalized'.congr' ?_
  filter_upwards [eventually_admissibleDegrees h,
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hwreal : (0 : ℝ) < (shellWeight a n : ℝ) := by
    exact_mod_cast hn.weight_pos
  have hcreal :
      (0 : ℝ) < ((n - shellWeight a n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - shellWeight a n by
      exact Nat.sub_pos_of_lt hn.weight_lt)
  unfold MetricCodes.Johnson.threshold
  field_simp [hnreal.ne', hwreal.ne', hcreal.ne']

theorem binaryRate_le_shellRate_of_eventually
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
          C * bassalygoWindowFibreQuotient a b g u n) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Hamming.binaryRate_le_of_eventually
    (tendsto_logb_const_mul_bassalygoWindowFibreQuotient h hC)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hcode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcodepositive :
      0 < (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) := by
    exact_mod_cast MetricCodes.Hamming.codeNumber_pos n
      (Nat.ceil (d * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).mpr
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcodepositive hcode

end Asymptotics

end

section

open scoped BigOperators InnerProductSpace Matrix

private def complementNegEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    ComplementCoordinates x ≃
      {i : Fin n // i ∉ MetricCodes.wordSupport (x : BinaryWord n)} :=
  Equiv.subtypeEquivRight (fun i => by simp only [Finset.mem_sdiff, Finset.mem_univ,
                                         mem_wordSupport, Bool.not_eq_true, true_and])

private def coordinateSumEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    SupportCoordinates x ⊕ ComplementCoordinates x ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl (SupportCoordinates x))
    (complementNegEquiv x)).trans
      (Equiv.sumCompl
        (fun i : Fin n => i ∈ MetricCodes.wordSupport (x : BinaryWord n)))

@[simp] theorem coordinateSumEquiv_symm_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x) :
    (coordinateSumEquiv x).symm (i : Fin n) = Sum.inl i := by
  have hi : coordinateSumEquiv x (Sum.inl i) = (i : Fin n) := rfl
  simpa only [hi] using
    (coordinateSumEquiv x).symm_apply_apply (Sum.inl i)

@[simp] theorem coordinateSumEquiv_symm_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x) :
    (coordinateSumEquiv x).symm (i : Fin n) = Sum.inr i := by
  have hi : coordinateSumEquiv x (Sum.inr i) = (i : Fin n) := rfl
  simpa only [hi] using
    (coordinateSumEquiv x).symm_apply_apply (Sum.inr i)

private def coordinateSplitEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    Finset (Fin n) ≃
      Finset (SupportCoordinates x) ×
        Finset (ComplementCoordinates x) :=
  (coordinateSumEquiv x).symm.finsetCongr.trans
    Finset.sumEquiv.toEquiv

theorem coordinateSplitEquiv_card {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    ((coordinateSplitEquiv x S).1).card +
      ((coordinateSplitEquiv x S).2).card = S.card := by
  change
    (((coordinateSumEquiv x).symm.finsetCongr S).toLeft).card +
      (((coordinateSumEquiv x).symm.finsetCongr S).toRight).card =
        S.card
  rw [Finset.card_toLeft_add_card_toRight]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

theorem coordinateSplitEquiv_insert_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (insert (i : Fin n) S) =
      (insert i (coordinateSplitEquiv x S).1,
        (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toLeft) =
          insert i
            (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    simp only [Equiv.finsetCongr_apply, Finset.map_insert, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_support, Finset.toLeft_insert_inl]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toRight) =
          (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    simp only [Equiv.finsetCongr_apply, Finset.map_insert, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_support, Finset.toRight_insert_inl]

theorem coordinateSplitEquiv_insert_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (insert (i : Fin n) S) =
      ((coordinateSplitEquiv x S).1,
        insert i (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toLeft) =
          (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    simp only [Equiv.finsetCongr_apply, Finset.map_insert, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_complement, Finset.toLeft_insert_inr]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toRight) =
          insert i
            (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    simp only [Equiv.finsetCongr_apply, Finset.map_insert, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_complement, Finset.toRight_insert_inr]

private def supportRaisedFunction {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p)) (r : ℕ) :
    Finset (SupportCoordinates x) → ℝ :=
  fun S =>
    MetricCodes.Boolean.harmonicEmbedding p r
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
      ((supportCoordinateEquiv x).finsetCongr S)

private def complementRaisedFunction {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q)) (r : ℕ) :
    Finset (ComplementCoordinates x) → ℝ :=
  fun S =>
    MetricCodes.Boolean.harmonicEmbedding q r
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
      ((complementCoordinateEquiv x).finsetCongr S)

theorem supportRaisedFunction_eq_zero_of_card_ne {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p)) (r : ℕ)
    (S : Finset (SupportCoordinates x))
    (hS : S.card ≠ p + r) :
    supportRaisedFunction x hp a r S = 0 := by
  unfold supportRaisedFunction
  apply
    ((MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a).1
      |>.harmonicEmbedding r)
  simpa only [Equiv.finsetCongr_apply, Finset.card_map, ne_eq] using hS

theorem complementRaisedFunction_eq_zero_of_card_ne {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q)) (r : ℕ)
    (S : Finset (ComplementCoordinates x))
    (hS : S.card ≠ q + r) :
    complementRaisedFunction x hq a r S = 0 := by
  unfold complementRaisedFunction
  apply
    ((MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
      (n - w) q hq a).1 |>.harmonicEmbedding r)
  simpa only [Equiv.finsetCongr_apply, Finset.card_map, ne_eq] using hS

theorem supportRaisedFunction_pairing {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p)) (r s : ℕ) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b s S) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicEmbedding p r
          (MetricCodes.Boolean.harmonicBasisFunction w p hp a))
        (MetricCodes.Boolean.harmonicEmbedding p s
          (MetricCodes.Boolean.harmonicBasisFunction w p hp b)) := by
  classical
  unfold supportRaisedFunction MetricCodes.Boolean.dot
  exact (supportCoordinateEquiv x).finsetCongr.sum_comp
    (fun S : Finset (Fin w) =>
      MetricCodes.Boolean.harmonicEmbedding p r
        (MetricCodes.Boolean.harmonicBasisFunction w p hp a) S *
      MetricCodes.Boolean.harmonicEmbedding p s
        (MetricCodes.Boolean.harmonicBasisFunction w p hp b) S)

theorem complementRaisedFunction_pairing {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a b : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (r s : ℕ) :
    (∑ S : Finset (ComplementCoordinates x),
      complementRaisedFunction x hq a r S *
        complementRaisedFunction x hq b s S) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicEmbedding q r
          (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a))
        (MetricCodes.Boolean.harmonicEmbedding q s
          (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b)) := by
  classical
  unfold complementRaisedFunction MetricCodes.Boolean.dot
  exact (complementCoordinateEquiv x).finsetCongr.sum_comp
    (fun S : Finset (Fin (n - w)) =>
      MetricCodes.Boolean.harmonicEmbedding q r
        (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a) S *
      MetricCodes.Boolean.harmonicEmbedding q s
        (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b) S)

theorem supportRaisedFunction_orthonormal {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hr : 2 * p + r ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p)) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b r S) =
      if a = b then 1 else 0 := by
  rw [supportRaisedFunction_pairing,
    MetricCodes.Boolean.harmonicEmbedding_isometry
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
      (MetricCodes.Boolean.harmonicBasisFunction w p hp b)
      (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp b)
      r hr,
    MetricCodes.Boolean.harmonicBasisFunction_dot]

theorem complementRaisedFunction_orthonormal {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hr : 2 * q + r ≤ n - w)
    (a b : Fin (MetricCodes.hammingFibreDimension (n - w) q)) :
    (∑ S : Finset (ComplementCoordinates x),
      complementRaisedFunction x hq a r S *
        complementRaisedFunction x hq b r S) =
      if a = b then 1 else 0 := by
  rw [complementRaisedFunction_pairing,
    MetricCodes.Boolean.harmonicEmbedding_isometry
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b)
      (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
        (n - w) q hq b)
      r hr,
    MetricCodes.Boolean.harmonicBasisFunction_dot]

theorem supportRaisedFunction_cross_orthogonal {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p))
    (r s : ℕ) (hrs : r ≠ s) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b s S) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S.card = p + r
  · have hother : S.card ≠ p + s := by omega
    rw [supportRaisedFunction_eq_zero_of_card_ne x hp b s S hother,
      mul_zero]
  · rw [supportRaisedFunction_eq_zero_of_card_ne x hp a r S hS,
      zero_mul]

private def splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    MetricCodes.Boolean.Function n :=
  fun S =>
    supportRaisedFunction x hp a.1 r
      (coordinateSplitEquiv x S).1 *
    complementRaisedFunction x hq a.2 s
      (coordinateSplitEquiv x S).2

theorem splitTensor_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    MetricCodes.Boolean.IsLevel ((p + r) + (q + s))
      (splitTensor x hp hq a r s) := by
  intro S hS
  have hcard := coordinateSplitEquiv_card x S
  by_cases hsupport :
      ((coordinateSplitEquiv x S).1).card = p + r
  · have hcomplement :
        ((coordinateSplitEquiv x S).2).card ≠ q + s := by
      omega
    unfold splitTensor
    rw [complementRaisedFunction_eq_zero_of_card_ne
      x hq a.2 s (coordinateSplitEquiv x S).2 hcomplement,
      mul_zero]
  · unfold splitTensor
    rw [supportRaisedFunction_eq_zero_of_card_ne
      x hp a.1 r (coordinateSplitEquiv x S).1 hsupport,
      zero_mul]

theorem splitTensor_pairing {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a b : HarmonicFibreIndex n w p q)
    (r s r' s' : ℕ) :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r' s') =
      (∑ A : Finset (SupportCoordinates x),
        supportRaisedFunction x hp a.1 r A *
          supportRaisedFunction x hp b.1 r' A) *
      (∑ B : Finset (ComplementCoordinates x),
        complementRaisedFunction x hq a.2 s B *
          complementRaisedFunction x hq b.2 s' B) := by
  classical
  calc
    MetricCodes.Boolean.dot
        (splitTensor x hp hq a r s)
        (splitTensor x hp hq b r' s') =
      ∑ T : Finset (SupportCoordinates x) ×
          Finset (ComplementCoordinates x),
        (supportRaisedFunction x hp a.1 r T.1 *
          complementRaisedFunction x hq a.2 s T.2) *
        (supportRaisedFunction x hp b.1 r' T.1 *
          complementRaisedFunction x hq b.2 s' T.2) := by
      unfold MetricCodes.Boolean.dot splitTensor
      exact (coordinateSplitEquiv x).sum_comp
        (fun T : Finset (SupportCoordinates x) ×
          Finset (ComplementCoordinates x) =>
          (supportRaisedFunction x hp a.1 r T.1 *
            complementRaisedFunction x hq a.2 s T.2) *
          (supportRaisedFunction x hp b.1 r' T.1 *
            complementRaisedFunction x hq b.2 s' T.2))
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring

theorem splitTensor_orthonormal {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hr : 2 * p + r ≤ w) (hs : 2 * q + s ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r s) =
      if a = b then 1 else 0 := by
  rw [splitTensor_pairing,
    supportRaisedFunction_orthonormal x hp hr,
    complementRaisedFunction_orthonormal x hq hs]
  by_cases hfirst : a.1 = b.1 <;>
    by_cases hsecond : a.2 = b.2 <;>
    simp [hfirst, hsecond, Prod.ext_iff]

theorem splitTensor_cross_orthogonal {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a b : HarmonicFibreIndex n w p q)
    (r s r' s' : ℕ) (hrr' : r ≠ r') :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r' s') = 0 := by
  rw [splitTensor_pairing,
    supportRaisedFunction_cross_orthogonal
      x hp a.1 b.1 r r' hrr', zero_mul]

private def clebschCoefficient (w N p q t : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 =>
      -clebschCoefficient w N p q t r *
        Real.sqrt (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) /
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))

theorem clebschCoefficient_succ_mul {w N p q t r : ℕ}
    (hbound : 2 * p + (r + 1) ≤ w) :
    clebschCoefficient w N p q t (r + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) =
      -clebschCoefficient w N p q t r *
        Real.sqrt (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
  have hpositive :
      0 < MetricCodes.Boolean.harmonicCoefficient w p (r + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos (Nat.succ_pos r) hbound
  have hnonzero :
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hpositive).ne'
  simp only [clebschCoefficient]
  field_simp [hnonzero]

private def clebschNormSq (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    clebschCoefficient w N p q t r.val ^ 2

theorem clebschNormSq_pos (w N p q t : ℕ) :
    0 < clebschNormSq w N p q t := by
  classical
  unfold clebschNormSq
  apply Finset.sum_pos'
  · intro r _
    exact sq_nonneg _
  · let r : Fin (t + 1) := ⟨0, by omega⟩
    refine ⟨r, Finset.mem_univ r, ?_⟩
    change 0 < clebschCoefficient w N p q t 0 ^ 2
    norm_num [clebschCoefficient]

private def coupledTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.Function n :=
  fun S =>
    ∑ r : Fin (t + 1),
      clebschCoefficient w (n - w) p q t r.val *
        splitTensor x hp hq a r.val (t - r.val) S

theorem coupledTensor_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.IsLevel (p + q + t)
      (coupledTensor x hp hq a t) := by
  classical
  intro S hS
  unfold coupledTensor
  apply Finset.sum_eq_zero
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hdegree :
      (p + r.val) + (q + (t - r.val)) = p + q + t := by
    omega
  have hzero :=
    splitTensor_isLevel x hp hq a r.val (t - r.val) S
      (by simpa only [hdegree, ne_eq] using hS)
  rw [hzero, mul_zero]

/-- The coupled harmonic used in the Johnson-code argument. -/
def coupledHarmonic {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.Function n :=
  (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ •
    coupledTensor x hp hq a t

theorem coupledHarmonic_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.IsLevel (p + q + t)
      (coupledHarmonic x hp hq a t) := by
  unfold coupledHarmonic
  exact (coupledTensor_isLevel x hp hq a t).smul _

theorem dot_fintype_weighted_sum
    {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ)
    (f : ι → MetricCodes.Boolean.Function n)
    (g : κ → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot
      (fun S => ∑ i : ι, c i * f i S)
      (fun S => ∑ j : κ, d j * g j S) =
      ∑ i : ι, ∑ j : κ,
        c i * d j * MetricCodes.Boolean.dot (f i) (g j) := by
  classical
  unfold MetricCodes.Boolean.dot
  calc
    (∑ S : Finset (Fin n),
      (∑ i : ι, c i * f i S) *
        (∑ j : κ, d j * g j S)) =
      ∑ S : Finset (Fin n), ∑ i : ι, ∑ j : κ,
        (c i * f i S) * (d j * g j S) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ j : κ, ∑ S : Finset (Fin n),
          (c i * f i S) * (d j * g j S) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : κ,
        c i * d j *
          (∑ S : Finset (Fin n), f i S * g j S) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem coupledTensor_dot {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (coupledTensor x hp hq a t)
      (coupledTensor x hp hq b t) =
      clebschNormSq w (n - w) p q t *
        (if a = b then 1 else 0) := by
  classical
  let c : Fin (t + 1) → ℝ :=
    fun r => clebschCoefficient w (n - w) p q t r.val
  let f : Fin (t + 1) → MetricCodes.Boolean.Function n :=
    fun r => splitTensor x hp hq a r.val (t - r.val)
  let g : Fin (t + 1) → MetricCodes.Boolean.Function n :=
    fun r => splitTensor x hp hq b r.val (t - r.val)
  have hpair :
      MetricCodes.Boolean.dot
        (coupledTensor x hp hq a t)
        (coupledTensor x hp hq b t) =
      ∑ r : Fin (t + 1), ∑ s : Fin (t + 1),
        c r * c s * MetricCodes.Boolean.dot (f r) (g s) := by
    change
      MetricCodes.Boolean.dot
        (fun S => ∑ r : Fin (t + 1), c r * f r S)
        (fun S => ∑ s : Fin (t + 1), c s * g s S) = _
    exact dot_fintype_weighted_sum c c f g
  rw [hpair]
  calc
    (∑ r : Fin (t + 1), ∑ s : Fin (t + 1),
      c r * c s * MetricCodes.Boolean.dot (f r) (g s)) =
      ∑ r : Fin (t + 1),
        c r ^ 2 * (if a = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ s : Fin (t + 1),
          c r * c s * MetricCodes.Boolean.dot (f r) (g s)) =
          ∑ s : Fin (t + 1),
            if s = r then
              c r ^ 2 * (if a = b then 1 else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hsr : s = r
          · subst s
            have hr : r.val ≤ t := by
              have hlt := r.isLt
              omega
            have hsupport : 2 * p + r.val ≤ w := by
              omega
            have hcomplement :
                2 * q + (t - r.val) ≤ n - w := by
              omega
            change
              c r * c r *
                  MetricCodes.Boolean.dot
                    (splitTensor x hp hq a r.val (t - r.val))
                    (splitTensor x hp hq b r.val (t - r.val)) =
                if r = r then
                  c r ^ 2 * (if a = b then 1 else 0)
                else 0
            rw [splitTensor_orthonormal x hp hq
              hsupport hcomplement a b]
            simp only [mul_ite, mul_one, mul_zero, ↓reduceIte, pow_two]
          · have hrs : r.val ≠ s.val := by
              intro heq
              exact hsr (Fin.ext heq.symm)
            change
              c r * c s *
                  MetricCodes.Boolean.dot
                    (splitTensor x hp hq a r.val (t - r.val))
                    (splitTensor x hp hq b s.val (t - s.val)) =
                if s = r then
                  c r ^ 2 * (if a = b then 1 else 0)
                else 0
            rw [splitTensor_cross_orthogonal x hp hq
              a b r.val (t - r.val) s.val (t - s.val) hrs]
            simp only [mul_zero, hsr, ↓reduceIte]
        _ = c r ^ 2 * (if a = b then 1 else 0) := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    _ = clebschNormSq w (n - w) p q t *
        (if a = b then 1 else 0) := by
      simp only [clebschNormSq, c, Finset.sum_mul]

theorem coupledHarmonic_dot {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (coupledHarmonic x hp hq a t)
      (coupledHarmonic x hp hq b t) =
      if a = b then 1 else 0 := by
  have hpositive := clebschNormSq_pos w (n - w) p q t
  have hsquare := Real.sq_sqrt hpositive.le
  have hnonzero :
      Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hpositive).ne'
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right,
    coupledTensor_dot x hp hq htsupport htcomplement a b]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    field_simp [hnonzero]
    exact hsquare.symm
  · simp only [hab, ↓reduceIte, mul_zero]

@[simp] theorem coordinateSplitEquiv_mem_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    i ∈ (coordinateSplitEquiv x S).1 ↔ (i : Fin n) ∈ S := by
  change
    i ∈ (((coordinateSumEquiv x).symm.finsetCongr S).toLeft) ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_toLeft]
  change
    Sum.inl i ∈ S.map (coordinateSumEquiv x).symm.toEmbedding ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_map_equiv]
  change (i : Fin n) ∈ S ↔ (i : Fin n) ∈ S
  rfl

@[simp] theorem coordinateSplitEquiv_mem_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    i ∈ (coordinateSplitEquiv x S).2 ↔ (i : Fin n) ∈ S := by
  change
    i ∈ (((coordinateSumEquiv x).symm.finsetCongr S).toRight) ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_toRight]
  change
    Sum.inr i ∈ S.map (coordinateSumEquiv x).symm.toEmbedding ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_map_equiv]
  change (i : Fin n) ∈ S ↔ (i : Fin n) ∈ S
  rfl

private def coordinateLower {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ i : α, if i ∈ S then 0 else f (insert i S)

theorem coordinateLower_reindex
    {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ Fin m) (f : MetricCodes.Boolean.Function m)
    (S : Finset α) :
    coordinateLower
        (fun T : Finset α => f (e.finsetCongr T)) S =
      MetricCodes.Boolean.lower f (e.finsetCongr S) := by
  classical
  unfold coordinateLower MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
  calc
    (∑ i : α,
      if i ∈ S then 0 else f (e.finsetCongr (insert i S))) =
      ∑ i : α,
        if e i ∈ e.finsetCongr S then 0
        else f (insert (e i) (e.finsetCongr S)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Equiv.finsetCongr_apply, Finset.map_insert, Function.Embedding.coeFn_mk,
        Finset.mem_map_mk]
    _ = ∑ i : Fin m,
        if i ∈ e.finsetCongr S then 0
        else f (insert i (e.finsetCongr S)) := by
      exact e.sum_comp (fun i : Fin m =>
        if i ∈ e.finsetCongr S then 0
        else f (insert i (e.finsetCongr S)))

theorem supportRaisedFunction_lower {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hbound : 2 * p + (r + 1) ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateLower (supportRaisedFunction x hp a (r + 1)) S =
      Real.sqrt (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
        supportRaisedFunction x hp a r S := by
  unfold supportRaisedFunction
  rw [coordinateLower_reindex]
  rw [MetricCodes.Boolean.lower_harmonicEmbedding
    (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a)
    r hbound]
  rfl

theorem complementRaisedFunction_lower {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hbound : 2 * q + (r + 1) ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateLower (complementRaisedFunction x hq a (r + 1)) S =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (r + 1)) *
        complementRaisedFunction x hq a r S := by
  unfold complementRaisedFunction
  rw [coordinateLower_reindex]
  rw [MetricCodes.Boolean.lower_harmonicEmbedding
    (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
      (n - w) q hq a)
    r hbound]
  rfl

theorem supportRaisedFunction_lower_zero {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateLower (supportRaisedFunction x hp a 0) S = 0 := by
  unfold supportRaisedFunction
  rw [coordinateLower_reindex]
  simpa only [Boolean.harmonicEmbedding, Boolean.harmonicNormFactor_zero, Real.sqrt_one, inv_one,
    Boolean.raised, one_smul, Equiv.finsetCongr_apply] using
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a).2 ((supportCoordinateEquiv
      x).finsetCongr S)

theorem complementRaisedFunction_lower_zero {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateLower (complementRaisedFunction x hq a 0) S = 0 := by
  unfold complementRaisedFunction
  rw [coordinateLower_reindex]
  simpa only [Boolean.harmonicEmbedding, Boolean.harmonicNormFactor_zero, Real.sqrt_one, inv_one,
    Boolean.raised, one_smul, Equiv.finsetCongr_apply] using
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic (n - w) q hq a).2
      ((complementCoordinateEquiv x).finsetCongr S)

theorem lower_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.lower (splitTensor x hp hq a r s) S =
      coordinateLower (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 +
      supportRaisedFunction x hp a.1 r
          (coordinateSplitEquiv x S).1 *
        coordinateLower (complementRaisedFunction x hq a.2 s)
          (coordinateSplitEquiv x S).2 := by
  classical
  calc
    MetricCodes.Boolean.lower (splitTensor x hp hq a r s) S =
      ∑ i : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x i ∈ S then 0
        else splitTensor x hp hq a r s
          (insert (coordinateSumEquiv x i) S) := by
      unfold MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
      symm
      exact (coordinateSumEquiv x).sum_comp
        (fun i : Fin n =>
          if i ∈ S then 0
          else splitTensor x hp hq a r s (insert i S))
    _ =
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a r s (insert (i : Fin n) S)) +
      (∑ i : ComplementCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a r s (insert (i : Fin n) S)) := by
      rw [Fintype.sum_sum_type]
      simp only [Finset.univ_eq_attach, coordinateSumEquiv, complementNegEquiv, Equiv.trans_apply,
        Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq, Equiv.sumCompl_apply_inl,
        Sum.map_inr, Equiv.sumCompl_apply_inr, Equiv.subtypeEquivRight_apply_coe]
    _ = _ := by
      congr 1
      · calc
          (∑ i : SupportCoordinates x,
            if (i : Fin n) ∈ S then 0
            else splitTensor x hp hq a r s
              (insert (i : Fin n) S)) =
            ∑ i : SupportCoordinates x,
              (if i ∈ (coordinateSplitEquiv x S).1 then 0
                else supportRaisedFunction x hp a.1 r
                  (insert i (coordinateSplitEquiv x S).1)) *
              complementRaisedFunction x hq a.2 s
                (coordinateSplitEquiv x S).2 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
                (coordinateSplitEquiv_mem_support x i S).mpr hi
              simp only [hi, ↓reduceIte, hi', zero_mul]
            · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_support x i S).mp hmem)
              simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_insert_support, hi']
          _ = _ := by
            unfold coordinateLower
            rw [Finset.sum_mul]
      · calc
          (∑ i : ComplementCoordinates x,
            if (i : Fin n) ∈ S then 0
            else splitTensor x hp hq a r s
              (insert (i : Fin n) S)) =
            ∑ i : ComplementCoordinates x,
              supportRaisedFunction x hp a.1 r
                (coordinateSplitEquiv x S).1 *
              (if i ∈ (coordinateSplitEquiv x S).2 then 0
                else complementRaisedFunction x hq a.2 s
                  (insert i (coordinateSplitEquiv x S).2)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).2 :=
                (coordinateSplitEquiv_mem_complement x i S).mpr hi
              simp only [hi, ↓reduceIte, hi', mul_zero]
            · have hi' : i ∉ (coordinateSplitEquiv x S).2 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_complement x i S).mp hmem)
              simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_insert_complement, hi']
          _ = _ := by
            unfold coordinateLower
            rw [Finset.mul_sum]

theorem lower_fintype_weighted_sum
    {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.lower
      (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * MetricCodes.Boolean.lower (f i) S := by
  classical
  funext S
  unfold MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
  calc
    (∑ j : Fin n,
      if j ∈ S then 0
      else ∑ i : ι, c i * f i (insert j S)) =
      ∑ j : Fin n, ∑ i : ι,
        c i * (if j ∈ S then 0 else f i (insert j S)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S <;> simp [hj]
    _ = ∑ i : ι, ∑ j : Fin n,
        c i * (if j ∈ S then 0 else f i (insert j S)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι,
        c i * (∑ j : Fin n,
          if j ∈ S then 0 else f i (insert j S)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem coupledTensor_lower_eq_zero {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.lower (coupledTensor x hp hq a t) = 0 := by
  classical
  funext S
  let A : Finset (SupportCoordinates x) :=
    (coordinateSplitEquiv x S).1
  let B : Finset (ComplementCoordinates x) :=
    (coordinateSplitEquiv x S).2
  have hsupport :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (coordinateLower
              (supportRaisedFunction x hp a.1 r.val) A *
            complementRaisedFunction x hq a.2
              (t - r.val) B)) =
        ∑ r : Fin t,
          clebschCoefficient w (n - w) p q t (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p
                (r.val + 1)) *
            splitTensor x hp hq a r.val
              (t - (r.val + 1)) S := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero,
      supportRaisedFunction_lower_zero, zero_mul, mul_zero,
      zero_add, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro r _
    have hr : r.val < t := r.isLt
    have hbound : 2 * p + (r.val + 1) ≤ w := by
      omega
    rw [supportRaisedFunction_lower x hp hbound a.1 A]
    change
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        (Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B) =
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        splitTensor x hp hq a r.val
          (t - (r.val + 1)) S
    change
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        (Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B) =
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        (supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B)
    ring
  have hcomplement :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (supportRaisedFunction x hp a.1 r.val A *
            coordinateLower
              (complementRaisedFunction x hq a.2
                (t - r.val)) B)) =
        ∑ r : Fin t,
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                (t - r.val)) *
            splitTensor x hp hq a r.val
              (t - (r.val + 1)) S := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self,
      complementRaisedFunction_lower_zero, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro r _
    have hr : r.val < t := r.isLt
    have hresidual :
        t - r.val = (t - (r.val + 1)) + 1 := by
      omega
    have hbound :
        2 * q + ((t - (r.val + 1)) + 1) ≤ n - w := by
      omega
    rw [hresidual,
      complementRaisedFunction_lower x hq hbound a.2 B]
    change
      clebschCoefficient w (n - w) p q t r.val *
        (supportRaisedFunction x hp a.1 r.val A *
          (Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                ((t - (r.val + 1)) + 1)) *
            complementRaisedFunction x hq a.2
              (t - (r.val + 1)) B)) =
      clebschCoefficient w (n - w) p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q
            ((t - (r.val + 1)) + 1)) *
        (supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B)
    ring
  calc
    MetricCodes.Boolean.lower (coupledTensor x hp hq a t) S =
      ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.lower
            (splitTensor x hp hq a r.val (t - r.val)) S := by
      change
        MetricCodes.Boolean.lower
          (fun T : Finset (Fin n) =>
            ∑ r : Fin (t + 1),
              clebschCoefficient w (n - w) p q t r.val *
                splitTensor x hp hq a r.val (t - r.val) T) S =
          ∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q t r.val *
              MetricCodes.Boolean.lower
                (splitTensor x hp hq a r.val (t - r.val)) S
      exact congrFun
        (lower_fintype_weighted_sum
          (fun r : Fin (t + 1) =>
            clebschCoefficient w (n - w) p q t r.val)
          (fun r : Fin (t + 1) =>
            splitTensor x hp hq a r.val (t - r.val))) S
    _ =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (coordinateLower
              (supportRaisedFunction x hp a.1 r.val) A *
            complementRaisedFunction x hq a.2
              (t - r.val) B)) +
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (supportRaisedFunction x hp a.1 r.val A *
            coordinateLower
              (complementRaisedFunction x hq a.2
                (t - r.val)) B)) := by
      simp_rw [lower_splitTensor]
      change
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (coordinateLower
                (supportRaisedFunction x hp a.1 r.val) A *
              complementRaisedFunction x hq a.2
                (t - r.val) B +
              supportRaisedFunction x hp a.1 r.val A *
                coordinateLower
                  (complementRaisedFunction x hq a.2
                    (t - r.val)) B)) = _
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ =
      (∑ r : Fin t,
        clebschCoefficient w (n - w) p q t (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S) +
      (∑ r : Fin t,
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient (n - w) q
              (t - r.val)) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S) := by
      rw [hsupport, hcomplement]
    _ =
      ∑ r : Fin t,
        (clebschCoefficient w (n - w) p q t (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) +
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                (t - r.val))) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hbound : 2 * p + (r.val + 1) ≤ w := by
        have hr := r.isLt
        omega
      rw [clebschCoefficient_succ_mul hbound]
      ring

theorem coupledHarmonic_isHarmonic {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.IsHarmonic (p + q + t)
      (coupledHarmonic x hp hq a t) := by
  refine ⟨coupledHarmonic_isLevel x hp hq a t, ?_⟩
  intro S
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.lower_smul,
    coupledTensor_lower_eq_zero x hp hq
      htsupport htcomplement a]
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero]

theorem AdmissibleDegrees.supportResidual_bound
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * p + i.val ≤ w := by
  have hi : p + q + i.val ≤ L := by
    have hfirst := h.first_le
    have hival := i.isLt
    omega
  have hleft :
      MetricCodes.johnsonLastDegree n w p q ≤ w - p + q := by
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hbound := (hi.trans h.last_le).trans hleft
  have hp := h.support_half
  omega

theorem AdmissibleDegrees.complementResidual_bound
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * q + i.val ≤ n - w := by
  have hi : p + q + i.val ≤ L := by
    have hfirst := h.first_le
    have hival := i.isLt
    omega
  have hright :
      MetricCodes.johnsonLastDegree n w p q ≤ n - w + p - q := by
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hbound := (hi.trans h.last_le).trans hright
  have hq := h.complement_half
  omega

theorem AdmissibleDegrees.window_degree_le_weight
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    p + q + i.val ≤ w := by
  have hival := i.isLt
  have hfirst := h.first_le
  have hterminal := h.terminal_le_weight
  omega

/-- The global harmonic vector used in the Johnson-code argument. -/
def globalHarmonicVector {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.harmonicEuclideanLayer n j :=
  ⟨WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f), by
    change
      WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f) ∈
        (MetricCodes.Boolean.harmonicLayer n j).map
          (WithLp.linearEquiv 2 ℝ
            (MetricCodes.Boolean.LayerFunction n j)).symm.toLinearMap
    apply Submodule.mem_map.mpr
    refine ⟨MetricCodes.Boolean.layerRestrict j f, ?_, rfl⟩
    apply (MetricCodes.Boolean.mem_harmonicLayer_iff _).mpr
    rw [MetricCodes.Boolean.layerExtend_layerRestrict_of_level f hf.1]
    exact hf⟩

theorem globalHarmonicVector_inner {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    @inner ℝ (MetricCodes.Boolean.harmonicEuclideanLayer n j) _
      (globalHarmonicVector f hf)
      (globalHarmonicVector g hg) =
        MetricCodes.Boolean.dot f g := by
  change
    @inner ℝ (MetricCodes.Boolean.EuclideanLayer n j) _
      (WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f))
      (WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j g)) =
        MetricCodes.Boolean.dot f g
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  symm
  simpa only [Boolean.layerRestrict, Boolean.layerDot] using
    MetricCodes.Boolean.dot_eq_layerDot_of_level f g hf.1 hg.1

theorem AdmissibleDegrees.window_degree_half
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * (p + q + i.val) ≤ n := by
  have hdegree := h.window_degree_le_weight i
  have hhalf := h.weight_half
  omega

/-- The coupled degree vector used in the Johnson-code argument. -/
def coupledDegreeVector {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.harmonicEuclideanLayer n (p + q + i.val) :=
  globalHarmonicVector
    (coupledHarmonic x h.support_half h.complement_half a i.val)
    (coupledHarmonic_isHarmonic x h.support_half h.complement_half
      (h.supportResidual_bound i)
      (h.complementResidual_bound i) a)

/-- The coupled degree coordinates used in the Johnson-code argument. -/
def coupledDegreeCoordinates {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a : HarmonicFibreIndex n w p q)
    (b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val))) : ℝ :=
  (MetricCodes.Boolean.harmonicOrthonormalBasis
    n (p + q + i.val) (h.window_degree_half i)).repr
      (coupledDegreeVector h x i a) b

theorem coupledDegreeCoordinates_pairing {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a b : HarmonicFibreIndex n w p q) :
    (∑ u : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val)),
      coupledDegreeCoordinates h x i a u *
        coupledDegreeCoordinates h x i b u) =
      if a = b then 1 else 0 := by
  let e := MetricCodes.Boolean.harmonicOrthonormalBasis
    n (p + q + i.val) (h.window_degree_half i)
  let A := coupledDegreeVector h x i a
  let B := coupledDegreeVector h x i b
  calc
    (∑ u : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val)),
      coupledDegreeCoordinates h x i a u *
        coupledDegreeCoordinates h x i b u) =
      @inner ℝ
        (EuclideanSpace ℝ
          (Fin (MetricCodes.hammingFibreDimension
            n (p + q + i.val)))) _
        (e.repr A) (e.repr B) := by
      change
        (∑ u : Fin (MetricCodes.hammingFibreDimension
          n (p + q + i.val)),
          e.repr A u * e.repr B u) =
        @inner ℝ
          (EuclideanSpace ℝ
            (Fin (MetricCodes.hammingFibreDimension
              n (p + q + i.val)))) _
          (e.repr A) (e.repr B)
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]
    _ = @inner ℝ
        (MetricCodes.Boolean.harmonicEuclideanLayer n
          (p + q + i.val)) _ A B :=
      e.repr.inner_map_map A B
    _ = MetricCodes.Boolean.dot
        (coupledHarmonic x h.support_half h.complement_half
          a i.val)
        (coupledHarmonic x h.support_half h.complement_half
          b i.val) := by
      exact globalHarmonicVector_inner
        (coupledHarmonic x h.support_half h.complement_half
          a i.val)
        (coupledHarmonic x h.support_half h.complement_half
          b i.val)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound i)
          (h.complementResidual_bound i) a)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound i)
          (h.complementResidual_bound i) b)
    _ = (if a = b then 1 else 0) :=
      coupledHarmonic_dot x h.support_half h.complement_half
        (h.supportResidual_bound i)
        (h.complementResidual_bound i) a b

/-- The johnson window fibre matrix used in the Johnson-code argument. -/
def johnsonWindowFibreMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (x : JohnsonSphere n w) :
    Matrix (ShellWindowIndex n p q L)
      (HarmonicFibreIndex n w p q) ℝ :=
  fun T a =>
    johnsonFibreAmplitude n w p q L v T.1 *
      coupledDegreeCoordinates h x T.1 a T.2

theorem johnsonWindowFibreMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (x : JohnsonSphere n w) :
    (johnsonWindowFibreMatrix h v x)ᵀ *
      johnsonWindowFibreMatrix h v x = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply]
  change
    (∑ T : ShellWindowIndex n p q L,
      johnsonWindowFibreMatrix h v x T a *
        johnsonWindowFibreMatrix h v x T b) =
      if a = b then 1 else 0
  calc
    (∑ T : ShellWindowIndex n p q L,
      johnsonWindowFibreMatrix h v x T a *
        johnsonWindowFibreMatrix h v x T b) =
      ∑ i : Index p q L,
        johnsonFibreAmplitude n w p q L v i ^ 2 *
          (∑ u : Fin (MetricCodes.booleanHarmonicDimension
            n (p + q + i.val)),
            coupledDegreeCoordinates h x i a u *
              coupledDegreeCoordinates h x i b u) := by
      simp only [johnsonWindowFibreMatrix]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ i : Index p q L,
        johnsonFibreAmplitude n w p q L v i ^ 2 *
          (if a = b then 1 else 0) := by
      simp_rw [coupledDegreeCoordinates_pairing h x]
    _ = (if a = b then 1 else 0) := by
      by_cases hab : a = b
      · simp only [hab, ↓reduceIte, mul_one, johnsonFibreAmplitude_sq_sum h v hv]
      · simp only [hab, ↓reduceIte, mul_zero, Finset.sum_const_zero]

/-- The johnson fibre matrix used in the Johnson-code argument. -/
def johnsonFibreMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (x : JohnsonSphere n w) :
    Matrix (Fin (MetricCodes.johnsonAmbientDimension n (p + q) L))
      (Fin (MetricCodes.johnsonFibreDimension n w p q)) ℝ :=
  fun i a =>
    johnsonWindowFibreMatrix h v x
      ((shellWindowIndexEquiv n p q L h.first_le).symm i)
      ((harmonicFibreIndexEquiv n w p q).symm a)

theorem johnsonFibreMatrix_transpose_mul {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (x : JohnsonSphere n w) :
    (johnsonFibreMatrix h v x)ᵀ *
      johnsonFibreMatrix h v x = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply]
  change
    (∑ i : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm a) *
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm b)) =
      if a = b then 1 else 0
  calc
    (∑ i : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm a) *
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm b)) =
      ∑ T : ShellWindowIndex n p q L,
        johnsonWindowFibreMatrix h v x T
          ((harmonicFibreIndexEquiv n w p q).symm a) *
        johnsonWindowFibreMatrix h v x T
          ((harmonicFibreIndexEquiv n w p q).symm b) :=
      (shellWindowIndexEquiv n p q L h.first_le).symm.sum_comp
        (fun T : ShellWindowIndex n p q L =>
          johnsonWindowFibreMatrix h v x T
            ((harmonicFibreIndexEquiv n w p q).symm a) *
          johnsonWindowFibreMatrix h v x T
            ((harmonicFibreIndexEquiv n w p q).symm b))
    _ = (if a = b then 1 else 0) := by
      have hmatrix := congrArg
        (fun M : Matrix (HarmonicFibreIndex n w p q)
          (HarmonicFibreIndex n w p q) ℝ =>
          M ((harmonicFibreIndexEquiv n w p q).symm a)
            ((harmonicFibreIndexEquiv n w p q).symm b))
        (johnsonWindowFibreMatrix_transpose_mul h v hv x)
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
        EmbeddingLike.apply_eq_iff_eq] using
        hmatrix

/-- The johnson projection family used in the Johnson-code argument. -/
def johnsonProjectionFamily {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i) :
    MetricCodes.ProjectionFamily (JohnsonSphere n w)
      (MetricCodes.johnsonAmbientDimension n (p + q) L)
      (MetricCodes.johnsonFibreDimension n w p q) where
  projection x :=
    johnsonFibreMatrix h v x *
      (johnsonFibreMatrix h v x)ᵀ
  symmetric x := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  idempotent x := by
    let A := johnsonFibreMatrix h v x
    change (A * Aᵀ) * (A * Aᵀ) = A * Aᵀ
    calc
      (A * Aᵀ) * (A * Aᵀ) = A * ((Aᵀ * A) * Aᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = A * Aᵀ := by
        rw [johnsonFibreMatrix_transpose_mul h v hv x,
          Matrix.one_mul]
  trace_eq x := by
    rw [Matrix.trace_mul_comm,
      johnsonFibreMatrix_transpose_mul h v hv x]
    simp only [Matrix.trace_one, Fintype.card_fin]

private def johnsonHarmonicGap (n j : ℕ) : ℝ :=
  (n : ℝ) - 2 * (j : ℝ)

theorem johnsonHarmonicGap_pos {n j : ℕ}
    (hj : 2 * j < n) :
    0 < johnsonHarmonicGap n j := by
  have hj' : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
    exact_mod_cast hj
  unfold johnsonHarmonicGap
  linarith

private def johnsonMiddleScale (n j : ℕ) : ℝ :=
  (j : ℝ) * johnsonHarmonicGap n j *
      ((n : ℝ) - (j : ℝ) + 1) /
    ((n : ℝ) * (johnsonHarmonicGap n j + 2))

private def johnsonUpperScale (n j : ℕ) : ℝ :=
  (johnsonHarmonicGap n j - 1) *
      ((n : ℝ) - (j : ℝ) + 1) /
    (johnsonHarmonicGap n j + 1)

theorem johnsonMiddleScale_pos {n j : ℕ}
    (hj : 0 < j) (hhalf : 2 * j < n) :
    0 < johnsonMiddleScale n j := by
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap := johnsonHarmonicGap_pos hhalf
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    have hcast : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  unfold johnsonMiddleScale
  positivity

theorem johnsonUpperScale_pos {n j : ℕ}
    (hhalf : 2 * (j + 1) ≤ n) :
    0 < johnsonUpperScale n j := by
  have hcast :
      (2 : ℝ) * ((j : ℝ) + 1) ≤ (n : ℝ) := by
    exact_mod_cast hhalf
  have hgap : 1 < johnsonHarmonicGap n j := by
    unfold johnsonHarmonicGap
    linarith
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    linarith
  unfold johnsonUpperScale
  positivity

theorem johnsonLowerAt_commutes {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.lowerAt a f) =
      MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.lower f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [Boolean.lower, Boolean.lowerAt, Finset.mem_insert, ha, or_true, ↓reduceIte, ite_self,
      Finset.sum_const_zero]
  · simp only [MetricCodes.Boolean.lower, MetricCodes.Boolean.lowerAt,
      ha, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ S
    · simp only [hb, ↓reduceIte, Finset.mem_insert, or_true]
    · by_cases hba : b = a
      · subst b
        simp only [ha, ↓reduceIte, Finset.mem_insert, or_false]
      · simp only [hb, ↓reduceIte, Finset.mem_insert, Ne.symm hba, ha, or_self, hba,
          Finset.insert_comm]

theorem johnsonLowerAt_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j (MetricCodes.Boolean.lowerAt a f) := by
  refine ⟨hf.1.lowerAt a, ?_⟩
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  intro S
  rw [johnsonLowerAt_commutes f a, hzero]
  simp only [Boolean.lowerAt, Pi.zero_apply, ite_self]

theorem johnsonLowerRaiseAt_commutator {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) S -
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S =
      f S - 2 *
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
  classical
  calc
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) S -
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S =
      ∑ b : Fin n,
        (MetricCodes.Boolean.lowerAt b (MetricCodes.Boolean.raiseAt a f) S -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt b f) S) := by
      change
        (∑ b : Fin n,
          MetricCodes.Boolean.lowerAt b (MetricCodes.Boolean.raiseAt a f) S) -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S = _
      rw [MetricCodes.Boolean.raiseAt_lower, ← Finset.sum_sub_distrib]
    _ = MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a f) S -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        rw [MetricCodes.Boolean.lowerAt_raiseAt_of_ne f b a hba S]
        exact sub_self _
      · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    _ = f S - 2 *
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
      rw [MetricCodes.Boolean.lowerAt_raiseAt_self,
        MetricCodes.Boolean.raiseAt_lowerAt_self]
      by_cases ha : a ∈ S <;> simp [ha]; ring

theorem johnsonLowerAt_lowerAt_self {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.lowerAt a f) = 0 := by
  classical
  funext S
  by_cases ha : a ∈ S <;>
    simp [MetricCodes.Boolean.lowerAt, ha]

theorem johnsonLowerRaiseAtLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) =
        MetricCodes.Boolean.lowerAt a f := by
  classical
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  have hlow :
      MetricCodes.Boolean.lower (MetricCodes.Boolean.lowerAt a f) = 0 := by
    rw [johnsonLowerAt_commutes f a, hzero]
    funext S
    simp only [Boolean.lowerAt, Pi.zero_apply, ite_self]
  have hdouble := johnsonLowerAt_lowerAt_self f a
  funext S
  have hcomm := johnsonLowerRaiseAt_commutator
    (MetricCodes.Boolean.lowerAt a f) a S
  rw [hlow, hdouble] at hcomm
  simpa only [Boolean.raiseAt, Pi.zero_apply, ite_self, sub_zero, mul_zero] using hcomm

theorem johnsonBooleanLower_sub {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.lower (f - g) =
      MetricCodes.Boolean.lower f - MetricCodes.Boolean.lower g := by
  change
    MetricCodes.Boolean.lowerLinear n (f - g) =
      MetricCodes.Boolean.lowerLinear n f -
        MetricCodes.Boolean.lowerLinear n g
  exact map_sub (MetricCodes.Boolean.lowerLinear n) f g

private def johnsonMiddleRaw {n : ℕ} (j : ℕ)
    (a : Fin n) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) -
      (johnsonHarmonicGap n j + 2)⁻¹ •
        MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) -
      ((j : ℝ) / (n : ℝ)) • f

theorem johnsonMiddleRaw_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (a : Fin n) :
    MetricCodes.Boolean.IsLevel j (johnsonMiddleRaw j a f) := by
  cases j with
  | zero => omega
  | succ k =>
      have hdown :
          MetricCodes.Boolean.IsLevel k (MetricCodes.Boolean.lowerAt a f) :=
        hf.1.lowerAt a
      have hmembership :
          MetricCodes.Boolean.IsLevel (k + 1)
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f)) :=
        hdown.raiseAt a
      have hraise :
          MetricCodes.Boolean.IsLevel (k + 1)
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) :=
        hdown.raise
      intro S hS
      simp only [johnsonMiddleRaw, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hmembership S hS, hraise S hS, hf.1 S hS]
      ring

theorem johnsonMiddleRaw_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (hhalf : 2 * j < n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j (johnsonMiddleRaw j a f) := by
  refine ⟨johnsonMiddleRaw_isLevel f hf hj a, ?_⟩
  cases j with
  | zero => omega
  | succ k =>
      have hlow := johnsonLowerAt_harmonic f hf a
      have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
      have hmembership :=
        johnsonLowerRaiseAtLowerAt_of_harmonic f hf a
      have hraise :
          MetricCodes.Boolean.lower
              (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) =
            (johnsonHarmonicGap n (k + 1) + 2) •
              MetricCodes.Boolean.lowerAt a f := by
        funext S
        rw [MetricCodes.Boolean.lower_raise_of_harmonic
          (MetricCodes.Boolean.lowerAt a f) hlow]
        change
          ((n : ℝ) - 2 * (k : ℝ)) *
              MetricCodes.Boolean.lowerAt a f S =
            (johnsonHarmonicGap n (k + 1) + 2) *
              MetricCodes.Boolean.lowerAt a f S
        unfold johnsonHarmonicGap
        push_cast
        ring
      have hden : johnsonHarmonicGap n (k + 1) + 2 ≠ 0 := by
        have hgap := johnsonHarmonicGap_pos hhalf
        linarith
      intro S
      unfold johnsonMiddleRaw
      rw [johnsonBooleanLower_sub,
        johnsonBooleanLower_sub,
        MetricCodes.Boolean.lower_smul,
        MetricCodes.Boolean.lower_smul,
        hmembership, hraise, hzero]
      simp only [Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, mul_zero, sub_zero]
      field_simp [hden]; simp only [sub_self, mul_zero]

private def johnsonUpperRaw {n : ℕ} (j : ℕ)
    (a : Fin n) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.raiseAt a f -
      (johnsonHarmonicGap n j)⁻¹ • MetricCodes.Boolean.raise f +
      (2 / johnsonHarmonicGap n j) •
        MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) -
      (johnsonHarmonicGap n j *
        (johnsonHarmonicGap n j + 1))⁻¹ •
        MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))

theorem johnsonLowerAt_eq_zero_of_level_zero {n : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel 0 f)
    (a : Fin n) :
    MetricCodes.Boolean.lowerAt a f = 0 := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [Boolean.lowerAt, ha, ↓reduceIte, Pi.zero_apply]
  · have hcard : (insert a S).card ≠ 0 :=
      Finset.card_ne_zero_of_mem (Finset.mem_insert_self a S)
    simp only [Boolean.lowerAt, ha, ↓reduceIte, hf (insert a S) hcard, Pi.zero_apply]

theorem johnsonMembership_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (a : Fin n) :
    MetricCodes.Boolean.IsLevel j
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) := by
  intro S hS
  rw [MetricCodes.Boolean.raiseAt_lowerAt_self]
  simp only [hf S hS, ite_self]

theorem johnsonUpperRaw_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.IsLevel (j + 1) (johnsonUpperRaw j a f) := by
  cases j with
  | zero =>
      have hzero := johnsonLowerAt_eq_zero_of_level_zero f hf.1 a
      have hcoordinate := hf.1.raiseAt a
      have hglobal := hf.1.raise
      intro S hS
      simp only [johnsonUpperRaw, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hcoordinate S hS, hglobal S hS, hzero]
      simp only [mul_zero, sub_self, Boolean.raise, Boolean.raiseAt, Finset.mem_erase, ne_eq,
        Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero, mul_inv_rev]
  | succ k =>
      have hdown :
          MetricCodes.Boolean.IsLevel k (MetricCodes.Boolean.lowerAt a f) :=
        hf.1.lowerAt a
      have hcoordinate := hf.1.raiseAt a
      have hglobal := hf.1.raise
      have hmembership :=
        (johnsonMembership_isLevel f hf.1 a).raise
      have hdouble := hdown.raise.raise
      intro S hS
      simp only [johnsonUpperRaw, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hcoordinate S hS, hglobal S hS,
        hmembership S hS, hdouble S hS]
      ring

theorem johnsonLowerRaise_of_level {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raise f) =
      MetricCodes.Boolean.raise (MetricCodes.Boolean.lower f) +
        johnsonHarmonicGap n j • f := by
  funext S
  have h :=
    MetricCodes.Boolean.lower_raise_sub_raise_lower_of_level f hf S
  have h' := sub_eq_iff_eq_add.mp h
  simpa only [johnsonHarmonicGap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using h'

theorem johnsonLowerRaiseAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) =
      f - (2 : ℝ) •
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) := by
  classical
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  funext S
  have h := johnsonLowerRaiseAt_commutator f a S
  rw [hzero] at h
  simpa only [Pi.sub_apply, Pi.smul_apply, Boolean.raiseAt, smul_eq_mul, mul_ite, mul_zero,
    Pi.zero_apply, ite_self, sub_zero] using h

theorem johnsonLowerRaise_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raise f) =
      johnsonHarmonicGap n j • f := by
  funext S
  simpa only [johnsonHarmonicGap, Pi.smul_apply, smul_eq_mul] using
    MetricCodes.Boolean.lower_raise_of_harmonic f hf S

theorem johnsonLowerDoubleRaiseLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raise
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))) =
      (2 * (johnsonHarmonicGap n j + 1)) •
        MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) := by
  cases j with
  | zero =>
      have hzero := johnsonLowerAt_eq_zero_of_level_zero f hf.1 a
      have hraise :
          MetricCodes.Boolean.raise (0 : MetricCodes.Boolean.Function n) = 0 := by
        change MetricCodes.Boolean.raiseLinear n
          (0 : MetricCodes.Boolean.Function n) = 0
        exact map_zero (MetricCodes.Boolean.raiseLinear n)
      have hlower :
          MetricCodes.Boolean.lower (0 : MetricCodes.Boolean.Function n) = 0 := by
        change MetricCodes.Boolean.lowerLinear n
          (0 : MetricCodes.Boolean.Function n) = 0
        exact map_zero (MetricCodes.Boolean.lowerLinear n)
      rw [hzero]
      simp only [hraise, hlower, smul_zero]
  | succ k =>
      have hdown := johnsonLowerAt_harmonic f hf a
      have h := MetricCodes.Boolean.lower_raised_succ_of_harmonic
        (MetricCodes.Boolean.lowerAt a f) hdown 1
      change
        MetricCodes.Boolean.lower
          (MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))) =
          MetricCodes.Boolean.harmonicCoefficient n k 2 •
            MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) at h
      have hcoefficient :
          MetricCodes.Boolean.harmonicCoefficient n k 2 =
            2 * (johnsonHarmonicGap n (k + 1) + 1) := by
        simp only [Boolean.harmonicCoefficient, Nat.cast_ofNat, johnsonHarmonicGap, Nat.cast_add,
          Nat.cast_one, mul_eq_mul_left_iff, add_left_inj, OfNat.ofNat_ne_zero, or_false]
        ring
      rw [hcoefficient] at h
      exact h

theorem johnsonLowerRaiseMembership_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raise
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))) =
      MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) +
        johnsonHarmonicGap n j •
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) := by
  rw [johnsonLowerRaise_of_level
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
    (johnsonMembership_isLevel f hf.1 a),
    johnsonLowerRaiseAtLowerAt_of_harmonic f hf a]

theorem johnsonUpperRaw_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic (j + 1)
      (johnsonUpperRaw j a f) := by
  refine ⟨johnsonUpperRaw_isLevel f hf a, ?_⟩
  have hgap : 0 < johnsonHarmonicGap n j := by
    apply johnsonHarmonicGap_pos
    omega
  have hgapone : johnsonHarmonicGap n j + 1 ≠ 0 := by
    linarith
  have hgapne : johnsonHarmonicGap n j ≠ 0 := hgap.ne'
  have hcoordinate := johnsonLowerRaiseAt_of_harmonic f hf a
  have hglobal := johnsonLowerRaise_of_harmonic f hf
  have hmembership :=
    johnsonLowerRaiseMembership_of_harmonic f hf a
  have hdouble :=
    johnsonLowerDoubleRaiseLowerAt_of_harmonic f hf a
  intro S
  unfold johnsonUpperRaw
  rw [johnsonBooleanLower_sub,
    MetricCodes.Boolean.lower_add,
    johnsonBooleanLower_sub,
    MetricCodes.Boolean.lower_smul,
    MetricCodes.Boolean.lower_smul,
    MetricCodes.Boolean.lower_smul,
    hcoordinate, hglobal, hmembership, hdouble]
  simp only [Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hgapne, hgapone]
  ring

theorem johnsonBooleanDot_sub_left {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot (f - g) h =
      MetricCodes.Boolean.dot f h - MetricCodes.Boolean.dot g h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem johnsonBooleanDot_sub_right {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (g - h) =
      MetricCodes.Boolean.dot f g - MetricCodes.Boolean.dot f h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem johnsonBooleanDot_add_left {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot (f + g) h =
      MetricCodes.Boolean.dot f h + MetricCodes.Boolean.dot g h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem johnsonDotRaise_harmonic_right {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    MetricCodes.Boolean.dot (MetricCodes.Boolean.raise f) g = 0 := by
  rw [MetricCodes.Boolean.dot_raise_eq_lower]
  have hzero : MetricCodes.Boolean.lower g = 0 := funext hg.2
  rw [hzero]
  simp only [Boolean.dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem johnsonLowerAtRaiseAtLowerAt {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lowerAt a
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) =
      MetricCodes.Boolean.lowerAt a f := by
  classical
  funext S
  rw [MetricCodes.Boolean.lowerAt_raiseAt_self]
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte, Boolean.lowerAt]
  · simp only [ha, ↓reduceIte]

theorem johnsonSumDotMembershipMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a
            (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))
    _ = ∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.lowerAt a g) := by
          simp_rw [johnsonLowerAtRaiseAtLowerAt]
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotMembershipLeft {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
            (MetricCodes.Boolean.lowerAt a f) g
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotMembershipRight {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsLevel j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) f := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_comm _ _
    _ = (j : ℝ) * MetricCodes.Boolean.dot g f :=
      johnsonSumDotMembershipLeft g f hg
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g := by
      rw [MetricCodes.Boolean.dot_comm g f]

theorem johnsonLowerRaiseLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (a : Fin n) :
    MetricCodes.Boolean.lower
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) =
      (johnsonHarmonicGap n j + 2) •
        MetricCodes.Boolean.lowerAt a f := by
  cases j with
  | zero => omega
  | succ k =>
      have hdown := johnsonLowerAt_harmonic f hf a
      funext S
      rw [MetricCodes.Boolean.lower_raise_of_harmonic
        (MetricCodes.Boolean.lowerAt a f) hdown]
      change
        ((n : ℝ) - 2 * (k : ℝ)) *
            MetricCodes.Boolean.lowerAt a f S =
          (johnsonHarmonicGap n (k + 1) + 2) *
            MetricCodes.Boolean.lowerAt a f S
      unfold johnsonHarmonicGap
      push_cast
      ring

theorem johnsonSumDotMembershipRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a f))
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g)) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a f)) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a g)
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a g)
                (MetricCodes.Boolean.lowerAt a f) := by
                  rw [johnsonLowerRaiseAtLowerAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a f)
                (MetricCodes.Boolean.lowerAt a g) :=
                MetricCodes.Boolean.dot_comm _ _
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf.1

theorem johnsonSumDotRaisedDeletionMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [MetricCodes.Boolean.dot_raise_eq_lower,
            johnsonLowerRaiseAtLowerAt_of_harmonic g hg a]
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotRaisedDeletionRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      (johnsonHarmonicGap n j + 2) *
        ((j : ℝ) * MetricCodes.Boolean.dot f g) := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lower
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raise_eq_lower
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))
    _ = ∑ a : Fin n,
          (johnsonHarmonicGap n j + 2) *
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.lowerAt a f)
              (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [johnsonLowerRaiseLowerAt_of_harmonic g hg hj a,
            MetricCodes.Boolean.dot_smul_right]
    _ = (johnsonHarmonicGap n j + 2) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.lowerAt a f)
              (MetricCodes.Boolean.lowerAt a g)) := by
          rw [Finset.mul_sum]
    _ = (johnsonHarmonicGap n j + 2) *
          ((j : ℝ) * MetricCodes.Boolean.dot f g) := by
          rw [MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf]

theorem johnsonSumDotRaisedDeletionHarmonicRight {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) g) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  exact johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a f) g hg

theorem johnsonSumDotHarmonicRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  rw [MetricCodes.Boolean.dot_comm]
  exact johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a g) f hf

theorem johnsonMiddleRaw_coordinateDot {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) (hhalf : 2 * j < n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw j a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      johnsonMiddleScale n j * MetricCodes.Boolean.dot f g := by
  classical
  let c : ℝ := (johnsonHarmonicGap n j + 2)⁻¹
  let b : ℝ := (j : ℝ) / (n : ℝ)
  let mf : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)
  let mg : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)
  let uf : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)
  let ug : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw j a f)
          (johnsonMiddleRaw j a g) =
        MetricCodes.Boolean.dot (mf a) (mg a) -
          c * MetricCodes.Boolean.dot (mf a) (ug a) -
          b * MetricCodes.Boolean.dot (mf a) g -
          c * MetricCodes.Boolean.dot (uf a) (mg a) +
          c ^ 2 * MetricCodes.Boolean.dot (uf a) (ug a) +
          c * b * MetricCodes.Boolean.dot (uf a) g -
          b * MetricCodes.Boolean.dot f (mg a) +
          b * c * MetricCodes.Boolean.dot f (ug a) +
          b ^ 2 * MetricCodes.Boolean.dot f g := by
    dsimp [mf, mg, uf, ug, c, b]
    simp only [johnsonMiddleRaw,
      johnsonBooleanDot_sub_left,
      johnsonBooleanDot_sub_right,
      MetricCodes.Boolean.dot_smul_left,
      MetricCodes.Boolean.dot_smul_right]
    ring
  have hn : 0 < n := by omega
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hgap := johnsonHarmonicGap_pos hhalf
  have hgapplus : johnsonHarmonicGap n j + 2 ≠ 0 := by
    linarith
  have hconstant :
      (∑ _a : Fin n, MetricCodes.Boolean.dot f g) =
        (n : ℝ) * MetricCodes.Boolean.dot f g := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw j a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) (mg a)) -
        c * (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) (ug a)) -
        b * (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) g) -
        c * (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) (mg a)) +
        c ^ 2 *
          (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) (ug a)) +
        c * b * (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) g) -
        b * (∑ a : Fin n, MetricCodes.Boolean.dot f (mg a)) +
        b * c * (∑ a : Fin n, MetricCodes.Boolean.dot f (ug a)) +
        b ^ 2 * (∑ _a : Fin n, MetricCodes.Boolean.dot f g) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          simp only [Finset.sum_add_distrib,
            Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = johnsonMiddleScale n j * MetricCodes.Boolean.dot f g := by
          dsimp only [mf, mg, uf, ug]
          rw [johnsonSumDotMembershipMembership f g hf.1,
            johnsonSumDotMembershipRaisedDeletion f g hf,
            johnsonSumDotMembershipLeft f g hf.1,
            johnsonSumDotRaisedDeletionMembership f g hf.1 hg,
            johnsonSumDotRaisedDeletionRaisedDeletion
              f g hf.1 hg hj,
            johnsonSumDotRaisedDeletionHarmonicRight f g hg,
            johnsonSumDotMembershipRight f g hg.1,
            johnsonSumDotHarmonicRaisedDeletion f g hf,
            hconstant]
          dsimp [c, b]
          unfold johnsonMiddleScale
          field_simp [hnreal, hgapplus]
          unfold johnsonHarmonicGap
          ring

private def johnsonMiddleChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a =>
    (Real.sqrt (johnsonMiddleScale n j))⁻¹ •
      johnsonMiddleRaw j a f

theorem johnsonMiddleChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) (hhalf : 2 * j < n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel j f)
        (johnsonMiddleChannel j g) =
      MetricCodes.Boolean.dot f g := by
  classical
  have hpos := johnsonMiddleScale_pos hj hhalf
  have hs : Real.sqrt (johnsonMiddleScale n j) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  have hsquare :
      Real.sqrt (johnsonMiddleScale n j) *
          Real.sqrt (johnsonMiddleScale n j) =
        johnsonMiddleScale n j :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j = 1 := by
    calc
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j =
        (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j) *
            Real.sqrt (johnsonMiddleScale n j)) := by
              rw [hsquare]
      _ = 1 := by
        field_simp [hs]
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel j f)
        (johnsonMiddleChannel j g) =
      ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        (Real.sqrt (johnsonMiddleScale n j))⁻¹) *
        MetricCodes.Boolean.coordinateDot
          (fun a : Fin n => johnsonMiddleRaw j a f)
          (fun a : Fin n => johnsonMiddleRaw j a g) := by
          simp only [MetricCodes.Boolean.coordinateDot,
            johnsonMiddleChannel,
            MetricCodes.Boolean.dot_smul_left,
            MetricCodes.Boolean.dot_smul_right,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹) *
        (johnsonMiddleScale n j * MetricCodes.Boolean.dot f g) := by
          rw [johnsonMiddleRaw_coordinateDot f g hf hg hj hhalf]
    _ = ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j) *
        MetricCodes.Boolean.dot f g := by
          ring
    _ = MetricCodes.Boolean.dot f g := by
          rw [hscalar, one_mul]

theorem johnsonSumDotRaiseAtRaise {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise g)) =
      johnsonHarmonicGap n j * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise g)) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raise g)) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a f
            (MetricCodes.Boolean.raise g)
    _ = MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.lower (MetricCodes.Boolean.raise g)) := by
          simp only [MetricCodes.Boolean.dot, MetricCodes.Boolean.lower,
            Finset.mul_sum]
          exact Finset.sum_comm
    _ = johnsonHarmonicGap n j * MetricCodes.Boolean.dot f g := by
          rw [johnsonLowerRaise_of_harmonic g hg,
            MetricCodes.Boolean.dot_smul_right]

theorem johnsonSumDotRaiseAtRaisedMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsLevel j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)))) =
      -(j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)))) =
      ∑ a : Fin n,
        (MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
          2 * MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g))) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)))
                (MetricCodes.Boolean.raiseAt a f) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a f)) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g))
                (f - (2 : ℝ) •
                  MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f)) := by
                  rw [johnsonLowerRaiseAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot f
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)) -
                2 * MetricCodes.Boolean.dot
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)) := by
                  rw [johnsonBooleanDot_sub_right,
                    MetricCodes.Boolean.dot_smul_right,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g)) f,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g))
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a f))]
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a g))) -
        2 * (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a g))) := by
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = -(j : ℝ) * MetricCodes.Boolean.dot f g := by
          rw [johnsonSumDotMembershipRight f g hg,
            johnsonSumDotMembershipMembership f g hf.1]
          ring

theorem johnsonSumDotRaiseAtDoubleRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)))) =
      -(2 * (j : ℝ)) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)))) =
      ∑ a : Fin n,
        (MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) -
          2 * MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g))) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)))
                (MetricCodes.Boolean.raiseAt a f) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a f)) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (f - (2 : ℝ) •
                  MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f)) := by
                  rw [johnsonLowerRaiseAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot f
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)) -
                2 * MetricCodes.Boolean.dot
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)) := by
                  rw [johnsonBooleanDot_sub_right,
                    MetricCodes.Boolean.dot_smul_right,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g)) f,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g))
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a f))]
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) -
        2 * (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = -(2 * (j : ℝ)) * MetricCodes.Boolean.dot f g := by
          rw [johnsonSumDotHarmonicRaisedDeletion f g hf,
            johnsonSumDotMembershipRaisedDeletion f g hf]
          ring

theorem johnsonUpperRaw_dot_eq_coordinateCreation {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.dot
        (johnsonUpperRaw j a f)
        (johnsonUpperRaw j a g) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a f)
        (johnsonUpperRaw j a g) := by
  have hup := johnsonUpperRaw_isHarmonic g hg hhalf a
  have hglobal := johnsonDotRaise_harmonic_right f
    (johnsonUpperRaw j a g) hup
  have hmembership := johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
    (johnsonUpperRaw j a g) hup
  have hdouble := johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
    (johnsonUpperRaw j a g) hup
  change
    MetricCodes.Boolean.dot
      (MetricCodes.Boolean.raiseAt a f -
        (johnsonHarmonicGap n j)⁻¹ •
          MetricCodes.Boolean.raise f +
        (2 / johnsonHarmonicGap n j) •
          MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f)) -
        (johnsonHarmonicGap n j *
          (johnsonHarmonicGap n j + 1))⁻¹ •
          MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raise
              (MetricCodes.Boolean.lowerAt a f)))
      (johnsonUpperRaw j a g) = _
  simp only [johnsonBooleanDot_sub_left,
    johnsonBooleanDot_add_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [hglobal, hmembership, hdouble]
  ring

theorem johnsonUpperRaw_coordinateDot {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonUpperRaw j a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      johnsonUpperScale n j * MetricCodes.Boolean.dot f g := by
  classical
  have hbelow : 2 * j < n := by omega
  have hgap := johnsonHarmonicGap_pos hbelow
  have hgapne : johnsonHarmonicGap n j ≠ 0 := hgap.ne'
  have hgapone : johnsonHarmonicGap n j + 1 ≠ 0 := by
    linarith
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonUpperRaw j a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.raiseAt a f)
          (johnsonUpperRaw j a g) := by
          unfold MetricCodes.Boolean.coordinateDot
          apply Finset.sum_congr rfl
          intro a _
          exact johnsonUpperRaw_dot_eq_coordinateCreation
            f g hg hhalf a
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a f)
            (MetricCodes.Boolean.raiseAt a g)) -
        (johnsonHarmonicGap n j)⁻¹ *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise g)) +
        (2 / johnsonHarmonicGap n j) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g)))) -
        (johnsonHarmonicGap n j *
            (johnsonHarmonicGap n j + 1))⁻¹ *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g)))) := by
          simp only [johnsonUpperRaw,
            johnsonBooleanDot_sub_right,
            MetricCodes.Boolean.dot_add_right,
            MetricCodes.Boolean.dot_smul_right,
            Finset.sum_add_distrib,
            Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = johnsonUpperScale n j * MetricCodes.Boolean.dot f g := by
          rw [MetricCodes.Boolean.sum_dot_raiseAt_of_level f g hf.1,
            johnsonSumDotRaiseAtRaise f g hg,
            johnsonSumDotRaiseAtRaisedMembership f g hf hg.1,
            johnsonSumDotRaiseAtDoubleRaisedDeletion f g hf]
          unfold johnsonUpperScale
          field_simp [hgapne, hgapone]
          unfold johnsonHarmonicGap
          ring

private def johnsonUpperChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a =>
    (Real.sqrt (johnsonUpperScale n j))⁻¹ •
      johnsonUpperRaw j a f

theorem johnsonUpperChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel j f)
        (johnsonUpperChannel j g) =
      MetricCodes.Boolean.dot f g := by
  classical
  have hpos := johnsonUpperScale_pos hhalf
  have hs : Real.sqrt (johnsonUpperScale n j) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  have hsquare :
      Real.sqrt (johnsonUpperScale n j) *
          Real.sqrt (johnsonUpperScale n j) =
        johnsonUpperScale n j :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j = 1 := by
    calc
      (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j =
        (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j) *
            Real.sqrt (johnsonUpperScale n j)) := by
              rw [hsquare]
      _ = 1 := by
        field_simp [hs]
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel j f)
        (johnsonUpperChannel j g) =
      ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
        (Real.sqrt (johnsonUpperScale n j))⁻¹) *
        MetricCodes.Boolean.coordinateDot
          (fun a : Fin n => johnsonUpperRaw j a f)
          (fun a : Fin n => johnsonUpperRaw j a g) := by
          simp only [MetricCodes.Boolean.coordinateDot,
            johnsonUpperChannel,
            MetricCodes.Boolean.dot_smul_left,
            MetricCodes.Boolean.dot_smul_right,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹) *
        (johnsonUpperScale n j * MetricCodes.Boolean.dot f g) := by
          rw [johnsonUpperRaw_coordinateDot f g hf hg hhalf]
    _ = ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j) *
        MetricCodes.Boolean.dot f g := by
          ring
    _ = MetricCodes.Boolean.dot f g := by
          rw [hscalar, one_mul]

private def johnsonLowerChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  MetricCodes.Boolean.deleteChannel j f

theorem johnsonLowerChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel j f)
        (johnsonLowerChannel j g) =
      MetricCodes.Boolean.dot f g := by
  exact MetricCodes.Boolean.deleteChannel_isometry hj f g hf.1

theorem johnsonDotHarmonicRaise {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) = 0 := by
  rw [MetricCodes.Boolean.dot_comm]
  exact johnsonDotRaise_harmonic_right g f hf

theorem johnsonSumDotRaiseAtRight {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g)) =
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) := by
  classical
  simp only [MetricCodes.Boolean.dot, MetricCodes.Boolean.raise,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem johnsonSumDotLowerAtRight {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) =
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_lowerAt_eq_raiseAt a f g
    _ = MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) :=
      johnsonSumDotRaiseAtRight f g

theorem johnsonDotMembershipRaiseAt {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
  classical
  calc
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.lowerAt a f)
        (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a g)) :=
      MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
        (MetricCodes.Boolean.lowerAt a f)
        (MetricCodes.Boolean.raiseAt a g)
    _ = MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
      unfold MetricCodes.Boolean.dot
      apply Finset.sum_congr rfl
      intro S _
      rw [MetricCodes.Boolean.lowerAt_raiseAt_self]
      by_cases ha : a ∈ S
      · simp only [Boolean.lowerAt, ha, ↓reduceIte, mul_zero, zero_mul]
      · simp only [ha, ↓reduceIte]

theorem johnsonDotRaisedDeletionRaiseAt {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) (a : Fin n) :
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
  rw [MetricCodes.Boolean.dot_raise_eq_lower,
    johnsonLowerRaiseAt_of_harmonic g hg a,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_smul_right,
    MetricCodes.Boolean.dot_lowerAt_raiseAt]
  ring

theorem johnsonLowerMiddleRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) = 0 := by
  classical
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (johnsonMiddleRaw j a g) =
        -((j : ℝ) / (n : ℝ)) *
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
    have hdown := johnsonLowerAt_harmonic f hf a
    have hraise := johnsonDotHarmonicRaise
      (MetricCodes.Boolean.lowerAt a f)
      (MetricCodes.Boolean.lowerAt a g) hdown
    simp only [johnsonMiddleRaw,
      johnsonBooleanDot_sub_right,
      MetricCodes.Boolean.dot_smul_right]
    rw [MetricCodes.Boolean.dot_lowerAt_raiseAt, hraise]
    ring
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      -((j : ℝ) / (n : ℝ)) *
        (∑ a : Fin n,
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [johnsonSumDotLowerAtRight f g,
            johnsonDotHarmonicRaise f g hf]
          ring

theorem johnsonLowerUpperRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 2) f) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonUpperRaw j a g) = 0 := by
  classical
  unfold MetricCodes.Boolean.coordinateDot
  apply Finset.sum_eq_zero
  intro a _
  have hf' : MetricCodes.Boolean.IsHarmonic ((j + 1) + 1) f := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hf
  have hdown := johnsonLowerAt_harmonic f hf' a
  have hglobal := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f) g hdown
  have hmembership := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f)
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) hdown
  have hdouble := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f)
    (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) hdown
  simp only [johnsonUpperRaw,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_add_right,
    MetricCodes.Boolean.dot_smul_right]
  rw [MetricCodes.Boolean.dot_lowerAt_raiseAt,
    hglobal, hmembership, hdouble]
  ring

theorem johnsonMiddleUpperRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) < n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw (j + 1) a f)
        (fun a : Fin n => johnsonUpperRaw j a g) = 0 := by
  classical
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (johnsonUpperRaw j a g) =
        (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g -
        (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
    have hmid := johnsonMiddleRaw_isHarmonic
      f hf (by omega) hhalf a
    have hglobal := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f) g hmid
    have hmembership := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f)
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) hmid
    have hdouble := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f)
      (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) hmid
    calc
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (johnsonUpperRaw j a g) =
        MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (MetricCodes.Boolean.raiseAt a g) := by
            change
              MetricCodes.Boolean.dot
                (johnsonMiddleRaw (j + 1) a f)
                (MetricCodes.Boolean.raiseAt a g -
                  (johnsonHarmonicGap n j)⁻¹ •
                    MetricCodes.Boolean.raise g +
                  (2 / johnsonHarmonicGap n j) •
                    MetricCodes.Boolean.raise
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g)) -
                  (johnsonHarmonicGap n j *
                    (johnsonHarmonicGap n j + 1))⁻¹ •
                    MetricCodes.Boolean.raise
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g))) = _
            simp only [johnsonBooleanDot_sub_right,
              MetricCodes.Boolean.dot_add_right,
              MetricCodes.Boolean.dot_smul_right]
            rw [hglobal, hmembership, hdouble]
            ring
      _ = (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
            MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g -
          (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
            MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
            unfold johnsonMiddleRaw
            simp only [johnsonBooleanDot_sub_left,
              MetricCodes.Boolean.dot_smul_left]
            rw [johnsonDotMembershipRaiseAt f g a,
              johnsonDotRaisedDeletionRaiseAt f g hg a]
            ring
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw (j + 1) a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) -
        (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g)) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = 0 := by
          rw [johnsonSumDotLowerAtRight f g,
            johnsonSumDotRaiseAtRight f g,
            johnsonDotHarmonicRaise f g hf]
          ring

theorem johnsonCoordinateDot_smul {n : ℕ}
    (c d : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot
        (fun a => c • f a)
        (fun a => d • g a) =
      (c * d) * MetricCodes.Boolean.coordinateDot f g := by
  classical
  simp only [MetricCodes.Boolean.coordinateDot,
    MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonLowerChannel_orthogonal_middleChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (j + 1) f)
        (johnsonMiddleChannel j g) = 0 := by
  unfold johnsonLowerChannel MetricCodes.Boolean.deleteChannel
    johnsonMiddleChannel
  rw [johnsonCoordinateDot_smul,
    johnsonLowerMiddleRaw_orthogonal f g hf]
  simp only [Nat.cast_add, Nat.cast_one, mul_zero]

theorem johnsonLowerChannel_orthogonal_upperChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 2) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (j + 2) f)
        (johnsonUpperChannel j g) = 0 := by
  unfold johnsonLowerChannel MetricCodes.Boolean.deleteChannel
    johnsonUpperChannel
  rw [johnsonCoordinateDot_smul,
    johnsonLowerUpperRaw_orthogonal f g hf]
  simp only [Nat.cast_add, Nat.cast_ofNat, mul_zero]

theorem johnsonMiddleChannel_orthogonal_upperChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) < n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (j + 1) f)
        (johnsonUpperChannel j g) = 0 := by
  unfold johnsonMiddleChannel johnsonUpperChannel
  rw [johnsonCoordinateDot_smul,
    johnsonMiddleUpperRaw_orthogonal f g hf hg hhalf]
  simp only [mul_zero]

theorem johnsonHarmonic_smul {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) (c : ℝ) :
    MetricCodes.Boolean.IsHarmonic j (c • f) := by
  refine ⟨hf.1.smul c, ?_⟩
  intro S
  rw [MetricCodes.Boolean.lower_smul]
  simp only [Pi.smul_apply, hf.2 S, smul_eq_mul, mul_zero]

theorem johnsonLowerChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j
      (johnsonLowerChannel (j + 1) f a) := by
  change
    MetricCodes.Boolean.IsHarmonic j
      ((Real.sqrt (((j + 1 : ℕ) : ℝ)))⁻¹ •
        MetricCodes.Boolean.lowerAt a f)
  exact johnsonHarmonic_smul
    (MetricCodes.Boolean.lowerAt a f)
    (johnsonLowerAt_harmonic f hf a)
    (Real.sqrt (((j + 1 : ℕ) : ℝ)))⁻¹

theorem johnsonMiddleChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * j < n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j
      (johnsonMiddleChannel j f a) := by
  cases j with
  | zero =>
      have hscale : johnsonMiddleScale n 0 = 0 := by
        simp only [johnsonMiddleScale, CharP.cast_eq_zero, zero_mul, sub_zero, zero_div]
      change
        MetricCodes.Boolean.IsHarmonic 0
          ((Real.sqrt (johnsonMiddleScale n 0))⁻¹ •
            johnsonMiddleRaw 0 a f)
      rw [hscale]
      simp only [Real.sqrt_zero, inv_zero, zero_smul]
      simpa only [zero_smul] using johnsonHarmonic_smul f hf (0 : ℝ)
  | succ j =>
      change
        MetricCodes.Boolean.IsHarmonic (j + 1)
          ((Real.sqrt (johnsonMiddleScale n (j + 1)))⁻¹ •
            johnsonMiddleRaw (j + 1) a f)
      exact johnsonHarmonic_smul
        (johnsonMiddleRaw (j + 1) a f)
        (johnsonMiddleRaw_isHarmonic f hf (by omega) hhalf a)
        (Real.sqrt (johnsonMiddleScale n (j + 1)))⁻¹

theorem johnsonUpperChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic (j + 1)
      (johnsonUpperChannel j f a) := by
  change
    MetricCodes.Boolean.IsHarmonic (j + 1)
      ((Real.sqrt (johnsonUpperScale n j))⁻¹ •
        johnsonUpperRaw j a f)
  exact johnsonHarmonic_smul
    (johnsonUpperRaw j a f)
    (johnsonUpperRaw_isHarmonic f hf hhalf a)
    (Real.sqrt (johnsonUpperScale n j))⁻¹

private def johnsonDiagonalChannelSign
    (n w p q j : ℕ) : ℝ :=
  if 0 ≤ MetricCodes.johnsonDiagonal n w p q j then 1 else -1

theorem johnsonDiagonalChannelSign_sq
    (n w p q j : ℕ) :
    johnsonDiagonalChannelSign n w p q j ^ 2 = 1 := by
  unfold johnsonDiagonalChannelSign
  split <;> norm_num

/-- The johnson adjacent channel used in the Johnson-code argument. -/
def johnsonAdjacentChannel
    (n w p q L : ℕ)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  if target.val + 1 = source.val then
    (-1 : ℝ) • johnsonLowerChannel (p + q + source.val) f
  else if target = source then
    johnsonDiagonalChannelSign n w p q (p + q + source.val) •
      johnsonMiddleChannel (p + q + source.val) f
  else if source.val + 1 = target.val then
    (-1 : ℝ) • johnsonUpperChannel (p + q + source.val) f
  else
    0

/-- The johnson channel active used in the Johnson-code argument. -/
def johnsonChannelActive
    (p q L : ℕ) (target source : Index p q L) : Prop :=
  target.val + 1 = source.val ∨
    (target = source ∧ 0 < p + q + source.val) ∨
    source.val + 1 = target.val

theorem johnsonSourceChannelCoefficient_eq_zero_of_not_active
    {n w p q L : ℕ}
    (source target : Index p q L)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    johnsonSourceChannelCoefficient n w p q L source target = 0 := by
  classical
  have hdown : target.val + 1 ≠ source.val := by
    intro h
    exact hinactive (Or.inl h)
  have hup : source.val + 1 ≠ target.val := by
    intro h
    exact hinactive (Or.inr (Or.inr h))
  by_cases heq : source = target
  · subst target
    have hzero : p + q + source.val = 0 := by
      by_contra hnonzero
      apply hinactive
      exact Or.inr
        (Or.inl ⟨rfl, Nat.pos_of_ne_zero hnonzero⟩)
    simp only [johnsonSourceChannelCoefficient, matrix, johnsonJacobiMatrix, ↓reduceIte,
      johnsonHattedDiagonal, hzero, zero_mul, zero_div]
  · simp only [johnsonSourceChannelCoefficient, matrix, johnsonJacobiMatrix, heq, ↓reduceIte, hup,
      hdown, zero_mul, zero_div]

theorem johnsonZero_isHarmonic (n j : ℕ) :
    MetricCodes.Boolean.IsHarmonic j
      (0 : MetricCodes.Boolean.Function n) := by
  refine ⟨?_, ?_⟩
  · intro S _
    rfl
  · have hzero :
        MetricCodes.Boolean.lower (0 : MetricCodes.Boolean.Function n) = 0 := by
      change MetricCodes.Boolean.lowerLinear n
        (0 : MetricCodes.Boolean.Function n) = 0
      exact map_zero (MetricCodes.Boolean.lowerLinear n)
    intro S
    exact congrFun hzero S

theorem johnsonMiddleChannel_zero_degree {n : ℕ}
    (f : MetricCodes.Boolean.Function n) :
    johnsonMiddleChannel 0 f = 0 := by
  funext a
  simp only [johnsonMiddleChannel, johnsonMiddleScale, CharP.cast_eq_zero, zero_mul, sub_zero,
    zero_div, Real.sqrt_zero, inv_zero, zero_smul, Pi.zero_apply]

theorem johnsonAdjacentChannel_eq_zero_of_not_active
    {n w p q L : ℕ}
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    johnsonAdjacentChannel n w p q L target source f = 0 := by
  classical
  have hdown : target.val + 1 ≠ source.val := by
    intro h
    exact hinactive (Or.inl h)
  have hup : source.val + 1 ≠ target.val := by
    intro h
    exact hinactive (Or.inr (Or.inr h))
  by_cases heq : target = source
  · subst target
    have hzero : p + q + source.val = 0 := by
      by_contra hnonzero
      exact hinactive
        (Or.inr
          (Or.inl ⟨rfl, Nat.pos_of_ne_zero hnonzero⟩))
    simp only [johnsonAdjacentChannel, Nat.add_eq_left, one_ne_zero, ↓reduceIte, hzero,
      johnsonMiddleChannel_zero_degree, smul_zero]
  · simp only [johnsonAdjacentChannel, hdown, ↓reduceIte, heq, hup]

theorem johnsonCoordinateDot_pi_smul {n : ℕ}
    (c d : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot (c • f) (d • g) =
      (c * d) * MetricCodes.Boolean.coordinateDot f g := by
  change
    MetricCodes.Boolean.coordinateDot
      (fun a => c • f a)
      (fun a => d • g a) = _
  exact johnsonCoordinateDot_smul c d f g

theorem johnsonAdjacentChannel_isHarmonic
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic
      (p + q + target.val)
      (johnsonAdjacentChannel n w p q L target source f a) := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · have hdegree :
        p + q + source.val = (p + q + target.val) + 1 := by
      omega
    have hf' :
        MetricCodes.Boolean.IsHarmonic
          ((p + q + target.val) + 1) f := by
      simpa only [hdegree] using hf
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte,
      Pi.smul_apply]
    rw [hdegree]
    exact johnsonHarmonic_smul
      (johnsonLowerChannel ((p + q + target.val) + 1) f a)
      (johnsonLowerChannel_isHarmonic f hf' a)
      (-1 : ℝ)
  · by_cases hdiag : target = source
    · subst source
      have hdegree := h.window_degree_le_weight target
      have hhalf : 2 * (p + q + target.val) < n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, ↓reduceIte,
        Pi.smul_apply]
      exact johnsonHarmonic_smul
        (johnsonMiddleChannel (p + q + target.val) f a)
        (johnsonMiddleChannel_isHarmonic f hf hhalf a)
        (johnsonDiagonalChannelSign
          n w p q (p + q + target.val))
    · by_cases hup : source.val + 1 = target.val
      · have hdegree :
            (p + q + source.val) + 1 =
              p + q + target.val := by
          omega
        have hhalf := h.window_degree_half target
        have hhalf' :
            2 * ((p + q + source.val) + 1) ≤ n := by
          omega
        simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte, Pi.smul_apply]
        rw [← hdegree]
        exact johnsonHarmonic_smul
          (johnsonUpperChannel (p + q + source.val) f a)
          (johnsonUpperChannel_isHarmonic f hf hhalf' a)
          (-1 : ℝ)
      · simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte, Pi.zero_apply]
        exact johnsonZero_isHarmonic n (p + q + target.val)

theorem johnsonAdjacentChannel_isometry
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hactive : johnsonChannelActive p q L target source)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (hg : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) g) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAdjacentChannel n w p q L target source g) =
      MetricCodes.Boolean.dot f g := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    rw [johnsonCoordinateDot_pi_smul,
      johnsonLowerChannel_isometry f g hf (by omega)]
    norm_num
  · by_cases hdiag : target = source
    · subst target
      have hj : 0 < p + q + source.val := by
        rcases hactive with hfirst | hmiddle | hlast
        · omega
        · exact hmiddle.2
        · omega
      have hdegree := h.window_degree_le_weight source
      have hhalf : 2 * (p + q + source.val) < n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
      rw [johnsonCoordinateDot_pi_smul,
        johnsonMiddleChannel_isometry f g hf hg hj hhalf,
        ← pow_two,
        johnsonDiagonalChannelSign_sq,
        one_mul]
    · have hup : source.val + 1 = target.val := by
        rcases hactive with hfirst | hmiddle | hlast
        · exact False.elim (hdown hfirst)
        · exact False.elim (hdiag hmiddle.1)
        · exact hlast
      have htarget := h.window_degree_half target
      have hhalf :
          2 * ((p + q + source.val) + 1) ≤ n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
        ↓reduceIte]
      rw [johnsonCoordinateDot_pi_smul,
        johnsonUpperChannel_isometry f g hf hg hhalf]
      norm_num

theorem johnsonAdjacentChannel_orthogonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source other : Index p q L)
    (hne : source ≠ other)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (hg : MetricCodes.Boolean.IsHarmonic
      (p + q + other.val) g) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAdjacentChannel n w p q L target other g) = 0 := by
  classical
  by_cases hs : johnsonChannelActive p q L target source
  swap
  · rw [johnsonAdjacentChannel_eq_zero_of_not_active
      target source f hs]
    simp only [Boolean.coordinateDot, Boolean.dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  by_cases ho : johnsonChannelActive p q L target other
  swap
  · rw [johnsonAdjacentChannel_eq_zero_of_not_active
      target other g ho]
    simp only [Boolean.coordinateDot, Boolean.dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rcases hs with hsdown | hsdiag | hsup
  · rcases ho with hodown | hodiag | houp
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · rcases hodiag with ⟨hother, _⟩
      subst other
      have hnotdown : target.val + 1 ≠ target.val := by omega
      have hsource_val_ne : source.val ≠ target.val := by omega
      have hdegree :
          p + q + source.val = (p + q + target.val) + 1 := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + target.val) + 1) f := by
        simpa only [hdegree] using hf
      simp only [johnsonAdjacentChannel, hsdown,         hsource_val_ne,
        ↓reduceIte]
      rw [hdegree, johnsonCoordinateDot_pi_smul,
        johnsonLowerChannel_orthogonal_middleChannel f g hf']
      ring
    · have hsource_degree :
          p + q + source.val = (p + q + other.val) + 2 := by
        omega
      have hother_notdown : target.val + 1 ≠ other.val := by
        omega
      have hother_notdiag : target ≠ other := by
        intro heq
        subst other
        omega
      have hsource_other_val_ne : source.val ≠ other.val := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + other.val) + 2) f := by
        simpa only [hsource_degree] using hf
      simp only [johnsonAdjacentChannel, hsdown,
        hother_notdiag, houp,
        hsource_other_val_ne, ↓reduceIte]
      rw [hsource_degree, johnsonCoordinateDot_pi_smul,
        johnsonLowerChannel_orthogonal_upperChannel f g hf']
      ring
  · rcases hsdiag with ⟨hsource, _⟩
    subst source
    rcases ho with hodown | hodiag | houp
    · have hnotdown : target.val + 1 ≠ target.val := by omega
      have hother_val_ne : other.val ≠ target.val := by omega
      have hother_degree :
          p + q + other.val = (p + q + target.val) + 1 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + target.val) + 1) g := by
        simpa only [hother_degree] using hg
      simp only [johnsonAdjacentChannel,         hodown, hother_val_ne, ↓reduceIte]
      rw [hother_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonLowerChannel_orthogonal_middleChannel g f hg']
      ring
    · exfalso
      apply hne
      exact hodiag.1
    · have hnotdown : target.val + 1 ≠ target.val := by omega
      have hother_notdown : target.val + 1 ≠ other.val := by
        omega
      have hother_notdiag : target ≠ other := by
        intro heq
        subst other
        omega
      have htarget_degree :
          p + q + target.val = (p + q + other.val) + 1 := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + other.val) + 1) f := by
        simpa only [htarget_degree] using hf
      have hhalf :
          2 * ((p + q + other.val) + 1) < n := by
        have hbound := h.window_degree_le_weight target
        omega
      simp only [johnsonAdjacentChannel, hnotdown,
        hother_notdown, hother_notdiag, houp, ↓reduceIte]
      rw [htarget_degree, johnsonCoordinateDot_pi_smul,
        johnsonMiddleChannel_orthogonal_upperChannel
          f g hf' hg hhalf]
      ring
  · rcases ho with hodown | hodiag | houp
    · have hsource_notdown : target.val + 1 ≠ source.val := by
        omega
      have hsource_notdiag : target ≠ source := by
        intro heq
        subst source
        omega
      have hother_source_val_ne : other.val ≠ source.val := by
        omega
      have hother_degree :
          p + q + other.val = (p + q + source.val) + 2 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + source.val) + 2) g := by
        simpa only [hother_degree] using hg
      simp only [johnsonAdjacentChannel,         hsource_notdiag, hsup, hodown,
        hother_source_val_ne, ↓reduceIte]
      rw [hother_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonLowerChannel_orthogonal_upperChannel g f hg']
      ring
    · rcases hodiag with ⟨hother, _⟩
      subst other
      have hsource_notdown : target.val + 1 ≠ source.val := by
        omega
      have hsource_notdiag : target ≠ source := by
        intro heq
        subst source
        omega
      have hnotdown : target.val + 1 ≠ target.val := by omega
      have htarget_degree :
          p + q + target.val = (p + q + source.val) + 1 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + source.val) + 1) g := by
        simpa only [htarget_degree] using hg
      have hhalf :
          2 * ((p + q + source.val) + 1) < n := by
        have hbound := h.window_degree_le_weight target
        omega
      simp only [johnsonAdjacentChannel, hsource_notdown,
        hsource_notdiag, hsup, hnotdown, ↓reduceIte]
      rw [htarget_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonMiddleChannel_orthogonal_upperChannel
          g f hg' hf hhalf]
      ring
    · exfalso
      apply hne
      apply Fin.ext
      omega

/-- The johnson axis tensor used in the Johnson-code argument. -/
def johnsonAxisTensor {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a => (geometricAxis x a) • f

private def johnsonAxisRaise {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a * MetricCodes.Boolean.raiseAt a f S

private def johnsonAxisLower {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a * MetricCodes.Boolean.lowerAt a f S

private def johnsonAxisMembership {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a *
      MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S

theorem sum_geometricAxis {n w : ℕ}
    (hn : 0 < n) (x : JohnsonSphere n w) :
    (∑ a : Fin n, geometricAxis x a) = 0 := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hweight : MetricCodes.binaryWeight (x : BinaryWord n) = w :=
    x.property
  change
    (∑ a : Fin n,
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (coordinateIndicator (x : BinaryWord n) a -
            (w : ℝ) / (n : ℝ))) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_coordinateIndicator, hweight]
  simp only [Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn']
  ring

theorem johnsonDot_axisRaise {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisRaise x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisRaise
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonDot_axisLower {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisLower x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.lowerAt a g) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisLower
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonDot_axisMembership {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisMembership x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisMembership
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonLowerChannel_axis_inner {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.coordinateDot (johnsonLowerChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (j : ℝ))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisRaise x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonLowerChannel
    MetricCodes.Boolean.deleteChannel johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [MetricCodes.Boolean.dot_lowerAt_eq_raiseAt]
  rw [johnsonDot_axisRaise, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonUpperRaw_dot_harmonic_right {n j k : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) (a : Fin n) :
    MetricCodes.Boolean.dot (johnsonUpperRaw j a f) g =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f) g := by
  simp only [johnsonUpperRaw,
    johnsonBooleanDot_sub_left,
    johnsonBooleanDot_add_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [johnsonDotRaise_harmonic_right f g hg,
    johnsonDotRaise_harmonic_right
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g hg,
    johnsonDotRaise_harmonic_right
      (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) g hg]
  ring

theorem johnsonUpperChannel_axis_inner {n w j k : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) :
    MetricCodes.Boolean.coordinateDot (johnsonUpperChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisLower x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonUpperChannel
    johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [johnsonUpperRaw_dot_harmonic_right f g hg,
    MetricCodes.Boolean.dot_raiseAt_eq_lowerAt]
  rw [johnsonDot_axisLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonMiddleRaw_dot_harmonic_right {n j k : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) (a : Fin n) :
    MetricCodes.Boolean.dot (johnsonMiddleRaw j a f) g =
      MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
        ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g := by
  simp only [johnsonMiddleRaw,
    johnsonBooleanDot_sub_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a f) g hg,
    MetricCodes.Boolean.dot_raiseAt_eq_lowerAt,
    MetricCodes.Boolean.dot_lowerAt_eq_raiseAt]
  ring

theorem johnsonMiddleChannel_axis_inner {n w j k : ℕ}
    (hn : 0 < n) (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) :
    MetricCodes.Boolean.coordinateDot (johnsonMiddleChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisMembership x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonMiddleChannel
    johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [johnsonMiddleRaw_dot_harmonic_right f g hg]
  rw [johnsonDot_axisMembership]
  have hcenter := sum_geometricAxis hn x
  calc
    (∑ a : Fin n,
      geometricAxis x a *
        ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
            ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g))) =
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        (∑ a : Fin n,
          (geometricAxis x a *
            MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
            ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g *
              geometricAxis x a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        ((∑ a : Fin n,
          geometricAxis x a *
            MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) -
          ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g *
            (∑ a : Fin n, geometricAxis x a)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hcenter]; ring

theorem sum_coordinateIndicator_on_subset {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    (∑ a : Fin n,
      if a ∈ S then coordinateIndicator (x : BinaryWord n) a else 0) =
      (((coordinateSplitEquiv x S).1).card : ℝ) := by
  classical
  calc
    (∑ a : Fin n,
      if a ∈ S then coordinateIndicator (x : BinaryWord n) a else 0) =
      ∑ a : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x a ∈ S then
          coordinateIndicator (x : BinaryWord n)
            (coordinateSumEquiv x a)
        else 0 := by
          exact ((coordinateSumEquiv x).sum_comp
            (fun a : Fin n =>
              if a ∈ S then
                coordinateIndicator (x : BinaryWord n) a
              else 0)).symm
    _ = ∑ a : SupportCoordinates x,
          if a ∈ (coordinateSplitEquiv x S).1 then (1 : ℝ)
          else 0 := by
          rw [Fintype.sum_sum_type]
          have hsupport (a : SupportCoordinates x) :
              coordinateIndicator (x : BinaryWord n)
                (a : Fin n) = 1 := by
            simp only [coordinateIndicator, a.property, ↓reduceIte]
          have hcomplement (a : ComplementCoordinates x) :
              coordinateIndicator (x : BinaryWord n)
                (a : Fin n) = 0 := by
            have ha :
                (a : Fin n) ∉
                  MetricCodes.wordSupport (x : BinaryWord n) := by
              exact (Finset.mem_sdiff.mp a.property).2
            simp only [coordinateIndicator, ha, ↓reduceIte]
          have hinl (i : SupportCoordinates x) :
              coordinateSumEquiv x (Sum.inl i) = (i : Fin n) := rfl
          have hinr (i : ComplementCoordinates x) :
              coordinateSumEquiv x (Sum.inr i) = (i : Fin n) := rfl
          simp_rw [hinl, hinr, hsupport, hcomplement]
          simp only [ite_self, Finset.sum_const_zero, add_zero]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : (a : Fin n) ∈ S
          · have ha' : a ∈ (coordinateSplitEquiv x S).1 :=
              (coordinateSplitEquiv_mem_support x a S).mpr ha
            simp only [ha, ↓reduceIte, ha']
          · have ha' : a ∉ (coordinateSplitEquiv x S).1 := by
              intro hmem
              exact ha
                ((coordinateSplitEquiv_mem_support x a S).mp hmem)
            simp only [ha, ↓reduceIte, ha']
    _ = (((coordinateSplitEquiv x S).1).card : ℝ) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem sum_geometricAxis_on_subset {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    (∑ a : Fin n,
      if a ∈ S then geometricAxis x a else 0) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          ((((coordinateSplitEquiv x S).1).card : ℝ) -
            (w : ℝ) / (n : ℝ) * (S.card : ℝ)) := by
  classical
  change
    (∑ a : Fin n,
      if a ∈ S then
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (coordinateIndicator (x : BinaryWord n) a -
              (w : ℝ) / (n : ℝ))
      else 0) = _
  calc
    (∑ a : Fin n,
      if a ∈ S then
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (coordinateIndicator (x : BinaryWord n) a -
              (w : ℝ) / (n : ℝ))
      else 0) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ a : Fin n,
          if a ∈ S then coordinateIndicator (x : BinaryWord n) a
          else 0) -
          (∑ a : Fin n,
            if a ∈ S then (w : ℝ) / (n : ℝ) else 0)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S <;> simp [ha]; ring
    _ = _ := by
      rw [sum_coordinateIndicator_on_subset x S,
        MetricCodes.Boolean.sum_mem_indicator]
      ring

theorem johnsonAxisMembership_apply {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n)
    (S : Finset (Fin n)) :
    johnsonAxisMembership x f S =
      (∑ a : Fin n,
        if a ∈ S then geometricAxis x a else 0) * f S := by
  classical
  unfold johnsonAxisMembership
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [MetricCodes.Boolean.raiseAt_lowerAt_self]
  by_cases ha : a ∈ S <;> simp [ha]

theorem johnsonAxisMembership_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    johnsonAxisMembership x (splitTensor x hp hq a r s) =
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p + r : ℕ) : ℝ) -
          (w : ℝ) / (n : ℝ) *
            (((p + r) + (q + s) : ℕ) : ℝ))) •
        splitTensor x hp hq a r s := by
  classical
  funext S
  rw [johnsonAxisMembership_apply,
    sum_geometricAxis_on_subset]
  by_cases hsupport :
      ((coordinateSplitEquiv x S).1).card = p + r
  swap
  · have hzero : splitTensor x hp hq a r s S = 0 := by
      unfold splitTensor
      rw [supportRaisedFunction_eq_zero_of_card_ne
        x hp a.1 r (coordinateSplitEquiv x S).1 hsupport,
        zero_mul]
    simp only [Nat.cast_nonneg, Real.sqrt_div, Real.sqrt_mul, hzero, mul_zero, Nat.cast_add,
      Pi.smul_apply, smul_eq_mul]
  by_cases hcomplement :
      ((coordinateSplitEquiv x S).2).card = q + s
  swap
  · have hzero : splitTensor x hp hq a r s S = 0 := by
      unfold splitTensor
      rw [complementRaisedFunction_eq_zero_of_card_ne
        x hq a.2 s (coordinateSplitEquiv x S).2 hcomplement,
        mul_zero]
    simp only [Nat.cast_nonneg, Real.sqrt_div, Real.sqrt_mul, hzero, mul_zero, Nat.cast_add,
      Pi.smul_apply, smul_eq_mul]
  have hcard : S.card = (p + r) + (q + s) := by
    have hsplit := coordinateSplitEquiv_card x S
    omega
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsupport, hcard]

theorem johnsonAxisMembership_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisMembership x (c • f) =
      c • johnsonAxisMembership x f := by
  classical
  funext S
  simp only [johnsonAxisMembership, Pi.smul_apply, smul_eq_mul,
    MetricCodes.Boolean.raiseAt, MetricCodes.Boolean.lowerAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]; ring

theorem johnsonDot_fintype_weighted_sum_right
    {n : ℕ} {ι : Type*} [Fintype ι]
    (f : MetricCodes.Boolean.Function n)
    (c : ι → ℝ)
    (g : ι → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f
        (fun S => ∑ i : ι, c i * g i S) =
      ∑ i : ι, c i * MetricCodes.Boolean.dot f (g i) := by
  classical
  unfold MetricCodes.Boolean.dot
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonAxisMembership_coupledTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    johnsonAxisMembership x (coupledTensor x hp hq a t) =
      fun S =>
        ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (Real.sqrt ((n : ℝ) /
              ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
                (((p + r.val : ℕ) : ℝ) -
                  (w : ℝ) / (n : ℝ) *
                    ((p + q + t : ℕ) : ℝ))) *
            splitTensor x hp hq a r.val (t - r.val) S := by
  classical
  funext S
  rw [johnsonAxisMembership_apply]
  change
    (∑ b : Fin n,
      if b ∈ S then geometricAxis x b else 0) *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hdegree :
      (p + r.val) + (q + (t - r.val)) = p + q + t := by
    omega
  have hsplit := congrFun
    (johnsonAxisMembership_splitTensor
      x hp hq a r.val (t - r.val)) S
  rw [johnsonAxisMembership_apply] at hsplit
  simp only [Pi.smul_apply, smul_eq_mul, hdegree] at hsplit
  calc
    (∑ b : Fin n,
        if b ∈ S then geometricAxis x b else 0) *
        (clebschCoefficient w (n - w) p q t r.val *
          splitTensor x hp hq a r.val (t - r.val) S) =
      clebschCoefficient w (n - w) p q t r.val *
        ((∑ b : Fin n,
          if b ∈ S then geometricAxis x b else 0) *
          splitTensor x hp hq a r.val (t - r.val) S) := by
      ring
    _ = _ := by rw [hsplit]; ring

theorem johnsonAxisMembership_coupledHarmonic_dot
    {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (t : ℕ) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f
        (johnsonAxisMembership x
          (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (((p + r.val : ℕ) : ℝ) -
              (w : ℝ) / (n : ℝ) *
                ((p + q + t : ℕ) : ℝ)) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a r.val (t - r.val))) := by
  unfold coupledHarmonic
  rw [johnsonAxisMembership_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonAxisMembership_coupledTensor]
  rw [johnsonDot_fintype_weighted_sum_right]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem coordinateSplitEquiv_erase_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (S.erase (i : Fin n)) =
      (((coordinateSplitEquiv x S).1).erase i,
        (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toLeft) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toLeft).erase i
    ext j
    simp only [Equiv.finsetCongr_apply, Finset.map_erase, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_support, Finset.mem_toLeft, Finset.mem_erase, ne_eq, Sum.inl.injEq,
      Finset.mem_map_equiv, Equiv.symm_symm]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toRight) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    ext j
    simp only [Equiv.finsetCongr_apply, Finset.map_erase, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_support, Finset.mem_toRight, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, Finset.mem_map_equiv, Equiv.symm_symm, true_and]

theorem coordinateSplitEquiv_erase_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (S.erase (i : Fin n)) =
      ((coordinateSplitEquiv x S).1,
        ((coordinateSplitEquiv x S).2).erase i) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toLeft) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    ext j
    simp only [Equiv.finsetCongr_apply, Finset.map_erase, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_complement, Finset.mem_toLeft, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, Finset.mem_map_equiv, Equiv.symm_symm, true_and]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toRight) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toRight).erase i
    ext j
    simp only [Equiv.finsetCongr_apply, Finset.map_erase, Function.Embedding.coeFn_mk,
      coordinateSumEquiv_symm_complement, Finset.mem_toRight, Finset.mem_erase, ne_eq,
      Sum.inr.injEq, Finset.mem_map_equiv, Equiv.symm_symm]

private def coordinateRaise {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ i : α, if i ∈ S then f (S.erase i) else 0

theorem coordinateRaise_reindex
    {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ Fin m) (f : MetricCodes.Boolean.Function m)
    (S : Finset α) :
    coordinateRaise
        (fun T : Finset α => f (e.finsetCongr T)) S =
      MetricCodes.Boolean.raise f (e.finsetCongr S) := by
  classical
  unfold coordinateRaise MetricCodes.Boolean.raise MetricCodes.Boolean.raiseAt
  calc
    (∑ i : α,
      if i ∈ S then f (e.finsetCongr (S.erase i)) else 0) =
      ∑ i : α,
        if e i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase (e i))
        else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Equiv.finsetCongr_apply, Finset.map_erase, Function.Embedding.coeFn_mk,
        Finset.mem_map_mk]
    _ = ∑ i : Fin m,
        if i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase i)
        else 0 := by
      exact e.sum_comp (fun i : Fin m =>
        if i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase i)
        else 0)

theorem supportRaisedFunction_raise {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hbound : 2 * p + (r + 1) ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateRaise (supportRaisedFunction x hp a r) S =
      Real.sqrt (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
        supportRaisedFunction x hp a (r + 1) S := by
  unfold supportRaisedFunction
  rw [coordinateRaise_reindex,
    MetricCodes.Boolean.raise_harmonicEmbedding
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a) r hbound]
  rfl

theorem complementRaisedFunction_raise {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hbound : 2 * q + (r + 1) ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateRaise (complementRaisedFunction x hq a r) S =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (r + 1)) *
        complementRaisedFunction x hq a (r + 1) S := by
  unfold complementRaisedFunction
  rw [coordinateRaise_reindex,
    MetricCodes.Boolean.raise_harmonicEmbedding
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
        r hbound]
  rfl

theorem raise_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) S =
      coordinateRaise (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 +
      supportRaisedFunction x hp a.1 r
          (coordinateSplitEquiv x S).1 *
        coordinateRaise (complementRaisedFunction x hq a.2 s)
          (coordinateSplitEquiv x S).2 := by
  classical
  calc
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) S =
      ∑ i : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x i ∈ S then
          splitTensor x hp hq a r s
            (S.erase (coordinateSumEquiv x i))
        else 0 := by
      unfold MetricCodes.Boolean.raise MetricCodes.Boolean.raiseAt
      symm
      exact (coordinateSumEquiv x).sum_comp
        (fun i : Fin n =>
          if i ∈ S then
            splitTensor x hp hq a r s (S.erase i)
          else 0)
    _ =
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) +
      (∑ i : ComplementCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) := by
      rw [Fintype.sum_sum_type]
      simp only [Finset.univ_eq_attach, coordinateSumEquiv, complementNegEquiv, Equiv.trans_apply,
        Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inl, id_eq, Equiv.sumCompl_apply_inl,
        Sum.map_inr, Equiv.sumCompl_apply_inr, Equiv.subtypeEquivRight_apply_coe]
    _ = _ := by
      congr 1
      · calc
          (∑ i : SupportCoordinates x,
            if (i : Fin n) ∈ S then
              splitTensor x hp hq a r s (S.erase (i : Fin n))
            else 0) =
            ∑ i : SupportCoordinates x,
              (if i ∈ (coordinateSplitEquiv x S).1 then
                supportRaisedFunction x hp a.1 r
                  (((coordinateSplitEquiv x S).1).erase i)
              else 0) *
                complementRaisedFunction x hq a.2 s
                  (coordinateSplitEquiv x S).2 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
                (coordinateSplitEquiv_mem_support x i S).mpr hi
              simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_erase_support, hi']
            · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_support x i S).mp hmem)
              simp only [hi, ↓reduceIte, hi', zero_mul]
          _ = _ := by
            unfold coordinateRaise
            rw [Finset.sum_mul]
      · calc
          (∑ i : ComplementCoordinates x,
            if (i : Fin n) ∈ S then
              splitTensor x hp hq a r s (S.erase (i : Fin n))
            else 0) =
            ∑ i : ComplementCoordinates x,
              supportRaisedFunction x hp a.1 r
                (coordinateSplitEquiv x S).1 *
              (if i ∈ (coordinateSplitEquiv x S).2 then
                complementRaisedFunction x hq a.2 s
                  (((coordinateSplitEquiv x S).2).erase i)
              else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).2 :=
                (coordinateSplitEquiv_mem_complement x i S).mpr hi
              simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_erase_complement, hi']
            · have hi' : i ∉ (coordinateSplitEquiv x S).2 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_complement x i S).mp hmem)
              simp only [hi, ↓reduceIte, hi', mul_zero]
          _ = _ := by
            unfold coordinateRaise
            rw [Finset.mul_sum]

theorem raise_splitTensor_eq {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (hcomplement : 2 * q + (s + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
        splitTensor x hp hq a (r + 1) s +
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (s + 1)) •
        splitTensor x hp hq a r (s + 1) := by
  funext S
  rw [raise_splitTensor,
    supportRaisedFunction_raise x hp hsupport,
    complementRaisedFunction_raise x hq hcomplement]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    splitTensor]
  ring

theorem johnsonHarmonic_dot_splitTensor_succ_mul
    {n w p q t r : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f)
    (hr : r < t) :
    Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
      MetricCodes.Boolean.dot f
        (splitTensor x hp hq a (r + 1) (t - (r + 1))) =
      -Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t - r)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a r (t - r)) := by
  have hsupport : 2 * p + (r + 1) ≤ w := by omega
  have hresidual : (t - (r + 1)) + 1 = t - r := by omega
  have hcomplement :
      2 * q + ((t - (r + 1)) + 1) ≤ n - w := by
    omega
  have hzero := johnsonDotHarmonicRaise f
    (splitTensor x hp hq a r (t - (r + 1))) hf
  rw [raise_splitTensor_eq x hp hq hsupport hcomplement a,
    MetricCodes.Boolean.dot_add_right,
    MetricCodes.Boolean.dot_smul_right,
    MetricCodes.Boolean.dot_smul_right,
    hresidual] at hzero
  linarith

theorem johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f)
    (r : ℕ) (hr : r ≤ t) :
    MetricCodes.Boolean.dot f
        (splitTensor x hp hq a r (t - r)) =
      clebschCoefficient w (n - w) p q t r *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  induction r with
  | zero =>
      simp only [tsub_zero, clebschCoefficient, one_mul]
  | succ r ihr =>
      have hr' : r < t := by omega
      have hbound : 2 * p + (r + 1) ≤ w := by omega
      have hsqrt :
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) ≠ 0 := by
        exact (Real.sqrt_pos.mpr
          (MetricCodes.Boolean.harmonicCoefficient_pos
            (Nat.succ_pos r) hbound)).ne'
      have hrec := johnsonHarmonic_dot_splitTensor_succ_mul
        x hp hq htsupport htcomplement a f hf hr'
      rw [ihr (by omega)] at hrec
      have hclebsch := clebschCoefficient_succ_mul
        (w := w) (N := n - w) (p := p) (q := q)
        (t := t) (r := r) hbound
      apply (mul_left_cancel₀ hsqrt)
      calc
        Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a (r + 1) (t - (r + 1))) =
          -Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t - r)) *
              (clebschCoefficient w (n - w) p q t r *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t)) := hrec
        _ = (Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
              clebschCoefficient w (n - w) p q t (r + 1)) *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t) := by
              rw [mul_comm
                (Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)))
                (clebschCoefficient w (n - w) p q t (r + 1)),
                hclebsch]
              ring
        _ = Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
              (clebschCoefficient w (n - w) p q t (r + 1) *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t)) := by
              ring

theorem johnsonHarmonic_dot_coupledHarmonic
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) =
      Real.sqrt (clebschNormSq w (n - w) p q t) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hsqrt : Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.dot_smul_right]
  change
    (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
      MetricCodes.Boolean.dot f
        (fun S => ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [johnsonDot_fintype_weighted_sum_right]
  simp_rw [johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    x hp hq htsupport htcomplement a f hf _
      (Nat.le_of_lt_succ (Fin.isLt _))]
  have hsq := Real.sq_sqrt hnorm.le
  have hscalar :
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        clebschNormSq w (n - w) p q t =
      Real.sqrt (clebschNormSq w (n - w) p q t) := by
    field_simp [hsqrt]
    nlinarith [hsq]
  calc
    (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (clebschCoefficient w (n - w) p q t r.val *
              MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (clebschNormSq w (n - w) p q t *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
      congr 1
      unfold clebschNormSq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [← mul_assoc, hscalar]

theorem sum_coordinateIndicator_mul_function {n w : ℕ}
    (x : JohnsonSphere n w) (F : Fin n → ℝ) :
    (∑ i : Fin n,
      coordinateIndicator (x : BinaryWord n) i * F i) =
      ∑ i : SupportCoordinates x, F (i : Fin n) := by
  classical
  calc
    (∑ i : Fin n,
      coordinateIndicator (x : BinaryWord n) i * F i) =
      ∑ i ∈ MetricCodes.wordSupport (x : BinaryWord n), F i := by
        calc
          (∑ i : Fin n,
            coordinateIndicator (x : BinaryWord n) i * F i) =
            ∑ i : Fin n,
              if i ∈ MetricCodes.wordSupport (x : BinaryWord n) then
                F i
              else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ MetricCodes.wordSupport (x : BinaryWord n)
            <;> simp [coordinateIndicator, hi]
          _ = _ := by
            rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i : SupportCoordinates x, F (i : Fin n) := by
      exact Finset.sum_subtype
        (MetricCodes.wordSupport (x : BinaryWord n))
        (fun i => Iff.rfl) F

private def johnsonSupportRaise {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) : MetricCodes.Boolean.Function n :=
  fun S => ∑ i : SupportCoordinates x,
    MetricCodes.Boolean.raiseAt (i : Fin n) f S

private def johnsonSupportLower {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) : MetricCodes.Boolean.Function n :=
  fun S => ∑ i : SupportCoordinates x,
    MetricCodes.Boolean.lowerAt (i : Fin n) f S

theorem johnsonAxisRaise_eq_support {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisRaise x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          (johnsonSupportRaise x f -
            ((w : ℝ) / (n : ℝ)) • MetricCodes.Boolean.raise f) := by
  classical
  funext S
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.raiseAt i f S) = _
  have hsupport := sum_coordinateIndicator_mul_function x
    (fun i : Fin n => MetricCodes.Boolean.raiseAt i f S)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    johnsonSupportRaise, MetricCodes.Boolean.raise]
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.raiseAt i f S) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ i : Fin n,
          coordinateIndicator (x : BinaryWord n) i *
            MetricCodes.Boolean.raiseAt i f S) -
          (w : ℝ) / (n : ℝ) *
            (∑ i : Fin n, MetricCodes.Boolean.raiseAt i f S)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hsupport]

theorem johnsonAxisLower_eq_support {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisLower x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          (johnsonSupportLower x f -
            ((w : ℝ) / (n : ℝ)) • MetricCodes.Boolean.lower f) := by
  classical
  funext S
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.lowerAt i f S) = _
  have hsupport := sum_coordinateIndicator_mul_function x
    (fun i : Fin n => MetricCodes.Boolean.lowerAt i f S)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    johnsonSupportLower, MetricCodes.Boolean.lower]
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.lowerAt i f S) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ i : Fin n,
          coordinateIndicator (x : BinaryWord n) i *
            MetricCodes.Boolean.lowerAt i f S) -
          (w : ℝ) / (n : ℝ) *
            (∑ i : Fin n, MetricCodes.Boolean.lowerAt i f S)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hsupport]

theorem johnsonAxisRaise_dot_harmonic_left {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.dot f (johnsonAxisRaise x g) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          MetricCodes.Boolean.dot f (johnsonSupportRaise x g) := by
  rw [johnsonAxisRaise_eq_support,
    MetricCodes.Boolean.dot_smul_right,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_smul_right,
    johnsonDotHarmonicRaise f g hf]
  ring

theorem johnsonAxisLower_eq_support_of_harmonic {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    johnsonAxisLower x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          johnsonSupportLower x f := by
  rw [johnsonAxisLower_eq_support]
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  rw [hzero]
  simp only [Nat.cast_nonneg, Real.sqrt_div, Real.sqrt_mul, smul_zero, sub_zero]

theorem johnsonSupportRaise_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonSupportRaise x (c • f) = c • johnsonSupportRaise x f := by
  classical
  funext S
  unfold johnsonSupportRaise MetricCodes.Boolean.raiseAt
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Fin n) ∈ S <;> simp [hi]

theorem johnsonSupportLower_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonSupportLower x (c • f) = c • johnsonSupportLower x f := by
  classical
  funext S
  unfold johnsonSupportLower MetricCodes.Boolean.lowerAt
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Fin n) ∈ S <;> simp [hi]

theorem johnsonSupportRaise_fintype_weighted_sum
    {n w : ℕ} {ι : Type*} [Fintype ι]
    (x : JohnsonSphere n w)
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    johnsonSupportRaise x
        (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * johnsonSupportRaise x (f i) S := by
  classical
  funext S
  unfold johnsonSupportRaise MetricCodes.Boolean.raiseAt
  calc
    (∑ a : SupportCoordinates x,
      if (a : Fin n) ∈ S then
        ∑ i : ι, c i * f i (S.erase (a : Fin n))
      else 0) =
      ∑ a : SupportCoordinates x, ∑ i : ι,
        c i *
          (if (a : Fin n) ∈ S then f i (S.erase (a : Fin n))
           else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (a : Fin n) ∈ S <;> simp [ha]
    _ = ∑ i : ι, ∑ a : SupportCoordinates x,
        c i *
          (if (a : Fin n) ∈ S then f i (S.erase (a : Fin n))
           else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem johnsonSupportLower_fintype_weighted_sum
    {n w : ℕ} {ι : Type*} [Fintype ι]
    (x : JohnsonSphere n w)
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    johnsonSupportLower x
        (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * johnsonSupportLower x (f i) S := by
  classical
  funext S
  unfold johnsonSupportLower MetricCodes.Boolean.lowerAt
  calc
    (∑ a : SupportCoordinates x,
      if (a : Fin n) ∈ S then 0
      else ∑ i : ι, c i * f i (insert (a : Fin n) S)) =
      ∑ a : SupportCoordinates x, ∑ i : ι,
        c i *
          (if (a : Fin n) ∈ S then 0
           else f i (insert (a : Fin n) S)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (a : Fin n) ∈ S <;> simp [ha]
    _ = ∑ i : ι, ∑ a : SupportCoordinates x,
        c i *
          (if (a : Fin n) ∈ S then 0
           else f i (insert (a : Fin n) S)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem johnsonSupportRaise_splitTensor {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportRaise x (splitTensor x hp hq a r s) =
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
          splitTensor x hp hq a (r + 1) s := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then
        splitTensor x hp hq a r s (S.erase (i : Fin n))
      else 0) = _
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) =
      coordinateRaise (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateRaise
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_erase_support, hi']
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp only [hi, ↓reduceIte, hi', zero_mul]
  rw [hcomponent, supportRaisedFunction_raise x hp hsupport]
  simp only [mul_assoc, Pi.smul_apply, splitTensor, smul_eq_mul]

theorem johnsonSupportLower_splitTensor_succ {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (splitTensor x hp hq a (r + 1) s) =
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
          splitTensor x hp hq a r s := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then 0
      else splitTensor x hp hq a (r + 1) s
        (insert (i : Fin n) S)) = _
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a (r + 1) s
          (insert (i : Fin n) S)) =
      coordinateLower (supportRaisedFunction x hp a.1 (r + 1))
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateLower
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp only [hi, ↓reduceIte, hi', zero_mul]
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_insert_support, hi']
  rw [hcomponent, supportRaisedFunction_lower x hp hsupport]
  simp only [mul_assoc, Pi.smul_apply, splitTensor, smul_eq_mul]

theorem johnsonSupportLower_splitTensor_zero {n w p q s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (splitTensor x hp hq a 0 s) = 0 := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then 0
      else splitTensor x hp hq a 0 s
        (insert (i : Fin n) S)) = 0
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a 0 s
          (insert (i : Fin n) S)) =
      coordinateLower (supportRaisedFunction x hp a.1 0)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateLower
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp only [hi, ↓reduceIte, hi', zero_mul]
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp only [hi, ↓reduceIte, splitTensor, coordinateSplitEquiv_insert_support, hi']
  rw [hcomponent, supportRaisedFunction_lower_zero]
  ring

theorem johnsonSupportRaise_coupledTensor {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportRaise x (coupledTensor x hp hq a t) =
      fun S => ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a (r.val + 1) (t - r.val) S := by
  change
    johnsonSupportRaise x
        (fun S => ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [johnsonSupportRaise_fintype_weighted_sum]
  funext S
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hbound : 2 * p + (r.val + 1) ≤ w := by omega
  rw [johnsonSupportRaise_splitTensor x hp hq hbound a]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem johnsonSupportLower_coupledTensor_succ
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (coupledTensor x hp hq a (t + 1)) =
      fun S => ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1) (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a r.val (t - r.val) S := by
  change
    johnsonSupportLower x
        (fun S => ∑ r : Fin ((t + 1) + 1),
          clebschCoefficient w (n - w) p q (t + 1) r.val *
            splitTensor x hp hq a r.val ((t + 1) - r.val) S) = _
  rw [johnsonSupportLower_fintype_weighted_sum]
  funext S
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero,
    johnsonSupportLower_splitTensor_zero, Pi.zero_apply,
    mul_zero, zero_add, Fin.val_succ]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hbound : 2 * p + (r.val + 1) ≤ w := by omega
  have hresidual : (t + 1) - (r.val + 1) = t - r.val := by
    omega
  rw [hresidual,
    johnsonSupportLower_splitTensor_succ x hp hq hbound a]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem johnsonAxisRaise_coupledHarmonic_dot
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisRaise x (coupledHarmonic x hp hq a t)) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x hp hq a (t + 1)) := by
  classical
  have hnorm := clebschNormSq_pos w (n - w) p q (t + 1)
  have hsqrt :
      Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  have hbase := johnsonHarmonic_dot_coupledHarmonic
    x hp hq htsupport htcomplement a f hf
  rw [johnsonAxisRaise_dot_harmonic_left x f _ hf]
  change
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      MetricCodes.Boolean.dot f
        (johnsonSupportRaise x
          ((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ •
            coupledTensor x hp hq a t)) = _
  rw [johnsonSupportRaise_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonSupportRaise_coupledTensor x hp hq htsupport a,
    johnsonDot_fintype_weighted_sum_right]
  have hpair (r : Fin (t + 1)) :
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a (r.val + 1) (t - r.val)) =
        clebschCoefficient w (n - w) p q (t + 1) (r.val + 1) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1)) := by
    have hr : r.val ≤ t := by
      have hlt := r.isLt
      omega
    have hresidual :
        (t + 1) - (r.val + 1) = t - r.val := by omega
    simpa only [hresidual] using
      (johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient x hp hq htsupport htcomplement a f
        hf (r.val + 1) (by omega))
  simp_rw [hpair]
  rw [hbase]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          (clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
              MetricCodes.Boolean.dot f
                (splitTensor x hp hq a 0 (t + 1)))) =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1)) *
        MetricCodes.Boolean.dot f
          (splitTensor x hp hq a 0 (t + 1)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  have hcancel :
      (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) = 1 :=
    inv_mul_cancel₀ hsqrt
  calc
    Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      ((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        ((∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1)))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1))) := by
      calc
        _ = Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
          (∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q t r.val *
              Real.sqrt
                (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
              clebschCoefficient w (n - w) p q (t + 1)
                (r.val + 1)) *
          (((Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
              Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a 0 (t + 1))) := by
          rw [hcancel]
          ring
        _ = _ := by ring

theorem johnsonAxisLower_coupledHarmonic_dot
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisLower x
          (coupledHarmonic x hp hq a (t + 1))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  classical
  have hsupport : 2 * p + t ≤ w := by omega
  have hcomplement : 2 * q + t ≤ n - w := by omega
  have htarget := coupledHarmonic_isHarmonic
    x hp hq htsupport htcomplement a
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hsqrt : Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  have hbase := johnsonHarmonic_dot_coupledHarmonic
    x hp hq hsupport hcomplement a f hf
  rw [johnsonAxisLower_eq_support_of_harmonic x _ htarget,
    MetricCodes.Boolean.dot_smul_right]
  change
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      MetricCodes.Boolean.dot f
        (johnsonSupportLower x
          ((Real.sqrt
            (clebschNormSq w (n - w) p q (t + 1)))⁻¹ •
              coupledTensor x hp hq a (t + 1))) = _
  rw [johnsonSupportLower_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonSupportLower_coupledTensor_succ x hp hq htsupport a,
    johnsonDot_fintype_weighted_sum_right]
  have hpair (r : Fin (t + 1)) :
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) :=
    johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
      x hp hq hsupport hcomplement a f hf r.val
        (by have hr := r.isLt; omega)
  simp_rw [hpair]
  rw [hbase]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          clebschCoefficient w (n - w) p q t r.val) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  have hcancel :
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        Real.sqrt (clebschNormSq w (n - w) p q t) = 1 :=
    inv_mul_cancel₀ hsqrt
  calc
    Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      ((Real.sqrt
        (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        ((∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt
          (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
      calc
        _ = Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (Real.sqrt
            (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
          (∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q (t + 1)
                (r.val + 1) *
              Real.sqrt
                (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
              clebschCoefficient w (n - w) p q t r.val) *
          (((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
              Real.sqrt (clebschNormSq w (n - w) p q t)) *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
          rw [hcancel]
          ring
        _ = _ := by ring

end

section


open scoped BigOperators InnerProductSpace Matrix

theorem clebschCoefficient_sq_succ_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + (r + 1) ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    clebschCoefficient w N p q t (r + 1) ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p (r + 1) =
      clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
  have hfirst :
      0 < MetricCodes.Boolean.harmonicCoefficient w p (r + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos r) hsupport
  have hsecond :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
    by_cases hzero : t - r = 0
    · simp only [hzero, Boolean.harmonicCoefficient_zero, Std.le_refl]
    · exact
        (MetricCodes.Boolean.harmonicCoefficient_pos
          (Nat.pos_of_ne_zero hzero) (by omega)).le
  calc
    clebschCoefficient w N p q t (r + 1) ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p (r + 1) =
      (clebschCoefficient w N p q t (r + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hfirst.le]
    _ = (-clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) ^ 2 := by
        rw [clebschCoefficient_succ_mul hsupport]
    _ = clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
        rw [mul_pow, Real.sq_sqrt hsecond]
        ring

private def clebschFirstMoment (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    (r.val : ℝ) * clebschCoefficient w N p q t r.val ^ 2

private def clebschSecondMoment (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    (r.val : ℝ) ^ 2 * clebschCoefficient w N p q t r.val ^ 2

theorem clebschCoefficient_sq_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
  classical
  calc
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ∑ r : Fin t,
        clebschCoefficient w N p q t (r.val + 1) ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ,
          MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, zero_add]
    _ = ∑ r : Fin t,
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
        apply Finset.sum_congr rfl
        intro r _
        apply clebschCoefficient_sq_succ_mul
        · have hr := r.isLt
          omega
        · exact hcomplement
    _ = ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]

theorem clebsch_support_moment_expansion
    (w N p q t : ℕ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ((w : ℝ) - 2 * (p : ℝ) + 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t := by
  classical
  unfold clebschFirstMoment clebschSecondMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold MetricCodes.Boolean.harmonicCoefficient
  ring

theorem clebsch_complement_moment_expansion
    (w N p q t : ℕ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) =
      (t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t +
        (2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t := by
  classical
  unfold clebschNormSq clebschFirstMoment clebschSecondMoment
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  simp only [MetricCodes.Boolean.harmonicCoefficient, Nat.cast_sub hr]
  ring

theorem clebschFirstMoment_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t =
      (t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
        clebschNormSq w N p q t := by
  classical
  have hbalance :=
    clebschCoefficient_sq_harmonic_balance hsupport hcomplement
  have hsupport' := clebsch_support_moment_expansion w N p q t
  have hcomplement' := clebsch_complement_moment_expansion w N p q t
  calc
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t =
      (((w : ℝ) - 2 * (p : ℝ) + 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          ring
    _ = (∑ r : Fin (t + 1),
          clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p r.val) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          rw [hsupport']
    _ = (∑ r : Fin (t + 1),
          clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          rw [hbalance]
    _ = (t : ℝ) *
        ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t := by
          rw [hcomplement']
          ring

theorem clebschFirstMoment_eq
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    clebschFirstMoment w N p q t =
      ((t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
        clebschNormSq w N p q t) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) := by
  have hfirst :
      2 * (p : ℝ) + (t : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hsecond :
      2 * (q : ℝ) + (t : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcomplement
  have hdenominator :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) := by
    linarith only [hfirst, hsecond]
  apply (eq_div_iff hdenominator.ne').2
  calc
    clebschFirstMoment w N p q t *
        (((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) =
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t := by
          ring
    _ = (t : ℝ) *
        ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t :=
      clebschFirstMoment_mul hsupport hcomplement

theorem clebschCoefficient_sq_weighted_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (∑ r : Fin (t + 1),
      ((r.val : ℝ) - 1) *
        (clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p r.val)) =
      ∑ r : Fin (t + 1),
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
  classical
  calc
    (∑ r : Fin (t + 1),
      ((r.val : ℝ) - 1) *
        (clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p r.val)) =
      ∑ r : Fin t,
        (r.val : ℝ) *
          (clebschCoefficient w N p q t (r.val + 1) ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ,
          Nat.cast_zero, Nat.cast_add, Nat.cast_one,
          MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_sub_cancel_right, zero_add]
    _ = ∑ r : Fin t,
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [clebschCoefficient_sq_succ_mul
          (by have hr := r.isLt; omega) hcomplement]
    _ = ∑ r : Fin (t + 1),
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]

theorem clebschSecondMoment_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 3) *
        clebschSecondMoment w N p q t =
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) * (t : ℝ) -
        (t : ℝ) ^ 2 + (t : ℝ) + 1) *
        clebschFirstMoment w N p q t := by
  classical
  have hbalance :=
    clebschCoefficient_sq_weighted_harmonic_balance
      hsupport hcomplement
  apply sub_eq_zero.mp
  calc
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 3) *
        clebschSecondMoment w N p q t -
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) * (t : ℝ) -
        (t : ℝ) ^ 2 + (t : ℝ) + 1) *
        clebschFirstMoment w N p q t =
      ∑ r : Fin (t + 1),
        (((r.val : ℝ) - 1) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p r.val) -
          (r.val : ℝ) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient N q (t - r.val))) := by
        unfold clebschFirstMoment clebschSecondMoment
        rw [Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _
        have hr : r.val ≤ t := by
          have hlt := r.isLt
          omega
        simp only [MetricCodes.Boolean.harmonicCoefficient,
          Nat.cast_sub hr]
        ring
    _ = (∑ r : Fin (t + 1),
          ((r.val : ℝ) - 1) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient w p r.val)) -
        ∑ r : Fin (t + 1),
          (r.val : ℝ) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
      rw [hbalance]
      ring

theorem clebschCoefficient_cross_degree_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hr : r ≤ t) :
    clebschCoefficient w N p q (t + 1) r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r)) =
      clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
  have hall : ∀ s : ℕ, s ≤ t →
      clebschCoefficient w N p q (t + 1) s *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - s)) =
        clebschCoefficient w N p q t s *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hs
        cases s with
        | zero =>
            simp only [clebschCoefficient, tsub_zero, one_mul]
        | succ r =>
            have hbound : 2 * p + (r + 1) ≤ w := by
              omega
            have hpositive :
                0 < MetricCodes.Boolean.harmonicCoefficient
                  w p (r + 1) :=
              MetricCodes.Boolean.harmonicCoefficient_pos
                (Nat.succ_pos r) hbound
            have hnonzero :
                Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient
                    w p (r + 1)) ≠ 0 :=
              (Real.sqrt_pos.mpr hpositive).ne'
            have hprevious := ih r (by omega) (by omega)
            have hnew := clebschCoefficient_succ_mul
              (w := w) (N := N) (p := p) (q := q)
              (t := t + 1) (r := r) hbound
            have hold := clebschCoefficient_succ_mul
              (w := w) (N := N) (p := p) (q := q)
              (t := t) (r := r) hbound
            have hsub : t + 1 - (r + 1) = t - r := by
              omega
            apply (mul_right_inj' hnonzero).mp
            rw [hsub]
            calc
              Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
                (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) =
                (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) := by
                    ring
              _ = (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    ring
              _ = (-clebschCoefficient w N p q (t + 1) r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    rw [hnew]
              _ = -(clebschCoefficient w N p q (t + 1) r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    ring
              _ = -(clebschCoefficient w N p q t r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    rw [hprevious]
              _ = (clebschCoefficient w N p q t (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
                    rw [hold]
                    ring
              _ = (clebschCoefficient w N p q t (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) := by
                    ring
              _ = Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
                  (clebschCoefficient w N p q t (r + 1) *
                    Real.sqrt
                      (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) := by
                    ring
  exact hall r hr

theorem clebschCoefficient_sq_cross_degree_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N)
    (hr : r ≤ t) :
    clebschCoefficient w N p q (t + 1) r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) =
      clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
  have hleft :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) := by
    by_cases hzero : t + 1 - r = 0
    · simp only [hzero, Boolean.harmonicCoefficient_zero, Std.le_refl]
    · exact
        (MetricCodes.Boolean.harmonicCoefficient_pos
          (Nat.pos_of_ne_zero hzero) (by omega)).le
  have hright :
      0 < MetricCodes.Boolean.harmonicCoefficient N q (t + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  calc
    clebschCoefficient w N p q (t + 1) r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) =
      (clebschCoefficient w N p q (t + 1) r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hleft]
    _ = (clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) ^ 2 := by
        rw [clebschCoefficient_cross_degree_mul hsupport hr]
    _ = clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
        rw [mul_pow, Real.sq_sqrt hright.le]

theorem clebschNormSq_cross_degree_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    MetricCodes.Boolean.harmonicCoefficient N q (t + 1) *
        clebschNormSq w N p q t =
      ∑ r : Fin ((t + 1) + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
  classical
  calc
    MetricCodes.Boolean.harmonicCoefficient N q (t + 1) *
        clebschNormSq w N p q t =
      ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
        unfold clebschNormSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ = ∑ r : Fin (t + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
        apply Finset.sum_congr rfl
        intro r _
        symm
        apply clebschCoefficient_sq_cross_degree_mul
        · omega
        · exact hcomplement
        · have hr := r.isLt
          omega
    _ = ∑ r : Fin ((t + 1) + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
        symm
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]


theorem clebschNormSq_succ_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    clebschNormSq w N p q t *
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ))) =
      clebschNormSq w N p q (t + 1) *
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
          ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) := by
  let A : ℝ := (w : ℝ) - 2 * (p : ℝ)
  let B : ℝ := (N : ℝ) - 2 * (q : ℝ)
  let T : ℝ := ((t + 1 : ℕ) : ℝ)
  let M₀ : ℝ := clebschNormSq w N p q (t + 1)
  let M₁ : ℝ := clebschFirstMoment w N p q (t + 1)
  let M₂ : ℝ := clebschSecondMoment w N p q (t + 1)
  let Mprev : ℝ := clebschNormSq w N p q t
  have hfirst := clebschFirstMoment_mul hsupport hcomplement
  change (A + B - 2 * T + 2) * M₁ =
    T * (B - T + 1) * M₀ at hfirst
  have hsecond := clebschSecondMoment_mul hsupport hcomplement
  change (A + B - 2 * T + 3) * M₂ =
    (A + B * T - T ^ 2 + T + 1) * M₁ at hsecond
  have hcross :=
    clebschNormSq_cross_degree_harmonic_balance hsupport hcomplement
  rw [clebsch_complement_moment_expansion] at hcross
  change
    T * (B - T + 1) * Mprev =
      T * (B - T + 1) * M₀ +
        (2 * T - B - 1) * M₁ - M₂ at hcross
  have hpositive :
      0 < T * (B - T + 1) := by
    change 0 < MetricCodes.Boolean.harmonicCoefficient N q (t + 1)
    exact MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  have hcancel :
      T * (B - T + 1) *
        (Mprev * ((A + B - 2 * T + 3) *
          (A + B - 2 * T + 2)) -
          M₀ * ((A + B - T + 2) *
            (A - T + 1))) = 0 := by
    linear_combination
      ((A + B - 2 * T + 2) *
        (A + B - 2 * T + 3)) * hcross -
      (A + B - 2 * T + 2) * hsecond +
      ((2 * T - B - 1) *
        (A + B - 2 * T + 3) -
        (A + B * T - T ^ 2 + T + 1)) * hfirst
  have hidentity :
      Mprev * ((A + B - 2 * T + 3) *
        (A + B - 2 * T + 2)) =
      M₀ * ((A + B - T + 2) * (A - T + 1)) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hcancel).resolve_left hpositive.ne'
  dsimp [A, B, T, M₀, Mprev] at hidentity
  push_cast at hidentity
  nlinarith only [hidentity]

theorem clebschNormSq_div_succ
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    clebschNormSq w N p q t /
        clebschNormSq w N p q (t + 1) =
      ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
          ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) /
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ))) := by
  have hleft :
      (t : ℝ) + 1 ≤ (w : ℝ) - 2 * (p : ℝ) := by
    have hs : ((2 * p + (t + 1) : ℕ) : ℝ) ≤ (w : ℝ) := by
      exact_mod_cast hsupport
    push_cast at hs
    linarith
  have hright :
      (t : ℝ) + 1 ≤ (N : ℝ) - 2 * (q : ℝ) := by
    have hs : ((2 * q + (t + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hcomplement
    push_cast at hs
    linarith
  have hfactor :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ)) := by
    apply mul_pos <;> linarith
  have hnorm := (clebschNormSq_pos w N p q (t + 1)).ne'
  have hidentity := clebschNormSq_succ_mul hsupport hcomplement
  apply (div_eq_div_iff hnorm hfactor.ne').2
  nlinarith only [hidentity]

private theorem centeredExpectation_diagonal_algebra
    {N W P Q T : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hNW : N - W ≠ 0)
    (hgap : N - 2 * W ≠ 0)
    (hden : N - 2 * P - 2 * Q - 2 * T + 2 ≠ 0)
    (hJ : N / 2 - (P + Q + T) ≠ 0)
    (hJone : N / 2 - (P + Q + T) + 1 ≠ 0) :
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) -
        W / N * (P + Q + T) =
      ((N *
          (((N / 2 - W) / 2) *
            (((N - W) / 2 - Q) * (((N - W) / 2 - Q) + 1) -
              (W / 2 - P) * ((W / 2 - P) + 1)) /
            ((N / 2 - (P + Q + T)) *
              ((N / 2 - (P + Q + T)) + 1))) -
            (N / 2 - W) ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W))) := by
  let j : ℝ := P + Q + T
  let J : ℝ := N / 2 - j
  let M : ℝ := N / 2 - W
  let U : ℝ := (N - W) / 2 - Q
  let V : ℝ := W / 2 - P
  let Z : ℝ := U * (U + 1) - V * (V + 1)
  let d : ℝ := N - 2 * P - 2 * Q - 2 * T + 2
  have hd : d ≠ 0 := hden
  have hJ' : J ≠ 0 := by
    simpa only [ne_eq] using hJ
  have hJone' : J + 1 ≠ 0 := by
    simpa only [ne_eq] using hJone
  have hM : M ≠ 0 := by
    intro hzero
    apply hgap
    dsimp [M] at hzero
    linarith
  have hgap' : N - 2 * W = 2 * M := by
    dsimp [M]
    ring
  have hj' : N - 2 * (P + Q + T) = 2 * J := by
    dsimp [J, j]
    ring
  have hdenJ :
      2 * (J + 1) =
        N - 2 * P - 2 * Q - 2 * T + 2 := by
    dsimp [J, j]
    ring
  change
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) - W / N * j =
      ((N * ((M / 2) * Z / (J * (J + 1))) - M ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W)))
  calc
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) - W / N * j =
      Z / (2 * (J + 1)) - M * J / N := by
        rw [hdenJ]
        change P + T * (N - W - 2 * Q - T + 1) / d -
          W / N * j = Z / d - M * J / N
        field_simp [hN, hd]
        dsimp [d, Z, U, V, J, M, j]
        ring
    _ = ((N * ((M / 2) * Z / (J * (J + 1))) - M ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W))) := by
      rw [hgap', hj']
      field_simp [hN, hW, hNW, hM, hJ', hJone']

theorem clebschCenteredExpectation_eq_johnsonDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L) :
    (p : ℝ) +
        clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val -
        (w : ℝ) / (n : ℝ) *
          ((p + q + source.val : ℕ) : ℝ) =
      MetricCodes.johnsonDiagonal n w p q (p + q + source.val) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 *
            ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hNreal : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hjbound := h.window_degree_le_weight source
  have hjreal :
      2 * ((p + q + source.val : ℕ) : ℝ) < (n : ℝ) := by
    have hj : 2 * (p + q + source.val) < n := by omega
    exact_mod_cast hj
  have hwgap : 0 < (n : ℝ) - 2 * (w : ℝ) := by
    have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    push_cast at hs
    linarith
  have hjgap :
      0 < (n : ℝ) -
        2 * ((p + q + source.val : ℕ) : ℝ) := by
    linarith
  have hJ :
      0 < MetricCodes.johnsonJ n (p + q + source.val) := by
    unfold MetricCodes.johnsonJ
    linarith
  have hJone :
      0 < MetricCodes.johnsonJ n (p + q + source.val) + 1 := by
    linarith
  have hnorm :=
    (clebschNormSq_pos w (n - w) p q source.val).ne'
  have hleftreal :
      2 * (p : ℝ) + (source.val : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hrightreal :
      2 * (q : ℝ) + (source.val : ℝ) ≤
        ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcomplement
  have hden :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2) := by
    linarith
  have hden' :
      0 < 2 + (n : ℝ) - 2 * (p : ℝ) -
        2 * (source.val : ℝ) - 2 * (q : ℝ) := by
    have hsub : ((n - w : ℕ) : ℝ) = (n : ℝ) - (w : ℝ) := by
      rw [Nat.cast_sub h.weight_lt.le]
    rw [hsub] at hden
    linarith
  have hcompreal : 0 < (n : ℝ) - (w : ℝ) := by
    have hs : (w : ℝ) < (n : ℝ) := by
      exact_mod_cast h.weight_lt
    linarith
  have hexpect :
      clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val =
        ((source.val : ℝ) *
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
            (source.val : ℝ) + 1)) /
          (((w : ℝ) - 2 * (p : ℝ)) +
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
            2 * (source.val : ℝ) + 2) := by
    rw [clebschFirstMoment_eq hsupport hcomplement]
    field_simp [hnorm, hden.ne']
  rw [hexpect]
  have hden'' :
      (n : ℝ) - 2 * (p : ℝ) - 2 * (q : ℝ) -
        2 * (source.val : ℝ) + 2 ≠ 0 := by
    nlinarith [hden']
  have hJ' :
      (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) ≠ 0 := by
    have hj : 0 < (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) := by
      exact_mod_cast hJ
    exact hj.ne'
  have hJone' :
      (n : ℝ) / 2 -
          ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) + 1 ≠ 0 := by
    have hj : 0 < (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) + 1 := by
      exact_mod_cast hJone
    exact hj.ne'
  have halgebra := centeredExpectation_diagonal_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (P := (p : ℝ)) (Q := (q : ℝ))
    (T := (source.val : ℝ))
    hnreal.ne' hwreal.ne' hcompreal.ne'
    hwgap.ne' hden'' hJ' hJone'
  simp only [Nat.cast_add, Nat.cast_sub h.weight_lt.le] at halgebra ⊢
  unfold MetricCodes.johnsonDiagonal MetricCodes.johnsonMu
    MetricCodes.johnsonM MetricCodes.johnsonJ MetricCodes.johnsonJ1
    MetricCodes.johnsonJ2
  rw [Nat.cast_sub h.weight_lt.le]
  push_cast
  rw [show
    (w : ℝ) - 2 * (p : ℝ) +
        ((n : ℝ) - (w : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2 =
      (n : ℝ) - 2 * (p : ℝ) - 2 * (q : ℝ) -
        2 * (source.val : ℝ) + 2 by ring]
  exact halgebra

theorem clebschClosedCenteredExpectation_eq_johnsonDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L) :
    (((p : ℝ) - (w : ℝ) / (n : ℝ) *
        ((p + q + source.val : ℕ) : ℝ)) +
      ((source.val : ℝ) *
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
          (source.val : ℝ) + 1)) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
          2 * (source.val : ℝ) + 2)) =
      MetricCodes.johnsonDiagonal n w p q (p + q + source.val) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 *
            ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hleftreal :
      2 * (p : ℝ) + (source.val : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hrightreal :
      2 * (q : ℝ) + (source.val : ℝ) ≤
        ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcomplement
  have hden :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2) := by
    linarith
  have hnorm :=
    (clebschNormSq_pos w (n - w) p q source.val).ne'
  calc
    (((p : ℝ) - (w : ℝ) / (n : ℝ) *
        ((p + q + source.val : ℕ) : ℝ)) +
      ((source.val : ℝ) *
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
          (source.val : ℝ) + 1)) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
          2 * (source.val : ℝ) + 2)) =
      (p : ℝ) +
        clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val -
        (w : ℝ) / (n : ℝ) *
          ((p + q + source.val : ℕ) : ℝ) := by
        rw [clebschFirstMoment_eq hsupport hcomplement]
        field_simp [hnorm, hden.ne']; ring
    _ = _ := clebschCenteredExpectation_eq_johnsonDiagonal
      h hstrict source

private theorem middleNormalization_algebra
    {N W C j J M R : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hC : C ≠ 0)
    (hj : j ≠ 0) (hJ : J ≠ 0) (hJone : J + 1 ≠ 0)
    (hM : M ≠ 0) (hR : R ≠ 0) :
    (j * J * R / (N * (J + 1)))⁻¹ *
        (N / (W * C)) *
        (W * C * J / (N * M)) ^ 2 =
      (M ^ 2 * j * R /
        (W * C * J * (J + 1)))⁻¹ := by
  field_simp [hN, hW, hC, hj, hJ, hJone, hM, hR]

theorem johnsonMiddleNormalization_sq_eq_inv_zonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L)
    (hsource : 0 < p + q + source.val) :
    ((Real.sqrt
          (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
        Real.sqrt
          ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) -
            2 * ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))))) ^ 2 =
      (MetricCodes.johnsonZonalDiagonal
        n w (p + q + source.val))⁻¹ := by
  let j : ℕ := p + q + source.val
  have hjw : j ≤ w := h.window_degree_le_weight source
  have hjhalf : 2 * j < n := by omega
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hjreal : 0 < (j : ℝ) := by exact_mod_cast hsource
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    have hj' : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
      exact_mod_cast hjhalf
    linarith
  have hJone : 0 < MetricCodes.johnsonJ n j + 1 := by linarith
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    have hw' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    linarith
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    have hjn : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  have hmiddle := johnsonMiddleScale_pos hsource hjhalf
  have haxis : 0 ≤ (n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by positivity
  have hF :
      ((w : ℝ) * ((n - w : ℕ) : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))) =
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          MetricCodes.johnsonJ n j) /
          ((n : ℝ) * MetricCodes.johnsonM n w) := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    have hwgap : (n : ℝ) - 2 * (w : ℝ) ≠ 0 := by
      have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
        exact_mod_cast hstrict
      push_cast at hs
      linarith
    field_simp [hnreal.ne', hwgap]
  have hK :
      johnsonMiddleScale n j =
        (j : ℝ) * MetricCodes.johnsonJ n j *
          ((n : ℝ) - (j : ℝ) + 1) /
          ((n : ℝ) * (MetricCodes.johnsonJ n j + 1)) := by
    unfold johnsonMiddleScale johnsonHarmonicGap
      MetricCodes.johnsonJ
    field_simp [hnreal.ne', hJone.ne']
  change
    ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      (((w : ℝ) * ((n - w : ℕ) : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ))) /
        ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))))) ^ 2 =
      (MetricCodes.johnsonZonalDiagonal n w j)⁻¹
  rw [mul_pow, mul_pow, inv_pow,
    Real.sq_sqrt hmiddle.le, Real.sq_sqrt haxis,
    hF, hK, zonalDiagonal_eq h.weight_pos hstrict hjw]
  exact middleNormalization_algebra hnreal.ne' hwreal.ne'
    hcomp.ne' hjreal.ne' hJ.ne' hJone.ne' hM.ne'
    hlast.ne'

theorem johnsonMiddleSignedScalar_eq_sqrt_hattedDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L)
    (hsource : 0 < p + q + source.val) :
    johnsonDiagonalChannelSign n w p q (p + q + source.val) *
        ((Real.sqrt
            (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
          Real.sqrt
            ((n : ℝ) /
              ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (((p : ℝ) - (w : ℝ) / (n : ℝ) *
              ((p + q + source.val : ℕ) : ℝ)) +
            ((source.val : ℝ) *
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
                (source.val : ℝ) + 1)) /
              (((w : ℝ) - 2 * (p : ℝ)) +
                (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
                2 * (source.val : ℝ) + 2))) =
      Real.sqrt
        (MetricCodes.johnsonHattedDiagonal
          n w p q (p + q + source.val)) := by
  let j : ℕ := p + q + source.val
  let z : ℝ := MetricCodes.johnsonZonalDiagonal n w j
  let D : ℝ := MetricCodes.johnsonDiagonal n w p q j
  let F : ℝ :=
    ((w : ℝ) * ((n - w : ℕ) : ℝ) *
      ((n : ℝ) - 2 * (j : ℝ))) /
      ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))
  let S : ℝ :=
    (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
      Real.sqrt
        ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) * F
  have hjw : j ≤ w := h.window_degree_le_weight source
  have hjhalf : 2 * j < n := by omega
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hgapj : 0 < (n : ℝ) - 2 * (j : ℝ) := by
    have hs : ((2 * j : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hjhalf
    push_cast at hs
    linarith
  have hgapw : 0 < (n : ℝ) - 2 * (w : ℝ) := by
    have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    push_cast at hs
    linarith
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have hmiddle := johnsonMiddleScale_pos hsource hjhalf
  have haxis : 0 < (n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    positivity
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hz : 0 < z := by
    dsimp [z, j]
    exact zonalDiagonal_pos h.weight_pos hstrict
      hsource hjw
  have hnorm : S ^ 2 = z⁻¹ := by
    dsimp [S, F, z, j]
    exact johnsonMiddleNormalization_sq_eq_inv_zonal
      h hstrict source hsource
  have hsign :
      0 ≤ johnsonDiagonalChannelSign n w p q j * D := by
    unfold johnsonDiagonalChannelSign
    split_ifs with hD
    · simpa only [one_mul] using hD
    · have hnegative : D < 0 := by
        dsimp [D]
        exact lt_of_not_ge hD
      dsimp [D] at hnegative ⊢
      linarith
  have hleft :
      0 ≤ (johnsonDiagonalChannelSign n w p q j * D) * S :=
    mul_nonneg hsign hS.le
  have hrad : 0 ≤ D ^ 2 / z :=
    div_nonneg (sq_nonneg D) hz.le
  have hsquare :
      ((johnsonDiagonalChannelSign n w p q j * D) * S) ^ 2 =
        D ^ 2 / z := by
    rw [mul_pow, mul_pow,
      johnsonDiagonalChannelSign_sq, one_mul, hnorm]
    ring
  have hsqrt :
      (Real.sqrt (D ^ 2 / z)) ^ 2 = D ^ 2 / z :=
    Real.sq_sqrt hrad
  have heq :
      (johnsonDiagonalChannelSign n w p q j * D) * S =
        Real.sqrt (D ^ 2 / z) := by
    nlinarith [hsquare, hsqrt,
      Real.sqrt_nonneg (D ^ 2 / z)]
  rw [clebschClosedCenteredExpectation_eq_johnsonDiagonal
    h hstrict source]
  have hhatted :
      MetricCodes.johnsonHattedDiagonal n w p q j = D ^ 2 / z := by
    have hjne : j ≠ 0 := by
      dsimp [j]
      exact hsource.ne'
    simp only [johnsonHattedDiagonal, hjne, ↓reduceIte, D, z]
  change
    johnsonDiagonalChannelSign n w p q j *
      ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (D * F)) =
      Real.sqrt (MetricCodes.johnsonHattedDiagonal n w p q j)
  rw [hhatted]
  calc
    johnsonDiagonalChannelSign n w p q j *
        ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (D * F)) =
      (johnsonDiagonalChannelSign n w p q j * D) * S := by
        dsimp [S]
        ring
    _ = Real.sqrt (D ^ 2 / z) := heq

end

section


open scoped BigOperators

theorem booleanHarmonicDimension_mul_degreeComplement
    (n j : ℕ) (hhalf : 2 * j ≤ n) :
    (MetricCodes.booleanHarmonicDimension n j : ℝ) *
        ((n : ℝ) - (j : ℝ) + 1) =
      (n.choose j : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ) + 1) := by
  cases j with
  | zero =>
      simp only [booleanHarmonicDimension, Nat.cast_one, CharP.cast_eq_zero, sub_zero, one_mul,
        Nat.choose_zero_right, mul_zero]
  | succ k =>
      have hmono : n.choose k ≤ n.choose (k + 1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      have hk : k ≤ n := by omega
      have hchoose :
          (n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
            (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n k
      rw [Nat.cast_sub hk] at hchoose
      rw [MetricCodes.booleanHarmonicDimension_succ, Nat.cast_sub hmono]
      push_cast at hchoose ⊢
      nlinarith [hchoose]

theorem booleanHarmonicDimension_succ_div
    {n j : ℕ} (hhalf : 2 * (j + 1) ≤ n) :
    (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
        (MetricCodes.booleanHarmonicDimension n j : ℝ) =
      (((n : ℝ) - 2 * (j : ℝ) - 1) *
        ((n : ℝ) - (j : ℝ) + 1)) /
        (((j : ℝ) + 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
  have hjhalf : 2 * j ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hd : 0 < (MetricCodes.booleanHarmonicDimension n j : ℝ) := by
    exact_mod_cast booleanHarmonicDimension_pos hjhalf
  have hnext :=
    booleanHarmonicDimension_mul_degreeComplement n (j + 1) hhalf
  have hcurrent :=
    booleanHarmonicDimension_mul_degreeComplement n j hjhalf
  have hchoose :
      (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
        (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  rw [Nat.cast_sub hjn] at hchoose
  push_cast at hnext hchoose
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hgap : 0 < (n : ℝ) - 2 * (j : ℝ) + 1 := by
    have hh : (2 : ℝ) * (j : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hjhalf
    linarith
  have hnminus : 0 < (n : ℝ) - (j : ℝ) := by
    have hh : (j : ℝ) + 1 ≤ (n : ℝ) := by
      have hnat : j + 1 ≤ n := by omega
      exact_mod_cast hnat
    linarith
  have hnext' :
      (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          ((n : ℝ) - (j : ℝ)) =
        (n.choose (j + 1) : ℝ) *
          ((n : ℝ) - 2 * (j : ℝ) - 1) := by
    convert hnext using 1 <;> ring
  apply (div_eq_div_iff hd.ne' (mul_pos hjpos hgap).ne').mpr
  apply (mul_right_inj' hnminus.ne').mp
  calc
    ((n : ℝ) - (j : ℝ)) *
        ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1))) =
      ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
        ((n : ℝ) - (j : ℝ))) *
        (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        ring
    _ = ((n.choose (j + 1) : ℝ) *
          ((n : ℝ) - 2 * (j : ℝ) - 1)) *
        (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        rw [hnext']
    _ = ((n.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        ring
    _ = ((n.choose j : ℝ) * ((n : ℝ) - (j : ℝ))) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        rw [hchoose]
    _ = ((n.choose j : ℝ) * ((n : ℝ) - 2 * (j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - (j : ℝ))) := by
        ring
    _ = ((MetricCodes.booleanHarmonicDimension n j : ℝ) *
          ((n : ℝ) - (j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - (j : ℝ))) := by
        rw [hcurrent]
    _ = ((n : ℝ) - (j : ℝ)) *
          ((((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - (j : ℝ) + 1)) *
              (MetricCodes.booleanHarmonicDimension n j : ℝ)) := by
        ring

theorem booleanHarmonicDimension_succ_div_eq_upperScale
    {n j : ℕ} (hhalf : 2 * (j + 1) ≤ n) :
    (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
        (MetricCodes.booleanHarmonicDimension n j : ℝ) =
      johnsonUpperScale n j / ((j : ℝ) + 1) := by
  rw [booleanHarmonicDimension_succ_div hhalf]
  unfold johnsonUpperScale johnsonHarmonicGap
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hgap : (n : ℝ) - 2 * (j : ℝ) + 1 ≠ 0 := by
    have hcast : (2 : ℝ) * ((j : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast hhalf
    linarith
  field_simp [hj, hgap]

theorem clebschCenteredAxis_sum
    (w N p q t : ℕ) (c : ℝ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        (((p + r.val : ℕ) : ℝ) -
          c * ((p + q + t : ℕ) : ℝ))) =
      ((p : ℝ) - c * ((p + q + t : ℕ) : ℝ)) *
        clebschNormSq w N p q t +
      clebschFirstMoment w N p q t := by
  unfold clebschNormSq clebschFirstMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  push_cast
  ring

theorem clebschCenteredAxis_sum_eq
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N)
    (c : ℝ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        (((p + r.val : ℕ) : ℝ) -
          c * ((p + q + t : ℕ) : ℝ))) =
      clebschNormSq w N p q t *
        (((p : ℝ) - c * ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2)) := by
  rw [clebschCenteredAxis_sum,
    clebschFirstMoment_eq hsupport hcomplement]
  ring

theorem clebschSignedAdjacentCross_sum
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (_hcomplement : 2 * q + (t + 1) ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q (t + 1) (r.val + 1)) =
      -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschNormSq w N p q t := by
  unfold clebschNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hrbound : 2 * p + (r.val + 1) ≤ w := by omega
  have hrow := clebschCoefficient_succ_mul
    (w := w) (N := N) (p := p) (q := q)
    (t := t + 1) (r := r.val) hrbound
  have hcross := clebschCoefficient_cross_degree_mul
    (w := w) (N := N) (p := p) (q := q)
    (t := t) (r := r.val) (by omega) hr
  calc
    clebschCoefficient w N p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q (t + 1) (r.val + 1) =
      clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q (t + 1) (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1))) := by
        ring
    _ = clebschCoefficient w N p q t r.val *
        (-clebschCoefficient w N p q (t + 1) r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q
              (t + 1 - r.val))) := by
        rw [hrow]
    _ = -clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q (t + 1) r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q
              (t + 1 - r.val))) := by
        ring
    _ = -clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) := by
        rw [hcross]
    _ = -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschCoefficient w N p q t r.val ^ 2 := by
        ring

theorem johnsonAxisRaise_coupledHarmonic_dot_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisRaise x (coupledHarmonic x hp hq a t)) =
      -Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a (t + 1)) := by
  rw [johnsonAxisRaise_coupledHarmonic_dot
    x hp hq htsupport htcomplement a f hf,
    clebschSignedAdjacentCross_sum htsupport htcomplement]
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  have hroot := (Real.sqrt_pos.mpr hnorm).ne'
  have hroot' := (Real.sqrt_pos.mpr hnext).ne'
  field_simp [hroot, hroot']
  rw [Real.sq_sqrt hnorm.le]
  ring

theorem johnsonLowerChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (p + q + (t + 1)) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      -(Real.sqrt (((p + q + (t + 1) : ℕ) : ℝ)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a (t + 1)) := by
  rw [johnsonLowerChannel_axis_inner x f
    (coupledHarmonic x hp hq a t),
    johnsonAxisRaise_coupledHarmonic_dot_closed
      x hp hq htsupport htcomplement a f hf]
  ring

theorem clebschSignedAdjacentCross_sum_comm
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q (t + 1) (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q t r.val) =
      -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschNormSq w N p q t := by
  rw [← clebschSignedAdjacentCross_sum hsupport hcomplement]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem johnsonAxisLower_coupledHarmonic_dot_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisLower x (coupledHarmonic x hp hq a (t + 1))) =
      -Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonAxisLower_coupledHarmonic_dot
    x hp hq htsupport htcomplement a f hf,
    clebschSignedAdjacentCross_sum_comm htsupport htcomplement]
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  have hroot := (Real.sqrt_pos.mpr hnorm).ne'
  have hroot' := (Real.sqrt_pos.mpr hnext).ne'
  field_simp [hroot, hroot']
  rw [Real.sq_sqrt hnorm.le]
  ring

theorem johnsonUpperChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a (t + 1))) =
      -(Real.sqrt (johnsonUpperScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonUpperChannel_axis_inner x f
    (coupledHarmonic x hp hq a (t + 1))
    (coupledHarmonic_isHarmonic x hp hq
      htsupport htcomplement a),
    johnsonAxisLower_coupledHarmonic_dot_closed
      x hp hq htsupport htcomplement a f hf]
  ring

theorem coupledHarmonic_dot_of_split_proportional
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) =
      Real.sqrt (clebschNormSq w (n - w) p q t) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  have hpos := clebschNormSq_pos w (n - w) p q t
  have hroot := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare := Real.sq_sqrt hpos.le
  unfold coupledHarmonic coupledTensor
  rw [MetricCodes.Boolean.dot_smul_right,
    johnsonDot_fintype_weighted_sum_right]
  simp_rw [hpair]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
        clebschNormSq w (n - w) p q t *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    unfold clebschNormSq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  field_simp [hroot]
  rw [hsquare]

theorem johnsonAxisMembership_coupledHarmonic_dot_of_split_proportional
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.dot f
        (johnsonAxisMembership x (coupledHarmonic x hp hq a t)) =
      Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonAxisMembership_coupledHarmonic_dot x hp hq a t f,
    coupledHarmonic_dot_of_split_proportional x hp hq a f hpair]
  simp_rw [hpair]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (((p + r.val : ℕ) : ℝ) -
            (w : ℝ) / (n : ℝ) * ((p + q + t : ℕ) : ℝ)) *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val ^ 2 *
            (((p + r.val : ℕ) : ℝ) -
              (w : ℝ) / (n : ℝ) * ((p + q + t : ℕ) : ℝ))) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum, clebschCenteredAxis_sum_eq htsupport htcomplement]
  have hpos := clebschNormSq_pos w (n - w) p q t
  have hroot := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare := Real.sq_sqrt hpos.le
  field_simp [hroot]
  rw [hsquare]
  ring

theorem johnsonMiddleChannel_coupled_axis_inner_of_split_proportional
    {n w p q t : ℕ}
    (hn : 0 < n)
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (johnsonMiddleScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonMiddleChannel_axis_inner hn x f
    (coupledHarmonic x hp hq a t)
    (coupledHarmonic_isHarmonic x hp hq
      htsupport htcomplement a)]
  rw [johnsonAxisMembership_coupledHarmonic_dot_of_split_proportional
    x hp hq htsupport htcomplement a f hpair]
  ring

theorem johnsonMiddleChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (hn : 0 < n)
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (johnsonMiddleScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  apply johnsonMiddleChannel_coupled_axis_inner_of_split_proportional
    hn x hp hq htsupport htcomplement a f
  intro r
  exact johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    x hp hq htsupport htcomplement a f hf r.val
      (by have hr := r.isLt; omega)

theorem johnsonSourceChannelCoefficient_diagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L source source =
      MetricCodes.johnsonHattedDiagonal n w p q (p + q + source.val) := by
  have hdimension :
      0 < (MetricCodes.booleanHarmonicDimension
        n (p + q + source.val) : ℝ) := by
    exact_mod_cast johnsonWindowHarmonicDimension_pos h source
  have hroot := (Real.sqrt_pos.mpr hdimension).ne'
  unfold johnsonSourceChannelCoefficient matrix
  rw [MetricCodes.johnsonJacobiMatrix_diag]
  field_simp [hroot]

theorem johnsonSourceChannelCoefficient_reverse_mul_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L target source *
        johnsonUpperScale n (p + q + target.val) =
      johnsonSourceChannelCoefficient n w p q L source target *
        (((p + q + target.val : ℕ) : ℝ) + 1) := by
  let j : ℕ := p + q + target.val
  have hsource : p + q + source.val = j + 1 := by
    dsimp [j]
    omega
  have hhalf : 2 * (j + 1) ≤ n := by
    have hweight := h.window_degree_le_weight source
    omega
  have htargetdim :
      0 < (MetricCodes.booleanHarmonicDimension n j : ℝ) := by
    dsimp [j]
    exact_mod_cast johnsonWindowHarmonicDimension_pos h target
  have hsourcedim :
      0 < (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) := by
    rw [← hsource]
    exact_mod_cast johnsonWindowHarmonicDimension_pos h source
  have htargetroot := (Real.sqrt_pos.mpr htargetdim).ne'
  have hsourceroot := (Real.sqrt_pos.mpr hsourcedim).ne'
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hratio := booleanHarmonicDimension_succ_div_eq_upperScale hhalf
  have hmul :
      (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          ((j : ℝ) + 1) =
        johnsonUpperScale n j *
          (MetricCodes.booleanHarmonicDimension n j : ℝ) :=
    (div_eq_div_iff htargetdim.ne' hj).mp hratio
  have hsym : matrix n w p q L target source =
      matrix n w p q L source target := by
    have heq := congrArg
      (fun A : Matrix (Index p q L) (Index p q L) ℝ =>
        A source target)
      (MetricCodes.johnsonJacobiMatrix_symmetric n w p q L)
    simpa only [matrix, Matrix.transpose_apply] using heq
  change
    johnsonSourceChannelCoefficient n w p q L target source *
        johnsonUpperScale n j =
      johnsonSourceChannelCoefficient n w p q L source target *
        ((j : ℝ) + 1)
  unfold johnsonSourceChannelCoefficient
  change
    (matrix n w p q L target source *
      Real.sqrt (MetricCodes.booleanHarmonicDimension n j : ℝ) /
      Real.sqrt
        (MetricCodes.booleanHarmonicDimension n
          (p + q + source.val) : ℝ)) *
        johnsonUpperScale n j =
      (matrix n w p q L source target *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n
            (p + q + source.val) : ℝ) /
        Real.sqrt (MetricCodes.booleanHarmonicDimension n j : ℝ)) *
          ((j : ℝ) + 1)
  rw [hsource]
  rw [hsym]
  field_simp [htargetroot, hsourceroot]
  rw [Real.sq_sqrt htargetdim.le,
    Real.sq_sqrt hsourcedim.le]
  linear_combination
    -(matrix n w p q L source target) * hmul

theorem johnsonSourceChannelCoefficient_reverse_eq_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L target source =
      johnsonSourceChannelCoefficient n w p q L source target *
        (((p + q + target.val : ℕ) : ℝ) + 1) /
          johnsonUpperScale n (p + q + target.val) := by
  have hhalf : 2 * (p + q + target.val + 1) ≤ n := by
    have hweight := h.window_degree_le_weight source
    omega
  have hscale := (johnsonUpperScale_pos hhalf).ne'
  exact (eq_div_iff hscale).mpr
    (johnsonSourceChannelCoefficient_reverse_mul_upperScale
      h hstrict target source hadj)

theorem johnsonSourceChannelCoefficient_reverse_sqrt_eq_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    Real.sqrt
        (johnsonSourceChannelCoefficient n w p q L target source) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) *
        Real.sqrt (((p + q + target.val : ℕ) : ℝ) + 1) /
          Real.sqrt (johnsonUpperScale n (p + q + target.val)) := by
  rw [johnsonSourceChannelCoefficient_reverse_eq_upperScale
    h hstrict target source hadj]
  have hsource := johnsonSourceChannelCoefficient_nonneg
    h hstrict source target
  have hdegree : 0 ≤ (((p + q + target.val : ℕ) : ℝ) + 1) := by
    positivity
  rw [Real.sqrt_div (mul_nonneg hsource hdegree),
    Real.sqrt_mul hsource]

theorem johnsonMiddleChannel_signed_axis_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q)
    (hsource : 0 < p + q + source.val) :
    MetricCodes.Boolean.coordinateDot
        (johnsonDiagonalChannelSign n w p q
            (p + q + source.val) •
          johnsonMiddleChannel (p + q + source.val) f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  have hn : 0 < n := by omega
  have hclosed := johnsonMiddleChannel_coupled_axis_inner_closed
    hn x h.support_half h.complement_half
    (h.supportResidual_bound source)
    (h.complementResidual_bound source) a f hf
  have hscalar := johnsonMiddleSignedScalar_eq_sqrt_hattedDiagonal
    h hstrict source hsource
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonDiagonalChannelSign n w p q
            (p + q + source.val) •
          johnsonMiddleChannel (p + q + source.val) f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      johnsonDiagonalChannelSign n w p q (p + q + source.val) *
        MetricCodes.Boolean.coordinateDot
          (johnsonMiddleChannel (p + q + source.val) f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a source.val)) := by
        simpa only [one_smul, mul_one] using
          johnsonCoordinateDot_pi_smul (johnsonDiagonalChannelSign n w p q (p + q + source.val)) 1
            (johnsonMiddleChannel (p + q + source.val) f)
            (johnsonAxisTensor x (coupledHarmonic x h.support_half h.complement_half a source.val))
    _ = (johnsonDiagonalChannelSign n w p q (p + q + source.val) *
          ((Real.sqrt
              (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
            Real.sqrt
              ((n : ℝ) /
                ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (((p : ℝ) - (w : ℝ) / (n : ℝ) *
                ((p + q + source.val : ℕ) : ℝ)) +
              ((source.val : ℝ) *
                (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
                  (source.val : ℝ) + 1)) /
                (((w : ℝ) - 2 * (p : ℝ)) +
                  (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
                  2 * (source.val : ℝ) + 2)))) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [hclosed]
        ring
    _ = Real.sqrt
          (MetricCodes.johnsonHattedDiagonal
            n w p q (p + q + source.val)) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [hscalar]
    _ = Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [johnsonSourceChannelCoefficient_diagonal h source]

theorem johnsonAdjacentChannel_axis_inner_of_not_active
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (a : HarmonicFibreIndex n w p q)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  rw [johnsonAdjacentChannel_eq_zero_of_not_active
    target source f hinactive,
    johnsonSourceChannelCoefficient_eq_zero_of_not_active
      source target hinactive]
  simp only [Boolean.coordinateDot, Boolean.dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    Real.sqrt_zero]

theorem johnsonAdjacentChannel_axis_inner_diagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L source source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  by_cases hsource : 0 < p + q + source.val
  · have hdown : source.val + 1 ≠ source.val := by omega
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    exact johnsonMiddleChannel_signed_axis_inner
      h hstrict x source f hf a hsource
  · apply johnsonAdjacentChannel_axis_inner_of_not_active
      h x source source f a
    intro hactive
    rcases hactive with hdown | hmiddle | hup
    · omega
    · exact hsource hmiddle.2
    · omega

end

section


theorem johnsonOffDiagonal_fourthPower_grouped_algebra
    {N W C G j A B E F : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hC : C ≠ 0)
    (hWj : W - j ≠ 0) (hCj : C - j ≠ 0)
    (hG : G ≠ 0) (hGminus : G - 1 ≠ 0)
    (hGplus : G + 1 ≠ 0) (hjone : j + 1 ≠ 0)
    (hlast : N - j + 1 ≠ 0) :
    (N * A * B * E * F) ^ 2 /
        (W * C * G * (G + 1)) ^ 2 / (j + 1) ^ 2 =
      (((N ^ 2 *
          ((W - j) * (C - j) * A * B * E * F)) /
          ((W * C) ^ 2 * G ^ 2 * ((G - 1) * (G + 1)))) ^ 2 /
        ((N ^ 2 *
            ((W - j) ^ 2 * (C - j) ^ 2 *
              (j + 1) * (N - j + 1))) /
          ((W * C) ^ 2 * G ^ 2 * ((G - 1) * (G + 1))))) *
        (((G - 1) * (N - j + 1)) /
          ((j + 1) * (G + 1))) := by
  field_simp [hN, hW, hC, hWj, hCj, hG,
    hGminus, hGplus, hjone, hlast]

theorem johnsonAdjacentRawSquare_compact_algebra
    {N W C P Q T : ℝ}
    (hNC : N = W + C)
    (hW : W ≠ 0) (hC : C ≠ 0)
    (hgap : N - 2 * (P + Q + T) ≠ 0)
    (hgapplus : N - 2 * (P + Q + T) + 1 ≠ 0) :
    (N / (W * C)) *
        ((T + 1) * (C - 2 * Q - T)) *
        ((((W - 2 * P) + (C - 2 * Q) - T + 1) *
            (W - 2 * P - T)) /
          (((W - 2 * P) + (C - 2 * Q) - 2 * T + 1) *
            ((W - 2 * P) + (C - 2 * Q) - 2 * T))) =
      (N * (W - (P + Q + T) - P + Q) *
        (C - (P + Q + T) + P - Q) *
        ((P + Q + T) - P - Q + 1) *
        (N - P - Q - (P + Q + T) + 1)) /
        (W * C * (N - 2 * (P + Q + T)) *
          (N - 2 * (P + Q + T) + 1)) := by
  let j : ℝ := P + Q + T
  let G : ℝ := N - 2 * j
  have hG : G ≠ 0 := hgap
  have hGone : G + 1 ≠ 0 := hgapplus
  have hden :
      ((W - 2 * P) + (C - 2 * Q) - 2 * T) = G := by
    dsimp [G, j]
    rw [hNC]
    ring
  have hdenone :
      ((W - 2 * P) + (C - 2 * Q) - 2 * T + 1) = G + 1 := by
    rw [hden]
  rw [hdenone, hden]
  change
    (N / (W * C)) *
        ((T + 1) * (C - 2 * Q - T)) *
        ((((W - 2 * P) + (C - 2 * Q) - T + 1) *
            (W - 2 * P - T)) / ((G + 1) * G)) =
      (N * (W - j - P + Q) * (C - j + P - Q) *
        (j - P - Q + 1) * (N - P - Q - j + 1)) /
        (W * C * G * (G + 1))
  field_simp [hW, hC, hG, hGone]
  dsimp [j]
  rw [hNC]
  ring

end

section


open scoped BigOperators

theorem johnsonNu_radicand_factor
    {n w p q j : ℕ} (hwn : w ≤ n) :
    ((MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2) *
      (MetricCodes.johnsonJ n j ^ 2 -
        MetricCodes.johnsonDelta n w p q ^ 2) *
      ((MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
        MetricCodes.johnsonJ n j ^ 2)) =
      ((w : ℝ) - (j : ℝ)) *
        (((n - w : ℕ) : ℝ) - (j : ℝ)) *
        ((w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ)) *
        (((n - w : ℕ) : ℝ) - (j : ℝ) +
          (p : ℝ) - (q : ℝ)) *
        ((j : ℝ) - (p : ℝ) - (q : ℝ) + 1) *
        ((n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1) := by
  unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    MetricCodes.johnsonDelta MetricCodes.johnsonSigma
    MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
  rw [Nat.cast_sub hwn]
  ring

theorem johnsonNu_denominator_factor (n j : ℕ) :
    (2 * MetricCodes.johnsonJ n j - 1) *
      (2 * MetricCodes.johnsonJ n j + 1) =
      ((n : ℝ) - 2 * (j : ℝ) - 1) *
        ((n : ℝ) - 2 * (j : ℝ) + 1) := by
  unfold MetricCodes.johnsonJ
  ring

theorem johnsonNu_radicand_pos
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 <
      ((MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2) *
        (MetricCodes.johnsonJ n j ^ 2 -
          MetricCodes.johnsonDelta n w p q ^ 2) *
        ((MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
          MetricCodes.johnsonJ n j ^ 2)) := by
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjleft : j < w - p + q :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hjright : j < n - w + p - q :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hcompnat : j < n - w := by omega
  have hleftreal : (j : ℝ) <
      (w : ℝ) - (p : ℝ) + (q : ℝ) := by
    have hcast : (j : ℝ) < ((w - p + q : ℕ) : ℝ) := by
      exact_mod_cast hjleft
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : p ≤ w)]
      using hcast
  have hrightreal : (j : ℝ) <
      ((n - w : ℕ) : ℝ) + (p : ℝ) - (q : ℝ) := by
    have hcast : (j : ℝ) < ((n - w + p - q : ℕ) : ℝ) := by
      exact_mod_cast hjright
    simpa only [Nat.cast_sub (by omega : q ≤ n - w + p),
      Nat.cast_add] using hcast
  have hfirstreal : (p : ℝ) + (q : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hfirst
  have hjreal : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hcompreal : (j : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcompnat
  have hlastreal :
      (p : ℝ) + (q : ℝ) + (j : ℝ) < (n : ℝ) + 1 := by
    have hnat : p + q + j < n + 1 := by omega
    exact_mod_cast hnat
  have hfactor1 : 0 < (w : ℝ) - (j : ℝ) := by linarith
  have hfactor2 : 0 < ((n - w : ℕ) : ℝ) - (j : ℝ) := by linarith
  have hfactor3 :
      0 < (w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ) := by
    linarith
  have hfactor4 :
      0 < ((n - w : ℕ) : ℝ) - (j : ℝ) +
        (p : ℝ) - (q : ℝ) := by
    linarith
  have hfactor5 :
      0 < (j : ℝ) - (p : ℝ) - (q : ℝ) + 1 := by
    linarith
  have hfactor6 :
      0 < (n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1 := by
    linarith
  rw [johnsonNu_radicand_factor (Nat.le_of_lt h.weight_lt)]
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (mul_pos hfactor1 hfactor2)
      hfactor3) hfactor4) hfactor5) hfactor6

theorem johnsonNu_denominator_pos
    {n w p q L j : ℕ}
    (_ : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 <
      (2 * MetricCodes.johnsonJ n j - 1) *
        (2 * MetricCodes.johnsonJ n j + 1) := by
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjbound : 2 * j + 1 < n := by omega
  have hjreal : (2 : ℝ) * (j : ℝ) + 1 < (n : ℝ) := by
    exact_mod_cast hjbound
  rw [johnsonNu_denominator_factor]
  apply mul_pos <;> linarith


theorem johnsonEdge_sq_factored
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    MetricCodes.johnsonEdge n w p q j ^ 2 =
      ((n : ℝ) ^ 2 *
        (((w : ℝ) - (j : ℝ)) *
          (((n - w : ℕ) : ℝ) - (j : ℝ)) *
          ((w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ)) *
          (((n - w : ℕ) : ℝ) - (j : ℝ) +
            (p : ℝ) - (q : ℝ)) *
          ((j : ℝ) - (p : ℝ) - (q : ℝ) + 1) *
          ((n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1))) /
        (((w : ℝ) * ((n - w : ℕ) : ℝ)) ^ 2 *
          ((n : ℝ) - 2 * (j : ℝ)) ^ 2 *
          (((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - 2 * (j : ℝ) + 1))) := by
  have hrad := johnsonNu_radicand_pos h hstrict hfirst hlast
  have hden := johnsonNu_denominator_pos h hstrict hlast
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    have hjw : j < w :=
      lt_of_lt_of_le hlast (by
        unfold MetricCodes.johnsonLastDegree
        exact min_le_left _ _)
    have hreal : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 2 * j < n by omega)
    unfold MetricCodes.johnsonJ
    linarith
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hN : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  have hroot := (Real.sqrt_pos.mpr hden).ne'
  unfold MetricCodes.johnsonEdge MetricCodes.johnsonNu
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hrad.le, Real.sq_sqrt hden.le,
    johnsonNu_radicand_factor (Nat.le_of_lt h.weight_lt),
    johnsonNu_denominator_factor]
  unfold MetricCodes.johnsonJ
  rw [← mul_div_assoc, div_div]
  congr 1
  ring

theorem johnsonZonalEdge_sq_factored
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hjw : j < w) :
    MetricCodes.johnsonZonalEdge n w j ^ 2 =
      ((n : ℝ) ^ 2 *
        (((w : ℝ) - (j : ℝ)) ^ 2 *
          (((n - w : ℕ) : ℝ) - (j : ℝ)) ^ 2 *
          ((j : ℝ) + 1) *
          ((n : ℝ) - (j : ℝ) + 1))) /
        (((w : ℝ) * ((n - w : ℕ) : ℝ)) ^ 2 *
          ((n : ℝ) - 2 * (j : ℝ)) ^ 2 *
          (((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - 2 * (j : ℝ) + 1))) := by
  have hhalf : w ≤ n - w := by omega
  have hlast : MetricCodes.johnsonLastDegree n w 0 0 = w := by
    simp only [johnsonLastDegree, tsub_zero, add_zero, min_eq_left hhalf, min_self]
  let hz : AdmissibleDegrees n w 0 0 w :=
    { weight_pos := h.weight_pos
      weight_lt := h.weight_lt
      weight_half := h.weight_half
      support_half := by omega
      complement_half := by omega
      first_le := by omega
      last_le := by rw [hlast] }
  have hlast' : j < MetricCodes.johnsonLastDegree n w 0 0 := by
    simpa only [hlast] using hjw
  unfold MetricCodes.johnsonZonalEdge
  rw [johnsonEdge_sq_factored hz hstrict (Nat.zero_le j) hlast']
  simp only [Nat.cast_zero, sub_zero, add_zero]
  ring

theorem johnsonSourceChannelCoefficient_sq
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source target : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L source target ^ 2 =
      matrix n w p q L source target ^ 2 *
        ((MetricCodes.booleanHarmonicDimension
          n (p + q + source.val) : ℝ) /
          (MetricCodes.booleanHarmonicDimension
            n (p + q + target.val) : ℝ)) := by
  have hsource :
      0 ≤ (MetricCodes.booleanHarmonicDimension
        n (p + q + source.val) : ℝ) := by
    exact_mod_cast (johnsonWindowHarmonicDimension_pos h source).le
  have htarget :
      0 ≤ (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val) : ℝ) := by
    exact_mod_cast (johnsonWindowHarmonicDimension_pos h target).le
  unfold johnsonSourceChannelCoefficient
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hsource, Real.sq_sqrt htarget]
  ring

private def johnsonAdjacentRawScalar
    (n w p q t : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
    Real.sqrt
      (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
    (Real.sqrt (clebschNormSq w (n - w) p q t) /
      Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))

private def johnsonLowerOffDiagonalScalar
    (n w p q t : ℕ) : ℝ :=
  (Real.sqrt (((p + q + (t + 1) : ℕ) : ℝ)))⁻¹ *
    johnsonAdjacentRawScalar n w p q t

private def johnsonUpperOffDiagonalScalar
    (n w p q t : ℕ) : ℝ :=
  (Real.sqrt (johnsonUpperScale n (p + q + t)))⁻¹ *
    johnsonAdjacentRawScalar n w p q t

theorem johnsonAdjacentRawScalar_sq
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (_ : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    johnsonAdjacentRawScalar n w p q t ^ 2 =
      ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) *
        (clebschNormSq w (n - w) p q t /
          clebschNormSq w (n - w) p q (t + 1)) := by
  have hn : 0 < n := by omega
  have haxis :
      0 ≤ (n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
    have hN : 0 < ((n - w : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hwn
    positivity
  have hcoefficient :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) :=
    (MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement).le
  have hnorm := (clebschNormSq_pos w (n - w) p q t).le
  have hnext := (clebschNormSq_pos w (n - w) p q (t + 1)).le
  unfold johnsonAdjacentRawScalar
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt haxis, Real.sq_sqrt hcoefficient,
    Real.sq_sqrt hnorm, Real.sq_sqrt hnext]

theorem johnsonAdjacentRawScalar_sq_factored
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    johnsonAdjacentRawScalar n w p q t ^ 2 =
      ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((t : ℝ) + 1) *
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ))) *
        (((((w : ℝ) - 2 * (p : ℝ)) +
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
            ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) /
          (((((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 1) *
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ))))) := by
  rw [johnsonAdjacentRawScalar_sq hw hwn hsupport hcomplement,
    clebschNormSq_div_succ hsupport hcomplement]
  unfold MetricCodes.Boolean.harmonicCoefficient
  push_cast
  ring

theorem johnsonAdjacentRawScalar_pos
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (_ : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    0 < johnsonAdjacentRawScalar n w p q t := by
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast hw
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hwn
  have hcoefficient :
      0 < MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  unfold johnsonAdjacentRawScalar
  positivity

theorem johnsonLowerOffDiagonalScalar_sq
    {n w p q t : ℕ}
    (_ : 0 < p + q + (t + 1)) :
    johnsonLowerOffDiagonalScalar n w p q t ^ 2 =
      johnsonAdjacentRawScalar n w p q t ^ 2 /
        (((p + q + (t + 1) : ℕ) : ℝ)) := by
  have hdegree' : 0 ≤ (((p + q + (t + 1) : ℕ) : ℝ)) := by
    positivity
  unfold johnsonLowerOffDiagonalScalar
  rw [mul_pow, inv_pow, Real.sq_sqrt hdegree']
  ring

theorem johnsonSourceChannelCoefficient_lower_sq
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L source target ^ 2 =
      MetricCodes.johnsonHattedEdge n w p q (p + q + target.val) ^ 2 *
        ((MetricCodes.booleanHarmonicDimension
          n (p + q + source.val) : ℝ) /
          (MetricCodes.booleanHarmonicDimension
            n (p + q + target.val) : ℝ)) := by
  have hne : source ≠ target := by
    intro heq
    subst source
    omega
  have hnotup : source.val + 1 ≠ target.val := by omega
  rw [johnsonSourceChannelCoefficient_sq h source target]
  simp only [matrix, johnsonJacobiMatrix, hne, ↓reduceIte, hnotup, hadj]

end

section


open scoped BigOperators InnerProductSpace

theorem johnsonAdjacentRawScalar_sq_degree_factored
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonAdjacentRawScalar n w p q target.val ^ 2 =
      ((n : ℝ) *
        ((w : ℝ) - ((p + q + target.val : ℕ) : ℝ) -
          (p : ℝ) + (q : ℝ)) *
        (((n - w : ℕ) : ℝ) -
          ((p + q + target.val : ℕ) : ℝ) +
          (p : ℝ) - (q : ℝ)) *
        (((p + q + target.val : ℕ) : ℝ) -
          (p : ℝ) - (q : ℝ) + 1) *
        ((n : ℝ) - (p : ℝ) - (q : ℝ) -
          ((p + q + target.val : ℕ) : ℝ) + 1)) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 * ((p + q + target.val : ℕ) : ℝ)) *
          ((n : ℝ) - 2 * ((p + q + target.val : ℕ) : ℝ) + 1)) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
  have hcomplement' :
      2 * q + (target.val + 1) ≤ n - w := by omega
  have hj := h.window_degree_le_weight target
  have hgap :
      (n : ℝ) -
        2 * ((p : ℝ) + (q : ℝ) + (target.val : ℝ)) ≠ 0 := by
    have hnat : 2 * (p + q + target.val) < n := by omega
    have hreal :
        (2 : ℝ) * ((p + q + target.val : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith
  have hgapplus :
      (n : ℝ) -
        2 * ((p : ℝ) + (q : ℝ) + (target.val : ℝ)) + 1 ≠ 0 := by
    have hnat : 2 * (p + q + target.val) < n := by omega
    have hreal :
        (2 : ℝ) * ((p + q + target.val : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith
  have hNC : (n : ℝ) = (w : ℝ) + ((n - w : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt h.weight_lt)]
    ring
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hC : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  rw [johnsonAdjacentRawScalar_sq_factored
    h.weight_pos h.weight_lt hsupport' hcomplement']
  have halgebra := johnsonAdjacentRawSquare_compact_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (C := ((n - w : ℕ) : ℝ))
    (P := (p : ℝ)) (Q := (q : ℝ))
    (T := (target.val : ℝ))
    hNC hw hC hgap hgapplus
  convert halgebra using 1; push_cast; ring


theorem johnsonLowerOffDiagonalScalar_fourthPower
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonLowerOffDiagonalScalar n w p q target.val ^ 4 =
      johnsonSourceChannelCoefficient n w p q L source target ^ 2 := by
  let j : ℕ := p + q + target.val
  have hjw : j < w := by
    have hsource := h.window_degree_le_weight source
    dsimp [j]
    omega
  have hlast : j < MetricCodes.johnsonLastDegree n w p q := by
    have hsource := h.window_degree_le_weight source
    have hwindow : p + q + source.val ≤ L := by
      have hi := source.isLt
      have hfirst := h.first_le
      omega
    have hlast' := h.last_le
    dsimp [j]
    omega
  have hfirst : p + q ≤ j := by
    dsimp [j]
    omega
  have hdegree : p + q + source.val = j + 1 := by
    dsimp [j]
    omega
  have hhalf : 2 * (j + 1) ≤ n := by
    have hsource := h.window_degree_half source
    omega
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < n by omega).ne'
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hC : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  have hjreal : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hCreal : (j : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (show j < n - w by omega)
  have hgapreal :
      (2 : ℝ) * (j : ℝ) + 1 < (n : ℝ) := by
    exact_mod_cast (show 2 * j + 1 < n by omega)
  have hWj : (w : ℝ) - (j : ℝ) ≠ 0 := by linarith
  have hCj : ((n - w : ℕ) : ℝ) - (j : ℝ) ≠ 0 := by linarith
  have hgap : (n : ℝ) - 2 * (j : ℝ) ≠ 0 := by linarith
  have hgapminus : (n : ℝ) - 2 * (j : ℝ) - 1 ≠ 0 := by
    linarith
  have hgapplus : (n : ℝ) - 2 * (j : ℝ) + 1 ≠ 0 := by
    linarith
  have hjone : (j : ℝ) + 1 ≠ 0 := by positivity
  have hlastreal : (n : ℝ) - (j : ℝ) + 1 ≠ 0 := by
    have hjn : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  have halgebra := johnsonOffDiagonal_fourthPower_grouped_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (C := ((n - w : ℕ) : ℝ))
    (G := (n : ℝ) - 2 * (j : ℝ))
    (j := (j : ℝ))
    (A := (w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ))
    (B := ((n - w : ℕ) : ℝ) - (j : ℝ) +
      (p : ℝ) - (q : ℝ))
    (E := (j : ℝ) - (p : ℝ) - (q : ℝ) + 1)
    (F := (n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1)
    hn hw hC hWj hCj hgap hgapminus hgapplus hjone hlastreal
  rw [show johnsonLowerOffDiagonalScalar
      n w p q target.val ^ 4 =
        (johnsonLowerOffDiagonalScalar
          n w p q target.val ^ 2) ^ 2 by ring,
    johnsonLowerOffDiagonalScalar_sq (by omega),
    johnsonAdjacentRawScalar_sq_degree_factored
      h hstrict target source hadj,
    johnsonSourceChannelCoefficient_lower_sq h target source hadj]
  rw [hdegree]
  change
    (_ / (((p + q + (target.val + 1) : ℕ) : ℝ))) ^ 2 =
      MetricCodes.johnsonHattedEdge n w p q j ^ 2 *
        ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
          (MetricCodes.booleanHarmonicDimension n j : ℝ))
  rw [booleanHarmonicDimension_succ_div hhalf]
  unfold MetricCodes.johnsonHattedEdge
  simp only [div_pow]
  rw [johnsonEdge_sq_factored h hstrict hfirst hlast,
    johnsonZonalEdge_sq_factored h hstrict hjw]
  dsimp [j] at halgebra ⊢
  push_cast at halgebra ⊢
  simpa only [add_assoc, mul_assoc] using halgebra

theorem johnsonLowerOffDiagonalScalar_eq_sqrt_source
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonLowerOffDiagonalScalar n w p q target.val =
      Real.sqrt
        (johnsonSourceChannelCoefficient
          n w p q L source target) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
  have hcomplement' :
      2 * q + (target.val + 1) ≤ n - w := by omega
  have hraw := johnsonAdjacentRawScalar_pos
    h.weight_pos h.weight_lt hsupport' hcomplement'
  have hdegree : 0 < ((p + q + (target.val + 1) : ℕ) : ℝ) := by
    positivity
  have hleft :
      0 < johnsonLowerOffDiagonalScalar n w p q target.val := by
    unfold johnsonLowerOffDiagonalScalar
    positivity
  have hright := johnsonSourceChannelCoefficient_nonneg
    h hstrict source target
  have hfourth := johnsonLowerOffDiagonalScalar_fourthPower
    h hstrict target source hadj
  have hsquare :
      johnsonLowerOffDiagonalScalar n w p q target.val ^ 2 =
        johnsonSourceChannelCoefficient
          n w p q L source target := by
    nlinarith [sq_nonneg
      (johnsonLowerOffDiagonalScalar n w p q target.val ^ 2 -
        johnsonSourceChannelCoefficient n w p q L source target)]
  have hroot := Real.sq_sqrt hright
  nlinarith [Real.sqrt_nonneg
    (johnsonSourceChannelCoefficient n w p q L source target)]

theorem johnsonUpperOffDiagonalScalar_eq_sqrt_source
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonUpperOffDiagonalScalar n w p q target.val =
      Real.sqrt
        (johnsonSourceChannelCoefficient
          n w p q L target source) := by
  have hhalf :
      2 * ((p + q + target.val) + 1) ≤ n := by
    have hsource := h.window_degree_half source
    omega
  have hscale := johnsonUpperScale_pos hhalf
  have hdegree :
      0 < (((p + q + target.val : ℕ) : ℝ) + 1) := by
    positivity
  have hrootdegree :
      Real.sqrt (((p + q + target.val : ℕ) : ℝ) + 1) ≠ 0 :=
    (Real.sqrt_pos.mpr hdegree).ne'
  have hrootscale :
      Real.sqrt (johnsonUpperScale n (p + q + target.val)) ≠ 0 :=
    (Real.sqrt_pos.mpr hscale).ne'
  rw [johnsonSourceChannelCoefficient_reverse_sqrt_eq_upperScale
    h hstrict target source hadj,
    ← johnsonLowerOffDiagonalScalar_eq_sqrt_source
      h hstrict target source hadj]
  unfold johnsonUpperOffDiagonalScalar
    johnsonLowerOffDiagonalScalar
  have hcast :
      (((p + q + (target.val + 1) : ℕ) : ℝ)) =
        (((p + q + target.val : ℕ) : ℝ) + 1) := by
    push_cast
    ring
  rw [hcast]
  field_simp [hrootdegree, hrootscale]

theorem johnsonCoordinateDot_smul_left
    {n : ℕ} (c : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot (c • f) g =
      c * MetricCodes.Boolean.coordinateDot f g := by
  simpa only [one_smul, mul_one] using johnsonCoordinateDot_pi_smul c (1 : ℝ) f g

theorem johnsonAdjacentChannel_axis_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · have hsupport := h.supportResidual_bound source
    have hcomplement := h.complementResidual_bound source
    have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
    have hcomplement' :
        2 * q + (target.val + 1) ≤ n - w := by omega
    have hsourceval : source.val = target.val + 1 := by omega
    have hf' :
        MetricCodes.Boolean.IsHarmonic
          (p + q + (target.val + 1)) f := by
      simpa only [hsourceval] using hf
    have hclosed := johnsonLowerChannel_coupled_axis_inner_closed
      x h.support_half h.complement_half
      hsupport' hcomplement' a f hf'
    have hscalar := johnsonLowerOffDiagonalScalar_eq_sqrt_source
      h hstrict target source hdown
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    rw [hsourceval, johnsonCoordinateDot_smul_left, hclosed]
    rw [← hscalar]
    unfold johnsonLowerOffDiagonalScalar johnsonAdjacentRawScalar
    ring
  · by_cases hdiag : target = source
    · subst target
      exact johnsonAdjacentChannel_axis_inner_diagonal
        h hstrict x source f hf a
    · by_cases hup : source.val + 1 = target.val
      · have hsupport := h.supportResidual_bound target
        have hcomplement := h.complementResidual_bound target
        have hsupport' : 2 * p + (source.val + 1) ≤ w := by
          omega
        have hcomplement' :
            2 * q + (source.val + 1) ≤ n - w := by
          omega
        have hclosed := johnsonUpperChannel_coupled_axis_inner_closed
          x h.support_half h.complement_half
          hsupport' hcomplement' a f hf
        have hscalar := johnsonUpperOffDiagonalScalar_eq_sqrt_source
          h hstrict source target hup
        simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte]
        rw [johnsonCoordinateDot_smul_left]
        have htargetval : target.val = source.val + 1 := by omega
        rw [htargetval, hclosed]
        rw [← hscalar]
        unfold johnsonUpperOffDiagonalScalar johnsonAdjacentRawScalar
        ring
      · apply johnsonAdjacentChannel_axis_inner_of_not_active
          h x target source f a
        intro hactive
        rcases hactive with hfirst | hmiddle | hlast
        · exact hdown hfirst
        · exact hdiag hmiddle.1
        · exact hup hlast

end

end Johnson

end MetricCodes

end MetricCodesNoncomputable
