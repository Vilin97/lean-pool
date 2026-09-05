/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.HarmonicAnalysis

/-!
# Spherical-code hierarchy

General spectral bounds, localization, compactification, and strict hierarchy estimates.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open Filter Topology
open scoped Topology

theorem variationalRate_lt_classical
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    variationalRate s <
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  obtain ⟨a, b, hf, hcost⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact lt_of_le_of_lt (variationalRate_le_of_feasible hf) hcost

theorem rateSet_nonempty_of_interior
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (rateSet s).Nonempty := by
  obtain ⟨a, b, hf, _⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact ⟨MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b,
    a, b, hf, rfl⟩

end

section

open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace

namespace GeneralSpectral

/-- The longitudinal degree used in the spherical-code argument. -/
def longitudinalDegree (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * (n : ℝ)⌋₊

/-- The transverse degree used in the spherical-code argument. -/
def transverseDegree (b : ℝ) (n : ℕ) : ℕ :=
  ⌊b * (n : ℝ)⌋₊

theorem sphericalCode_bound_of_actual_harmonic_channels
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < SpherePacking.Jacobi.topEigenvalue n k L)
    (C : SpherePacking.SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue n k L - s)) *
        ((SpherePacking.truncatedHarmonicDimension n k L : ℝ) /
          (SpherePacking.Gegenbauer.fibreDimension n k : ℝ)) := by
  exact
    SpherePacking.HarmonicCoordinateChannels.sphericalCode_bound_of_sourceSpectralRow
      hn hkl.le
      (SpherePacking.harmonicDegreeFibre hn k L)
      (SpherePacking.HarmonicCoordinateChannels.sourceSpectralRowDataOfAdjacent
        hn hkl (SpherePacking.harmonicDegreeFibre hn k L)
        (SpherePacking.HarmonicAdjacentChannelTransport.actualSourceAdjacentChannelData
          hn k L))
      hs hgap C

theorem tendsto_longitudinal_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ =>
      (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  exact SpherePacking.SpectralAsymptotics.tendsto_floored_ratio ha

theorem tendsto_transverse_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ =>
      (transverseDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  exact SpherePacking.SpectralAsymptotics.tendsto_floored_ratio hb

theorem tendsto_longitudinalDegree_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (longitudinalDegree a) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop a ha

theorem tendsto_terminal_degree_ratio {a : ℝ}
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset :
      Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [
    (tendsto_longitudinalDegree_atTop ha).eventually
      (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring

theorem normalizedCoefficient_eq_Gamma
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    SpherePacking.SpectralAsymptotics.normalizedCoefficient a b 0 =
      MetricCodes.Gamma a b := by
  have hfactor : 0 ≤ a * (1 + a) := by positivity
  have hlin : 0 ≤ 1 + 2 * a := by positivity
  unfold SpherePacking.SpectralAsymptotics.normalizedCoefficient
    MetricCodes.Gamma
  have hrad :
      Real.sqrt
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) =
        (1 + 2 * a) * Real.sqrt (a * (1 + a)) := by
    have hpoly :
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) =
          (a * (1 + a)) * (1 + 2 * a) ^ 2 := by
      ring
    rw [hpoly, Real.sqrt_mul hfactor, Real.sqrt_sq hlin]
    ring
  rw [hrad]
  congr 1
  ring

theorem tendsto_terminal_coefficient {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n) (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.Gamma a b)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul
    (((hx.add hy).add hone).sub (htwo.mul hz))
  have hrad := (((hx.add hz).mul
    ((hx.add hone).sub (htwo.mul hz))).mul
      (((htwo.mul hx).add hone).sub (htwo.mul hz))).mul
        ((htwo.mul hx).add hone)
  have hroot := hrad.sqrt
  have hrootne :
      Real.sqrt
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hone : 0 < a + 1 := by linarith
    have htwo : 0 < 2 * a + 1 := by linarith
    simpa only [add_zero, mul_zero, sub_zero,
      gt_iff_lt] using mul_pos (mul_pos (mul_pos ha hone) htwo) htwo
  have hnorm := hnum.div hroot hrootne
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm' :
      Tendsto
        (fun n : ℕ =>
          SpherePacking.SpectralAsymptotics.normalizedCoefficient
            (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
            ((transverseDegree b n : ℝ) / (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (SpherePacking.SpectralAsymptotics.normalizedCoefficient a b 0)) := by
    simpa only [SpherePacking.SpectralAsymptotics.normalizedCoefficient, one_div, add_zero,
      mul_zero, sub_zero] using pointwise_div hnorm
  rw [normalizedCoefficient_eq_Gamma ha b] at hnorm'
  refine hnorm'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact
    (SpherePacking.SpectralAsymptotics.jacobiCoefficient_eq_normalized
      n (transverseDegree b n) (longitudinalDegree a n - r) hn).symm

theorem eventually_transverse_add_le_longitudinal
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  let δ : ℝ := (a - b) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlt : δ < a - b := by
    dsimp [δ]
    linarith
  have hratio :=
    ((tendsto_longitudinal_ratio ha.le).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hδlt)
  have hgrowth :
      Tendsto (fun n : ℕ => δ * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hδ
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually
    (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [ne_of_gt hnreal]
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- The terminal edge rayleigh used in the spherical-code argument. -/
def terminalEdgeRayleigh (a b : ℝ) (m n : ℕ) : ℝ :=
  (2 * ∑ r ∈ Finset.range m,
    SpherePacking.Gegenbauer.jacobiCoefficient
      n (transverseDegree b n)
      (longitudinalDegree a n - (m - r))) /
        ((m : ℝ) + 1)

theorem tendsto_terminalEdgeRayleigh {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b))) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m, MetricCodes.Gamma a b)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change
    Tendsto (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b)))
  simpa only [terminalEdgeRayleigh, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hquot

theorem terminalEdgeRayleigh_le_top
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact SpherePacking.SpectralAsymptotics.terminal_edge_sum_le_top
    n (transverseDegree b n) (longitudinalDegree a n) m hkl hm

theorem eventually_topEigenvalue_gt {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hgamma : 0 < 2 * MetricCodes.Gamma a b := by
    exact mul_pos (by norm_num) (MetricCodes.Gamma_pos hb hba)
  let g : ℝ := 2 * MetricCodes.Gamma a b
  let ε : ℝ := (g - s) / 2
  have hε : 0 < ε := by
    dsimp [ε, g]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (g / ε)
  have hprod : g < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : g / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith [hgamma]
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * g =
        g - g / ((m : ℝ) + 1) := by
    field_simp [hden.ne']; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * g := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot :=
    (tendsto_terminalEdgeRayleigh ha hb m).eventually
      (lt_mem_nhds (show
        s < ((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b) by
        simpa only [g] using hbelow))
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m]
      with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)

/-- The spectral gap used in the spherical-code argument. -/
def spectralGap (s a b : ℝ) : ℝ :=
  (2 * MetricCodes.Gamma a b - s) / 2

theorem spectralGap_pos {s a b : ℝ}
    (h : s < 2 * MetricCodes.Gamma a b) :
    0 < spectralGap s a b := by
  unfold spectralGap
  linarith

theorem eventually_topEigenvalue_uniform_gap {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s + spectralGap s a b <
        SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) := by
  apply eventually_topEigenvalue_gt hb hba
  unfold spectralGap
  linarith

/-- The spectral prefactor used in the spherical-code argument. -/
def spectralPrefactor (s a b : ℝ) : ℝ :=
  (1 - s) / spectralGap s a b

theorem spectralPrefactor_pos {s a b : ℝ}
    (hs : s < 1) (hgap : s < 2 * MetricCodes.Gamma a b) :
    0 < spectralPrefactor s a b := by
  unfold spectralPrefactor
  exact div_pos (sub_pos.mpr hs) (spectralGap_pos hgap)

theorem legacy_binaryEntropy_eq_sphericalEntropy (u : ℝ) :
    SpherePacking.NumericalCertificate.binaryEntropy u =
      MetricCodes.sphericalEntropy u := by
  unfold SpherePacking.NumericalCertificate.binaryEntropy
    MetricCodes.sphericalEntropy Real.logb
  ring

theorem eventually_sphericalCode_card_le_harmonicQuotient
    {s a b : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) ≤
        spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n := by
  have hgap : 0 < spectralGap s a b := spectralGap_pos hspectral
  have hpref : 0 ≤ spectralPrefactor s a b :=
    (spectralPrefactor_pos hs hspectral).le
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    eventually_transverse_add_le_longitudinal hb.le hba 1,
    eventually_topEigenvalue_uniform_gap hb.le hba hspectral]
      with n hn hdegrees heigen
  intro C
  have hkl : transverseDegree b n < longitudinalDegree a n := by omega
  have heigengap :
      s < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
    linarith
  have hactual := sphericalCode_bound_of_actual_harmonic_channels
    hn hkl hs.le heigengap C
  change
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) - s)) *
        SpherePacking.truncatedDimensionQuotient a b n at hactual
  have hden :
      0 < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) - s := by
    linarith
  have hfrac :
      (1 - s) /
          (SpherePacking.Jacobi.topEigenvalue
            n (transverseDegree b n) (longitudinalDegree a n) - s) ≤
        spectralPrefactor s a b := by
    unfold spectralPrefactor
    apply (div_le_div_iff₀ hden hgap).2
    apply mul_le_mul_of_nonneg_left
    · linarith
    · linarith
  have htruncated :
      0 ≤ SpherePacking.truncatedDimensionQuotient a b n := by
    unfold SpherePacking.truncatedDimensionQuotient
    positivity
  calc
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) - s)) *
        SpherePacking.truncatedDimensionQuotient a b n := hactual
    _ ≤ spectralPrefactor s a b *
        SpherePacking.truncatedDimensionQuotient a b n :=
      mul_le_mul_of_nonneg_right hfrac htruncated
    _ ≤ spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n :=
      mul_le_mul_of_nonneg_left
        (SpherePacking.truncatedDimensionQuotient_le_harmonicDimensionQuotient
          a b hn) hpref

theorem tendsto_log_spectral_harmonicQuotient
    {s a b : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2)
      atTop
      (nhds (MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b)) := by
  have ha : 0 < a := hb.trans hba
  have h := SpherePacking.tendsto_log_const_mul_harmonicDimensionQuotient
    a b (spectralPrefactor s a b) ha hb
    (spectralPrefactor_pos hs hspectral)
  rw [legacy_binaryEntropy_eq_sphericalEntropy a,
    legacy_binaryEntropy_eq_sphericalEntropy b] at h
  exact h

theorem eventually_sphericalCode_card_lt_rpow
    {s a b r : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b)
    (hr : MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b < r) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (r * (n : ℝ)) := by
  have hlimit :=
    tendsto_log_spectral_harmonicQuotient hs hb hba hspectral
  have hrate :
      ∀ᶠ n : ℕ in atTop,
        (Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2 < r :=
    hlimit.eventually (Iio_mem_nhds hr)
  filter_upwards [
    eventually_sphericalCode_card_le_harmonicQuotient hs hb hba hspectral,
    hrate, eventually_ge_atTop (3 : ℕ)] with n hcode hnrate hn
  intro C
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hpositive :
      0 < spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n :=
    mul_pos (spectralPrefactor_pos hs hspectral)
      (SpherePacking.harmonicDimensionQuotient_pos a b hn)
  have hfirst :
      Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n) / (n : ℝ) <
        r * Real.log 2 :=
    (div_lt_iff₀ hlogtwo).mp hnrate
  have hsecond :
      Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n) <
        (r * Real.log 2) * (n : ℝ) :=
    (div_lt_iff₀ hnreal).mp hfirst
  calc
    (C.points.card : ℝ) ≤
      spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n := hcode C
    _ = Real.exp
      (Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n)) :=
      (Real.exp_log hpositive).symm
    _ < Real.exp (Real.log 2 * (r * (n : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      calc
        Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) <
          (r * Real.log 2) * (n : ℝ) := hsecond
        _ = Real.log 2 * (r * (n : ℝ)) := by ring
    _ = (2 : ℝ) ^ (r * (n : ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num) _).symm

end GeneralSpectral

end

end Spherical

end MetricCodes


section

open scoped InnerProductSpace

namespace SpherePacking

private def spherePointEmbedding_metriccodes2_d60650ef (n : ℕ) : MetricCodes.Sphere n ↪
  Euclidean n :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def attachedSphereEmbedding_metriccodes2_d60650ef {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    {x : Euclidean n // x ∈ C.points} ↪ MetricCodes.Sphere n where
  toFun x := ⟨x.1, C.unit_norm x.1 x.2⟩
  inj' := by
    intro x y h
    exact Subtype.ext
      (congrArg (fun z : MetricCodes.Sphere n => (z : Euclidean n)) h)

private theorem sphericalCode_ext_metriccodes2_d60650ef {n : ℕ} {s : ℝ}
    {C D : SphericalCode n s} (h : C.points = D.points) : C = D := by
  cases C
  cases D
  simpa only [SphericalCode.mk.injEq] using h

private theorem codesSphericalCode_ext_metriccodes2_d60650ef {n : ℕ} {s : ℝ}
    {C D : MetricCodes.SphericalCode n s} (h : C.points = D.points) : C = D := by
  cases C
  cases D
  simpa only [MetricCodes.SphericalCode.mk.injEq] using h

/-- The to codes used in the spherical-code argument. -/
def SphericalCode.toCodes {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) : MetricCodes.SphericalCode n s where
  points := C.points.attach.map (attachedSphereEmbedding_metriccodes2_d60650ef C)
  inner_le := by
    intro x hx y hy hxy
    obtain ⟨x', _, hx'⟩ := Finset.mem_map.mp hx
    obtain ⟨y', _, hy'⟩ := Finset.mem_map.mp hy
    subst x
    subst y
    apply C.inner_le x'.1 x'.2 y'.1 y'.2
    intro h
    apply hxy
    exact Subtype.ext h

/-- The of codes used in the spherical-code argument. -/
def SphericalCode.ofCodes {n : ℕ} {s : ℝ}
    (C : MetricCodes.SphericalCode n s) : SphericalCode n s where
  points := C.points.map (spherePointEmbedding_metriccodes2_d60650ef n)
  unit_norm := by
    intro x hx
    obtain ⟨x', _, rfl⟩ := Finset.mem_map.mp hx
    exact x'.property
  inner_le := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    apply C.inner_le hx' hy'
    intro h
    apply hxy
    exact congrArg Subtype.val h

@[simp] theorem SphericalCode.toCodes_card {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    C.toCodes.points.card = C.points.card := by
  simp only [toCodes, Finset.card_map, Finset.card_attach]

@[simp] theorem SphericalCode.ofCodes_card {n : ℕ} {s : ℝ}
    (C : MetricCodes.SphericalCode n s) :
    (SphericalCode.ofCodes C).points.card = C.points.card := by
  simp only [ofCodes, Finset.card_map]

private def sphericalCodeEquiv (n : ℕ) (s : ℝ) :
    SphericalCode n s ≃ MetricCodes.SphericalCode n s where
  toFun := SphericalCode.toCodes
  invFun := SphericalCode.ofCodes
  left_inv := by
    intro C
    apply sphericalCode_ext_metriccodes2_d60650ef
    change (C.toCodes.points.map (spherePointEmbedding_metriccodes2_d60650ef n)) = C.points
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
      obtain ⟨w, _hw, hwz⟩ := Finset.mem_map.mp hz
      have hwx : (w : Euclidean n) = x :=
        (congrArg Subtype.val hwz).trans hzx
      simpa only [hwx] using w.property
    · intro hx
      let w : {u : Euclidean n // u ∈ C.points} := ⟨x, hx⟩
      let z : MetricCodes.Sphere n :=
        attachedSphereEmbedding_metriccodes2_d60650ef C w
      exact Finset.mem_map.mpr ⟨z,
        Finset.mem_map.mpr ⟨w, Finset.mem_attach _ _, rfl⟩, rfl⟩
  right_inv := by
    intro C
    apply codesSphericalCode_ext_metriccodes2_d60650ef
    ext x
    change
      x ∈ (SphericalCode.ofCodes C).points.attach.map
        (attachedSphereEmbedding_metriccodes2_d60650ef (SphericalCode.ofCodes C)) ↔
        x ∈ C.points
    constructor
    · intro hx
      obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hx
      obtain ⟨w, hw, hwz⟩ :=
        Finset.mem_map.mp (show z.1 ∈ (SphericalCode.ofCodes C).points from z.2)
      have hval : (w : Euclidean n) = (z : Euclidean n) := hwz
      have hxw : x = w := by
        apply Subtype.ext
        exact (congrArg Subtype.val hz).symm.trans hval.symm
      simpa [hxw] using hw
    · intro hx
      let z : {u : Euclidean n // u ∈ (SphericalCode.ofCodes C).points} :=
        ⟨(x : Euclidean n), Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
      exact Finset.mem_map.mpr
        ⟨z, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The spherical code number used in the spherical-code argument. -/
def sphericalCodeNumber (n : ℕ) (s : ℝ) : ℕ∞ :=
  ⨆ C : SphericalCode n s, (C.points.card : ℕ∞)

theorem sphericalCode_card_le_number {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    (C.points.card : ℕ∞) ≤ sphericalCodeNumber n s := by
  exact le_iSup (fun D : SphericalCode n s => (D.points.card : ℕ∞)) C

theorem sphericalCodeNumber_eq_codes (n : ℕ) (s : ℝ) :
    sphericalCodeNumber n s = MetricCodes.sphericalCodeNumber n s := by
  unfold sphericalCodeNumber MetricCodes.sphericalCodeNumber
  exact (sphericalCodeEquiv n s).iSup_congr
    (fun C => congrArg (fun k : ℕ => (k : ℕ∞)) C.toCodes_card)

theorem sphericalCodeNumber_lt_top {n : ℕ} {s : ℝ} (hs : s < 1) :
    sphericalCodeNumber n s < ⊤ := by
  rw [sphericalCodeNumber_eq_codes]
  exact MetricCodes.sphericalCodeNumber_lt_top hs

theorem exists_maximal_sphericalCode {n : ℕ} {s : ℝ} (hs : s < 1) :
    ∃ C : SphericalCode n s,
      (C.points.card : ℕ∞) = sphericalCodeNumber n s := by
  obtain ⟨C, hC⟩ := MetricCodes.exists_maximal_sphericalCode hs
  refine ⟨SphericalCode.ofCodes C, ?_⟩
  simpa only [SphericalCode.ofCodes_card, sphericalCodeNumber_eq_codes] using hC

end SpherePacking

end

namespace MetricCodes

namespace Spherical

section

open Filter Topology

namespace MaximalCodeBounds

theorem exists_sphericalCode_card_eq_number_toNat
    {n : ℕ} {s : ℝ} (hs : s < 1) :
    ∃ C : SpherePacking.SphericalCode n s,
      C.points.card = (SpherePacking.sphericalCodeNumber n s).toNat := by
  obtain ⟨C, hC⟩ := SpherePacking.exists_maximal_sphericalCode hs
  refine ⟨C, ?_⟩
  simpa only [ENat.toNat_natCast] using congrArg ENat.toNat hC

theorem sphericalCodeNumber_toNat_lt_iff
    {n : ℕ} {s B : ℝ} (hs : s < 1) :
    ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) < B ↔
      ∀ C : SpherePacking.SphericalCode n s, (C.points.card : ℝ) < B := by
  constructor
  · intro h C
    have hnumber :
        ((SpherePacking.sphericalCodeNumber n s).toNat : ℕ∞) =
          SpherePacking.sphericalCodeNumber n s :=
      ENat.natCast_toNat (ne_of_lt (SpherePacking.sphericalCodeNumber_lt_top hs))
    have hcard : C.points.card ≤
        (SpherePacking.sphericalCodeNumber n s).toNat := by
      exact_mod_cast hnumber.symm ▸ SpherePacking.sphericalCode_card_le_number C
    exact lt_of_le_of_lt (by exact_mod_cast hcard) h
  · intro h
    obtain ⟨C, hC⟩ := exists_sphericalCode_card_eq_number_toNat hs
    simpa only [hC] using h C

end MaximalCodeBounds

end

section

open Filter Topology
open scoped Topology

namespace HigherHierarchy

theorem exists_oneRow_certificate_better_than_levelZero
    {s a : ℝ} (ha : 0 < a)
    (hspectral : s < 2 * spectralAtom a) :
    ∃ A b : ℝ, 0 < b ∧ b < A ∧
      s < 2 * MetricCodes.Gamma A b ∧
      MetricCodes.sphericalEntropy A - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy a := by
  have hgamma := MetricCodes.Spherical.eventually_Gamma_improvement ha
  have hentropy := MetricCodes.Spherical.eventually_sphericalEntropy_improvement ha
  have hclassical : MetricCodes.Gamma a 0 = spectralAtom a := by
    simpa only [spectralAtom] using (MetricCodes.Spherical.Gamma_zero ha)
  have hslope := MetricCodes.Spherical.sphericalImprovementSlope_gt_one ha
  have hgood :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < b ∧
          b < MetricCodes.Spherical.sphericalImprovementPath a b ∧
          s < 2 * MetricCodes.Gamma
            (MetricCodes.Spherical.sphericalImprovementPath a b) b ∧
          MetricCodes.sphericalEntropy
              (MetricCodes.Spherical.sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hγ hbentropy (hb : 0 < b)
    refine ⟨hb, ?_, ?_, hbentropy⟩
    · unfold MetricCodes.Spherical.sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hslope) hb]
    · rw [hclassical] at hγ
      nlinarith
  obtain ⟨b, hb, hba, hgap, hcost⟩ := hgood.exists
  exact ⟨MetricCodes.Spherical.sphericalImprovementPath a b,
    b, hb, hba, hgap, hcost⟩

theorem eventually_sphericalCode_card_lt_levelZero
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (a : Fin 1 → ℝ) (b : Fin 0 → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s < 2 * Gamma a b) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) <
        (2 : ℝ) ^ (Phi a b * (n : ℝ)) := by
  have ha_nonneg : 0 ≤ a 0 := hinterlacing.ambient_nonneg 0
  have ha : 0 < a 0 := by
    by_contra hnot
    have hazero : a 0 = 0 := le_antisymm (le_of_not_gt hnot) ha_nonneg
    rw [Gamma_zero, hazero] at hspectral
    norm_num [spectralAtom] at hspectral
    linarith
  rw [Gamma_zero] at hspectral
  obtain ⟨A, B, hB, hBA, hgap, hcost⟩ :=
    exists_oneRow_certificate_better_than_levelZero ha hspectral
  rw [Phi_zero]
  exact MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
    hs' hB hBA hgap hcost

end HigherHierarchy

end

section


open Filter Topology
open scoped Topology

theorem zero_fibre_spectral_iff_classicalThreshold_lt
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1) (ha : 0 < a) :
    s < 2 * MetricCodes.Gamma a 0 ↔ MetricCodes.classicalThreshold s < a := by
  have hvariance : 0 < a * (1 + a) := by positivity
  have hroot : 0 < Real.sqrt (a * (1 + a)) :=
    Real.sqrt_pos.mpr hvariance
  have hroot_sq := Real.sq_sqrt hvariance.le
  have hradical : 0 < 1 - s ^ 2 := by nlinarith
  have hclassical : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.mpr hradical
  have hclassical_sq := Real.sq_sqrt hradical.le
  have hlinear : 0 < 1 + 2 * a := by positivity
  rw [Gamma_zero ha]
  have hleft :
      s < 2 * (Real.sqrt (a * (1 + a)) / (1 + 2 * a)) ↔
        s * (1 + 2 * a) < 2 * Real.sqrt (a * (1 + a)) := by
    rw [← mul_div_assoc, lt_div_iff₀ hlinear]
  rw [hleft]
  have hsquares :
      (Real.sqrt (1 - s ^ 2) * (1 + 2 * a)) ^ 2 - 1 =
        (2 * Real.sqrt (a * (1 + a))) ^ 2 -
          (s * (1 + 2 * a)) ^ 2 := by
    rw [mul_pow, hclassical_sq, mul_pow, hroot_sq]
    ring
  have hcompare :
      s * (1 + 2 * a) < 2 * Real.sqrt (a * (1 + a)) ↔
        1 < Real.sqrt (1 - s ^ 2) * (1 + 2 * a) := by
    constructor
    · intro h
      have hsq := (sq_lt_sq₀
        (mul_nonneg hs.le hlinear.le)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hroot.le)).mpr h
      apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hclassical.le hlinear.le)).mp
      nlinarith [hsquares]
    · intro h
      have hsq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hclassical.le hlinear.le)).mpr h
      apply (sq_lt_sq₀
        (mul_nonneg hs.le hlinear.le)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hroot.le)).mp
      nlinarith [hsquares]
  rw [hcompare]
  unfold MetricCodes.classicalThreshold
  constructor
  · intro h
    have hdiv : 1 / Real.sqrt (1 - s ^ 2) < 1 + 2 * a := by
      apply (div_lt_iff₀ hclassical).mpr
      nlinarith
    linarith
  · intro h
    have hdiv : 1 / Real.sqrt (1 - s ^ 2) < 1 + 2 * a := by
      linarith
    have hmul := (div_lt_iff₀ hclassical).mp hdiv
    nlinarith

theorem boundaryQuadratic_pos_iff_classicalThreshold_lt
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1) (ha : 0 < a) :
    0 < boundaryQuadratic s a ↔ MetricCodes.classicalThreshold s < a := by
  have hzero := spectral_iff_quadratic (s := s) (a := a) (b := 0) ha
  simp only [zero_mul] at hzero
  exact hzero.symm.trans
    (zero_fibre_spectral_iff_classicalThreshold_lt hs hs' ha)

theorem boundaryDegree_lt_longitudinal
    {s a : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hquadratic : 0 < boundaryQuadratic s a) :
    boundaryDegree s a < a := by
  have hb := boundaryDegree_pos hquadratic
  have heq := boundaryDegree_mul_one_add hquadratic.le
  have hroot : 0 < Real.sqrt (a * (1 + a)) := by positivity
  have hstrict : boundaryQuadratic s a < a * (1 + a) := by
    unfold boundaryQuadratic
    have hterm : 0 < (s / 2) * (1 + 2 * a) *
        Real.sqrt (a * (1 + a)) := by positivity
    linarith
  nlinarith [sq_nonneg (a - boundaryDegree s a)]

theorem feasible_iff_boundary
    {s a b : ℝ} (hs : 0 < s) (hs' : s < 1) :
    Feasible s a b ↔
      MetricCodes.classicalThreshold s < a ∧
        0 < b ∧ b < boundaryDegree s a := by
  constructor
  · rintro ⟨hb, hba, hspectral⟩
    have ha : 0 < a := hb.trans hba
    have hquadratic : 0 < boundaryQuadratic s a := by
      have hstrict := (spectral_iff_quadratic ha).mp hspectral
      nlinarith [mul_pos hb (by linarith : 0 < 1 + b)]
    exact ⟨(boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mp hquadratic, hb,
      (quadratic_iff_boundaryDegree hb.le hquadratic).mp
        ((spectral_iff_quadratic ha).mp hspectral)⟩
  · rintro ⟨hthreshold, hb, hboundary⟩
    have hthreshold_pos := MetricCodes.classicalThreshold_pos hs hs'
    have ha : 0 < a := hthreshold_pos.trans hthreshold
    have hquadratic :=
      (boundaryQuadratic_pos_iff_classicalThreshold_lt
        hs hs' ha).mpr hthreshold
    have hba : b < a := hboundary.trans
      (boundaryDegree_lt_longitudinal hs ha hquadratic)
    refine ⟨hb, hba, (spectral_iff_quadratic ha).mpr ?_⟩
    exact (quadratic_iff_boundaryDegree hb.le hquadratic).mpr
      hboundary

/-- The boundary rate set used in the spherical-code argument. -/
def boundaryRateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
    r = MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy (boundaryDegree s a)}

/-- The boundary variational rate used in the spherical-code argument. -/
def boundaryVariationalRate (s : ℝ) : ℝ :=
  sInf (boundaryRateSet s)

theorem boundaryRateSet_bddBelow
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    BddBelow (boundaryRateSet s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, hthreshold, rfl⟩
  have ha := (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  exact sphericalEntropy_sub_nonneg
    (boundaryDegree_pos hquadratic).le
    (boundaryDegree_lt_longitudinal hs ha hquadratic).le

theorem variationalRate_le_boundaryObjective
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hthreshold : MetricCodes.classicalThreshold s < a) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy (boundaryDegree s a) := by
  have ha := (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  have hpositive := boundaryDegree_pos hquadratic
  let endpoint : ℝ := boundaryDegree s a
  let F : Filter ℝ := 𝓝[<] endpoint
  have hlimit :
      Tendsto
        (fun b : ℝ =>
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b)
        F (𝓝 (MetricCodes.sphericalEntropy a -
          MetricCodes.sphericalEntropy endpoint)) := by
    have hcontinuous : Continuous
        (fun b : ℝ =>
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b) :=
      continuous_const.sub sphericalEntropy_continuous
    exact hcontinuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hbound :
      ∀ᶠ b : ℝ in F,
        variationalRate s ≤
          MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
    have hpos : ∀ᶠ b : ℝ in F, 0 < b :=
      nhdsWithin_le_nhds (lt_mem_nhds hpositive)
    filter_upwards [hpos, self_mem_nhdsWithin]
      with b hb (hupper : b < endpoint)
    apply variationalRate_le_of_feasible
    apply (feasible_iff_boundary hs hs').mpr
    exact ⟨hthreshold, hb, hupper⟩
  exact ge_of_tendsto hlimit hbound

theorem variationalRate_eq_boundaryVariationalRate
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    variationalRate s = boundaryVariationalRate s := by
  have hnonempty := rateSet_nonempty_of_interior hs hs'
  apply le_antisymm
  · unfold boundaryVariationalRate
    apply le_csInf
    · obtain ⟨r, a, b, hfeasible, hr⟩ := hnonempty
      have hdomain := (feasible_iff_boundary hs hs').mp hfeasible
      exact ⟨MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy (boundaryDegree s a),
        a, hdomain.1, rfl⟩
    · rintro r ⟨a, hthreshold, rfl⟩
      exact variationalRate_le_boundaryObjective hs hs' hthreshold
  · unfold variationalRate
    apply le_csInf hnonempty
    rintro r ⟨a, b, hfeasible, rfl⟩
    have hdomain := (feasible_iff_boundary hs hs').mp hfeasible
    have ha : 0 < a := hfeasible.1.trans hfeasible.2.1
    have hquadratic :=
      (boundaryQuadratic_pos_iff_classicalThreshold_lt
        hs hs' ha).mpr hdomain.1
    calc
      boundaryVariationalRate s ≤
          MetricCodes.sphericalEntropy a -
            MetricCodes.sphericalEntropy (boundaryDegree s a) := by
        exact csInf_le (boundaryRateSet_bddBelow hs hs')
          ⟨a, hdomain.1, rfl⟩
      _ ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
        apply sub_le_sub_left
        exact sphericalEntropy_strictMono.monotoneOn
          hdomain.2.1.le
          (boundaryDegree_pos hquadratic).le
          hdomain.2.2.le

end

section

open Filter Topology
open scoped Topology

theorem sphericalEntropy_upper_logb_add
    {a : ℝ} (ha : 0 < a) :
    MetricCodes.sphericalEntropy a ≤
      Real.logb 2 (1 + a) + 1 / Real.log 2 := by
  rw [sphericalEntropy_eq_logb_add_mul_logb ha]
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < (1 + a) / a by positivity)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hone : a * (((1 + a) / a) - 1) = 1 := by
    field_simp
    ring
  have hupper : a * Real.log ((1 + a) / a) ≤ 1 := by
    calc
      a * Real.log ((1 + a) / a) ≤
          a * (((1 + a) / a) - 1) :=
        mul_le_mul_of_nonneg_left hlog ha.le
      _ = 1 := hone
  unfold Real.logb
  have hfraction :
      a * (Real.log ((1 + a) / a) / Real.log 2) ≤
        1 / Real.log 2 := by
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hlogtwo).mpr hupper
  linarith

end

section

open scoped InnerProductSpace Topology

namespace SidelnikovLocalization

/-- The slice cost used in the spherical-code argument. -/
def sliceCost (s t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 ((1 - t) / (1 - s))

theorem sliceCost_nonneg {s t : ℝ}
    (hts : t ≤ s) (hs : s < 1) :
    0 ≤ sliceCost s t := by
  unfold sliceCost
  apply mul_nonneg (by norm_num)
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact (le_div_iff₀ (by linarith)).2 (by linarith)

@[simp] theorem sliceCost_self {s : ℝ} (hs : s < 1) :
    sliceCost s s = 0 := by
  unfold sliceCost
  rw [div_self (by linarith : 1 - s ≠ 0)]
  simp only [one_div, Real.logb_one, mul_zero]

/-- The localized envelope used in the spherical-code argument. -/
def localizedEnvelope (κ : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf ((fun t => κ t + sliceCost s t) '' Set.Icc 0 s)

theorem localizedEnvelope_bddBelow {κ : ℝ → ℝ} {s : ℝ}
    (hs : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t) :
    BddBelow ((fun t => κ t + sliceCost s t) '' Set.Icc 0 s) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact add_nonneg (hκ t ht) (sliceCost_nonneg ht.2 hs)

theorem localizedEnvelope_le {κ : ℝ → ℝ} {s t : ℝ}
    (hs : s < 1) (ht : t ∈ Set.Icc (0 : ℝ) s)
    (hκ : ∀ x ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ x) :
    localizedEnvelope κ s ≤ κ t + sliceCost s t := by
  exact csInf_le (localizedEnvelope_bddBelow hs hκ)
    ⟨t, ht, rfl⟩

end SidelnikovLocalization

end

namespace HigherHierarchy

section

open Filter Topology
open scoped BigOperators Topology

private def appendAmbient {r : ℕ} (a : Fin (r + 1) → ℝ) : Fin (r + 2) → ℝ :=
  Fin.snoc a 0

private def appendStabilizer {r : ℕ} (b : Fin r → ℝ) (ε : ℝ) : Fin (r + 1) → ℝ :=
  Fin.snoc b ε

theorem interlacing_append {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε < a (Fin.last r)) :
    Interlacing (appendAmbient a) (appendStabilizer b ε) := by
  constructor
  · simp only [appendAmbient, Fin.snoc_last, Std.le_refl]
  · intro i
    induction i using Fin.lastCases with
    | last =>
        simpa only [appendAmbient, Fin.snoc_castSucc, appendStabilizer, Fin.snoc_last, gt_iff_lt,
          Fin.succ_last, Nat.succ_eq_add_one] using ⟨hεa, hε⟩
    | cast i =>
        simpa only [appendAmbient, Fin.snoc_castSucc, appendStabilizer, gt_iff_lt,
          ← Fin.castSucc_succ] using h.2 i

theorem lagrangeNumerator_append_castSucc {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ε : ℝ) (i : Fin (r + 1)) :
    lagrangeNumerator (appendAmbient a) (appendStabilizer b ε) i.castSucc =
      lagrangeNumerator a b i *
        (((a i) * (1 + (a i))) - (ε * (1 + ε))) := by
  unfold lagrangeNumerator appendAmbient appendStabilizer
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem lagrangeDenominator_append_castSucc {r : ℕ}
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    lagrangeDenominator (appendAmbient a) i.castSucc =
      lagrangeDenominator a i * ((a i) * (1 + (a i))) := by
  unfold lagrangeDenominator appendAmbient
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.castSucc_succAbove_castSucc,
    Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i), Fin.snoc_last, add_zero, mul_one, sub_zero]

theorem lagrangeWeight_append_castSucc {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    (ε : ℝ) (i : Fin (r + 1)) :
    lagrangeWeight (appendAmbient a) (appendStabilizer b ε) i.castSucc =
      lagrangeWeight a b i *
        (1 - (ε * (1 + ε)) / ((a i) * (1 + (a i)))) := by
  have hai : 0 < a i :=
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hquad : ((a i) * (1 + (a i))) ≠ 0 := by
    positivity
  have hden : lagrangeDenominator a i ≠ 0 :=
    h.lagrangeDenominator_ne_zero i
  unfold lagrangeWeight
  rw [lagrangeNumerator_append_castSucc,
    lagrangeDenominator_append_castSucc]
  field_simp [hquad, hden]

private def appendSpectralLoss {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i * spectralAtom (a i) /
      ((a i) * (1 + (a i)))

theorem Gamma_append {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    (ε : ℝ) :
    Gamma (appendAmbient a) (appendStabilizer b ε) =
      Gamma a b - (ε * (1 + ε)) * appendSpectralLoss a b := by
  unfold Gamma
  rw [Fin.sum_univ_castSucc]
  have hzero : spectralAtom ((appendAmbient a) (Fin.last (r + 1))) = 0 := by
    simp only [spectralAtom, appendAmbient, Fin.snoc_last, add_zero, mul_one,
      Real.sqrt_zero, mul_zero, div_one]
  rw [hzero, mul_zero, add_zero]
  simp_rw [lagrangeWeight_append_castSucc h hlast ε]
  simp only [appendAmbient, Fin.snoc_castSucc]
  unfold appendSpectralLoss
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Phi_append {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) :
    Phi (appendAmbient a) (appendStabilizer b ε) =
      Phi a b - MetricCodes.sphericalEntropy ε := by
  unfold Phi
  calc
    (∑ i : Fin (r + 2), MetricCodes.sphericalEntropy (appendAmbient a i)) -
          ∑ i : Fin (r + 1),
            MetricCodes.sphericalEntropy (appendStabilizer b ε i) =
        ((∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i)) +
          MetricCodes.sphericalEntropy 0) -
          ((∑ i : Fin r, MetricCodes.sphericalEntropy (b i)) +
            MetricCodes.sphericalEntropy ε) := by
              congr 1
              · rw [Fin.sum_univ_castSucc]
                simp only [appendAmbient, Fin.snoc_castSucc, Fin.snoc_last, sphericalEntropy_zero,
                  add_zero]
              · rw [Fin.sum_univ_castSucc]
                simp only [appendStabilizer, Fin.snoc_castSucc, Fin.snoc_last]
    _ = (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i)) -
          (∑ i : Fin r, MetricCodes.sphericalEntropy (b i)) -
            MetricCodes.sphericalEntropy ε := by
              simp only [sphericalEntropy, Finset.sum_sub_distrib, add_zero, Real.logb_one,
                mul_zero, Real.logb_zero, sub_self]
              ring

private def scaleCoordinate (c u : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * c * (u * (1 + u))) - 1) / 2

theorem scaleCoordinate_nonneg {c u : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) : 0 ≤ scaleCoordinate c u := by
  have hx : 0 ≤ (u * (1 + u)) := by
    positivity
  have hrad : 0 ≤ 1 + 4 * c * (u * (1 + u)) := by positivity
  have hsquare := Real.sq_sqrt hrad
  have hsqrt := Real.sqrt_nonneg (1 + 4 * c * (u * (1 + u)))
  unfold scaleCoordinate
  nlinarith [mul_nonneg hc hx]

theorem quadraticCoordinate_scaleCoordinate {c u : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) :
    ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) =
      c * (u * (1 + u)) := by
  have hx : 0 ≤ (u * (1 + u)) := by
    positivity
  have hrad : 0 ≤ 1 + 4 * c * (u * (1 + u)) := by positivity
  have hsquare := Real.sq_sqrt hrad
  unfold scaleCoordinate at *
  nlinarith

@[simp] theorem scaleCoordinate_one {u : ℝ} (hu : 0 ≤ u) :
    scaleCoordinate 1 u = u := by
  apply quadraticCoordinate_strictMonoOn.injOn
    (scaleCoordinate_nonneg (by norm_num) hu) hu
  simpa only [one_mul] using quadraticCoordinate_scaleCoordinate (by norm_num : (0 : ℝ) ≤ 1) hu

@[simp] theorem scaleCoordinate_zero (c : ℝ) : scaleCoordinate c 0 = 0 := by
  simp only [scaleCoordinate, add_zero, mul_one, mul_zero, Real.sqrt_one,
    sub_self, zero_div]

theorem scaleCoordinate_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (scaleCoordinate c) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  have hquad : (u * (1 + u)) < (v * (1 + v)) :=
    quadraticCoordinate_strictMonoOn hu hv huv
  have hscaled :
      ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) <
        ((scaleCoordinate c v) * (1 + (scaleCoordinate c v))) := by
    rw [quadraticCoordinate_scaleCoordinate hc.le hu,
      quadraticCoordinate_scaleCoordinate hc.le hv]
    exact mul_lt_mul_of_pos_left hquad hc
  by_contra hnot
  have hrev : scaleCoordinate c v ≤ scaleCoordinate c u := le_of_not_gt hnot
  have hmono := quadraticCoordinate_strictMonoOn.monotoneOn
    (scaleCoordinate_nonneg hc.le hv)
    (scaleCoordinate_nonneg hc.le hu) hrev
  exact (not_le_of_gt hscaled) hmono

theorem scaleCoordinate_pos {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    0 < scaleCoordinate c u := by
  simpa only [scaleCoordinate_zero] using
    scaleCoordinate_strictMonoOn hc (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show u ∈ Set.Ici 0 from
      hu.le) hu

private def scaleAmbient {r : ℕ} (c : ℝ) (a : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun i => scaleCoordinate c (a i)

private def scaleStabilizer {r : ℕ} (c : ℝ) (b : Fin r → ℝ) : Fin r → ℝ :=
  fun i => scaleCoordinate c (b i)

theorem Interlacing.scale {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c) :
    Interlacing (scaleAmbient c a) (scaleStabilizer c b) := by
  constructor
  · exact scaleCoordinate_nonneg hc.le (h.ambient_nonneg _)
  · intro i
    constructor
    · exact scaleCoordinate_strictMonoOn hc
        (h.stabilizer_pos i).le
        (h.ambient_nonneg i.castSucc) (h.2 i).1
    · exact scaleCoordinate_strictMonoOn hc
        (h.ambient_nonneg i.succ)
        (h.stabilizer_pos i).le (h.2 i).2

theorem lagrangeWeight_scale {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c)
    (i : Fin (r + 1)) :
    lagrangeWeight (scaleAmbient c a) (scaleStabilizer c b) i =
      lagrangeWeight a b i := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
    scaleAmbient scaleStabilizer
  rw [← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [quadraticCoordinate_scaleCoordinate hc.le (h.ambient_nonneg i),
    quadraticCoordinate_scaleCoordinate hc.le (h.stabilizer_pos j).le,
    quadraticCoordinate_scaleCoordinate hc.le
      (h.ambient_nonneg (i.succAbove j))]
  field_simp [hc.ne']

theorem spectralAtom_sq {u : ℝ} (hu : 0 ≤ u) :
    spectralAtom u ^ 2 =
      (u * (1 + u)) / (1 + 4 * (u * (1 + u))) := by
  have hrad : 0 ≤ (u * (1 + u)) := by
    positivity
  have hlin : 0 < 1 + 2 * u := by positivity
  have hsquare := Real.sq_sqrt hrad
  unfold spectralAtom
  rw [div_pow, hsquare]
  field_simp [hlin.ne']
  ring

theorem spectralAtom_strictMonoOn :
    StrictMonoOn spectralAtom (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hquad := quadraticCoordinate_strictMonoOn hu hv huv
  have hqu : 0 ≤ (u * (1 + u)) := by
    positivity
  have hqv : 0 ≤ (v * (1 + v)) := by
    positivity
  have hdenu : 0 < 1 + 4 * (u * (1 + u)) := by positivity
  have hdenv : 0 < 1 + 4 * (v * (1 + v)) := by positivity
  have hsquare : spectralAtom u ^ 2 < spectralAtom v ^ 2 := by
    rw [spectralAtom_sq hu, spectralAtom_sq hv]
    apply (div_lt_div_iff₀ hdenu hdenv).mpr
    nlinarith
  have hnonneg := spectralAtom_nonneg hu
  have hnonneg' := spectralAtom_nonneg hv
  nlinarith

theorem spectralAtom_scale_lt {c u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    spectralAtom u < spectralAtom (scaleCoordinate c u) := by
  have hquad : (u * (1 + u)) <
      ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) := by
    rw [quadraticCoordinate_scaleCoordinate (by linarith) hu.le]
    have hx : 0 < (u * (1 + u)) := by
      positivity
    nlinarith
  have hcoord : u < scaleCoordinate c u := by
    by_contra hnot
    have hrev : scaleCoordinate c u ≤ u := le_of_not_gt hnot
    exact (not_le_of_gt hquad)
      (quadraticCoordinate_strictMonoOn.monotoneOn
        (scaleCoordinate_nonneg (by linarith) hu.le) hu.le hrev)
  exact spectralAtom_strictMonoOn hu.le
    (scaleCoordinate_nonneg (by linarith) hu.le) hcoord

theorem Gamma_scale_gt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    {c : ℝ} (hc : 1 < c) :
    Gamma a b < Gamma (scaleAmbient c a) (scaleStabilizer c b) := by
  unfold Gamma
  apply Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r + 1))).Nonempty)
  intro i _
  rw [lagrangeWeight_scale h (by linarith) i]
  apply mul_lt_mul_of_pos_left _ (h.lagrangeWeight_pos i)
  exact spectralAtom_scale_lt hc
    (hlast.trans_le (h.strictAnti_ambient.antitone i.le_last))

theorem spectralAtom_scale_sub_lower_bound {c u : ℝ}
    (hc : 1 ≤ c) (hc' : c ≤ 2) (hu : 0 ≤ u) :
    (u * (1 + u)) * (c - 1) /
        ((1 + 8 * (u * (1 + u))) *
          (1 + 4 * (u * (1 + u)))) ≤
      spectralAtom (scaleCoordinate c u) - spectralAtom u := by
  let x : ℝ := (u * (1 + u))
  let q : ℝ := spectralAtom u
  let Q : ℝ := spectralAtom (scaleCoordinate c u)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hcpos : 0 < c := by linarith
  have hscale : 0 ≤ scaleCoordinate c u :=
    scaleCoordinate_nonneg hcpos.le hu
  have hsq : Q ^ 2 - q ^ 2 =
      x * (c - 1) / ((1 + 4 * c * x) * (1 + 4 * x)) := by
    dsimp [Q, q]
    rw [spectralAtom_sq hscale, spectralAtom_sq hu,
      quadraticCoordinate_scaleCoordinate hcpos.le hu]
    change c * x / (1 + 4 * (c * x)) - x / (1 + 4 * x) = _
    have hden₁ : 1 + 4 * c * x ≠ 0 := by positivity
    have hden₂ : 1 + 4 * x ≠ 0 := by positivity
    field_simp [hden₁, hden₂]
    ring
  have hqu : 0 ≤ q := spectralAtom_nonneg hu
  have hQ : 0 ≤ Q := spectralAtom_nonneg hscale
  have hqhalf : q < (1 / 2 : ℝ) := spectralAtom_lt_half hu
  have hQhalf : Q < (1 / 2 : ℝ) := spectralAtom_lt_half hscale
  have hqle : q ≤ Q := by
    have hquad : (u * (1 + u)) ≤
        ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) := by
      rw [quadraticCoordinate_scaleCoordinate hcpos.le hu]
      dsimp [x] at hx ⊢
      nlinarith
    by_contra hnot
    have hreverse : Q < q := lt_of_not_ge hnot
    have hreverse' : scaleCoordinate c u < u := by
      by_contra hnot'
      exact (not_le_of_gt hreverse)
        (spectralAtom_strictMonoOn.monotoneOn hu hscale
          (le_of_not_gt hnot'))
    exact (not_le_of_gt (quadraticCoordinate_strictMonoOn hscale hu hreverse'))
      hquad
  have hfactor : Q ^ 2 - q ^ 2 ≤ Q - q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqle)
      (show 0 ≤ 1 - (Q + q) by linarith)]
  have hden₁ : 0 < (1 + 4 * c * x) * (1 + 4 * x) := by positivity
  have hden₂ : 0 < (1 + 8 * x) * (1 + 4 * x) := by positivity
  have hnum : 0 ≤ x * (c - 1) := mul_nonneg hx (sub_nonneg.mpr hc)
  have hdenle :
      (1 + 4 * c * x) * (1 + 4 * x) ≤
        (1 + 8 * x) * (1 + 4 * x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc') hx]
  have hfractions :
      x * (c - 1) / ((1 + 8 * x) * (1 + 4 * x)) ≤
        x * (c - 1) / ((1 + 4 * c * x) * (1 + 4 * x)) := by
    exact (div_le_div_iff₀ hden₂ hden₁).mpr
      (mul_le_mul_of_nonneg_left hdenle hnum)
  dsimp [x, Q, q] at hfractions hfactor hsq ⊢
  linarith

private def scalingGainCoefficient {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i *
      (((a i) * (1 + (a i))) /
        ((1 + 8 * ((a i) * (1 + (a i)))) *
          (1 + 4 * ((a i) * (1 + (a i))))))

theorem scalingGainCoefficient_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    0 < scalingGainCoefficient a b := by
  unfold scalingGainCoefficient
  apply Finset.sum_pos'
  · intro i _
    have hai : 0 < a i :=
      hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
    have hquad : 0 < ((a i) * (1 + (a i))) := by
      positivity
    exact (mul_pos (h.lagrangeWeight_pos i) (by positivity)).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have ha : 0 < a 0 :=
      hlast.trans_le (h.strictAnti_ambient.antitone (Fin.zero_le _))
    have hquad : 0 < ((a 0) * (1 + (a 0))) := by
      positivity
    exact mul_pos (h.lagrangeWeight_pos 0) (by positivity)

theorem Gamma_scale_sub_lower_bound {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ}
    (hc : 1 ≤ c) (hc' : c ≤ 2) :
    (c - 1) * scalingGainCoefficient a b ≤
      Gamma (scaleAmbient c a) (scaleStabilizer c b) - Gamma a b := by
  unfold Gamma scalingGainCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [lagrangeWeight_scale h (by linarith) i]
  have hbound := spectralAtom_scale_sub_lower_bound
    hc hc' (h.ambient_nonneg i)
  have hweighted := mul_le_mul_of_nonneg_left hbound
    (h.lagrangeWeight_nonneg i)
  dsimp [scaleAmbient]
  convert hweighted using 1 <;> ring

private def appendSpectralLossUpper {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i / (2 * ((a i) * (1 + (a i))))

theorem appendSpectralLossUpper_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    0 < appendSpectralLossUpper a b := by
  unfold appendSpectralLossUpper
  apply Finset.sum_pos'
  · intro i _
    have ha : 0 < a i :=
      hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
    have hquad : 0 < ((a i) * (1 + (a i))) := by
      positivity
    exact (div_pos (h.lagrangeWeight_pos i) (by positivity)).le
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have ha : 0 < a 0 :=
      hlast.trans_le (h.strictAnti_ambient.antitone (Fin.zero_le _))
    have hquad : 0 < ((a 0) * (1 + (a 0))) := by
      positivity
    exact div_pos (h.lagrangeWeight_pos 0) (by positivity)

theorem append_scaled_spectralLoss_le {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) :
    ((scaleCoordinate c ε) * (1 + (scaleCoordinate c ε))) *
        appendSpectralLoss (scaleAmbient c a) (scaleStabilizer c b) ≤
      (ε * (1 + ε)) * appendSpectralLossUpper a b := by
  rw [quadraticCoordinate_scaleCoordinate hc.le hε]
  unfold appendSpectralLoss appendSpectralLossUpper
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [lagrangeWeight_scale h hc i]
  dsimp [scaleAmbient]
  rw [quadraticCoordinate_scaleCoordinate hc.le (h.ambient_nonneg i)]
  change c * (ε * (1 + ε)) *
      (lagrangeWeight a b i * spectralAtom (scaleCoordinate c (a i)) /
        (c * ((a i) * (1 + (a i))))) ≤
      (ε * (1 + ε)) *
        (lagrangeWeight a b i / (2 * ((a i) * (1 + (a i)))))
  have hai : 0 < a i :=
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hx : 0 < ((a i) * (1 + (a i))) := by
    positivity
  have he : 0 ≤ (ε * (1 + ε)) := by
    positivity
  have hatom := spectralAtom_lt_half
    (scaleCoordinate_nonneg hc.le hai.le)
  have hweight := h.lagrangeWeight_pos i
  field_simp [hc.ne', hx.ne']
  nlinarith [mul_nonneg he hweight.le,
    mul_nonneg (mul_nonneg he hweight.le)
      (sub_nonneg.mpr hatom.le)]

private def compensatedScalingSlope {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (appendSpectralLossUpper a b + 1) / scalingGainCoefficient a b

theorem compensatedScalingSlope_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    0 < compensatedScalingSlope a b := by
  unfold compensatedScalingSlope
  exact div_pos (by linarith [appendSpectralLossUpper_pos h hlast])
    (scalingGainCoefficient_pos h hlast)

private def compensatedScalingFactor {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) : ℝ :=
  1 + compensatedScalingSlope a b * (ε * (1 + ε))

theorem Gamma_compensated_append_gt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    {ε : ℝ} (hε : 0 < ε)
    (hmoderate : compensatedScalingFactor a b ε ≤ 2) :
    Gamma a b <
      Gamma
        (appendAmbient (scaleAmbient (compensatedScalingFactor a b ε) a))
        (appendStabilizer
          (scaleStabilizer (compensatedScalingFactor a b ε) b)
          (scaleCoordinate (compensatedScalingFactor a b ε) ε)) := by
  let c : ℝ := compensatedScalingFactor a b ε
  let e : ℝ := (ε * (1 + ε))
  let D : ℝ := scalingGainCoefficient a b
  let M : ℝ := appendSpectralLossUpper a b
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hD : 0 < D := scalingGainCoefficient_pos h hlast
  have hM : 0 < M := appendSpectralLossUpper_pos h hlast
  have hslope : 0 < compensatedScalingSlope a b :=
    compensatedScalingSlope_pos h hlast
  have hc : 1 < c := by
    dsimp [c, compensatedScalingFactor]
    nlinarith
  have hscale : Interlacing (scaleAmbient c a) (scaleStabilizer c b) :=
    h.scale (by linarith)
  have hlast' : 0 < scaleAmbient c a (Fin.last r) :=
    scaleCoordinate_pos (by linarith) hlast
  have hgain := Gamma_scale_sub_lower_bound h hc.le hmoderate
  have hloss := append_scaled_spectralLoss_le h hlast
    (show 0 < c by linarith) hε.le
  have hrelation : (c - 1) * D = e * (M + 1) := by
    dsimp [c, D, M, compensatedScalingFactor, compensatedScalingSlope]
    field_simp [(scalingGainCoefficient_pos h hlast).ne']
    ring
  rw [Gamma_append hscale hlast']
  dsimp [c] at hgain hloss hrelation ⊢
  nlinarith

@[simp] theorem compensatedScalingFactor_zero {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    compensatedScalingFactor a b 0 = 1 := by
  simp only [compensatedScalingFactor, add_zero, mul_one, mul_zero]

@[fun_prop] theorem compensatedScalingFactor_differentiableAt_zero {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    DifferentiableAt ℝ (compensatedScalingFactor a b) 0 := by
  unfold compensatedScalingFactor
  fun_prop

theorem scaleCoordinate_compensated_differentiableAt_zero {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    DifferentiableAt ℝ
      (fun ε => scaleCoordinate (compensatedScalingFactor a b ε) u) 0 := by
  have hquad : 0 ≤ (u * (1 + u)) := by
    positivity
  have hinner : DifferentiableAt ℝ
      (fun ε => 1 + 4 * compensatedScalingFactor a b ε * (u * (1 + u)))
      0 := by
    fun_prop
  have hrad :
      1 + 4 * compensatedScalingFactor a b 0 * (u * (1 + u)) ≠ 0 := by
    rw [compensatedScalingFactor_zero]
    positivity
  unfold scaleCoordinate
  exact ((hinner.sqrt hrad).sub_const 1).div_const 2

private def compensatedPhiPath {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) : ℝ :=
  Phi (scaleAmbient (compensatedScalingFactor a b ε) a)
    (scaleStabilizer (compensatedScalingFactor a b ε) b)

@[simp] theorem compensatedPhiPath_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    compensatedPhiPath a b 0 = Phi a b := by
  unfold compensatedPhiPath Phi scaleAmbient scaleStabilizer
  simp_rw [compensatedScalingFactor_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [scaleCoordinate_one (h.ambient_nonneg i)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [scaleCoordinate_one (h.stabilizer_pos i).le]

theorem compensatedPhiPath_differentiableAt_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    DifferentiableAt ℝ (compensatedPhiPath a b) 0 := by
  unfold compensatedPhiPath Phi scaleAmbient scaleStabilizer
  apply DifferentiableAt.sub
  · apply DifferentiableAt.fun_sum
    intro i _
    have hai : 0 < a i :=
      hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
    have hinner := scaleCoordinate_compensated_differentiableAt_zero
      a b hai.le
    have hvalue :
        scaleCoordinate (compensatedScalingFactor a b 0) (a i) = a i := by
      rw [compensatedScalingFactor_zero, scaleCoordinate_one hai.le]
    have houter : DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (scaleCoordinate (compensatedScalingFactor a b 0) (a i)) := by
      rw [hvalue]
      exact (MetricCodes.Spherical.hasDerivAt_sphericalEntropy hai).differentiableAt
    simpa only [Function.comp_def] using houter.comp 0 hinner
  · apply DifferentiableAt.fun_sum
    intro i _
    have hbi := h.stabilizer_pos i
    have hinner := scaleCoordinate_compensated_differentiableAt_zero
      a b hbi.le
    have hvalue :
        scaleCoordinate (compensatedScalingFactor a b 0) (b i) = b i := by
      rw [compensatedScalingFactor_zero, scaleCoordinate_one hbi.le]
    have houter : DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (scaleCoordinate (compensatedScalingFactor a b 0) (b i)) := by
      rw [hvalue]
      exact (MetricCodes.Spherical.hasDerivAt_sphericalEntropy hbi).differentiableAt
    simpa only [Function.comp_def] using houter.comp 0 hinner

theorem eventually_sub_sphericalEntropy_lt_of_differentiable
    {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      f ε - MetricCodes.sphericalEntropy ε < f 0 := by
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ε⁻¹ * (f ε - f 0) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with ε hε
    simpa only [zero_add, smul_eq_mul] using hε
  have hloglim : Tendsto (fun ε : ℝ => -Real.logb 2 ε)
      (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ ε : ℝ in 𝓝[>] 0, M < -Real.logb 2 ε :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with ε hbound hlogε (hε : 0 < ε)
  have hold : f ε - f 0 < ε * M := by
    calc
      f ε - f 0 = ε * (ε⁻¹ * (f ε - f 0)) := by
        field_simp [hε.ne']
      _ < ε * M := mul_lt_mul_of_pos_left hbound hε
  have hnew : ε * M < ε * (-Real.logb 2 ε) :=
    mul_lt_mul_of_pos_left hlogε hε
  have hentropy :=
    MetricCodes.Spherical.neg_mul_logb_le_sphericalEntropy hε.le
  linarith

theorem le_scaleCoordinate_of_one_le {c u : ℝ}
    (hc : 1 ≤ c) (hu : 0 ≤ u) : u ≤ scaleCoordinate c u := by
  have hquad : (u * (1 + u)) ≤
      ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) := by
    rw [quadraticCoordinate_scaleCoordinate (by linarith) hu]
    have hx : 0 ≤ (u * (1 + u)) := by
      positivity
    nlinarith
  by_contra hnot
  have hreverse : scaleCoordinate c u < u := lt_of_not_ge hnot
  exact (not_le_of_gt
    (quadraticCoordinate_strictMonoOn
      (scaleCoordinate_nonneg (by linarith) hu) hu hreverse)) hquad

theorem eventually_Phi_compensated_append_lt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Phi
        (appendAmbient (scaleAmbient (compensatedScalingFactor a b ε) a))
        (appendStabilizer
          (scaleStabilizer (compensatedScalingFactor a b ε) b)
          (scaleCoordinate (compensatedScalingFactor a b ε) ε)) < Phi a b := by
  have hslope := compensatedScalingSlope_pos h hlast
  have hsmall := eventually_sub_sphericalEntropy_lt_of_differentiable
    (compensatedPhiPath_differentiableAt_zero h hlast)
  filter_upwards [hsmall, self_mem_nhdsWithin]
    with ε hεbound (hε : 0 < ε)
  let c : ℝ := compensatedScalingFactor a b ε
  have hquad : 0 < (ε * (1 + ε)) := by
    positivity
  have hc : 1 ≤ c := by
    dsimp [c, compensatedScalingFactor]
    nlinarith
  have hcoordinate : ε ≤ scaleCoordinate c ε :=
    le_scaleCoordinate_of_one_le hc hε.le
  have hentropy :
      MetricCodes.sphericalEntropy ε ≤
        MetricCodes.sphericalEntropy (scaleCoordinate c ε) :=
    MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      hε.le (scaleCoordinate_nonneg (by linarith) hε.le) hcoordinate
  rw [Phi_append]
  change compensatedPhiPath a b ε -
      MetricCodes.sphericalEntropy (scaleCoordinate c ε) < Phi a b
  rw [← compensatedPhiPath_zero h]
  linarith

theorem exists_nextLevel_strict_refinement {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ Gamma a b < Gamma A B ∧ Phi A B < Phi a b := by
  have hfactor : Continuous (compensatedScalingFactor a b) := by
    unfold compensatedScalingFactor
    fun_prop
  have hmoderate :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, compensatedScalingFactor a b ε < 2 := by
    have hnear := hfactor.continuousAt.tendsto.eventually
      (Iio_mem_nhds
        (show compensatedScalingFactor a b 0 < 2 by simp only [compensatedScalingFactor_zero,
                                                      Nat.one_lt_ofNat]))
    exact nhdsWithin_le_nhds hnear
  have hterminal :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < a (Fin.last r) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hlast)
  have hentropy := eventually_Phi_compensated_append_lt h hlast
  have hall :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
          Interlacing A B ∧ Gamma a b < Gamma A B ∧ Phi A B < Phi a b := by
    filter_upwards [hmoderate, hterminal, hentropy, self_mem_nhdsWithin]
      with ε hεtwo hεlast hεentropy (hε : 0 < ε)
    let c : ℝ := compensatedScalingFactor a b ε
    have hc : 0 < c := by
      have hslope := compensatedScalingSlope_pos h hlast
      have hquad : 0 < (ε * (1 + ε)) := by
        positivity
      dsimp [c, compensatedScalingFactor]
      nlinarith
    let A := appendAmbient (scaleAmbient c a)
    let B := appendStabilizer (scaleStabilizer c b) (scaleCoordinate c ε)
    refine ⟨A, B, ?_, ?_, ?_⟩
    · apply interlacing_append (h.scale hc)
      · exact scaleCoordinate_pos hc hε
      · exact scaleCoordinate_strictMonoOn hc hε.le
          (h.ambient_nonneg (Fin.last r)) hεlast
    · exact Gamma_compensated_append_gt h hlast hε hεtwo.le
    · exact hεentropy
  obtain ⟨ε, hε⟩ := hall.exists
  exact hε

theorem Phi_eq_sum_entropy_gaps {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    Phi a b =
      (∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i))) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) := by
  unfold Phi
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_sub_distrib]
  ring

theorem Interlacing.Phi_nonneg_refinement {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      (h.stabilizer_pos i).le (h.2 i).1.le
  · have hmono := MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      (show (0 : ℝ) ∈ Set.Ici 0 by simp only [Set.mem_Ici, Std.le_refl])
      (show a (Fin.last r) ∈ Set.Ici 0 from h.1) h.1
    simpa only [sphericalEntropy, sub_nonneg, ge_iff_le, add_zero, Real.logb_one, mul_zero,
      Real.logb_zero, sub_self] using hmono

private def levelRateSet (r : ℕ) (s : ℝ) : Set ℝ :=
  {R | ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ R = Phi a b}

/-- The level rate used in the spherical-code argument. -/
def levelRate (r : ℕ) (s : ℝ) : ℝ := sInf (levelRateSet r s)

theorem levelRateSet_bddBelow (r : ℕ) (s : ℝ) :
    BddBelow (levelRateSet r s) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨a, b, h, _, rfl⟩
  exact h.Phi_nonneg_refinement

theorem levelRate_le {r : ℕ} {s : ℝ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hspectral : s < 2 * Gamma a b) :
    levelRate r s ≤ Phi a b := by
  exact csInf_le (levelRateSet_bddBelow r s)
    ⟨a, b, h, hspectral, rfl⟩

theorem classical_le_levelRate_zero {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) ≤
      levelRate 0 s := by
  have ha₀ : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  let a : Fin 1 → ℝ := fun _ => MetricCodes.classicalThreshold s + 1
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero ha₀] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  have hgap : s < 2 * Gamma a b := by
    rw [Gamma_zero]
    have hmono := spectralAtom_strictMonoOn ha₀.le
      (show 0 ≤ a 0 by dsimp [a]; linarith)
      (show MetricCodes.classicalThreshold s < a 0 by dsimp [a]; linarith)
    linarith
  have hnonempty : (levelRateSet 0 s).Nonempty :=
    ⟨Phi a b, a, b, ha, hgap, rfl⟩
  unfold levelRate
  apply le_csInf hnonempty
  rintro R ⟨A, B, hA, hgapA, rfl⟩
  rw [Gamma_zero] at hgapA
  rw [Phi_zero]
  have hAnonneg : 0 ≤ A 0 := hA.ambient_nonneg 0
  have hstrict : MetricCodes.classicalThreshold s < A 0 := by
    by_contra hnot
    have hle : A 0 ≤ MetricCodes.classicalThreshold s := le_of_not_gt hnot
    have hmono := spectralAtom_strictMonoOn.monotoneOn
      hAnonneg ha₀.le hle
    linarith
  exact (MetricCodes.Spherical.sphericalEntropy_strictMono
    ha₀.le hAnonneg hstrict).le

theorem localizedEnvelope_lt_of_minimizer
    {κ κ' : ℝ → ℝ} {s t : ℝ}
    (hs : s < 1) (ht : t ∈ Set.Icc (0 : ℝ) s)
    (hκ' : ∀ x ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ' x)
    (hmin : MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
      κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : κ' t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  calc
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s ≤
        κ' t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t :=
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_le hs ht hκ'
    _ < κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
      linarith
    _ = MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s :=
      hmin.symm

private def openingAmbient {r : ℕ}
    (a : Fin (r + 1) → ℝ) (x z : ℝ) : Fin (r + 1) → ℝ :=
  Function.update
    (Function.update a 0 (a 0 - x)) (Fin.last r) z

@[simp] theorem openingAmbient_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ}
    (hzero : a (Fin.last r) = 0) : openingAmbient a 0 0 = a := by
  unfold openingAmbient
  simp only [sub_zero, Function.update_eq_self, Function.update_eq_self_iff, hzero]

theorem zero_ne_last_of_level_pos {r : ℕ} (hr : 0 < r) :
    (0 : Fin (r + 1)) ≠ Fin.last r := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_last] at hval
  omega

private def ScaledOpeningDerivative (η : ℝ) (f g : ℝ → ℝ) : Prop :=
  f 0 = g 0 ∧ ∃ d : ℝ, HasDerivAt f (η * d) 0 ∧ HasDerivAt g d 0

theorem ScaledOpeningDerivative.const (η k : ℝ) :
    ScaledOpeningDerivative η (fun _ : ℝ => k) (fun _ : ℝ => k) := by
  refine ⟨rfl, 0, ?_, ?_⟩ <;> simpa using hasDerivAt_const (0 : ℝ) k

theorem ScaledOpeningDerivative.add {η : ℝ}
    {f g F G : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F)
    (h' : ScaledOpeningDerivative η g G) :
    ScaledOpeningDerivative η (fun t => f t + g t)
      (fun t => F t + G t) := by
  obtain ⟨hvalue, d, hd, hD⟩ := h
  obtain ⟨hvalue', e, he, hE⟩ := h'
  refine ⟨by simp only [hvalue, hvalue'], d + e, ?_, ?_⟩
  · simpa only [mul_add] using hd.fun_add he
  · exact hD.fun_add hE

theorem ScaledOpeningDerivative.sub {η : ℝ}
    {f g F G : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F)
    (h' : ScaledOpeningDerivative η g G) :
    ScaledOpeningDerivative η (fun t => f t - g t)
      (fun t => F t - G t) := by
  obtain ⟨hvalue, d, hd, hD⟩ := h
  obtain ⟨hvalue', e, he, hE⟩ := h'
  refine ⟨by simp only [hvalue, hvalue'], d - e, ?_, ?_⟩
  · simpa only [mul_sub] using hd.fun_sub he
  · exact hD.fun_sub hE

theorem ScaledOpeningDerivative.mul {η : ℝ}
    {f g F G : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F)
    (h' : ScaledOpeningDerivative η g G) :
    ScaledOpeningDerivative η (fun t => f t * g t)
      (fun t => F t * G t) := by
  obtain ⟨hvalue, d, hd, hD⟩ := h
  obtain ⟨hvalue', e, he, hE⟩ := h'
  refine ⟨by simp only [hvalue, hvalue'], d * G 0 + F 0 * e, ?_, ?_⟩
  · have hmul := hd.fun_mul he
    change HasDerivAt (fun t => f t * g t)
      ((η * d) * g 0 + f 0 * (η * e)) 0 at hmul
    rw [hvalue, hvalue'] at hmul
    convert hmul using 1; first | rfl | ring
  · exact hD.fun_mul hE

theorem ScaledOpeningDerivative.inv {η : ℝ}
    {f F : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F) (hne : F 0 ≠ 0) :
    ScaledOpeningDerivative η (fun t => (f t)⁻¹)
      (fun t => (F t)⁻¹) := by
  obtain ⟨hvalue, d, hd, hD⟩ := h
  have hfne : f 0 ≠ 0 := hvalue.symm ▸ hne
  refine ⟨by change (f 0)⁻¹ = (F 0)⁻¹; rw [hvalue],
    -(d / (F 0) ^ 2), ?_, ?_⟩
  · have hinv := hd.fun_inv hfne
    change HasDerivAt (fun t => (f t)⁻¹)
      (-(η * d) / (f 0) ^ 2) 0 at hinv
    rw [hvalue] at hinv
    convert hinv using 1; first | rfl | ring
  · have hinv := hD.fun_inv hne
    change HasDerivAt (fun t => (F t)⁻¹)
      (-d / (F 0) ^ 2) 0 at hinv
    simpa only [neg_div] using hinv

theorem ScaledOpeningDerivative.div {η : ℝ}
    {f g F G : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F)
    (h' : ScaledOpeningDerivative η g G) (hne : G 0 ≠ 0) :
    ScaledOpeningDerivative η (fun t => f t / g t)
      (fun t => F t / G t) := by
  simpa only [div_eq_mul_inv] using h.mul (h'.inv hne)

theorem ScaledOpeningDerivative.sqrt {η : ℝ}
    {f F : ℝ → ℝ}
    (h : ScaledOpeningDerivative η f F) (hne : F 0 ≠ 0) :
    ScaledOpeningDerivative η (fun t => Real.sqrt (f t))
      (fun t => Real.sqrt (F t)) := by
  obtain ⟨hvalue, d, hd, hD⟩ := h
  have hfne : f 0 ≠ 0 := hvalue.symm ▸ hne
  refine ⟨by change Real.sqrt (f 0) = Real.sqrt (F 0); rw [hvalue],
    d / (2 * Real.sqrt (F 0)), ?_, ?_⟩
  · have hsqrt := (Real.hasDerivAt_sqrt hfne).comp 0 hd
    change HasDerivAt (fun t => Real.sqrt (f t))
      (1 / (2 * Real.sqrt (f 0)) * (η * d)) 0 at hsqrt
    rw [hvalue] at hsqrt
    convert hsqrt using 1; first | rfl | ring
  · have hsqrt := (Real.hasDerivAt_sqrt hne).comp 0 hD
    change HasDerivAt (fun t => Real.sqrt (F t))
      (1 / (2 * Real.sqrt (F 0)) * d) 0 at hsqrt
    convert hsqrt using 1; first | rfl | ring

theorem ScaledOpeningDerivative.finset_sum {ι : Type*} {η : ℝ}
    (s : Finset ι) {f F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ScaledOpeningDerivative η (f i) (F i)) :
    ScaledOpeningDerivative η
      (fun t => ∑ i ∈ s, f i t)
      (fun t => ∑ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ScaledOpeningDerivative.const η 0
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ScaledOpeningDerivative.finset_prod {ι : Type*} {η : ℝ}
    (s : Finset ι) {f F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ScaledOpeningDerivative η (f i) (F i)) :
    ScaledOpeningDerivative η
      (fun t => ∏ i ∈ s, f i t)
      (fun t => ∏ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using ScaledOpeningDerivative.const η 1
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem openingAmbient_scaledDerivative {r : ℕ}
    (a : Fin (r + 1) → ℝ) (η : ℝ) (i : Fin (r + 1)) :
    ScaledOpeningDerivative η
      (fun t => openingAmbient a (η * t) (t ^ 2) i)
      (fun t => openingAmbient a t (t ^ 2) i) := by
  unfold openingAmbient
  simp only [Function.update_apply]
  split_ifs
  · have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      simpa only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_zero, mul_one] using
        (hasDerivAt_id (0 : ℝ)).fun_pow 2
    exact ⟨by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow], 0, by simpa
      using hsq, hsq⟩
  · refine ⟨by simp only [mul_zero, sub_zero], -1, ?_, ?_⟩
    · simpa only [mul_neg, mul_one, id_eq, zero_sub] using
        (hasDerivAt_const (0 : ℝ) (a 0)).fun_sub ((hasDerivAt_id (0 : ℝ)).const_mul η)
    · simpa only [id_eq,
        zero_sub] using (hasDerivAt_const (0 : ℝ) (a 0)).fun_sub (hasDerivAt_id (0 : ℝ))
  · exact ScaledOpeningDerivative.const η (a i)

theorem ScaledOpeningDerivative.quadraticCoordinate {η : ℝ}
    {f F : ℝ → ℝ} (h : ScaledOpeningDerivative η f F) :
    ScaledOpeningDerivative η
      (fun t => ((f t) * (1 + (f t))))
      (fun t => ((F t) * (1 + (F t)))) := by
  simpa only using h.mul ((ScaledOpeningDerivative.const η 1).add h)

theorem ScaledOpeningDerivative.spectralAtom {η : ℝ}
    {f F : ℝ → ℝ} (h : ScaledOpeningDerivative η f F)
    (hpositive : 0 < F 0) :
    ScaledOpeningDerivative η
      (fun t => spectralAtom (f t))
      (fun t => spectralAtom (F t)) := by
  unfold MetricCodes.Spherical.HigherHierarchy.spectralAtom
  have hquad := h.quadraticCoordinate
  have hqpos : (F 0) * (1 + (F 0)) ≠ 0 := by
    positivity
  have hden := (ScaledOpeningDerivative.const η 1).add
    ((ScaledOpeningDerivative.const η 2).mul h)
  have hdenzero : 1 + 2 * F 0 ≠ 0 := by positivity
  simpa only using (hquad.sqrt hqpos).div hden hdenzero

theorem lagrangeWeight_opening_scaledDerivative {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    (η : ℝ) (i : Fin (r + 1)) :
    ScaledOpeningDerivative η
      (fun t => lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b i)
      (fun t => lagrangeWeight (openingAmbient a t (t ^ 2)) b i) := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
  have hnum : ScaledOpeningDerivative η
      (fun t => ∏ j : Fin r,
        (((openingAmbient a (η * t) (t ^ 2) i) * (1 + (openingAmbient a (η * t) (t ^ 2) i))) -
          ((b j) * (1 + (b j)))))
      (fun t => ∏ j : Fin r,
        (((openingAmbient a t (t ^ 2) i) * (1 + (openingAmbient a t (t ^ 2) i))) -
          ((b j) * (1 + (b j))))) := by
    exact ScaledOpeningDerivative.finset_prod Finset.univ fun j _ =>
      (openingAmbient_scaledDerivative a η i).quadraticCoordinate.sub
        (ScaledOpeningDerivative.const η (((b j) * (1 + (b j)))))
  have hden : ScaledOpeningDerivative η
      (fun t => ∏ j : Fin r,
        (((openingAmbient a (η * t) (t ^ 2) i) * (1 + (openingAmbient a (η * t) (t ^ 2) i))) -
          ((openingAmbient a (η * t) (t ^ 2) (i.succAbove j)) *
            (1 + (openingAmbient a (η * t) (t ^ 2) (i.succAbove j))))))
      (fun t => ∏ j : Fin r,
        (((openingAmbient a t (t ^ 2) i) * (1 + (openingAmbient a t (t ^ 2) i))) -
          ((openingAmbient a t (t ^ 2) (i.succAbove j)) *
            (1 + (openingAmbient a t (t ^ 2) (i.succAbove j)))))) := by
    exact ScaledOpeningDerivative.finset_prod Finset.univ fun j _ =>
      (openingAmbient_scaledDerivative a η i).quadraticCoordinate.sub
        (openingAmbient_scaledDerivative a η (i.succAbove j)).quadraticCoordinate
  have hnonzero :
      (∏ j : Fin r,
        (((openingAmbient a 0 0 i) * (1 + (openingAmbient a 0 0 i))) -
          ((openingAmbient a 0 0 (i.succAbove j)) * (1 + (openingAmbient a 0 0 (i.succAbove
            j)))))) ≠ 0 := by
    change lagrangeDenominator (openingAmbient a 0 0) i ≠ 0
    rw [openingAmbient_zero hzero]
    exact h.lagrangeDenominator_ne_zero i
  simpa only using hnum.div hden (by simpa [zero_pow (by norm_num : 2 ≠ 0)] using hnonzero)

private def openingRegularGamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (η t : ℝ) : ℝ :=
  ∑ i : Fin r,
    lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b i.castSucc *
      spectralAtom (openingAmbient a (η * t) (t ^ 2) i.castSucc)

theorem openingRegularGamma_scaledDerivative {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    (η : ℝ) :
    ScaledOpeningDerivative η
      (openingRegularGamma a b η) (openingRegularGamma a b 1) := by
  unfold openingRegularGamma
  simpa only [one_mul] using
    (ScaledOpeningDerivative.finset_sum Finset.univ fun i _ =>
    (lagrangeWeight_opening_scaledDerivative h hzero η i.castSucc).mul
      ((openingAmbient_scaledDerivative a η i.castSucc).spectralAtom
        (by simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          openingAmbient_zero hzero] using
              (h.stabilizer_pos i).trans (h.2 i).1)))

theorem tendsto_spectralAtom_sq_div :
    Tendsto (fun t : ℝ => spectralAtom (t ^ 2) / t)
      (𝓝[>] 0) (nhds 1) := by
  let q : ℝ → ℝ := fun t =>
    Real.sqrt (1 + t ^ 2) / (1 + 2 * t ^ 2)
  have hq : Continuous q := by
    dsimp [q]
    apply Continuous.div₀
    · exact Real.continuous_sqrt.comp
        (continuous_const.add (continuous_id.pow 2))
    · exact continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))
    · intro t
      positivity
  have htend : Tendsto q (𝓝[>] 0) (nhds 1) := by
    convert hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1;
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one,
        mul_zero, one_ne_zero, div_self, q]
  have heq : (fun t : ℝ => spectralAtom (t ^ 2) / t) =ᶠ[𝓝[>] 0] q := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    unfold spectralAtom q
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]
    field_simp [ht.ne']
  exact htend.congr' heq.symm

theorem tendsto_sphericalEntropy_sq_div :
    Tendsto (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2) / t)
      (𝓝[>] 0) (nhds 0) := by
  let f : ℝ → ℝ := fun t =>
    (1 + t ^ 2) * Real.logb 2 (1 + t ^ 2)
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_zero, mul_one] using
      (hasDerivAt_id (0 : ℝ)).fun_pow 2
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := by
    simpa only [hasDerivAt_const_add_iff,
      add_zero] using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_add hsquare
  have hlog : HasDerivAt (fun t : ℝ => Real.logb 2 (1 + t ^ 2)) 0 0 := by
    unfold Real.logb
    have hlogbase : HasDerivAt Real.log 1 (1 + (0 : ℝ) ^ 2) := by
      simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, inv_one] using
        Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have hnatural := hlogbase.comp 0 hinner
    simpa only [Function.comp_apply, mul_zero, zero_div] using hnatural.div_const (Real.log 2)
  have hf : HasDerivAt f 0 0 := by
    dsimp [f]
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.logb_one, mul_zero] using
      hinner.fun_mul hlog
  have hfirst : Tendsto (fun t : ℝ => f t / t)
      (𝓝[>] 0) (nhds 0) := by
    have hslope := hf.tendsto_slope_zero_right
    simpa [f, div_eq_mul_inv, mul_comm, smul_eq_mul] using hslope
  have hsecond : Tendsto (fun t : ℝ => 2 * (t * Real.logb 2 t))
      (𝓝[>] 0) (nhds 0) := by
    have hnatural := Real.continuous_mul_log.continuousAt
      (x := (0 : ℝ))
    have hbase : Tendsto (fun t : ℝ => t * Real.logb 2 t)
        (𝓝[>] 0) (nhds 0) := by
      unfold Real.logb
      have h : Tendsto (fun t : ℝ => (t * Real.log t) / Real.log 2)
          (nhds (0 : ℝ)) (nhds 0) := by
        simpa only [Real.log_zero, mul_zero, zero_div] using hnatural.tendsto.div_const (Real.log 2)
      simpa only [div_eq_mul_inv,
        mul_assoc] using h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    convert hbase.const_mul 2 using 1; simp only [mul_zero]
  have heq : (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2) / t)
      =ᶠ[𝓝[>] 0] (fun t => f t / t - 2 * (t * Real.logb 2 t)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    unfold MetricCodes.sphericalEntropy
    rw [Real.logb_pow]
    dsimp [f]
    field_simp [ht.ne']
  simpa only [sub_self] using (hfirst.sub hsecond).congr' heq.symm

theorem tendsto_opening_entropy_slope {a η : ℝ}
    (ha : 0 < a) :
    Tendsto
      (fun t : ℝ =>
        (MetricCodes.sphericalEntropy (a - η * t) -
          MetricCodes.sphericalEntropy a +
          MetricCodes.sphericalEntropy (t ^ 2)) / t)
      (𝓝[>] 0)
      (nhds (-(η * Real.logb 2 ((1 + a) / a)))) := by
  have hlinear : HasDerivAt (fun t : ℝ => a - η * t) (-η) 0 := by
    simpa only [id_eq, mul_one, zero_sub] using
      (hasDerivAt_const (0 : ℝ) a).fun_sub ((hasDerivAt_id (0 : ℝ)).const_mul η)
  have hbase : HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + a) / a)) (a - η * (0 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using MetricCodes.Spherical.hasDerivAt_sphericalEntropy ha
  have houter := hbase.comp 0 hlinear
  have hfirst : Tendsto
      (fun t : ℝ =>
        (MetricCodes.sphericalEntropy (a - η * t) -
          MetricCodes.sphericalEntropy a) / t)
      (𝓝[>] 0)
      (nhds (-(η * Real.logb 2 ((1 + a) / a)))) := by
    convert houter.tendsto_slope_zero_right using 1 <;>
      simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  have h := hfirst.add tendsto_sphericalEntropy_sq_div
  convert h using 1 <;> simp [add_div]

theorem Gamma_opening_eq_regular_add {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (η t : ℝ) :
    Gamma (openingAmbient a (η * t) (t ^ 2)) b =
      openingRegularGamma a b η t +
        lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b (Fin.last r) *
          spectralAtom (t ^ 2) := by
  unfold Gamma openingRegularGamma
  rw [Fin.sum_univ_castSucc]
  simp only [openingAmbient, ne_eq, Fin.castSucc_ne_last, not_false_eq_true, Function.update_of_ne,
    Function.update_self]

theorem openingRegularGamma_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hzero : a (Fin.last r) = 0) (η : ℝ) :
    openingRegularGamma a b η 0 = Gamma a b := by
  have hsplit := Gamma_opening_eq_regular_add a b η 0
  simpa only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    openingAmbient_zero hzero, spectralAtom, add_zero, mul_one, Real.sqrt_zero,
    div_one] using hsplit.symm

theorem tendsto_opening_terminalWeight {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) (η : ℝ) :
    Tendsto
      (fun t : ℝ =>
        lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b (Fin.last r))
      (𝓝[>] 0)
      (nhds (lagrangeWeight a b (Fin.last r))) := by
  obtain ⟨_, d, hd, _⟩ :=
    lagrangeWeight_opening_scaledDerivative h hzero η (Fin.last r)
  have ht := hd.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    openingAmbient_zero hzero] using ht

theorem tendsto_openingRegularGamma_slope {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) (η : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (openingRegularGamma a b η t - Gamma a b) / t)
      (𝓝[>] 0)
      (nhds (η * deriv (openingRegularGamma a b 1) 0)) := by
  obtain ⟨_, d, hd, hunit⟩ :=
    openingRegularGamma_scaledDerivative h hzero η
  have hdvalue : d = deriv (openingRegularGamma a b 1) 0 :=
    hunit.deriv.symm
  have hslope := hd.tendsto_slope_zero_right
  rw [hdvalue] at hslope
  simpa only [div_eq_mul_inv, mul_comm, zero_add, openingRegularGamma_zero hzero,
    smul_eq_mul] using hslope

theorem tendsto_Gamma_opening_slope {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) (η : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (Gamma (openingAmbient a (η * t) (t ^ 2)) b - Gamma a b) / t)
      (𝓝[>] 0)
      (nhds (η * deriv (openingRegularGamma a b 1) 0 +
        lagrangeWeight a b (Fin.last r))) := by
  have hregular := tendsto_openingRegularGamma_slope h hzero η
  have hterminal :=
    (tendsto_opening_terminalWeight h hzero η).mul
      tendsto_spectralAtom_sq_div
  have hsum := hregular.add hterminal
  have heq :
      (fun t : ℝ =>
        (Gamma (openingAmbient a (η * t) (t ^ 2)) b - Gamma a b) / t)
        =ᶠ[𝓝[>] 0]
      (fun t =>
        (openingRegularGamma a b η t - Gamma a b) / t +
          lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b
            (Fin.last r) * (spectralAtom (t ^ 2) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Gamma_opening_eq_regular_add]
    field_simp [ht.ne']
    ring
  simpa only [mul_one] using hsum.congr' heq.symm

theorem sum_sphericalEntropy_update {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    (∑ j : Fin n, MetricCodes.sphericalEntropy (Function.update a i x j)) =
      (∑ j : Fin n, MetricCodes.sphericalEntropy (a j)) -
        MetricCodes.sphericalEntropy (a i) + MetricCodes.sphericalEntropy x := by
  classical
  have hupdate :
      (fun j : Fin n => MetricCodes.sphericalEntropy (Function.update a i x j)) =
        Function.update (fun j : Fin n => MetricCodes.sphericalEntropy (a j))
          i (MetricCodes.sphericalEntropy x) := by
    funext j
    by_cases hij : j = i <;> simp [hij]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun j => MetricCodes.sphericalEntropy (a j)) (Finset.mem_univ i)
  linarith

theorem Phi_opening_eq {r : ℕ}
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hzero : a (Fin.last r) = 0) (η t : ℝ) :
    Phi (openingAmbient a (η * t) (t ^ 2)) b - Phi a b =
      MetricCodes.sphericalEntropy (a 0 - η * t) -
        MetricCodes.sphericalEntropy (a 0) +
        MetricCodes.sphericalEntropy (t ^ 2) := by
  have hne := zero_ne_last_of_level_pos hr
  unfold Phi openingAmbient
  rw [sum_sphericalEntropy_update, sum_sphericalEntropy_update]
  have hlast :
      Function.update a 0 (a 0 - η * t) (Fin.last r) = 0 := by
    simp only [ne_eq, Ne.symm hne, not_false_eq_true, Function.update_of_ne, hzero]
  rw [hlast]
  simp only [sphericalEntropy, Finset.sum_sub_distrib, add_zero, Real.logb_one, mul_zero,
    Real.logb_zero, sub_self, sub_zero, sub_sub_sub_cancel_right]
  ring

theorem eventually_Phi_opening_lt {r : ℕ}
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Phi (openingAmbient a (η * t) (t ^ 2)) b < Phi a b := by
  let i : Fin r := ⟨0, hr⟩
  have ha : 0 < a 0 := by
    have hi := (h.stabilizer_pos i).trans (h.2 i).1
    simpa [i] using hi
  have hlog : 0 < Real.logb 2 ((1 + a 0) / a 0) := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact (lt_div_iff₀ ha).mpr (by linarith)
  have hnegative : -(η * Real.logb 2 ((1 + a 0) / a 0)) < 0 := by
    exact neg_neg_of_pos (mul_pos hη hlog)
  have hlimit := tendsto_opening_entropy_slope (η := η) ha
  have hevent := hlimit.eventually (gt_mem_nhds hnegative)
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  have hnegative' := (div_lt_iff₀ htpos).mp ht
  have hphi := Phi_opening_eq (b := b) hr hzero η t
  linarith

private def openingContractionSpeed {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  lagrangeWeight a b (Fin.last r) /
    (2 * (|deriv (openingRegularGamma a b 1) 0| + 1))

theorem openingContractionSpeed_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 < openingContractionSpeed a b := by
  unfold openingContractionSpeed
  exact div_pos (h.lagrangeWeight_pos (Fin.last r)) (by positivity)

theorem opening_spectralSlope_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    0 < openingContractionSpeed a b *
        deriv (openingRegularGamma a b 1) 0 +
      lagrangeWeight a b (Fin.last r) := by
  let D : ℝ := deriv (openingRegularGamma a b 1) 0
  let w : ℝ := lagrangeWeight a b (Fin.last r)
  let η : ℝ := openingContractionSpeed a b
  have hw : 0 < w := h.lagrangeWeight_pos (Fin.last r)
  have hη : 0 < η := openingContractionSpeed_pos h
  have hidentity : 2 * η * (|D| + 1) = w := by
    dsimp [η, D, w, openingContractionSpeed]
    field_simp
  have hbound : -|D| ≤ D := neg_abs_le D
  have hηbound := mul_le_mul_of_nonneg_left hbound hη.le
  dsimp [η, D, w] at hidentity hηbound ⊢
  nlinarith [abs_nonneg (deriv (openingRegularGamma a b 1) 0)]

theorem eventually_Gamma_opening_gt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Gamma a b <
        Gamma
          (openingAmbient a (openingContractionSpeed a b * t) (t ^ 2)) b := by
  let η : ℝ := openingContractionSpeed a b
  have hlimit := tendsto_Gamma_opening_slope h hzero η
  have hpositive : 0 < η * deriv (openingRegularGamma a b 1) 0 +
      lagrangeWeight a b (Fin.last r) := opening_spectralSlope_pos h
  have hevent := hlimit.eventually (lt_mem_nhds hpositive)
  filter_upwards [hevent, self_mem_nhdsWithin]
    with t ht (htpos : 0 < t)
  have hdiff := (lt_div_iff₀ htpos).mp ht
  dsimp [η] at hdiff ⊢
  linarith

theorem eventually_opening_interlacing {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    (η : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Interlacing (openingAmbient a (η * t) (t ^ 2)) b := by
  have hcontinuous (i : Fin (r + 1)) :
      Continuous (fun t : ℝ => openingAmbient a (η * t) (t ^ 2) i) := by
    unfold openingAmbient
    simp only [Function.update_apply]
    split_ifs <;> fun_prop
  have htend (i : Fin (r + 1)) :
      Tendsto (fun t : ℝ => openingAmbient a (η * t) (t ^ 2) i)
        (nhds 0) (nhds (a i)) := by
    have hi := (hcontinuous i).continuousAt (x := (0 : ℝ))
    convert hi.tendsto using 1; simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                                  zero_pow, openingAmbient_zero hzero]
  have hpair (i : Fin r) :
      ∀ᶠ t : ℝ in nhds (0 : ℝ),
        b i < openingAmbient a (η * t) (t ^ 2) i.castSucc ∧
          openingAmbient a (η * t) (t ^ 2) i.succ < b i := by
    exact (htend i.castSucc).eventually (lt_mem_nhds (h.2 i).1) |>.and
      ((htend i.succ).eventually (gt_mem_nhds (h.2 i).2))
  have hall : ∀ᶠ t : ℝ in nhds (0 : ℝ), ∀ i : Fin r,
      b i < openingAmbient a (η * t) (t ^ 2) i.castSucc ∧
        openingAmbient a (η * t) (t ^ 2) i.succ < b i :=
    eventually_all.2 hpair
  filter_upwards [nhdsWithin_le_nhds hall] with t ht
  refine ⟨?_, ht⟩
  simp only [openingAmbient, Function.update_self, sq_nonneg]

theorem exists_sameLevel_opening_strict_refinement {r : ℕ}
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) :
    ∃ A : Fin (r + 1) → ℝ,
      0 < A (Fin.last r) ∧ Interlacing A b ∧
        Gamma a b < Gamma A b ∧ Phi A b < Phi a b := by
  let η : ℝ := openingContractionSpeed a b
  have hη : 0 < η := openingContractionSpeed_pos h
  have hspectral := eventually_Gamma_opening_gt h hzero
  have hentropy := eventually_Phi_opening_lt hr h hzero hη
  have hinterlacing := eventually_opening_interlacing h hzero η
  have hgood : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∃ A : Fin (r + 1) → ℝ,
        0 < A (Fin.last r) ∧ Interlacing A b ∧
          Gamma a b < Gamma A b ∧ Phi A b < Phi a b := by
    filter_upwards [hspectral, hentropy, hinterlacing, self_mem_nhdsWithin]
      with t htGamma htPhi htInterlacing (ht : 0 < t)
    refine ⟨openingAmbient a (η * t) (t ^ 2), ?_,
      htInterlacing, htGamma, htPhi⟩
    simp only [openingAmbient, Function.update_self, sq_pos_of_pos ht]
  obtain ⟨t, ht⟩ := hgood.exists
  exact ht

end

section

theorem exists_nextLevel_feasible_lt {r : ℕ} {s : ℝ}
    (hs : 0 < s)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hgap : s < 2 * Gamma a b) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < Phi a b := by
  by_cases hlast : 0 < a (Fin.last r)
  · obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
      exists_nextLevel_strict_refinement h hlast
    exact ⟨A, B, hAB, by linarith, hPhi⟩
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast) (h.ambient_nonneg _)
    cases r with
    | zero =>
        rw [Gamma_zero] at hgap
        have ha : a 0 = 0 := by simpa only [Fin.isValue, Fin.last_zero] using hzero
        simp only [spectralAtom, Fin.isValue, ha, add_zero, mul_one,
          Real.sqrt_zero, mul_zero, div_one] at hgap
        linarith
    | succ r =>
        obtain ⟨A, hlastA, hA, hGammaA, hPhiA⟩ :=
          exists_sameLevel_opening_strict_refinement (Nat.zero_lt_succ r) h hzero
        obtain ⟨C, D, hCD, hGammaC, hPhiC⟩ :=
          exists_nextLevel_strict_refinement hA hlastA
        exact ⟨C, D, hCD, by linarith, lt_trans hPhiC hPhiA⟩

theorem levelRate_nonneg_of_nonempty {r : ℕ} {s : ℝ}
    (h : (levelRateSet r s).Nonempty) :
    0 ≤ levelRate r s := by
  unfold levelRate
  apply le_csInf h
  rintro _ ⟨a, b, hinterlacing, _, rfl⟩
  exact hinterlacing.Phi_nonneg_refinement

theorem levelRate_succ_le_of_feasible {r : ℕ} {s : ℝ}
    (hs : 0 < s) (h : (levelRateSet r s).Nonempty) :
    levelRate (r + 1) s ≤ levelRate r s := by
  unfold levelRate
  apply le_csInf h
  rintro _ ⟨a, b, hinterlacing, hgap, rfl⟩
  obtain ⟨A, B, hAB, hgapAB, hPhi⟩ :=
    exists_nextLevel_feasible_lt hs hinterlacing hgap
  exact (levelRate_le hAB hgapAB).trans hPhi.le

theorem levelRateSet_zero_nonempty_of_interior {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (levelRateSet 0 s).Nonempty := by
  have hthreshold : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  let a : Fin 1 → ℝ := fun _ => MetricCodes.classicalThreshold s + 1
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero hthreshold] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  refine ⟨Phi a b, a, b, ha, ?_, rfl⟩
  rw [Gamma_zero]
  have hmono := spectralAtom_strictMonoOn hthreshold.le
    (show 0 ≤ a 0 by dsimp [a]; linarith)
    (show MetricCodes.classicalThreshold s < a 0 by dsimp [a]; linarith)
  linarith

theorem levelRateSet_nonempty_of_interior (r : ℕ) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (levelRateSet r s).Nonempty := by
  induction r with
  | zero =>
      exact levelRateSet_zero_nonempty_of_interior hs hs'
  | succ r ih =>
      obtain ⟨_, a, b, h, hgap, rfl⟩ := ih
      obtain ⟨A, B, hAB, hgapAB, _⟩ :=
        exists_nextLevel_feasible_lt hs h hgap
      exact ⟨Phi A B, A, B, hAB, hgapAB, rfl⟩

theorem levelRate_succ_le {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    levelRate (r + 1) s ≤ levelRate r s :=
  levelRate_succ_le_of_feasible hs
    (levelRateSet_nonempty_of_interior r hs hs')

theorem levelRate_le_levelRate_zero {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    levelRate r s ≤ levelRate 0 s := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact (levelRate_succ_le hs hs').trans ih

theorem levelRate_mono {r : ℕ} {s t : ℝ}
    (hst : s ≤ t) (ht : 0 < t) (ht' : t < 1) :
    levelRate r s ≤ levelRate r t := by
  unfold levelRate
  apply csInf_le_csInf (levelRateSet_bddBelow r s)
    (levelRateSet_nonempty_of_interior r ht ht')
  rintro _ ⟨a, b, h, hgap, hPhi⟩
  exact ⟨a, b, h, hst.trans_lt hgap, hPhi⟩

theorem levelRate_nonneg_all (r : ℕ) (s : ℝ) : 0 ≤ levelRate r s := by
  by_cases hnonempty : (levelRateSet r s).Nonempty
  · exact levelRate_nonneg_of_nonempty hnonempty
  · have hempty : levelRateSet r s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [levelRate, hempty, Real.sInf_empty, Std.le_refl]

theorem levelRate_nonnegOn_Icc (r : ℕ) (s : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ levelRate r t := by
  intro t _
  exact levelRate_nonneg_all r t

end

section

open Set Filter Topology

theorem exists_localized_minimizer_of_lowerSemicontinuous
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hlsc : LowerSemicontinuousOn
      (fun t => κ t +
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
      (Set.Icc 0 s)) :
    ∃ t ∈ Set.Icc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  obtain ⟨t, ht, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      (Set.nonempty_Icc.mpr hs) isCompact_Icc hlsc
  refine ⟨t, ht, ?_⟩
  unfold MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_antisymm
  · exact csInf_le
      (MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_bddBelow
        hs' hκ)
      ⟨t, ht, rfl⟩
  · apply le_csInf (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs))
    rintro _ ⟨x, hx, rfl⟩
    exact hmin hx

theorem exists_positive_localized_minimizer_of_lowerSemicontinuous
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hlsc : LowerSemicontinuousOn
      (fun t => κ t +
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
      (Set.Icc 0 s))
    (hzero : ∃ u ∈ Set.Icc (0 : ℝ) s,
      κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u <
        κ 0 + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  obtain ⟨t, ht, heq⟩ :=
    exists_localized_minimizer_of_lowerSemicontinuous hs hs' hκ hlsc
  obtain ⟨u, hu, huzero⟩ := hzero
  have htu :
      κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t ≤
        κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u := by
    rw [← heq]
    exact MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_le
      hs' hu hκ
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht.1 with htpos | rfl
    · exact htpos
    · linarith
  exact ⟨t, ⟨htpos, ht.2⟩, heq⟩

theorem sliceCost_sub_zero {s t : ℝ}
    (hs : s < 1) (ht : t < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 =
      (1 / 2 : ℝ) * Real.logb 2 (1 - t) := by
  have hs' : 1 - s ≠ 0 := by linarith
  have ht' : 1 - t ≠ 0 := by linarith
  unfold MetricCodes.Spherical.SidelnikovLocalization.sliceCost
  norm_num only [sub_zero]
  rw [Real.logb_div ht' hs',
    Real.logb_div (by norm_num : (1 : ℝ) ≠ 0) hs']
  simp only [one_div, Real.logb_one, zero_sub, mul_neg, sub_neg_eq_add]
  ring

theorem sliceCost_sub_zero_le_neg_linear {s t : ℝ}
    (hs : s < 1) (ht : t < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 ≤
      -t / (2 * Real.log 2) := by
  rw [sliceCost_sub_zero hs ht]
  have hlog : Real.log (1 - t) ≤ -t := by
    simpa only [sub_sub_cancel_left] using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - t)
  have hbase : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Real.logb
  calc
    (1 / 2 : ℝ) * (Real.log (1 - t) / Real.log 2) =
        Real.log (1 - t) / (2 * Real.log 2) := by
          field_simp
    _ ≤ -t / (2 * Real.log 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).2 hlog

theorem sliceCost_continuousOn {s : ℝ} (hs : s < 1) :
    ContinuousOn
      (MetricCodes.Spherical.SidelnikovLocalization.sliceCost s)
      (Set.Icc (0 : ℝ) s) := by
  intro t ht
  have harg : (1 - t) / (1 - s) ≠ 0 := by
    exact (div_pos (by linarith [ht.2]) (by linarith)).ne'
  unfold MetricCodes.Spherical.SidelnikovLocalization.sliceCost Real.logb
  fun_prop

theorem levelRate_zero_le_squared_entropy_of_spectral {t : ℝ}
    (ht : 0 < t) (hspectral : t < 2 * spectralAtom (t ^ 2)) :
    levelRate 0 t ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
  let a : Fin 1 → ℝ := fun _ => t ^ 2
  let b : Fin 0 → ℝ := Fin.elim0
  have ha : Interlacing a b := by
    constructor
    · dsimp [a]
      positivity
    · intro i
      exact Fin.elim0 i
  calc
    levelRate 0 t ≤ Phi a b :=
      levelRate_le ha (by simpa only [Gamma_zero, a] using hspectral)
    _ = MetricCodes.sphericalEntropy (t ^ 2) := by
      simp only [Phi_zero, a]

theorem eventually_squared_spectralCertificate :
    ∀ᶠ t : ℝ in 𝓝[>] 0, t < 2 * spectralAtom (t ^ 2) := by
  have hratio :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (1 / 2 : ℝ) < spectralAtom (t ^ 2) / t :=
    tendsto_spectralAtom_sq_div.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hratio, self_mem_nhdsWithin] with t hratio (ht : 0 < t)
  have hmul := (lt_div_iff₀ ht).mp hratio
  linarith

theorem eventually_levelRate_zero_le_squared_entropy :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate 0 t ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
  filter_upwards [eventually_squared_spectralCertificate,
    self_mem_nhdsWithin] with t hspec (ht : 0 < t)
  exact levelRate_zero_le_squared_entropy_of_spectral ht hspec

theorem exists_sliceCost_endpoint_improvement_of_smallEntropy
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hzero : κ 0 = 0)
    (hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      κ t ≤ MetricCodes.sphericalEntropy (t ^ 2)) :
    ∃ u ∈ Set.Icc (0 : ℝ) s,
      κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u <
        κ 0 + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 := by
  have hbase : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquarter : 0 < 1 / (4 * Real.log 2) := by positivity
  have hentropy : ∀ᶠ t : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (t ^ 2) / t < 1 / (4 * Real.log 2) :=
    tendsto_sphericalEntropy_sq_div.eventually (Iio_mem_nhds hquarter)
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < s :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hs)
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨t, htpos, htupper, hκ, hent⟩ :=
    (hpositive.and (hupper.and (hsmall.and hentropy))).exists
  refine ⟨t, ⟨htpos.le, htupper.le⟩, ?_⟩
  have hent' : MetricCodes.sphericalEntropy (t ^ 2) <
      t / (4 * Real.log 2) := by
    calc
      MetricCodes.sphericalEntropy (t ^ 2) <
          (1 / (4 * Real.log 2)) * t := (div_lt_iff₀ htpos).mp hent
      _ = t / (4 * Real.log 2) := by ring
  have hcost := sliceCost_sub_zero_le_neg_linear hs' (lt_trans htupper hs')
  have hcost' :
      MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 ≤
        -(t / (2 * Real.log 2)) := by
    simpa only [neg_div] using hcost
  have hlinear : t / (4 * Real.log 2) < t / (2 * Real.log 2) := by
    exact (div_lt_div_iff_of_pos_left htpos (by positivity) (by positivity)).2
      (by nlinarith)
  rw [hzero]
  linarith

theorem exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hzero : κ 0 = 0)
    (hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      κ t ≤ MetricCodes.sphericalEntropy (t ^ 2))
    (hlsc : LowerSemicontinuousOn κ (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  exact exists_positive_localized_minimizer_of_lowerSemicontinuous hs.le hs' hκ
    (hlsc.add (sliceCost_continuousOn hs').lowerSemicontinuousOn)
    (exists_sliceCost_endpoint_improvement_of_smallEntropy hs hs' hzero hsmall)

theorem exists_positive_localized_levelRate_minimizer_of_lsc_and_zero
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ levelRate r t)
    (hzero : levelRate r 0 = 0)
    (hupper : ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate r t ≤ levelRate 0 t)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s =
        levelRate r t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  apply exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    hs hs' hκ hzero _ hlsc
  filter_upwards [hupper, eventually_levelRate_zero_le_squared_entropy]
    with t hrt hzero
  exact hrt.trans hzero

theorem levelRate_at_zero (r : ℕ) :
    levelRate r 0 = 0 := by
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (nhds 0) := by
    simpa only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0)).pow 2).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hentropy : Tendsto
      (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2))
      (𝓝[>] 0) (nhds 0) := by
    simpa only [sphericalEntropy, Function.comp_def, add_zero, Real.logb_one, mul_zero,
      Real.logb_zero,
      sub_self] using (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt (x := (0 :
        ℝ))).tendsto.comp hsquare
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t :=
    self_mem_nhdsWithin
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      levelRate r 0 ≤ MetricCodes.sphericalEntropy (t ^ 2) := by
    filter_upwards [eventually_levelRate_zero_le_squared_entropy,
      hpositive, hupper] with t hclassical ht ht'
    exact (levelRate_mono ht.le ht ht').trans
      ((levelRate_le_levelRate_zero ht ht').trans hclassical)
  exact le_antisymm (ge_of_tendsto hentropy hbound)
    (levelRate_nonneg_all r 0)

theorem exists_positive_localized_levelRate_minimizer_of_lsc
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s =
        levelRate r t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  apply exists_positive_localized_levelRate_minimizer_of_lsc_and_zero
    hs hs' (levelRate_nonnegOn_Icc r s) (levelRate_at_zero r) _ hlsc
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hupper] with t (ht : 0 < t) ht'
  exact levelRate_le_levelRate_zero ht ht'

end

section

open Filter
open scoped BigOperators Topology

namespace CompactificationEntropy

theorem logb_one_add_le_sphericalEntropy {u : ℝ} (hu : 0 ≤ u) :
    Real.logb 2 (1 + u) ≤ MetricCodes.sphericalEntropy u := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num [MetricCodes.sphericalEntropy]
  · rw [MetricCodes.sphericalEntropy_eq_log_add hu]
    have hratio : 1 ≤ (1 + u) / u := by
      apply (le_div_iff₀ hu).2
      linarith
    have hlog : 0 ≤ Real.logb 2 ((1 + u) / u) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio
    nlinarith [mul_nonneg hu.le hlog]

theorem entropy_gap_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    0 ≤ MetricCodes.sphericalEntropy (a i.castSucc) -
      MetricCodes.sphericalEntropy (b i) :=
  MetricCodes.Spherical.sphericalEntropy_sub_nonneg
    (h.stabilizer_pos i).le (h.2 i).1.le

theorem terminal_entropy_le_Phi {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    MetricCodes.sphericalEntropy (a (Fin.last r)) ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  have hsum : 0 ≤ ∑ i : Fin r,
      (MetricCodes.sphericalEntropy (a i.castSucc) -
        MetricCodes.sphericalEntropy (b i)) :=
    Finset.sum_nonneg fun i _ => entropy_gap_nonneg h i
  linarith

theorem entropy_gap_le_Phi {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    MetricCodes.sphericalEntropy (a i.castSucc) -
        MetricCodes.sphericalEntropy (b i) ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  have hterminal : 0 ≤ MetricCodes.sphericalEntropy (a (Fin.last r)) := by
    have hmono := MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      (show (0 : ℝ) ∈ Set.Ici 0 by simp only [Set.mem_Ici, Std.le_refl])
      (show a (Fin.last r) ∈ Set.Ici 0 from h.1) h.1
    simpa only [sphericalEntropy, sub_nonneg, ge_iff_le, add_zero, Real.logb_one, mul_zero,
      Real.logb_zero, sub_self] using hmono
  have hsum :
      MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i) ≤
        ∑ j : Fin r,
          (MetricCodes.sphericalEntropy (a j.castSucc) -
            MetricCodes.sphericalEntropy (b j)) := by
    exact Finset.single_le_sum
      (fun j _ => entropy_gap_nonneg h j) (Finset.mem_univ i)
  linarith

theorem degree_le_rpow_sub_one_of_sphericalEntropy_le
    {u C : ℝ} (hu : 0 ≤ u)
    (hC : MetricCodes.sphericalEntropy u ≤ C) :
    u ≤ (2 : ℝ) ^ C - 1 := by
  have hlog : Real.logb 2 (1 + u) ≤ C :=
    (logb_one_add_le_sphericalEntropy hu).trans hC
  have hpow : 1 + u ≤ (2 : ℝ) ^ C :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by linarith : 0 < 1 + u)).mp hlog
  linarith

theorem terminal_degree_le_rpow_sub_one_of_Phi_le {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {C : ℝ} (hC : Phi a b ≤ C) :
    a (Fin.last r) ≤ (2 : ℝ) ^ C - 1 :=
  degree_le_rpow_sub_one_of_sphericalEntropy_le h.1
    ((terminal_entropy_le_Phi h).trans hC)

theorem shifted_degree_ratio_le_rpow_of_entropy_gap_le
    {a b C : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hC : MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy b ≤ C) :
    (1 + a) / (1 + b) ≤
      (2 : ℝ) ^ (C + 1 / Real.log 2) := by
  have ha : 0 < a := hb.trans_le hba
  have hlower := logb_one_add_le_sphericalEntropy ha.le
  have hupper :=
    MetricCodes.Spherical.sphericalEntropy_upper_logb_add hb
  have hlog :
      Real.logb 2 (1 + a) - Real.logb 2 (1 + b) ≤
        C + 1 / Real.log 2 := by
    linarith
  have hratio :
      Real.logb 2 ((1 + a) / (1 + b)) ≤
        C + 1 / Real.log 2 := by
    rw [Real.logb_div (by positivity) (by positivity)]
    exact hlog
  exact (Real.logb_le_iff_le_rpow
    (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hratio

theorem degree_ratio_lower_bound_of_entropy_gap_le
    {a b C : ℝ} (hb : 1 ≤ b) (hba : b ≤ a)
    (hC : MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy b ≤ C) :
    (2 * (2 : ℝ) ^ (C + 1 / Real.log 2))⁻¹ ≤ b / a := by
  have hb₀ : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have ha : 0 < a := hb₀.trans_le hba
  let D : ℝ := (2 : ℝ) ^ (C + 1 / Real.log 2)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hratio : (1 + a) / (1 + b) ≤ D :=
    shifted_degree_ratio_le_rpow_of_entropy_gap_le hb₀ hba hC
  have hshift : 1 + a ≤ D * (1 + b) :=
    (div_le_iff₀ (by positivity : 0 < 1 + b)).mp hratio
  have hdouble : 1 + b ≤ 2 * b := by linarith
  have hbound : a ≤ (2 * D) * b := by
    have hmul := mul_le_mul_of_nonneg_left hdouble hD.le
    nlinarith
  apply (le_div_iff₀ ha).2
  calc
    (2 * D)⁻¹ * a = a / (2 * D) := by ring
    _ ≤ b := (div_le_iff₀ (by positivity : 0 < 2 * D)).mpr
      (by simpa only [mul_comm] using hbound)

theorem tendsto_sphericalEntropy_sub_logb_one_add :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a - Real.logb 2 (1 + a))
      atTop (𝓝 (1 / Real.log 2)) := by
  have hmain :=
    (Real.tendsto_mul_log_one_add_div_atTop 1).div_const (Real.log 2)
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [MetricCodes.sphericalEntropy_eq_log_add ha]
  have hratio : (1 + a) / a = 1 + 1 / a := by
    field_simp
    ring
  rw [hratio]
  unfold Real.logb
  ring

theorem tendsto_sphericalEntropy_sub_of_ratio
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f atTop atTop)
    (hratio : Tendsto (fun a : ℝ => f a / a) atTop (𝓝 c)) :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy (f a))
      atTop (𝓝 (-Real.logb 2 c)) := by
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hnormalized :
      Tendsto (fun a : ℝ =>
        (a⁻¹ + f a / a) / (a⁻¹ + 1)) atTop (𝓝 c) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext a
      rfl
    · norm_num
  have hshifted :
      Tendsto (fun a : ℝ => (1 + f a) / (1 + a))
        atTop (𝓝 c) := by
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    field_simp
  have hlog : Tendsto
      (fun a : ℝ => Real.logb 2 ((1 + f a) / (1 + a)))
        atTop (𝓝 (Real.logb 2 c)) :=
    (Real.continuousAt_logb hc.ne').tendsto.comp hshifted
  have hfirst := tendsto_sphericalEntropy_sub_logb_one_add
  have hsecond := tendsto_sphericalEntropy_sub_logb_one_add.comp hf
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 c =
        -Real.logb 2 c := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_gt_atTop (0 : ℝ))] with a ha hfa
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring

private def normalizedBoundaryQuadratic (s u : ℝ) : ℝ :=
  1 + u - (s / 2) * (u + 2) * Real.sqrt (1 + u)

private def normalizedBoundaryDegree (s u : ℝ) : ℝ :=
  (Real.sqrt (u ^ 2 + 4 * normalizedBoundaryQuadratic s u) - u) / 2

theorem sqrt_degree_mul_one_add_eq
    {a : ℝ} (ha : 0 < a) :
    Real.sqrt (a * (1 + a)) = a * Real.sqrt (1 + a⁻¹) := by
  have hfactor : a * (1 + a) = a ^ 2 * (1 + a⁻¹) := by
    field_simp
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

theorem boundaryQuadratic_eq_sq_mul_normalized
    {s a : ℝ} (ha : 0 < a) :
    MetricCodes.Spherical.boundaryQuadratic s a =
      a ^ 2 * normalizedBoundaryQuadratic s a⁻¹ := by
  unfold MetricCodes.Spherical.boundaryQuadratic
    normalizedBoundaryQuadratic
  rw [sqrt_degree_mul_one_add_eq ha]
  field_simp
  ring

theorem boundaryDegree_div_eq_normalized
    {s a : ℝ} (ha : 0 < a) :
    MetricCodes.Spherical.boundaryDegree s a / a =
      normalizedBoundaryDegree s a⁻¹ := by
  have hfactor :
      1 + 4 * MetricCodes.Spherical.boundaryQuadratic s a =
        a ^ 2 *
          (a⁻¹ ^ 2 + 4 * normalizedBoundaryQuadratic s a⁻¹) := by
    rw [boundaryQuadratic_eq_sq_mul_normalized ha]
    field_simp
  unfold MetricCodes.Spherical.boundaryDegree normalizedBoundaryDegree
  rw [hfactor, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  field_simp

theorem tendsto_boundaryDegree_div
    {s : ℝ} :
    Tendsto
      (fun a : ℝ => MetricCodes.Spherical.boundaryDegree s a / a)
      atTop (𝓝 (Real.sqrt (1 - s))) := by
  have hcontinuous : Continuous (fun u : ℝ =>
      normalizedBoundaryDegree s u) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    fun_prop
  have hzero : normalizedBoundaryDegree s 0 =
      Real.sqrt (1 - s) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    have hfactor : (0 : ℝ) ^ 2 +
        4 * (1 + 0 - (s / 2) * (0 + 2) * Real.sqrt (1 + 0)) =
          4 * (1 - s) := by
      norm_num
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hlimit := hcontinuous.continuousAt.tendsto.comp hinv
  rw [hzero] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (boundaryDegree_div_eq_normalized ha).symm

theorem tendsto_boundaryDegree_atTop
    {s : ℝ} (hs : s < 1) :
    Tendsto (MetricCodes.Spherical.boundaryDegree s) atTop atTop := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have hproduct := tendsto_id.atTop_mul_pos hroot
    (tendsto_boundaryDegree_div (s := s))
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  field_simp
  simp only [id_eq, mul_comm]

theorem tendsto_entropy_sub_boundaryDegree
    {s : ℝ} (hs' : s < 1) :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree s a))
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s))) := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs')
  have hlimit := tendsto_sphericalEntropy_sub_of_ratio hroot
    (tendsto_boundaryDegree_atTop hs') (tendsto_boundaryDegree_div (s := s))
  have hconstant :
      -Real.logb 2 (Real.sqrt (1 - s)) =
        -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
    unfold Real.logb
    rw [Real.log_sqrt (sub_pos.mpr hs').le]
    ring
  rw [hconstant] at hlimit
  exact hlimit

end CompactificationEntropy

end

section


open Filter Topology
open scoped BigOperators Topology

private def compactifiedHierarchyCoordinate (u : ℝ) : ℝ := (1 + u)⁻¹

theorem compactifiedHierarchyCoordinate_mem_Ioc {u : ℝ} (hu : 0 ≤ u) :
    compactifiedHierarchyCoordinate u ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact (inv_le_one₀ (by linarith)).2 (by linarith)

theorem compactifiedHierarchyCoordinate_mem_Icc {u : ℝ} (hu : 0 ≤ u) :
    compactifiedHierarchyCoordinate u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(compactifiedHierarchyCoordinate_mem_Ioc hu).1.le,
    (compactifiedHierarchyCoordinate_mem_Ioc hu).2⟩

theorem compactifiedHierarchyCoordinate_inv_sub_one (u : ℝ) :
    (compactifiedHierarchyCoordinate u)⁻¹ - 1 = u := by
  simp only [compactifiedHierarchyCoordinate, inv_inv, add_sub_cancel_left]

theorem tendsto_of_compactifiedHierarchyCoordinate_pos
    {f : ℕ → ℝ} {x : ℝ}
    (hx : 0 < x)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds x)) :
    Tendsto f atTop (nhds (x⁻¹ - 1)) := by
  have hi := h.inv₀ hx.ne'
  have hs :
      Tendsto
        (fun k : ℕ => (compactifiedHierarchyCoordinate (f k))⁻¹ - (1 : ℝ))
        atTop (nhds (x⁻¹ - 1)) :=
    hi.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  simpa only [compactifiedHierarchyCoordinate_inv_sub_one] using hs

theorem tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
    {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds 0)) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  let T : ℝ := max M 0
  have hT : 0 < 1 + T := by
    dsimp [T]
    linarith [le_max_right M 0]
  have hevent :
      ∀ᶠ k in atTop,
        compactifiedHierarchyCoordinate (f k) < (1 + T)⁻¹ :=
    (tendsto_order.1 h).2 _ (inv_pos.mpr hT)
  filter_upwards [hevent] with k hk
  have hfk : 0 < 1 + f k := by linarith [hf k]
  have hlt : T < f k := by
    have hinv : (1 + f k)⁻¹ < (1 + T)⁻¹ := hk
    have hraw : 1 + T < 1 + f k :=
      (inv_lt_inv₀ hfk hT).mp hinv
    linarith
  exact (le_max_left M 0).trans hlt.le

theorem compactifiedHierarchyCoordinate_limit_pos_of_bddAbove
    {f : ℕ → ℝ} {x C : ℝ}
    (hf : ∀ k, 0 ≤ f k)
    (hC : ∀ k, f k ≤ C)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds x)) :
    0 < x := by
  have hC₀ : 0 ≤ C := (hf 0).trans (hC 0)
  have hCpos : 0 < 1 + C := by linarith
  have hlower : (1 + C)⁻¹ ≤ x := by
    apply ge_of_tendsto h
    exact Filter.Eventually.of_forall fun k =>
      (inv_le_inv₀ hCpos (by linarith [hf k])).mpr (by linarith [hC k])
  exact lt_of_lt_of_le (inv_pos.mpr hCpos) hlower

theorem compactifiedHierarchyCoordinate_antitone
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ≤ v) :
    compactifiedHierarchyCoordinate v ≤ compactifiedHierarchyCoordinate u := by
  exact (inv_le_inv₀ (by linarith : 0 < 1 + v)
    (by linarith : 0 < 1 + u)).mpr (by linarith)

theorem compactifiedHierarchyCoordinate_recovered_nonneg
    {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1) :
    0 ≤ x⁻¹ - 1 := by
  have hinv : (1 : ℝ) ≤ x⁻¹ := by
    simpa only [inv_one] using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hx).mpr hx'
  linarith

theorem compactifiedHierarchyCoordinate_recovered_antitone
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    y⁻¹ - 1 ≤ x⁻¹ - 1 := by
  have hinv := (inv_le_inv₀ hy hx).mpr hxy
  linarith

theorem exists_levelRate_minimizing_sequence {r : ℕ} {s : ℝ}
    (hne : (levelRateSet r s).Nonempty) :
    ∃ (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ),
      (∀ k, Interlacing (a k) (b k) ∧ s < 2 * Gamma (a k) (b k)) ∧
      Antitone (fun k => Phi (a k) (b k)) ∧
      Tendsto (fun k => Phi (a k) (b k)) atTop (nhds (levelRate r s)) := by
  obtain ⟨z, hanti, hlim, hz⟩ :=
    exists_seq_tendsto_sInf hne (levelRateSet_bddBelow r s)
  have hdata : ∀ k : ℕ,
      ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
        Interlacing a b ∧ s < 2 * Gamma a b ∧ z k = Phi a b := hz
  choose a b hinter hgap heq using hdata
  refine ⟨a, b, fun k => ⟨hinter k, hgap k⟩, ?_, ?_⟩
  · simpa only [← heq] using hanti
  · simpa only [levelRate, ← heq] using hlim

theorem levelRate_minimizing_sequence_bddAbove {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    (hanti : Antitone (fun k => Phi (a k) (b k))) (k : ℕ) :
    Phi (a k) (b k) ≤ Phi (a 0) (b 0) :=
  hanti (Nat.zero_le k)

private abbrev HierarchyCompactIndex (r : ℕ) := Fin (r + 1) ⊕ Fin r

private def compactifiedHierarchyTuple {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    HierarchyCompactIndex r → ℝ :=
  Sum.elim (fun i => compactifiedHierarchyCoordinate (a i))
    (fun i => compactifiedHierarchyCoordinate (b i))

private def hierarchyCompactCube (r : ℕ) : Set (HierarchyCompactIndex r → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

theorem compactifiedHierarchyTuple_mem_cube {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    compactifiedHierarchyTuple a b ∈ hierarchyCompactCube r := by
  intro i _
  cases i with
  | inl i =>
      exact compactifiedHierarchyCoordinate_mem_Icc (h.ambient_nonneg i)
  | inr i =>
      exact compactifiedHierarchyCoordinate_mem_Icc (h.stabilizer_pos i).le

theorem isCompact_hierarchyCompactCube (r : ℕ) :
    IsCompact (hierarchyCompactCube r) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem exists_compactifiedHierarchyTuple_subsequence {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (h : ∀ k, Interlacing (a k) (b k)) :
    ∃ (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
        atTop (nhds (B i))) := by
  obtain ⟨z, hz, φ, hmono, hlim⟩ :=
    (isCompact_hierarchyCompactCube r).tendsto_subseq
      (fun k => compactifiedHierarchyTuple_mem_cube (h k))
  refine ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), φ,
    hmono, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hz (Sum.inl i) (Set.mem_univ _)
  · intro i
    exact hz (Sum.inr i) (Set.mem_univ _)
  · intro i
    have hi := (tendsto_pi_nhds.mp hlim) (Sum.inl i)
    exact hi
  · intro i
    have hi := (tendsto_pi_nhds.mp hlim) (Sum.inr i)
    exact hi

theorem compactifiedHierarchyTuple_limit_weak_interlacing {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ} {φ : ℕ → ℕ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hA : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
      atTop (nhds (B i))) :
    ∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ := by
  intro i
  constructor
  · have hlim := (hA i.castSucc).sub (hB i)
    have hle : A i.castSucc - B i ≤ 0 := by
      apply le_of_tendsto hlim
      exact Filter.Eventually.of_forall fun k => sub_nonpos.mpr
        (compactifiedHierarchyCoordinate_antitone
          ((h (φ k)).stabilizer_pos i).le
          ((h (φ k)).ambient_nonneg i.castSucc)
          ((h (φ k)).2 i).1.le)
    linarith
  · have hlim := (hB i).sub (hA i.succ)
    have hle : B i - A i.succ ≤ 0 := by
      apply le_of_tendsto hlim
      exact Filter.Eventually.of_forall fun k => sub_nonpos.mpr
        (compactifiedHierarchyCoordinate_antitone
          ((h (φ k)).ambient_nonneg i.succ)
          ((h (φ k)).stabilizer_pos i).le
          ((h (φ k)).2 i).2.le)
    linarith

theorem compactifiedHierarchyTuple_recovered_weak_interlacing {r : ℕ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (hA : ∀ i, A i ∈ Set.Ioc (0 : ℝ) 1)
    (hB : ∀ i, B i ∈ Set.Ioc (0 : ℝ) 1)
    (hinter : ∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ) :
    0 ≤ (A (Fin.last r))⁻¹ - 1 ∧
      ∀ i : Fin r,
        (B i)⁻¹ - 1 ≤ (A i.castSucc)⁻¹ - 1 ∧
          (A i.succ)⁻¹ - 1 ≤ (B i)⁻¹ - 1 := by
  constructor
  · exact compactifiedHierarchyCoordinate_recovered_nonneg
      (hA (Fin.last r)).1 (hA (Fin.last r)).2
  · intro i
    exact ⟨compactifiedHierarchyCoordinate_recovered_antitone
      (hA i.castSucc).1 (hB i).1 (hinter i).1,
      compactifiedHierarchyCoordinate_recovered_antitone
        (hB i).1 (hA i.succ).1 (hinter i).2⟩

theorem compactifiedHierarchyTuple_terminal_limit_pos {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C)
    (hA : Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) (Fin.last r)))
      atTop (nhds (A (Fin.last r)))) :
    0 < A (Fin.last r) := by
  apply compactifiedHierarchyCoordinate_limit_pos_of_bddAbove
    (fun k => (h (φ k)).ambient_nonneg (Fin.last r))
    (C := (2 : ℝ) ^ C - 1)
  · exact fun k =>
      CompactificationEntropy.terminal_degree_le_rpow_sub_one_of_Phi_le
        (h (φ k)) (hbound (φ k))
  · exact hA

theorem exists_bounded_hierarchy_entropy_subsequence {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C) :
    ∃ (L : ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ L ∈ Set.Icc (0 : ℝ) C ∧
      Tendsto (fun k => Phi (a (φ k)) (b (φ k)))
        atTop (nhds L) := by
  obtain ⟨L, hL, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).tendsto_subseq
      (fun k => ⟨(h k).Phi_nonneg_refinement, hbound k⟩)
  exact ⟨L, φ, hφ, hL, hlim⟩

theorem exists_compactified_bounded_hierarchy_subsequence {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (φ : ℕ → ℕ),
      StrictMono φ ∧ L ∈ Set.Icc (0 : ℝ) C ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
        atTop (nhds (B i))) ∧
      (∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ) ∧
      0 < A (Fin.last r) ∧
      Tendsto (fun k => Phi (a (φ k)) (b (φ k)))
        atTop (nhds L) := by
  obtain ⟨L, ψ, hψ, hL, hlim⟩ :=
    exists_bounded_hierarchy_entropy_subsequence a b h hbound
  obtain ⟨A, B, χ, hχ, hA, hB, ha, hb⟩ :=
    exists_compactifiedHierarchyTuple_subsequence
      (fun k => a (ψ k)) (fun k => b (ψ k))
      (fun k => h (ψ k))
  let φ : ℕ → ℕ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have ha' : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
      atTop (nhds (A i)) := by
    intro i
    exact ha i
  have hb' : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
      atTop (nhds (B i)) := by
    intro i
    exact hb i
  refine ⟨L, A, B, φ, hφ, hL, hA, hB, ha', hb',
    compactifiedHierarchyTuple_limit_weak_interlacing h ha' hb',
    compactifiedHierarchyTuple_terminal_limit_pos h hbound
      (ha' (Fin.last r)), ?_⟩
  exact hlim.comp hχ.tendsto_atTop

end

section

open Set Filter Topology

private def FixedLevelCompactifiedCertificateClosure (r : ℕ) : Prop :=
  ∀ {s R : ℝ}, 0 < s → s < 1 →
    ∀ (u : ℕ → ℝ)
      (a : ℕ → Fin (r + 1) → ℝ)
      (b : ℕ → Fin r → ℝ),
      Tendsto u atTop (nhds s) →
      (∀ n, Interlacing (a n) (b n)) →
      (∀ n, u n < 2 * Gamma (a n) (b n)) →
      (∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) →
      levelRate r s ≤ R

theorem levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
    {r : ℕ} {s : ℝ} (_hs : 0 ≤ s) (hs' : s < 1)
    (hclosure : FixedLevelCompactifiedCertificateClosure r) :
    LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro R
  let V : Set ℝ := Set.Icc (0 : ℝ) s ∩ (levelRate r) ⁻¹' Set.Iic R
  refine ⟨V, ?_, ?_⟩
  · apply IsSeqClosed.isClosed
    intro u x hu hux
    have hx : x ∈ Set.Icc (0 : ℝ) s :=
      isClosed_Icc.mem_of_tendsto hux
        (Filter.Eventually.of_forall fun n => (hu n).1)
    refine ⟨hx, ?_⟩
    change levelRate r x ≤ R
    by_cases hxzero : x = 0
    · rw [hxzero, levelRate_at_zero]
      exact (levelRate_nonneg_all r (u 0)).trans ((hu 0).2)
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
      have hxone : x < 1 := hx.2.trans_lt hs'
      have hevent : ∀ᶠ n : ℕ in atTop,
          0 < u n ∧ u n < 1 :=
        (hux.eventually (Ioi_mem_nhds hxpos)).and
          (hux.eventually (Iio_mem_nhds hxone))
      obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
      let v : ℕ → ℝ := fun n => u (n + N)
      have hvlim : Tendsto v atTop (nhds x) :=
        hux.comp (tendsto_add_atTop_nat N)
      have hvpos : ∀ n, 0 < v n :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).1
      have hvone : ∀ n, v n < 1 :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).2
      have hvrate : ∀ n, levelRate r (v n) ≤ R :=
        fun n => (hu (n + N)).2
      have hdata : ∀ n : ℕ,
          ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
            Interlacing a b ∧ v n < 2 * Gamma a b ∧
              Phi a b < R + 1 / ((n : ℝ) + 1) := by
        intro n
        have hnonempty :=
          levelRateSet_nonempty_of_interior r (hvpos n) (hvone n)
        have hstrict : levelRate r (v n) < R + 1 / ((n : ℝ) + 1) :=
          lt_of_le_of_lt (hvrate n)
            (lt_add_of_pos_right _ (by positivity))
        obtain ⟨_, ⟨a, b, hinterlacing, hgap, rfl⟩, hrate⟩ :=
          exists_lt_of_csInf_lt hnonempty hstrict
        exact ⟨a, b, hinterlacing, hgap, hrate⟩
      choose a b hinter hgap hPhi using hdata
      exact hclosure hxpos hxone v a b hvlim hinter hgap
        (fun n => (hPhi n).le)
  · ext x
    simp only [mem_inter_iff, mem_Icc, mem_preimage, mem_Iic, and_self_left, V]

end

section

open Filter Topology
open scoped BigOperators Topology

private def prependAmbient {r : ℕ} (u : ℝ) (a : Fin (r + 1) → ℝ) :
    Fin (r + 2) → ℝ :=
  Fin.cons u a

private def prependStabilizer {r : ℕ} (v : ℝ) (b : Fin r → ℝ) :
    Fin (r + 1) → ℝ :=
  Fin.cons v b

theorem interlacing_prepend {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {u v : ℝ}
    (huv : v < u) (hva : a 0 < v) :
    Interlacing (prependAmbient u a) (prependStabilizer v b) := by
  constructor
  · simpa only [prependAmbient, Fin.cons_last] using h.1
  · intro i
    induction i using Fin.cases with
    | zero =>
        simpa only [prependAmbient, Fin.castSucc_zero, Fin.cons_zero, prependStabilizer, gt_iff_lt,
          Fin.succ_zero_eq_one, Fin.cons_one] using ⟨huv, hva⟩
    | succ i =>
        simpa only [prependAmbient, Fin.castSucc_succ, Fin.cons_succ, prependStabilizer,
          gt_iff_lt] using h.2 i

theorem Phi_prepend {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (u v : ℝ) :
    Phi (prependAmbient u a) (prependStabilizer v b) =
      Phi a b +
        (MetricCodes.sphericalEntropy u - MetricCodes.sphericalEntropy v) := by
  simp only [Phi, prependAmbient, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    prependStabilizer]
  ring

theorem lagrangeNumerator_prepend_succ {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (u v : ℝ) (i : Fin (r + 1)) :
    lagrangeNumerator (prependAmbient u a) (prependStabilizer v b) i.succ =
      (((a i) * (1 + (a i))) - (v * (1 + v))) *
        lagrangeNumerator a b i := by
  simp only [lagrangeNumerator, prependAmbient, Fin.cons_succ, prependStabilizer,
    Fin.prod_univ_succ, Fin.cons_zero]

theorem lagrangeDenominator_prepend_succ {r : ℕ}
    (a : Fin (r + 1) → ℝ) (u : ℝ) (i : Fin (r + 1)) :
    lagrangeDenominator (prependAmbient u a) i.succ =
      (((a i) * (1 + (a i))) - (u * (1 + u))) *
        lagrangeDenominator a i := by
  simp only [lagrangeDenominator, prependAmbient, Fin.cons_succ, Fin.prod_univ_succ, ne_eq,
    Fin.succ_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero, Fin.cons_zero,
    Fin.succ_succAbove_succ]

theorem lagrangeWeight_prepend_succ {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (u v : ℝ) (i : Fin (r + 1))
    (hne : ((a i) * (1 + (a i))) - (u * (1 + u)) ≠ 0) :
    lagrangeWeight (prependAmbient u a) (prependStabilizer v b) i.succ =
      lagrangeWeight a b i *
        ((((a i) * (1 + (a i))) - (v * (1 + v))) /
          (((a i) * (1 + (a i))) - (u * (1 + u)))) := by
  unfold lagrangeWeight
  rw [lagrangeNumerator_prepend_succ, lagrangeDenominator_prepend_succ]
  field_simp [hne, h.lagrangeDenominator_ne_zero i]

theorem tendsto_scaleCoordinate_sq_div_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => scaleCoordinate (c ^ 2) u / u)
      atTop (𝓝 c) := by
  have hinv : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hinside :
      Tendsto
        (fun u : ℝ => u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1))
        atTop (𝓝 (4 * c ^ 2)) := by
    convert (hinv.pow 2).add
      ((hinv.add tendsto_const_nhds).const_mul (4 * c ^ 2)) using 1;
      norm_num
  have hroot : Real.sqrt (4 * c ^ 2) = 2 * c := by
    rw [show (4 : ℝ) * c ^ 2 = (2 * c) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          (Real.sqrt (u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1)) - u⁻¹) / 2)
        atTop (𝓝 c) := by
    convert (hinside.sqrt.sub hinv).div_const 2 using 1;
      simp [hroot]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hquadratic : 0 ≤ (u * (1 + u)) := by
    positivity
  have hrad : 0 ≤ 1 + 4 * c ^ 2 * (u * (1 + u)) := by positivity
  have hsmall :
      0 ≤ u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1) := by positivity
  have hsqrt :
      Real.sqrt (u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1)) =
        Real.sqrt (1 + 4 * c ^ 2 * (u * (1 + u))) / u := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg (Real.sqrt_nonneg _) hu.le)).mp
    rw [Real.sq_sqrt hsmall, div_pow, Real.sq_sqrt hrad]
    field_simp [hu.ne']
  rw [hsqrt]
  unfold scaleCoordinate
  field_simp [hu.ne']

theorem tendsto_scaleCoordinate_sq_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => scaleCoordinate (c ^ 2) u) atTop atTop := by
  have hratio := tendsto_scaleCoordinate_sq_div_atTop hc
  have hevent :
      ∀ᶠ u : ℝ in atTop, c / 2 < scaleCoordinate (c ^ 2) u / u :=
    hratio.eventually (Ioi_mem_nhds (by linarith))
  have hle :
      (fun u : ℝ => (c / 2) * u) ≤ᶠ[atTop]
        (fun u : ℝ => scaleCoordinate (c ^ 2) u) := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with u hu hupos
    have hmul := (lt_div_iff₀ hupos).mp hu
    exact hmul.le
  exact tendsto_atTop_mono' atTop hle
    (tendsto_id.const_mul_atTop (by linarith))

theorem scaleCoordinate_sq_lt_self {c u : ℝ}
    (hc : 0 < c) (hc' : c < 1) (hu : 0 < u) :
    scaleCoordinate (c ^ 2) u < u := by
  have hscale : 0 ≤ scaleCoordinate (c ^ 2) u :=
    scaleCoordinate_nonneg (sq_nonneg c) hu.le
  have hquad : 0 < (u * (1 + u)) := by
    positivity
  by_contra hnot
  have hle : u ≤ scaleCoordinate (c ^ 2) u := le_of_not_gt hnot
  have hmon := quadraticCoordinate_strictMonoOn.monotoneOn hu.le hscale hle
  rw [quadraticCoordinate_scaleCoordinate (sq_nonneg c) hu.le] at hmon
  nlinarith [mul_pos (sub_pos.mpr hc') (by linarith : 0 < 1 + c)]

theorem eventually_interlacing_prepend_scale {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    ∀ᶠ u : ℝ in atTop,
      Interlacing (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b) := by
  have hlarge := (tendsto_scaleCoordinate_sq_atTop hc).eventually
    (eventually_gt_atTop (a 0))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with u hu hupos
  exact interlacing_prepend h (scaleCoordinate_sq_lt_self hc hc' hupos) hu

theorem tendsto_entropy_prepend_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      MetricCodes.sphericalEntropy u -
        MetricCodes.sphericalEntropy (scaleCoordinate (c ^ 2) u))
      atTop (𝓝 (-Real.logb 2 c)) :=
  CompactificationEntropy.tendsto_sphericalEntropy_sub_of_ratio hc
    (tendsto_scaleCoordinate_sq_atTop hc)
    (tendsto_scaleCoordinate_sq_div_atTop hc)

theorem tendsto_Phi_prepend_scale {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      Phi (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (Phi a b - Real.logb 2 c)) := by
  simpa only [Phi_prepend, sub_eq_add_neg] using
    (tendsto_const_nhds (x := Phi a b)).add
      (tendsto_entropy_prepend_scale hc)

end

section

open Filter Topology
open scoped Topology

theorem tendsto_spectralAtom_atTop_half :
    Tendsto spectralAtom atTop (nhds ((1 : ℝ) / 2)) := by
  have hinv : Tendsto (fun u : ℝ => u⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hnormal :
      Tendsto (fun u : ℝ =>
        Real.sqrt (1 + u⁻¹) / (u⁻¹ + 2)) atTop (nhds ((1 : ℝ) / 2)) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).sqrt.div
      (hinv.add_const 2) (by norm_num : (0 : ℝ) + 2 ≠ 0) using 1 <;>
      norm_num; rfl
  apply hnormal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  unfold spectralAtom
  have hfactor : u * (1 + u) = u ^ 2 * (1 + u⁻¹) := by
    field_simp [hu.ne']
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq_eq_abs,
    abs_of_pos hu]
  field_simp [hu.ne']

theorem tendsto_retainedQuadraticResidueFactor_atTop
    (z c : ℝ) :
    Tendsto (fun u : ℝ =>
      ((z * (1 + z)) - c ^ 2 * (u * (1 + u))) /
        ((z * (1 + z)) - (u * (1 + u))))
      atTop (nhds (c ^ 2)) := by
  have hu : Tendsto (fun u : ℝ => u⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hq : Tendsto (fun u : ℝ => (u * (1 + u))⁻¹)
      atTop (nhds 0) := by
    have hnorm : Tendsto (fun u : ℝ => u⁻¹ * (1 + u)⁻¹)
        atTop (nhds 0) := by
      have hshift : Tendsto (fun u : ℝ => (1 + u)⁻¹)
          atTop (nhds 0) := by
        exact tendsto_inv_atTop_zero.comp
          ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop tendsto_id)
      simpa only [mul_zero] using hu.mul hshift
    simpa only [mul_inv_rev, mul_comm] using hnorm
  have hnormal :
      Tendsto (fun u : ℝ =>
        ((z * (1 + z)) * (u * (1 + u))⁻¹ - c ^ 2) /
          ((z * (1 + z)) * (u * (1 + u))⁻¹ - 1))
        atTop (nhds (c ^ 2)) := by
    convert ((hq.const_mul (z * (1 + z))).sub_const (c ^ 2)).div
      ((hq.const_mul (z * (1 + z))).sub_const 1)
      (by norm_num : ((z * (1 + z)) * 0 - 1 : ℝ) ≠ 0) using 1 <;>
      norm_num; rfl
  apply hnormal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hquad : (u * (1 + u)) ≠ 0 := by
    positivity
  field_simp [hquad]

end

section


open Filter Topology
open scoped BigOperators Topology

theorem Gamma_prepend_eq_spectralAtom_add_retained
    {r : ℕ} (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (u v : ℝ)
    (h : Interlacing (prependAmbient u a) (prependStabilizer v b)) :
    Gamma (prependAmbient u a) (prependStabilizer v b) =
      spectralAtom u +
        ∑ i : Fin (r + 1),
          lagrangeWeight (prependAmbient u a)
              (prependStabilizer v b) i.succ *
            (spectralAtom (a i) - spectralAtom u) := by
  have hweights :
      lagrangeWeight (prependAmbient u a)
          (prependStabilizer v b) 0 +
        ∑ i : Fin (r + 1),
          lagrangeWeight (prependAmbient u a)
            (prependStabilizer v b) i.succ = 1 := by
    simpa only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] using h.sum_lagrangeWeight
  unfold Gamma
  rw [Fin.sum_univ_succ]
  simp only [prependAmbient, Fin.cons_zero, Fin.cons_succ]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change lagrangeWeight (Fin.cons u a) (prependStabilizer v b) 0 +
    ∑ i : Fin (r + 1), lagrangeWeight (Fin.cons u a)
      (prependStabilizer v b) i.succ = 1 at hweights
  nlinarith [congrArg (fun z : ℝ => z * spectralAtom u) hweights]

theorem tendsto_lagrangeWeight_prepend_scale_succ
    {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (c : ℝ) (i : Fin (r + 1)) :
    Tendsto
      (fun u : ℝ =>
        lagrangeWeight (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) i.succ)
      atTop (𝓝 (c ^ 2 * lagrangeWeight a b i)) := by
  have hfactor :=
    tendsto_retainedQuadraticResidueFactor_atTop (a i) c
  have hlimit :
      Tendsto
        (fun u : ℝ => lagrangeWeight a b i *
          ((((a i) * (1 + (a i))) - c ^ 2 * (u * (1 + u))) /
            (((a i) * (1 + (a i))) - (u * (1 + u)))))
        atTop (𝓝 (c ^ 2 * lagrangeWeight a b i)) := by
    simpa only [mul_comm] using hfactor.const_mul (lagrangeWeight a b i)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (max 0 (a i))] with u hu
  have hu0 : 0 < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hau : a i < u := lt_of_le_of_lt (le_max_right _ _) hu
  have hquad : ((a i) * (1 + (a i))) < (u * (1 + u)) :=
    quadraticCoordinate_strictMonoOn (h.ambient_nonneg i) hu0.le hau
  have hne : ((a i) * (1 + (a i))) - (u * (1 + u)) ≠ 0 := by
    linarith
  rw [lagrangeWeight_prepend_succ h u
    (scaleCoordinate (c ^ 2) u) i hne,
    quadraticCoordinate_scaleCoordinate (sq_nonneg c) hu0.le]

end

section

open scoped BigOperators

theorem prepend_spectral_limit_algebra {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (c : ℝ) :
    (1 / 2 : ℝ) +
        ∑ i : Fin (r + 1),
          (c ^ 2 * lagrangeWeight a b i) *
            (spectralAtom (a i) - 1 / 2) =
      (1 - c ^ 2) / 2 + c ^ 2 * Gamma a b := by
  calc
    (1 / 2 : ℝ) +
        ∑ i : Fin (r + 1),
          (c ^ 2 * lagrangeWeight a b i) *
            (spectralAtom (a i) - 1 / 2) =
        1 / 2 +
          (c ^ 2 * (∑ i : Fin (r + 1),
            lagrangeWeight a b i * spectralAtom (a i)) -
            (c ^ 2 / 2) * (∑ i : Fin (r + 1), lagrangeWeight a b i)) := by
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (1 - c ^ 2) / 2 + c ^ 2 * Gamma a b := by
      rw [h.sum_lagrangeWeight]
      unfold Gamma
      ring

end

section

open Filter Topology
open scoped BigOperators Topology

theorem tendsto_Gamma_prepend_scale {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b)) := by
  have hatom := tendsto_spectralAtom_atTop_half
  have hterm (i : Fin (r + 1)) :
      Tendsto
        (fun u : ℝ =>
          lagrangeWeight (prependAmbient u a)
              (prependStabilizer (scaleCoordinate (c ^ 2) u) b) i.succ *
            (spectralAtom (a i) - spectralAtom u))
        atTop
        (𝓝 ((c ^ 2 * lagrangeWeight a b i) *
          (spectralAtom (a i) - (1 / 2 : ℝ)))) :=
    (tendsto_lagrangeWeight_prepend_scale_succ h c i).mul
      ((tendsto_const_nhds (x := spectralAtom (a i))).sub hatom)
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => hterm i)
  have hlimit := hatom.add hsum
  rw [prepend_spectral_limit_algebra h c] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_interlacing_prepend_scale h hc hc']
    with u hu
  exact (Gamma_prepend_eq_spectralAtom_add_retained a b u
    (scaleCoordinate (c ^ 2) u) hu).symm

theorem rateSet_subset_hierarchyRateSet (s : ℝ) :
    MetricCodes.Spherical.rateSet s ⊆ hierarchyRateSet s := by
  rintro z ⟨a, b, ⟨hb, hba, hgap⟩, rfl⟩
  have ha : 0 < a := hb.trans hba
  refine ⟨1, ![a, 0], ![b],
    oneRowInterlacing_iff.mpr ⟨hb, hba⟩, ?_, ?_⟩
  · simpa only [Gamma_oneRow ha] using hgap
  · simp only [Phi_oneRow]

theorem hierarchyRateSet_nonempty_of_interior
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (hierarchyRateSet s).Nonempty :=
  (MetricCodes.Spherical.rateSet_nonempty_of_interior hs hs').mono
    (rateSet_subset_hierarchyRateSet s)

theorem hierarchyVariationalRate_nonneg
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    0 ≤ hierarchyVariationalRate s := by
  unfold hierarchyVariationalRate
  apply le_csInf (hierarchyRateSet_nonempty_of_interior hs hs')
  rintro z ⟨r, a, b, h, _, rfl⟩
  exact h.Phi_nonneg

end

section

open Filter Topology
open scoped Topology

theorem exists_nextLevel_compactified_certificate_lt_of_spectral_limit
    {r : ℕ} {s c R : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hR : Phi a b - Real.logb 2 c < R)
    (hGamma : Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b))) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < R := by
  have htarget :
      s < 2 * (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b) := by
    nlinarith
  have hspectral :
      ∀ᶠ u : ℝ in atTop,
        s < 2 * Gamma (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) :=
    (hGamma.const_mul 2).eventually (Ioi_mem_nhds htarget)
  have hentropy :
      ∀ᶠ u : ℝ in atTop,
        Phi (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) < R :=
    (tendsto_Phi_prepend_scale a b hc).eventually (Iio_mem_nhds hR)
  have hinter := eventually_interlacing_prepend_scale h hc hc'
  obtain ⟨u, hu⟩ := (hinter.and (hspectral.and hentropy)).exists
  exact ⟨prependAmbient u a,
    prependStabilizer (scaleCoordinate (c ^ 2) u) b,
    hu.1, hu.2.1, hu.2.2⟩

theorem hierarchyVariationalRate_le_compactified_certificate_of_spectral_limit
    {r : ℕ} {s c : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hGamma : Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b))) :
    hierarchyVariationalRate s ≤ Phi a b - Real.logb 2 c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨A, B, hAB, hgap, hPhi⟩ :=
    exists_nextLevel_compactified_certificate_lt_of_spectral_limit
      (R := Phi a b - Real.logb 2 c + ε)
      hc hc' a b h hscaled (by linarith) hGamma
  exact (hierarchyVariationalRate_le_of_feasible hAB hgap).trans hPhi.le

theorem exists_nextLevel_compactified_certificate_lt
    {r : ℕ} {s c R : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hR : Phi a b - Real.logb 2 c < R) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < R :=
  exists_nextLevel_compactified_certificate_lt_of_spectral_limit
    hc hc' a b h hscaled hR (tendsto_Gamma_prepend_scale h hc hc')

theorem levelRate_succ_le_compactified_certificate
    {r : ℕ} {s c : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b)) :
    levelRate (r + 1) s ≤ Phi a b - Real.logb 2 c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨A, B, hAB, hgap, hPhi⟩ :=
    exists_nextLevel_compactified_certificate_lt
      (R := Phi a b - Real.logb 2 c + ε)
      hc hc' a b h hscaled (by linarith)
  exact (levelRate_le hAB hgap).trans hPhi.le

theorem levelRate_antitone_level
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    {j k : ℕ} (hjk : j ≤ k) :
    levelRate k s ≤ levelRate j s := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hle hind =>
      exact (levelRate_succ_le hs hs').trans hind

theorem levelRate_le_compactified_datum
    {k j : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hlevels : (c = 1 ∧ j ≤ k) ∨ (c < 1 ∧ j + 1 ≤ k)) :
    levelRate k s ≤ Phi a b - Real.logb 2 c := by
  rcases hlevels with ⟨rfl, hjk⟩ | ⟨hc', hjk⟩
  · have hgap : s < 2 * Gamma a b := by
      norm_num at hscaled ⊢
      linarith
    simpa only [Real.logb_one, sub_zero, ge_iff_le] using
      (levelRate_antitone_level hs hs' hjk).trans (levelRate_le h hgap)
  · exact (levelRate_antitone_level hs hs' hjk).trans
      (levelRate_succ_le_compactified_certificate hc hc' a b h hscaled)

end

section

open Filter Topology
open scoped BigOperators Topology

theorem continuous_scaleCoordinate_factor (u : ℝ) :
    Continuous (fun t : ℝ => scaleCoordinate t u) := by
  unfold scaleCoordinate
  fun_prop

theorem continuous_Phi_common_scale {j : ℕ}
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ) :
    Continuous
      (fun t : ℝ => Phi (scaleAmbient t a) (scaleStabilizer t b)) := by
  unfold Phi scaleAmbient scaleStabilizer
  apply Continuous.sub
  · exact continuous_finsetSum _ fun i _ =>
      MetricCodes.Spherical.sphericalEntropy_continuous.comp
        (continuous_scaleCoordinate_factor (a i))
  · exact continuous_finsetSum _ fun i _ =>
      MetricCodes.Spherical.sphericalEntropy_continuous.comp
        (continuous_scaleCoordinate_factor (b i))

theorem levelRate_le_of_non_strict_spectral
    {j : ℕ} {s : ℝ} (hs : 0 < s)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b) (hboundary : s ≤ 2 * Gamma a b) :
    levelRate j s ≤ Phi a b := by
  by_cases hlast : 0 < a (Fin.last j)
  · have honeA : scaleAmbient 1 a = a := by
      funext i
      exact scaleCoordinate_one (h.ambient_nonneg i)
    have honeB : scaleStabilizer 1 b = b := by
      funext i
      exact scaleCoordinate_one (h.stabilizer_pos i).le
    have hlimit :
        Tendsto
          (fun t : ℝ => Phi (scaleAmbient t a) (scaleStabilizer t b))
          (𝓝[>] (1 : ℝ)) (𝓝 (Phi a b)) := by
      have htend :=
        (continuous_Phi_common_scale a b).continuousAt (x := (1 : ℝ)) |>.tendsto
      rw [honeA, honeB] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcost := hlimit.eventually
      (Iio_mem_nhds (lt_add_of_pos_right (Phi a b) hε))
    have hside : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), 1 < t :=
      self_mem_nhdsWithin
    let : (𝓝[>] (1 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    obtain ⟨t, ht, hPhi⟩ :=
      (hside.and hcost).exists
    have htpos : 0 < t := by linarith
    have hinter :
        Interlacing (scaleAmbient t a) (scaleStabilizer t b) :=
      h.scale htpos
    have hgain := Gamma_scale_gt h hlast ht
    have hgap :
        s < 2 * Gamma (scaleAmbient t a) (scaleStabilizer t b) := by
      linarith
    exact (levelRate_le hinter hgap).trans hPhi.le
  · have hzero : a (Fin.last j) = 0 :=
      le_antisymm (le_of_not_gt hlast) h.1
    cases j with
    | zero =>
        have ha0 : a 0 = 0 := by simpa only [Fin.isValue, Fin.last_zero] using hzero
        rw [Gamma_zero, ha0] at hboundary
        norm_num [spectralAtom] at hboundary
        linarith
    | succ j =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos j) h hzero
        exact (levelRate_le hA (by linarith)).trans hPhi.le

theorem levelRate_le_compactified_boundary_datum
    {r j : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c) (hc' : c ≤ 1)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b)
    (hscaled : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hlevels : (c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) :
    levelRate r s ≤ Phi a b - Real.logb 2 c := by
  rcases hlevels with ⟨rfl, hjr⟩ | ⟨hc_lt, hjr⟩
  · have hboundary : s ≤ 2 * Gamma a b := by
      norm_num at hscaled ⊢
      linarith
    simpa only [Real.logb_one, sub_zero, ge_iff_le] using
      (levelRate_antitone_level hs hs' hjr).trans (levelRate_le_of_non_strict_spectral hs a b h
        hboundary)
  · have hpositive : 0 < 1 - 2 * Gamma a b := by
      linarith [h.Gamma_lt_half]
    have hlog :
        Tendsto (fun d : ℝ => Phi a b - Real.logb 2 d)
          (𝓝[<] c) (𝓝 (Phi a b - Real.logb 2 c)) := by
      exact tendsto_const_nhds.sub
        ((Real.continuousAt_logb hc.ne').tendsto.mono_left
          nhdsWithin_le_nhds)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcost := hlog.eventually
      (Iio_mem_nhds
        (lt_add_of_pos_right (Phi a b - Real.logb 2 c) hε))
    have hpos : ∀ᶠ d : ℝ in 𝓝[<] c, 0 < d :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (Ioi_mem_nhds hc)
    have hside : ∀ᶠ d : ℝ in 𝓝[<] c, d < c :=
      self_mem_nhdsWithin
    let : (𝓝[<] c).NeBot := nhdsWithin_Iio_neBot le_rfl
    obtain ⟨d, hd_lt, hd_pos, hd_cost⟩ :=
      (hside.and (hpos.and hcost)).exists
    have hd_one : d < 1 := hd_lt.trans hc_lt
    have hsquare : d ^ 2 < c ^ 2 := by
      nlinarith [mul_pos hd_pos (sub_pos.mpr hd_lt),
        mul_pos hc (sub_pos.mpr hd_lt)]
    have hstrict : s < 1 - d ^ 2 * (1 - 2 * Gamma a b) := by
      nlinarith [mul_pos (sub_pos.mpr hsquare) hpositive]
    exact
      (levelRate_le_compactified_datum hs hs' hd_pos a b h hstrict
        (Or.inr ⟨hd_one, hjr⟩)).trans hd_cost.le

end

section

open MeasureTheory
open scoped BigOperators Interval

theorem Interlacing.quadratic_phase_interval {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    ((b i) * (1 + (b i))) < ((a i.castSucc) * (1 + (a i.castSucc))) :=
  quadraticCoordinate_strictMonoOn (h.stabilizer_pos i).le
    (h.ambient_nonneg i.castSucc) (h.2 i).1

theorem stieltjesPhase_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    0 ≤ stieltjesPhase a b t := by
  rw [stieltjesPhase_eq_log_sum h ht]
  apply add_nonneg
  · apply Real.log_nonneg
    apply (le_div_iff₀ ht).2
    simpa only [one_mul, le_add_iff_nonneg_right] using h.ambient_quadratic_nonneg (Fin.last r)
  · apply Finset.sum_nonneg
    intro i _
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith [h.stabilizer_quadratic_pos i])).2
    nlinarith [h.quadratic_phase_interval i]

theorem stieltjesPhaseProduct_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    0 < stieltjesPhaseProduct a b t := by
  unfold stieltjesPhaseProduct
  apply div_pos
  · apply mul_pos ht
    exact Finset.prod_pos fun i _ => by
      linarith [h.stabilizer_quadratic_pos i]
  · exact Finset.prod_pos fun i _ => by
      linarith [h.ambient_quadratic_nonneg i]

theorem stieltjesPhaseProduct_le_one {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    stieltjesPhaseProduct a b t ≤ 1 := by
  rw [← exp_neg_stieltjesPhase_eq_product h ht]
  exact (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (stieltjesPhase_nonneg h ht)))

end

section


open scoped BigOperators

private def WeakInterlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, b i ≤ a i.castSucc ∧ a i.succ ≤ b i

theorem WeakInterlacing.antitone_ambient {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) : Antitone a := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

theorem WeakInterlacing.ambient_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) (i : Fin (r + 1)) : 0 ≤ a i :=
  h.1.trans (h.antitone_ambient i.le_last)

theorem WeakInterlacing.tail {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b) :
    WeakInterlacing (Fin.tail a) (Fin.tail b) := by
  constructor
  · simpa only [Fin.tail, Fin.succ_last, Nat.succ_eq_add_one] using h.1
  · intro i
    simpa only [Fin.tail, Fin.castSucc_succ] using h.2 i.succ

theorem WeakInterlacing.drop_second {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b)
    (hcollision : b 0 = a (1 : Fin (r + 2))) :
    WeakInterlacing
      (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) := by
  cases r with
  | zero =>
      constructor
      · simpa only [Nat.reduceAdd, Fin.isValue, Fin.last_zero,
          Fin.cons_zero] using h.ambient_nonneg 0
      · intro i
        exact Fin.elim0 i
  | succ r =>
      constructor
      · simpa only [Fin.cons_last, Fin.tail, Fin.succ_last, Nat.succ_eq_add_one] using h.1
      · intro i
        induction i using Fin.cases with
        | zero =>
            constructor
            · change b (1 : Fin (r + 2)) ≤ a 0
              exact ((h.2 (1 : Fin (r + 2))).1).trans
                (h.antitone_ambient (Fin.zero_le _))
            · change a (2 : Fin (r + 3)) ≤ b (1 : Fin (r + 2))
              exact (h.2 (1 : Fin (r + 2))).2
        | succ i =>
            simpa only [Fin.tail, Fin.castSucc_succ, Fin.cons_succ] using h.2 i.succ.succ

private def hierarchyStieltjesRatio {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
    (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))

theorem hierarchyStieltjesRatio_prepend {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (u v t : ℝ) :
    hierarchyStieltjesRatio (prependAmbient u a)
      (prependStabilizer v b) t =
        (t + (v * (1 + v))) / (t + (u * (1 + u))) *
          hierarchyStieltjesRatio a b t := by
  simp only [hierarchyStieltjesRatio, prependStabilizer, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, prependAmbient, div_eq_mul_inv, mul_inv_rev]
  ring

theorem Phi_tail_of_head_collision {r : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hcollision : a 0 = b 0) :
    Phi a b = Phi (Fin.tail a) (Fin.tail b) := by
  conv_lhs =>
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
  change Phi (prependAmbient (a 0) (Fin.tail a))
    (prependStabilizer (b 0) (Fin.tail b)) = _
  rw [Phi_prepend]
  simp only [hcollision, sub_self, add_zero]

theorem Phi_drop_second_of_collision {r : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hcollision : b 0 = a (1 : Fin (r + 2))) :
    Phi a b =
      Phi (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) := by
  simp only [Phi, Fin.sum_univ_succ, Fin.succ_zero_eq_one, hcollision, Fin.cons_zero, Fin.cons_succ,
    Fin.tail]
  ring

private theorem cancel_common_quadratic_factor_metriccodes2_79e88af7
    (x A B C : ℝ) (hx : x ≠ 0) :
    (x * A) / (B * (x * C)) = A / (B * C) := by
  calc
    (x * A) / (B * (x * C)) =
        (x * x⁻¹) * (A * (C⁻¹ * B⁻¹)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = A / (B * C) := by
      rw [mul_inv_cancel₀ hx]
      simp only [one_mul, div_eq_mul_inv, mul_inv_rev]

theorem hierarchyStieltjesRatio_tail_of_head_collision {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b) (hcollision : a 0 = b 0)
    {t : ℝ} (ht : 0 < t) :
    hierarchyStieltjesRatio a b t =
      hierarchyStieltjesRatio (Fin.tail a) (Fin.tail b) t := by
  conv_lhs =>
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
  change hierarchyStieltjesRatio
    (prependAmbient (a 0) (Fin.tail a))
    (prependStabilizer (b 0) (Fin.tail b)) t = _
  rw [hierarchyStieltjesRatio_prepend]
  have hfactor : t + ((a 0) * (1 + (a 0))) ≠ 0 := by
    have ha := h.ambient_nonneg 0
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ 1 + a 0)]
  rw [← hcollision]
  simp only [ne_eq, hfactor, not_false_eq_true, div_self, one_mul]

theorem hierarchyStieltjesRatio_drop_second_of_collision {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b)
    (hcollision : b 0 = a (1 : Fin (r + 2)))
    {t : ℝ} (ht : 0 < t) :
    hierarchyStieltjesRatio a b t =
      hierarchyStieltjesRatio
        (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) t := by
  have hfactor : t + ((a (1 : Fin (r + 2))) * (1 + (a (1 : Fin (r + 2))))) ≠ 0 := by
    have ha := h.ambient_nonneg (1 : Fin (r + 2))
    nlinarith [mul_nonneg ha
      (by linarith : 0 ≤ 1 + a (1 : Fin (r + 2)))]
  simp only [hierarchyStieltjesRatio, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.tail]
  rw [hcollision]
  simpa only [Fin.succ_zero_eq_one] using
    cancel_common_quadratic_factor_metriccodes2_79e88af7 (t + ((a (1 : Fin (r + 2))) * (1 + (a
      (1 : Fin (r + 2))))))
      (∏ i : Fin r, (t + ((b i.succ) * (1 + (b i.succ))))) (t + ((a 0) * (1 + (a 0))))
      (∏ i : Fin r, (t + ((a i.succ.succ) * (1 + (a i.succ.succ))))) hfactor

private theorem exists_strict_residual_aux_metriccodes2_79e88af7 :
    ∀ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      WeakInterlacing a b →
        ∃ (j : ℕ) (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ),
          j ≤ r ∧ Interlacing A B ∧ A 0 ≤ a 0 ∧
            Phi A B = Phi a b ∧
              ∀ t : ℝ, 0 < t →
                hierarchyStieltjesRatio a b t =
                  hierarchyStieltjesRatio A B t := by
  intro r
  induction r with
  | zero =>
      intro a b h
      refine ⟨0, a, b, le_rfl, ?_, le_rfl, rfl, ?_⟩
      · exact ⟨h.1, fun i => Fin.elim0 i⟩
      · intro t _
        rfl
  | succ r ih =>
      intro a b h
      by_cases hhead : a 0 = b 0
      · obtain ⟨j, A, B, hj, hinter, htop, hphi, hratio⟩ :=
          ih (Fin.tail a) (Fin.tail b) h.tail
        refine ⟨j, A, B, hj.trans (Nat.le_succ r), hinter, ?_, ?_, ?_⟩
        · exact htop.trans (h.antitone_ambient (Fin.zero_le _))
        · calc
            Phi A B = Phi (Fin.tail a) (Fin.tail b) := hphi
            _ = Phi a b := (Phi_tail_of_head_collision a b hhead).symm
        · intro t ht
          exact (hierarchyStieltjesRatio_tail_of_head_collision
            h hhead ht).trans (hratio t ht)
      · by_cases hsecond : b 0 = a (1 : Fin (r + 2))
        · let a' : Fin (r + 1) → ℝ :=
            Fin.cons (a 0) (Fin.tail (Fin.tail a))
          let b' : Fin r → ℝ := Fin.tail b
          have hweak : WeakInterlacing a' b' :=
            h.drop_second hsecond
          obtain ⟨j, A, B, hj, hinter, htop, hphi, hratio⟩ :=
            ih a' b' hweak
          refine ⟨j, A, B, hj.trans (Nat.le_succ r), hinter, ?_, ?_, ?_⟩
          · simpa [a'] using htop
          · calc
              Phi A B = Phi a' b' := hphi
              _ = Phi a b :=
                (Phi_drop_second_of_collision a b hsecond).symm
          · intro t ht
            exact (hierarchyStieltjesRatio_drop_second_of_collision
              h hsecond ht).trans (hratio t ht)
        · obtain ⟨j, A, B, hj, hinter, htop, hphi, hratio⟩ :=
            ih (Fin.tail a) (Fin.tail b) h.tail
          have hfirst := h.2 (0 : Fin (r + 1))
          have hu : b 0 < a 0 :=
            lt_of_le_of_ne hfirst.1 (Ne.symm hhead)
          have hv : a (1 : Fin (r + 2)) < b 0 :=
            lt_of_le_of_ne hfirst.2 (Ne.symm hsecond)
          have hbelow : A 0 < b 0 :=
            htop.trans_lt hv
          refine ⟨j + 1, prependAmbient (a 0) A,
            prependStabilizer (b 0) B, Nat.succ_le_succ hj,
            interlacing_prepend hinter hu hbelow, ?_, ?_, ?_⟩
          · simp only [prependAmbient, Fin.cons_zero, Std.le_refl]
          · rw [Phi_prepend, hphi]
            conv_rhs =>
              rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
            change _ = Phi
              (prependAmbient (a 0) (Fin.tail a))
              (prependStabilizer (b 0) (Fin.tail b))
            rw [Phi_prepend]
          · intro t ht
            conv_lhs =>
              rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
            change hierarchyStieltjesRatio
              (prependAmbient (a 0) (Fin.tail a))
              (prependStabilizer (b 0) (Fin.tail b)) t = _
            rw [hierarchyStieltjesRatio_prepend,
              hierarchyStieltjesRatio_prepend, hratio t ht]

theorem exists_strict_residual_of_weak_interlacing {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) :
    ∃ (j : ℕ) (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ),
      j ≤ r ∧ Interlacing A B ∧ Phi A B = Phi a b ∧
        ∀ t : ℝ, 0 < t →
          (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
              (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i))))) =
            (∏ i : Fin j, (t + ((B i) * (1 + (B i))))) /
              (∏ i : Fin (j + 1), (t + ((A i) * (1 + (A i))))) := by
  obtain ⟨j, A, B, hj, hinter, _, hphi, hratio⟩ :=
    exists_strict_residual_aux_metriccodes2_79e88af7 r a b h
  exact ⟨j, A, B, hj, hinter, hphi, fun t ht => hratio t ht⟩

end

section

open Filter Topology
open scoped BigOperators Topology

theorem tendsto_shifted_degree_ratio_of_tendsto_ratio
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n => (1 + v n) / (1 + u n))
      atTop (nhds d) := by
  have hinv : Tendsto (fun n => (u n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hnormalized :
      Tendsto (fun n => ((u n)⁻¹ + v n / u n) /
        ((u n)⁻¹ + 1)) atTop (nhds d) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  apply hnormalized.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  field_simp

theorem tendsto_sphericalEntropy_sub_of_sequence_ratio
    {u v : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hu : Tendsto u atTop atTop)
    (hv : Tendsto v atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (u n) -
        MetricCodes.sphericalEntropy (v n))
      atTop (nhds (-Real.logb 2 d)) := by
  have hshifted :=
    tendsto_shifted_degree_ratio_of_tendsto_ratio hu hratio
  have hlog : Tendsto
      (fun n => Real.logb 2 ((1 + v n) / (1 + u n)))
        atTop (nhds (Real.logb 2 d)) :=
    (Real.continuousAt_logb hd.ne').tendsto.comp hshifted
  have hfirst :=
    CompactificationEntropy.tendsto_sphericalEntropy_sub_logb_one_add.comp hu
  have hsecond :=
    CompactificationEntropy.tendsto_sphericalEntropy_sub_logb_one_add.comp hv
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 d =
        -Real.logb 2 d := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ)),
    hv.eventually (eventually_gt_atTop (0 : ℝ))] with n hun hvn
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring

theorem paired_stabilizer_tendsto_atTop_of_ambient
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (i : Fin r)
    (ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop) :
    Tendsto (fun n => b (φ n) i) atTop atTop := by
  let D : ℝ := (2 : ℝ) ^ (C + 1 / Real.log 2)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hgap : ∀ n,
      MetricCodes.sphericalEntropy (a (φ n) i.castSucc) -
        MetricCodes.sphericalEntropy (b (φ n) i) ≤ C :=
    fun n =>
      (CompactificationEntropy.entropy_gap_le_Phi (h (φ n)) i).trans
        (hPhi (φ n))
  have hbound : ∀ n,
      a (φ n) i.castSucc / D - 1 ≤ b (φ n) i := by
    intro n
    have hratio :=
      CompactificationEntropy.shifted_degree_ratio_le_rpow_of_entropy_gap_le
        ((h (φ n)).stabilizer_pos i)
        ((h (φ n)).2 i).1.le (hgap n)
    change (1 + a (φ n) i.castSucc) /
      (1 + b (φ n) i) ≤ D at hratio
    have hmul : 1 + a (φ n) i.castSucc ≤
        D * (1 + b (φ n) i) :=
      (div_le_iff₀
        (by linarith [(h (φ n)).stabilizer_pos i])).mp hratio
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hleft : Tendsto
      (fun n => a (φ n) i.castSucc / D - 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1)
      (ha.atTop_div_const hD) using 1
    ext n
    ring
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall hbound) hleft

theorem paired_infinity_iff
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ} {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i) :
    ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0 := by
  intro i
  constructor
  · intro hzero
    have hatop : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (h (φ n)).ambient_nonneg i.castSucc)
        (hzero ▸ hA i.castSucc)
    have hbtop := paired_stabilizer_tendsto_atTop_of_ambient
      h hPhi i hatop
    have hone : Tendsto (fun n => 1 + b (φ n) i) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 hbtop
    have hzero' : Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
          atTop (nhds 0) := by
      exact tendsto_inv_atTop_zero.comp hone
    exact tendsto_nhds_unique (hB i) hzero'
  · intro hzero
    have hweak := compactifiedHierarchyTuple_limit_weak_interlacing
      h hA hB i
    exact le_antisymm (hzero ▸ hweak.1) (hAnonneg i.castSucc)

end

section

open Set Filter Topology
open scoped BigOperators Topology

private def compactifiedAmbientSuffix {r k j : ℕ}
    (h : k + j = r) (A : Fin (r + 1) → ℝ) :
    Fin (j + 1) → ℝ :=
  fun i => A ⟨k + i.val, by omega⟩

private def compactifiedStabilizerSuffix {r k j : ℕ}
    (h : k + j = r) (B : Fin r → ℝ) :
    Fin j → ℝ :=
  fun i => B ⟨k + i.val, by omega⟩

theorem compactifiedAmbient_monotone_of_weak_interlacing {r : ℕ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (hinter : ∀ i : Fin r,
      A i.castSucc ≤ B i ∧ B i ≤ A i.succ) :
    Monotone A := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact (hinter i).1.trans (hinter i).2

theorem exists_positive_compactified_suffix {r : ℕ}
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ i, B i ∈ Set.Icc (0 : ℝ) 1)
    (hinter : ∀ i : Fin r,
      A i.castSucc ≤ B i ∧ B i ≤ A i.succ)
    (hpaired : ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0)
    (hlast : 0 < A (Fin.last r)) :
    ∃ (k j : ℕ) (hkj : k + j = r),
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) := by
  let P : ℕ → Prop := fun n =>
    ∃ i : Fin (r + 1), i.val = n ∧ 0 < A i
  have hP : ∃ n, P n :=
    ⟨r, Fin.last r, by simp only [Fin.val_last], hlast⟩
  let k := Nat.find hP
  obtain ⟨i₀, hi₀, hpos⟩ := Nat.find_spec hP
  have hkle : k ≤ r := by
    change (Nat.find hP) ≤ r
    omega
  let j := r - k
  have hkj : k + j = r := by
    dsimp [j]
    omega
  refine ⟨k, j, hkj, ?_, ?_, ?_, ?_⟩
  · intro i hik
    have hnot : ¬ 0 < A i.castSucc := by
      intro hpositive
      have hmin := Nat.find_min' hP ⟨i.castSucc, rfl, hpositive⟩
      change k ≤ i.val at hmin
      omega
    have hazero : A i.castSucc = 0 :=
      le_antisymm (le_of_not_gt hnot) (hA i.castSucc).1
    exact ⟨hazero, (hpaired i).mp hazero⟩
  · intro i
    constructor
    · have hle : i₀ ≤ (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
        apply Fin.mk_le_mk.mpr
        omega
      exact hpos.trans_le
        (compactifiedAmbient_monotone_of_weak_interlacing hinter hle)
    · exact (hA ⟨k + i.val, by omega⟩).2
  · intro i
    constructor
    · have hpositive : 0 < A (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
        have hle : i₀ ≤ (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
          apply Fin.mk_le_mk.mpr
          omega
        exact hpos.trans_le
          (compactifiedAmbient_monotone_of_weak_interlacing hinter hle)
      exact hpositive.trans_le
        (hinter (⟨k + i.val, by omega⟩ : Fin r)).1
    · exact (hB ⟨k + i.val, by omega⟩).2
  · intro i
    have h := hinter (⟨k + i.val, by omega⟩ : Fin r)
    constructor
    · simpa only [compactifiedAmbientSuffix, Fin.val_castSucc, compactifiedStabilizerSuffix,
      Fin.castSucc_mk] using
        h.1
    · change B (⟨k + i.val, by omega⟩ : Fin r) ≤
        A (⟨k + (i.val + 1), by omega⟩ : Fin (r + 1))
      simpa only [Fin.succ_mk, Nat.add_assoc] using h.2

theorem compactified_finite_suffix_weak_interlacing
    {r k j : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (hA : ∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1)
    (hB : ∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1)
    (hinter : ∀ i : Fin j,
      compactifiedAmbientSuffix hkj A i.castSucc ≤
        compactifiedStabilizerSuffix hkj B i ∧
      compactifiedStabilizerSuffix hkj B i ≤
        compactifiedAmbientSuffix hkj A i.succ) :
    WeakInterlacing
      (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
      (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) :=
  compactifiedHierarchyTuple_recovered_weak_interlacing hA hB hinter

end

section

open Filter Topology
open scoped Topology

theorem tendsto_quadraticCoordinate_ratio_of_tendsto_degree_ratio
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n => ((v n) * (1 + (v n))) /
      ((u n) * (1 + (u n)))) atTop (nhds (d ^ 2)) := by
  have hshift := tendsto_shifted_degree_ratio_of_tendsto_ratio hu hratio
  have hmul := hratio.mul hshift
  have hlimit : Tendsto
      (fun n => (v n / u n) * ((1 + v n) / (1 + u n)))
      atTop (nhds (d ^ 2)) := by
    simpa only [pow_two] using hmul
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  field_simp [hn.ne']

theorem interlacing_paired_degree_ratio_mem_Icc {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    b i / a i.castSucc ∈ Set.Icc (0 : ℝ) 1 := by
  have hb : 0 < b i := h.stabilizer_pos i
  have ha : 0 < a i.castSucc := hb.trans (h.2 i).1
  constructor
  · exact div_nonneg hb.le ha.le
  · exact (div_le_one ha).2 (h.2 i).1.le

theorem paired_ratio_limit_pos_of_ambient_tendsto_atTop
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {φ : ℕ → ℕ} {C d : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (i : Fin r)
    (ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop)
    (hratio : Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds d)) :
    0 < d := by
  have hb := paired_stabilizer_tendsto_atTop_of_ambient h hPhi i ha
  let K : ℝ := (2 * (2 : ℝ) ^ (C + 1 / Real.log 2))⁻¹
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      K ≤ b (φ n) i / a (φ n) i.castSucc := by
    filter_upwards [hb.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hbn
    apply CompactificationEntropy.degree_ratio_lower_bound_of_entropy_gap_le
      hbn ((h (φ n)).2 i).1.le
    exact (CompactificationEntropy.entropy_gap_le_Phi (h (φ n)) i).trans
      (hPhi (φ n))
  exact hK.trans_le (ge_of_tendsto hratio hbound)

theorem exists_compactified_paired_ratio_subsequence
    {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C) :
    ∃ (d : Fin r → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        0 < d i) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        Tendsto (fun n =>
          ((b (φ n) i) * (1 + (b (φ n) i))) /
            ((a (φ n) i.castSucc) * (1 + (a (φ n) i.castSucc))))
          atTop (nhds (d i ^ 2))) := by
  let K : Set (Fin r → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hcompact : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  let f : ℕ → Fin r → ℝ := fun n i => b n i / a n i.castSucc
  have hmem : ∀ n, f n ∈ K := by
    intro n i _
    exact interlacing_paired_degree_ratio_mem_Icc (h n) i
  obtain ⟨d, hd, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  have hratios : ∀ i : Fin r, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)) := by
    intro i
    exact (tendsto_pi_nhds.mp hlim) i
  refine ⟨d, φ, hφ, fun i => hd i (Set.mem_univ i), hratios, ?_, ?_⟩
  · intro i hai
    exact paired_ratio_limit_pos_of_ambient_tendsto_atTop
      h hPhi i hai (hratios i)
  · intro i hai
    exact tendsto_quadraticCoordinate_ratio_of_tendsto_degree_ratio
      hai (hratios i)

end

section

open Set Filter Topology
open scoped BigOperators Topology

theorem exists_compactified_residual_of_closure_sequence
    {r : ℕ} {s R : ℝ}
    (u : ℕ → ℝ)
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ)
    (hu : Tendsto u atTop (nhds s))
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hgap : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (d : Fin r → ℝ) (φ : ℕ → ℕ)
      (k j : ℕ) (hkj : k + j = r)
      (q : ℕ) (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
      (c : ℝ),
      StrictMono φ ∧
      0 ≤ L ∧ L ≤ R ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
        atTop (nhds (B i))) ∧
      Tendsto (fun n => u (φ n)) atTop (nhds s) ∧
      (∀ n, u (φ n) < 2 * Gamma (a (φ n)) (b (φ n))) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop (nhds L) ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 →
        0 < d i ∧
        Tendsto
          (fun n => ((b (φ n) i) * (1 + (b (φ n) i))) /
            ((a (φ n) i.castSucc) * (1 + (a (φ n) i.castSucc))))
          atTop (nhds (d i ^ 2))) ∧
      q ≤ j ∧ Interlacing a₀ b₀ ∧
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) ∧
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) ∧
      (∀ t : ℝ, 0 < t →
        hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
            hierarchyStieltjesRatio a₀ b₀ t) ∧
      c = ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i ∧
      0 < c ∧ c ≤ 1 ∧ (c < 1 → q < r) := by
  have hbound : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    refine (hPhi n).trans ?_
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    have hfrac : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    linarith
  obtain ⟨L, A, B, ψ, hψ, hL, hA, hB, hAψ, hBψ,
      hweak, hlast, hLψ⟩ :=
    exists_compactified_bounded_hierarchy_subsequence a b hinter hbound
  let aψ : ℕ → Fin (r + 1) → ℝ := fun n => a (ψ n)
  let bψ : ℕ → Fin r → ℝ := fun n => b (ψ n)
  obtain ⟨d, χ, hχ, hd, hdχ, hdpos, hdquadratic⟩ :=
    exists_compactified_paired_ratio_subsequence aψ bψ
      (fun n => hinter (ψ n)) (fun n => hbound (ψ n))
  let φ : ℕ → ℕ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have hAφ : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)) := by
    intro i
    exact (hAψ i).comp hχ.tendsto_atTop
  have hBφ : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)) := by
    intro i
    exact (hBψ i).comp hχ.tendsto_atTop
  have hLφ : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L) := by
    exact hLψ.comp hχ.tendsto_atTop
  have hpaired : ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0 :=
    paired_infinity_iff hinter hbound hAφ hBφ
      (fun i => (hA i).1)
  obtain ⟨k, j, hkj, hprefix, hpositiveA, hpositiveB, hweakSuffix⟩ :=
    exists_positive_compactified_suffix
      A B hA hB hweak hpaired hlast
  obtain ⟨q, a₀, b₀, hq, hresidual, hresidualPhi, hstieltjes⟩ :=
    exists_strict_residual_of_weak_interlacing
      (compactified_finite_suffix_weak_interlacing
        hkj A B hpositiveA hpositiveB hweakSuffix)
  have hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k := by
    intro i
    constructor
    · intro hi
      by_contra hnot
      have hki : k ≤ i.val := Nat.le_of_not_gt hnot
      let i₀ : Fin (r + 1) := ⟨k, by omega⟩
      have hpositive : 0 < A i₀ := by
        simpa only [compactifiedAmbientSuffix, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero] using
          (hpositiveA (0 : Fin (j + 1))).1
      have hle : i₀ ≤ i.castSucc := Fin.mk_le_mk.mpr hki
      exact (ne_of_gt
        (hpositive.trans_le
          (compactifiedAmbient_monotone_of_weak_interlacing hweak hle))) hi
    · intro hi
      exact (hprefix i hi).1
  have hratio : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)) := by
    intro i
    simpa [φ, aψ, bψ, Function.comp_apply] using hdχ i
  have hescape : ∀ i : Fin r, A i.castSucc = 0 →
      0 < d i ∧
        Tendsto (fun n => ((b (φ n) i) * (1 + (b (φ n) i))) /
          ((a (φ n) i.castSucc) * (1 + (a (φ n) i.castSucc))))
          atTop (nhds (d i ^ 2)) := by
    intro i hi
    have hatop : Tendsto (fun n => a (φ n) i.castSucc)
        atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (hinter (φ n)).ambient_nonneg i.castSucc)
        (hi ▸ hAφ i.castSucc)
    have hatop' : Tendsto (fun n => aψ (χ n) i.castSucc)
        atTop atTop := by
      simpa [aψ, φ, Function.comp_apply] using hatop
    exact ⟨hdpos i hatop', by
      simpa only [Function.comp_apply, φ, bψ, aψ] using hdquadratic i hatop'⟩
  let c : ℝ := ∏ i ∈ Finset.univ.filter
    (fun i : Fin r => i.val < k), d i
  have hcpos : 0 < c := by
    dsimp [c]
    apply Finset.prod_pos
    intro i hi
    exact (hescape i (hprefix i (Finset.mem_filter.mp hi).2).1).1
  have hcle : c ≤ 1 := by
    dsimp [c]
    apply Finset.prod_le_one
    · intro i _
      exact (hd i).1
    · intro i _
      exact (hd i).2
  have hdrop : c < 1 → q < r := by
    intro hc
    have hk : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
      have hcunit : c = 1 := by
        simp only [hkzero, not_lt_zero, Finset.filter_false, Finset.prod_empty, c]
      linarith
    omega
  have herror : Tendsto
      (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (nhds R) := by
    simpa only [one_div, add_zero] using
      (tendsto_const_nhds (x := R)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have herrorsub : Tendsto
      (fun n : ℕ => R + 1 / (((φ n : ℕ) : ℝ) + 1))
      atTop (nhds R) := by
    exact herror.comp hφ.tendsto_atTop
  have hdiff : Tendsto
      (fun n : ℕ =>
        Phi (a (φ n)) (b (φ n)) -
          (R + 1 / (((φ n : ℕ) : ℝ) + 1)))
      atTop (nhds (L - R)) := hLφ.sub herrorsub
  have hLR : L ≤ R := by
    have hle : L - R ≤ 0 := le_of_tendsto hdiff
      (Filter.Eventually.of_forall fun n => sub_nonpos.mpr (hPhi (φ n)))
    linarith
  refine ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
    hφ, hL.1, hLR, hA, hB, hAφ, hBφ, ?_, ?_, hLφ,
    hd, hratio, hpaired, hescape, hq, hresidual,
    hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
    hresidualPhi, hstieltjes, rfl, hcpos, hcle, hdrop⟩
  · exact hu.comp hφ.tendsto_atTop
  · intro n
    exact hgap (φ n)

end

section

open Filter Topology
open scoped BigOperators Topology

theorem tendsto_entropy_gap_of_compactified_paired_ratio
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B d : Fin r → ℝ}
    {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hd : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)))
    (i : Fin r) :
    Tendsto
      (fun n =>
        MetricCodes.sphericalEntropy (a (φ n) i.castSucc) -
          MetricCodes.sphericalEntropy (b (φ n) i))
      atTop
      (nhds
        (if A i.castSucc = 0 then -Real.logb 2 (d i)
         else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
           MetricCodes.sphericalEntropy ((B i)⁻¹ - 1))) := by
  by_cases hzero : A i.castSucc = 0
  · simp only [hzero, ↓reduceIte]
    have ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (h (φ n)).ambient_nonneg i.castSucc)
        (hzero ▸ hA i.castSucc)
    have hb : Tendsto (fun n => b (φ n) i) atTop atTop :=
      paired_stabilizer_tendsto_atTop_of_ambient h hPhi i ha
    have hpositive : 0 < d i :=
      paired_ratio_limit_pos_of_ambient_tendsto_atTop
        h hPhi i ha (hd i)
    exact tendsto_sphericalEntropy_sub_of_sequence_ratio
      hpositive ha hb (hd i)
  · simp only [hzero, ↓reduceIte]
    have hApos : 0 < A i.castSucc :=
      lt_of_le_of_ne (hAnonneg i.castSucc) (Ne.symm hzero)
    have hBzero : B i ≠ 0 := by
      intro hz
      have hpaired := paired_infinity_iff h hPhi hA hB
        hAnonneg i
      exact hzero (hpaired.mpr hz)
    have hBpos : 0 < B i :=
      lt_of_le_of_ne (hBnonneg i) (Ne.symm hBzero)
    have ha : Tendsto (fun n => a (φ n) i.castSucc)
        atTop (nhds ((A i.castSucc)⁻¹ - 1)) :=
      tendsto_of_compactifiedHierarchyCoordinate_pos hApos (hA i.castSucc)
    have hb : Tendsto (fun n => b (φ n) i)
        atTop (nhds ((B i)⁻¹ - 1)) :=
      tendsto_of_compactifiedHierarchyCoordinate_pos hBpos (hB i)
    exact
      (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp ha).sub
        (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp hb)

theorem tendsto_Phi_of_compactified_paired_ratios
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B d : Fin r → ℝ}
    {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hlast : 0 < A (Fin.last r))
    (hd : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i))) :
    Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop
      (nhds
        ((∑ i : Fin r,
            if A i.castSucc = 0 then -Real.logb 2 (d i)
            else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
              MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
          MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1))) := by
  have hgaps := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_entropy_gap_of_compactified_paired_ratio
      h hPhi hA hB hAnonneg hBnonneg hd i
  have hterminal : Tendsto (fun n => a (φ n) (Fin.last r))
      atTop (nhds ((A (Fin.last r))⁻¹ - 1)) :=
    tendsto_of_compactifiedHierarchyCoordinate_pos hlast
      (hA (Fin.last r))
  have hentropy :=
    MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp
      hterminal
  have htotal := hgaps.add hentropy
  apply htotal.congr'
  exact Filter.Eventually.of_forall fun n =>
    (Phi_eq_sum_entropy_gaps (a (φ n)) (b (φ n))).symm

end

section

open scoped BigOperators

private def compactifiedEscapingRatioProduct {r k j : ℕ}
    (hkj : k + j = r) (d : Fin r → ℝ) : ℝ :=
  ∏ i : Fin k, d ⟨i.val, by omega⟩

theorem sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
    {r k j : ℕ} (hkj : k + j = r) (d : Fin r → ℝ)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin k, -Real.logb 2 (d ⟨i.val, by omega⟩)) =
      -Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
  rw [Finset.sum_neg_distrib, compactifiedEscapingRatioProduct,
    Real.logb_prod]
  intro i _
  exact (hd ⟨i.val, by omega⟩ i.isLt).ne'

theorem forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
    {r k j : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) -
          Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
  classical
  subst r
  have hkj : k + j = k + j := rfl
  rw [Fin.sum_univ_add]
  have hprefix :
      (∑ i : Fin k,
        if A (i.castAdd j).castSucc = 0
        then -Real.logb 2 (d (i.castAdd j))
        else MetricCodes.sphericalEntropy
          ((A (i.castAdd j).castSucc)⁻¹ - 1) -
          MetricCodes.sphericalEntropy ((B (i.castAdd j))⁻¹ - 1)) =
        -Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
    rw [← sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
      hkj d hd]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.castAdd j).val < k := i.isLt
    rw [ite_eq_left ((hzero (i.castAdd j)).mpr hi)]
    congr 2
  have hsuffix :
      (∑ i : Fin j,
        if A (i.natAdd k).castSucc = 0
        then -Real.logb 2 (d (i.natAdd k))
        else MetricCodes.sphericalEntropy
          ((A (i.natAdd k).castSucc)⁻¹ - 1) -
          MetricCodes.sphericalEntropy ((B (i.natAdd k))⁻¹ - 1)) =
        ∑ i : Fin j,
          (MetricCodes.sphericalEntropy
            ((compactifiedAmbientSuffix hkj A i.castSucc)⁻¹ - 1) -
            MetricCodes.sphericalEntropy
              ((compactifiedStabilizerSuffix hkj B i)⁻¹ - 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : ¬ (i.natAdd k).val < k := by
      simp only [Fin.val_natAdd]
      omega
    rw [ite_eq_right (mt (hzero (i.natAdd k)).mp hi)]
    congr 2
  rw [hprefix, hsuffix,
    Phi_eq_sum_entropy_gaps
      (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
      (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1)]
  have hterminal :
      compactifiedAmbientSuffix hkj A (Fin.last j) =
        A (Fin.last (k + j)) := by
    unfold compactifiedAmbientSuffix
    congr 1
  rw [hterminal]
  ring

end

section

open Filter Topology
open scoped BigOperators Topology

theorem compactifiedEscapingRatioProduct_eq_filtered
    {r k j : ℕ} (hkj : k + j = r) (d : Fin r → ℝ) :
    compactifiedEscapingRatioProduct hkj d =
      ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i := by
  classical
  subst r
  unfold compactifiedEscapingRatioProduct
  apply Finset.prod_bij
    (fun i _ => (i.castAdd j : Fin (k + j)))
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i₁ _ i₂ _ heq
    apply Fin.ext
    simpa only [Fin.val_castAdd] using congrArg (fun z : Fin (k + j) => z.val) heq
  · intro i hi
    have hik : i.val < k := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hik⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

theorem compactified_entropy_sum_eq_residual_sub_logb
    {r k j q : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ) (c : ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i)
    (hresidualPhi :
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1))
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin r => i.val < k), d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi a₀ b₀ - Real.logb 2 c := by
  rw [forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
    hkj A B d hzero hd]
  rw [← hresidualPhi, compactifiedEscapingRatioProduct_eq_filtered hkj d,
    ← hc]

theorem compactified_entropy_limit_eq_residual_sub_logb
    {r k j q : ℕ} (hkj : k + j = r)
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B d : Fin r → ℝ}
    {φ : ℕ → ℕ} {C L c : ℝ}
    (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hlast : 0 < A (Fin.last r))
    (hratio : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)))
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i)
    (hlimit : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L))
    (hresidualPhi :
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1))
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin r => i.val < k), d i) :
    L = Phi a₀ b₀ - Real.logb 2 c := by
  have hforward := tendsto_Phi_of_compactified_paired_ratios
    hinter hPhi hA hB hAnonneg hBnonneg hlast hratio
  have hvalue := tendsto_nhds_unique hlimit hforward
  exact hvalue.trans
    (compactified_entropy_sum_eq_residual_sub_logb hkj A B d
      a₀ b₀ c hzero hd hresidualPhi hc)

theorem exists_forward_residual_entropy_of_closure_sequence
    {r : ℕ} {s R : ℝ}
    (u : ℕ → ℝ)
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ)
    (hu : Tendsto u atTop (nhds s))
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hgap : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (d : Fin r → ℝ) (φ : ℕ → ℕ)
      (k j : ℕ) (hkj : k + j = r)
      (q : ℕ) (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
      (c : ℝ),
      StrictMono φ ∧
      0 ≤ L ∧ L ≤ R ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
        atTop (nhds (B i))) ∧
      Tendsto (fun n => u (φ n)) atTop (nhds s) ∧
      (∀ n, u (φ n) < 2 * Gamma (a (φ n)) (b (φ n))) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop (nhds L) ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 →
        0 < d i ∧
        Tendsto
          (fun n => ((b (φ n) i) * (1 + (b (φ n) i))) /
            ((a (φ n) i.castSucc) * (1 + (a (φ n) i.castSucc))))
          atTop (nhds (d i ^ 2))) ∧
      q ≤ j ∧ Interlacing a₀ b₀ ∧
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) ∧
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) ∧
      (∀ t : ℝ, 0 < t →
        hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
            hierarchyStieltjesRatio a₀ b₀ t) ∧
      c = ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i ∧
      0 < c ∧ c ≤ 1 ∧ (c < 1 → q < r) ∧
      L = Phi a₀ b₀ - Real.logb 2 c := by
  obtain ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
      hφ, hLnonneg, hLR, hA, hB, hAlim, hBlim, hulim, hgaplim,
      hLlim, hd, hratio, hpaired, hescape, hq, hresidual,
      hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
      hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop⟩ :=
    exists_compactified_residual_of_closure_sequence
      u a b hu hinter hgap hPhi
  have hbound : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    refine (hPhi n).trans ?_
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    have hfrac : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    linarith
  have hlast : 0 < A (Fin.last r) := by
    have h := (hpositiveA (Fin.last j)).1
    have hindex :
        compactifiedAmbientSuffix hkj A (Fin.last j) = A (Fin.last r) := by
      unfold compactifiedAmbientSuffix
      congr 1
      apply Fin.ext
      simp only [Fin.val_last]
      exact hkj
    rw [hindex] at h
    exact h
  have hdprefix : ∀ i : Fin r, i.val < k → 0 < d i := by
    intro i hi
    exact (hescape i ((hzero i).mpr hi)).1
  have hentropy : L = Phi a₀ b₀ - Real.logb 2 c :=
    compactified_entropy_limit_eq_residual_sub_logb hkj a₀ b₀
      hinter hbound hAlim hBlim (fun i => (hA i).1)
      (fun i => (hB i).1) hlast hratio hzero hdprefix
      hLlim hresidualPhi hc
  exact ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
    hφ, hLnonneg, hLR, hA, hB, hAlim, hBlim, hulim, hgaplim,
    hLlim, hd, hratio, hpaired, hescape, hq, hresidual,
    hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
    hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop, hentropy⟩

end

section


open Filter Topology
open scoped BigOperators Topology

theorem quadratic_residue_ratio_eq_normalized
    (x u v : ℝ) (hu : u ≠ 0) :
    (x - (v * (1 + v))) / (x - (u * (1 + u))) =
      (x * (u⁻¹) ^ 2 - (v / u) ^ 2 - (v / u) * u⁻¹) /
        (x * (u⁻¹) ^ 2 - 1 - u⁻¹) := by
  field_simp [hu]
  ring

theorem tendsto_quadratic_residue_ratio_of_degree_ratio
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hd : Tendsto (fun k => v k / u k) atTop (𝓝 d))
    (x : ℝ) :
    Tendsto
      (fun k =>
        (x - ((v k) * (1 + (v k)))) /
          (x - ((u k) * (1 + (u k)))))
      atTop (𝓝 (d ^ 2)) := by
  have hinv : Tendsto (fun k => (u k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hnum : Tendsto
      (fun k => x * ((u k)⁻¹) ^ 2 - (v k / u k) ^ 2 -
        (v k / u k) * (u k)⁻¹)
      atTop (𝓝 (-d ^ 2)) := by
    convert ((tendsto_const_nhds.mul (hinv.pow 2)).sub
      (hd.pow 2)).sub (hd.mul hinv) using 1; norm_num
  have hden : Tendsto
      (fun k => x * ((u k)⁻¹) ^ 2 - 1 - (u k)⁻¹)
      atTop (𝓝 (-1)) := by
    convert ((tendsto_const_nhds.mul (hinv.pow 2)).sub
      tendsto_const_nhds).sub hinv using 1; norm_num
  have hlimit := hnum.div hden (by norm_num : (-1 : ℝ) ≠ 0)
  have hvalue : -d ^ 2 / (-1 : ℝ) = d ^ 2 := by ring
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with k hk
  exact (quadratic_residue_ratio_eq_normalized x (u k) (v k) hk.ne').symm

end

section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

private abbrev compactificationArcsineMeasure_metriccodes2_275785c2 : Measure ℝ :=
  (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)

theorem tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
    {r j : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A B) (c : ℝ)
    (hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c * stieltjesPhaseProduct A B t))) :
    Tendsto (fun n => 1 - 2 * Gamma (a n) (b n))
      atTop (𝓝 (c * (1 - 2 * Gamma A B))) := by
  have hdom :
      Tendsto
        (fun n => ∫ t : ℝ,
          stieltjesPhaseProduct (a n) (b n) t ∂compactificationArcsineMeasure_metriccodes2_275785c2)
        atTop
        (𝓝 (∫ t : ℝ,
          c * stieltjesPhaseProduct A B t
            ∂compactificationArcsineMeasure_metriccodes2_275785c2)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · intro n
      apply Measurable.aestronglyMeasurable
      unfold stieltjesPhaseProduct
      fun_prop
    · exact integrable_const (1 : ℝ)
    · intro n
      filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos] with t ht
      rw [Real.norm_eq_abs,
        abs_of_pos (stieltjesPhaseProduct_pos (h n) ht)]
      exact stieltjesPhaseProduct_le_one (h n) ht
    · filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos] with t ht
      exact hproduct t ht
  have hnormalizer {q : ℕ}
      (x : Fin (q + 1) → ℝ) (y : Fin q → ℝ)
      (hxy : Interlacing x y) :
      (∫ t : ℝ, stieltjesPhaseProduct x y t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        1 - 2 * Gamma x y := by
    calc
      (∫ t : ℝ,
          stieltjesPhaseProduct x y t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        ∫ t : ℝ,
          Real.exp (-stieltjesPhase x y t) ∂compactificationArcsineMeasure_metriccodes2_275785c2
            := by
            apply integral_congr_ae
            filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos]
              with t ht
            exact (exp_neg_stieltjesPhase_eq_product hxy ht).symm
      _ = 1 - 2 * Gamma x y := by
        apply integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma hxy
          compactificationArcsineMeasure_metriccodes2_275785c2
          ArcsineTransform.betaMap_half_half_ae_pos
        intro i
        rw [ArcsineTransform.arcsine_integral_self_div_add
          (hxy.ambient_quadratic_nonneg i),
          quadratic_spectralAtom_identity (hxy.ambient_nonneg i)]
  have htarget :
      (∫ t : ℝ,
        c * stieltjesPhaseProduct A B t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        c * (1 - 2 * Gamma A B) := by
    rw [integral_const_mul, hnormalizer A B hAB]
  simpa only [hnormalizer (a _) (b _) (h _), htarget] using hdom

theorem tendsto_Gamma_of_stieltjesPhaseProduct
    {r j : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A B) (c : ℝ)
    (hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c * stieltjesPhaseProduct A B t))) :
    Tendsto (fun n => Gamma (a n) (b n))
      atTop (𝓝 ((1 - c) / 2 + c * Gamma A B)) := by
  have hlimit :=
    tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
      a b A B h hAB c hproduct
  have hrecover := ((tendsto_const_nhds
    (x := (1 : ℝ))).sub hlimit).div_const 2
  convert hrecover using 1
  · ext n
    ring
  · ring_nf

end

section


open Filter Topology
open scoped BigOperators Topology

theorem hierarchyStieltjesRatio_append {k r : ℕ}
    (u v : Fin k → ℝ)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) :
    hierarchyStieltjesRatio
        (Fin.append (m := k) (n := r + 1) u a)
        (Fin.append (m := k) (n := r) v b) t =
      (∏ p : Fin k,
        (t + ((v p) * (1 + (v p)))) /
          (t + ((u p) * (1 + (u p))))) *
        hierarchyStieltjesRatio a b t := by
  unfold hierarchyStieltjesRatio
  change
    ((∏ p : Fin (k + r), _) /
      (∏ p : Fin (k + (r + 1)), _)) = _
  rw [Fin.prod_univ_add (a := k) (b := r),
    Fin.prod_univ_add (a := k) (b := r + 1)]
  simp only [Fin.append_left, Fin.append_right]
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem tendsto_quadraticCoordinate_of_tendsto
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => ((u n) * (1 + (u n))))
      atTop (𝓝 (x * (1 + x))) := by
  exact hu.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hu)

theorem tendsto_stieltjes_pair_factor_of_degree_ratio
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hd : Tendsto (fun n => v n / u n) atTop (𝓝 d))
    (t : ℝ) :
    Tendsto
      (fun n =>
        (t + ((v n) * (1 + (v n)))) /
          (t + ((u n) * (1 + (u n)))))
      atTop (𝓝 (d ^ 2)) := by
  have hlimit :=
    tendsto_quadratic_residue_ratio_of_degree_ratio hu hd (-t)
  apply hlimit.congr'
  filter_upwards [] with n
  rw [show -t - ((v n) * (1 + (v n))) =
      -(t + ((v n) * (1 + (v n)))) by ring,
    show -t - ((u n) * (1 + (u n))) =
      -(t + ((u n) * (1 + (u n)))) by ring]
  exact neg_div_neg_eq _ _

theorem tendsto_hierarchyStieltjesRatio_of_coordinatewise
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => hierarchyStieltjesRatio (a n) (b n) t)
      atTop (𝓝 (hierarchyStieltjesRatio A B t)) := by
  have hnum :
      Tendsto (fun n =>
        ∏ i : Fin r, (t + ((b n i) * (1 + (b n i)))))
        atTop (𝓝 (∏ i : Fin r, (t + ((B i) * (1 + (B i)))))) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact (tendsto_const_nhds (x := t)).add
      (tendsto_quadraticCoordinate_of_tendsto (hb i))
  have hden :
      Tendsto (fun n =>
        ∏ i : Fin (r + 1), (t + ((a n i) * (1 + (a n i)))))
        atTop (𝓝 (∏ i : Fin (r + 1), (t + ((A i) * (1 + (A i)))))) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact (tendsto_const_nhds (x := t)).add
      (tendsto_quadraticCoordinate_of_tendsto (ha i))
  have hnonzero :
      (∏ i : Fin (r + 1), (t + ((A i) * (1 + (A i))))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hq : 0 ≤ ((A i) * (1 + (A i))) := by
      exact mul_nonneg (hA i) (by linarith [hA i])
    linarith
  exact hnum.div hden hnonzero

theorem tendsto_hierarchyStieltjesRatio_append_of_escaping
    {k r : ℕ}
    {u v : ℕ → Fin k → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    {d : Fin k → ℝ}
    (hu : ∀ i, Tendsto (fun n => u n i) atTop atTop)
    (hd : ∀ i, Tendsto (fun n => v n i / u n i) atTop (𝓝 (d i)))
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n => hierarchyStieltjesRatio
        (Fin.append (m := k) (n := r + 1) (u n) (a n))
        (Fin.append (m := k) (n := r) (v n) (b n)) t)
      atTop
      (𝓝 ((∏ i : Fin k, d i ^ 2) * hierarchyStieltjesRatio A B t)) := by
  have hprefix :
      Tendsto (fun n =>
        ∏ i : Fin k,
          (t + ((v n i) * (1 + (v n i)))) /
            (t + ((u n i) * (1 + (u n i)))))
        atTop (𝓝 (∏ i : Fin k, d i ^ 2)) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact tendsto_stieltjes_pair_factor_of_degree_ratio (hu i) (hd i) t
  have htail :=
    tendsto_hierarchyStieltjesRatio_of_coordinatewise ha hb hA ht
  have hproduct := hprefix.mul htail
  apply hproduct.congr'
  filter_upwards [] with n
  exact (hierarchyStieltjesRatio_append (u n) (v n) (a n) (b n) t).symm

theorem stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
    {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) :
    stieltjesPhaseProduct a b t =
      t * hierarchyStieltjesRatio a b t := by
  unfold stieltjesPhaseProduct hierarchyStieltjesRatio
  ring

theorem tendsto_stieltjesPhaseProduct_append_of_escaping
    {k r : ℕ}
    {u v : ℕ → Fin k → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    {d : Fin k → ℝ}
    (hu : ∀ i, Tendsto (fun n => u n i) atTop atTop)
    (hd : ∀ i, Tendsto (fun n => v n i / u n i) atTop (𝓝 (d i)))
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n => stieltjesPhaseProduct
        (Fin.append (m := k) (n := r + 1) (u n) (a n))
        (Fin.append (m := k) (n := r) (v n) (b n)) t)
      atTop
      (𝓝 ((∏ i : Fin k, d i ^ 2) * stieltjesPhaseProduct A B t)) := by
  have hratio := tendsto_hierarchyStieltjesRatio_append_of_escaping
    hu hd ha hb hA ht
  have hlimit := (tendsto_const_nhds (x := t)).mul hratio
  convert hlimit using 1
  · ext n
    rw [stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio]
  · rw [stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio]
    ring_nf

theorem append_ambient_prefix_suffix {k r : ℕ}
    (a : Fin (k + r + 1) → ℝ) :
    Fin.append (m := k) (n := r + 1)
        (fun i : Fin k => a (i.castAdd (r + 1)))
        (fun i : Fin (r + 1) => a (i.natAdd k)) = a := by
  funext i
  refine Fin.addCases (m := k) (n := r + 1) ?_ ?_ i
  · intro p
    simp only [Fin.append_left]
  · intro p
    simp only [Fin.append_right]

theorem append_stabilizer_prefix_suffix {k r : ℕ}
    (b : Fin (k + r) → ℝ) :
    Fin.append (m := k) (n := r)
        (fun i : Fin k => b (i.castAdd r))
        (fun i : Fin r => b (i.natAdd k)) = b := by
  funext i
  refine Fin.addCases (m := k) (n := r) ?_ ?_ i
  · intro p
    simp only [Fin.append_left]
  · intro p
    simp only [Fin.append_right]

theorem tendsto_stieltjesPhaseProduct_of_escaping_prefix
    {k r : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (d : Fin k → ℝ)
    (hu : ∀ i : Fin k,
      Tendsto (fun n => a n (i.castAdd (r + 1))) atTop atTop)
    (hd : ∀ i : Fin k,
      Tendsto (fun n =>
        b n (i.castAdd r) / a n (i.castAdd (r + 1)))
        atTop (𝓝 (d i)))
    (ha : ∀ i : Fin (r + 1),
      Tendsto (fun n => a n (i.natAdd k)) atTop (𝓝 (A i)))
    (hb : ∀ i : Fin r,
      Tendsto (fun n => b n (i.natAdd k)) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop (𝓝 ((∏ i : Fin k, d i ^ 2) * stieltjesPhaseProduct A B t)) := by
  have hlimit := tendsto_stieltjesPhaseProduct_append_of_escaping
    (u := fun n i => a n (i.castAdd (r + 1)))
    (v := fun n i => b n (i.castAdd r))
    (a := fun n i => a n (i.natAdd k))
    (b := fun n i => b n (i.natAdd k))
    hu hd ha hb hA ht
  apply hlimit.congr'
  filter_upwards [] with n
  rw [append_ambient_prefix_suffix, append_stabilizer_prefix_suffix]

theorem tendsto_stieltjesPhaseProduct_of_escaping_prefix_strict_residual
    {k r q : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (d : Fin k → ℝ)
    (hu : ∀ i : Fin k,
      Tendsto (fun n => a n (i.castAdd (r + 1))) atTop atTop)
    (hd : ∀ i : Fin k,
      Tendsto (fun n =>
        b n (i.castAdd r) / a n (i.castAdd (r + 1)))
        atTop (𝓝 (d i)))
    (ha : ∀ i : Fin (r + 1),
      Tendsto (fun n => a n (i.natAdd k)) atTop (𝓝 (A i)))
    (hb : ∀ i : Fin r,
      Tendsto (fun n => b n (i.natAdd k)) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio A B t = hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop (𝓝 ((∏ i : Fin k, d i ^ 2) * stieltjesPhaseProduct A' B' t)) := by
  have hlimit := tendsto_stieltjesPhaseProduct_of_escaping_prefix
    a b A B d hu hd ha hb hA ht
  convert hlimit using 1
  rw [stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio,
    stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio,
    hratio t ht]

theorem tendsto_stieltjesPhaseProduct_of_compactified_prefix
    {k r q : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (k + r + 1) → ℝ)
    (B d : Fin (k + r) → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (a n i))
        atTop (𝓝 (A i)))
    (hb : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (b n i))
        atTop (𝓝 (B i)))
    (hd : ∀ i,
      Tendsto (fun n => b n i / a n i.castSucc)
        atTop (𝓝 (d i)))
    (hzero : ∀ i : Fin k, A (i.castAdd (r + 1)) = 0)
    (hpositiveA : ∀ i : Fin (r + 1), 0 < A (i.natAdd k))
    (hpositiveB : ∀ i : Fin r, 0 < B (i.natAdd k))
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i : Fin (r + 1) => (A (i.natAdd k))⁻¹ - 1)
          (fun i : Fin r => (B (i.natAdd k))⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop
      (𝓝 ((∏ i : Fin k, d (i.castAdd r) ^ 2) *
        stieltjesPhaseProduct A' B' t)) := by
  apply tendsto_stieltjesPhaseProduct_of_escaping_prefix_strict_residual
    a b
    (fun i : Fin (r + 1) => (A (i.natAdd k))⁻¹ - 1)
    (fun i : Fin r => (B (i.natAdd k))⁻¹ - 1)
    A' B' (fun i : Fin k => d (i.castAdd r))
    (t := t)
  · intro i
    apply tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
      (fun n => (h n).ambient_nonneg (i.castAdd (r + 1)))
    simpa only [hzero i] using ha (i.castAdd (r + 1))
  · intro i
    have hindex : (i.castAdd r).castSucc = i.castAdd (r + 1) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_castAdd]
    simpa only [hindex] using hd (i.castAdd r)
  · intro i
    exact tendsto_of_compactifiedHierarchyCoordinate_pos
      (hpositiveA i) (ha (i.natAdd k))
  · intro i
    exact tendsto_of_compactifiedHierarchyCoordinate_pos
      (hpositiveB i) (hb (i.natAdd k))
  · intro i
    exact compactifiedHierarchyCoordinate_recovered_nonneg
      (hpositiveA i) (hA (i.natAdd k)).2
  · exact hratio
  · exact ht

theorem tendsto_stieltjesPhaseProduct_of_compactified_suffix
    {R k j q : ℕ} (hkj : k + j = R)
    (a : ℕ → Fin (R + 1) → ℝ)
    (b : ℕ → Fin R → ℝ)
    (A : Fin (R + 1) → ℝ)
    (B d : Fin R → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (a n i))
        atTop (𝓝 (A i)))
    (hb : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (b n i))
        atTop (𝓝 (B i)))
    (hd : ∀ i,
      Tendsto (fun n => b n i / a n i.castSucc)
        atTop (𝓝 (d i)))
    (hzero : ∀ i : Fin R, i.val < k → A i.castSucc = 0)
    (hpositiveA : ∀ i,
      0 < compactifiedAmbientSuffix hkj A i)
    (hpositiveB : ∀ i,
      0 < compactifiedStabilizerSuffix hkj B i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop
      (𝓝 ((compactifiedEscapingRatioProduct hkj d) ^ 2 *
        stieltjesPhaseProduct A' B' t)) := by
  subst R
  have hzero' : ∀ i : Fin k, A (i.castAdd (j + 1)) = 0 := by
    intro i
    have hz := hzero (i.castAdd j) i.isLt
    have hindex : (i.castAdd j).castSucc = i.castAdd (j + 1) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_castAdd]
    simpa only [hindex] using hz
  have hindexA (i : Fin (j + 1)) :
      compactifiedAmbientSuffix (rfl : k + j = k + j) A i =
        A (i.natAdd k) := by
    unfold compactifiedAmbientSuffix
    congr 1
  have hindexB (i : Fin j) :
      compactifiedStabilizerSuffix (rfl : k + j = k + j) B i =
        B (i.natAdd k) := by
    unfold compactifiedStabilizerSuffix
    congr 1
  have hpositiveA' : ∀ i : Fin (j + 1), 0 < A (i.natAdd k) := by
    intro i
    simpa only [hindexA] using hpositiveA i
  have hpositiveB' : ∀ i : Fin j, 0 < B (i.natAdd k) := by
    intro i
    simpa only [hindexB] using hpositiveB i
  have hratio' : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i : Fin (j + 1) => (A (i.natAdd k))⁻¹ - 1)
          (fun i : Fin j => (B (i.natAdd k))⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t := by
    intro t ht
    simpa only [hindexA, hindexB] using hratio t ht
  have hlimit := tendsto_stieltjesPhaseProduct_of_compactified_prefix
    a b A B d A' B' h hA ha hb hd hzero' hpositiveA' hpositiveB'
    hratio' ht
  have hproduct :
      compactifiedEscapingRatioProduct (rfl : k + j = k + j) d =
        ∏ i : Fin k, d (i.castAdd j) := by
    unfold compactifiedEscapingRatioProduct
    apply Finset.prod_congr rfl
    intro i _
    congr 1
  rw [hproduct, ← Finset.prod_pow]
  exact hlimit

theorem compactifiedEscapingRatioProduct_eq_filtered_prefix
    {R k j : ℕ} (hkj : k + j = R) (d : Fin R → ℝ) :
    compactifiedEscapingRatioProduct hkj d =
      ∏ i ∈ Finset.univ.filter (fun i : Fin R => i.val < k), d i := by
  classical
  subst R
  unfold compactifiedEscapingRatioProduct
  apply Finset.prod_bij
    (fun i _ => (i.castAdd j : Fin (k + j)))
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
  · intro i₁ _ i₂ _ heq
    apply Fin.ext
    simpa only [Fin.val_castAdd] using congrArg (fun z : Fin (k + j) => z.val) heq
  · intro i hi
    have hik : i.val < k := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hik⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

theorem tendsto_Gamma_of_compactified_suffix
    {R k j q : ℕ} (hkj : k + j = R)
    (a : ℕ → Fin (R + 1) → ℝ)
    (b : ℕ → Fin R → ℝ)
    (A : Fin (R + 1) → ℝ)
    (B d : Fin R → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (c : ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A' B')
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (a n i))
        atTop (𝓝 (A i)))
    (hb : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (b n i))
        atTop (𝓝 (B i)))
    (hd : ∀ i,
      Tendsto (fun n => b n i / a n i.castSucc)
        atTop (𝓝 (d i)))
    (hzero : ∀ i : Fin R, i.val < k → A i.castSucc = 0)
    (hpositiveA : ∀ i,
      0 < compactifiedAmbientSuffix hkj A i)
    (hpositiveB : ∀ i,
      0 < compactifiedStabilizerSuffix hkj B i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin R => i.val < k), d i) :
    Tendsto (fun n => Gamma (a n) (b n))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A' B')) := by
  have hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c ^ 2 * stieltjesPhaseProduct A' B' t)) := by
    intro t ht
    have hlimit := tendsto_stieltjesPhaseProduct_of_compactified_suffix
      hkj a b A B d A' B' h hA ha hb hd hzero
      hpositiveA hpositiveB hratio ht
    rw [compactifiedEscapingRatioProduct_eq_filtered_prefix hkj d,
      ← hc] at hlimit
    exact hlimit
  exact tendsto_Gamma_of_stieltjesPhaseProduct
    a b A' B' h hAB (c ^ 2) hproduct

end

section

open Filter Topology
open scoped Topology

theorem tendsto_certificate_slack_of_strictMono
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1))
      atTop (nhds 0) := by
  exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    hφ.tendsto_atTop

theorem compactified_certificate_entropy_le
    {r : ℕ} {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ} {φ : ℕ → ℕ} {R L : ℝ}
    (hφ : StrictMono φ)
    (hbound : ∀ n, Phi (a n) (b n) ≤
      R + 1 / ((n : ℝ) + 1))
    (hlimit : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L)) :
    L ≤ R := by
  have hupper : Tendsto
      (fun n : ℕ => R + 1 / ((φ n : ℝ) + 1))
      atTop (nhds R) := by
    simpa only [one_div, add_zero] using
      (tendsto_const_nhds (x := R)).add (tendsto_certificate_slack_of_strictMono hφ)
  exact le_of_tendsto_of_tendsto hlimit hupper
    (Filter.Eventually.of_forall fun n => hbound (φ n))

theorem compactified_certificate_threshold_le
    {r : ℕ} {u : ℕ → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ} {φ : ℕ → ℕ} {s Q : ℝ}
    (hφ : StrictMono φ)
    (hthreshold : Tendsto u atTop (nhds s))
    (hfeasible : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hspectral : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n))) atTop (nhds Q)) :
    s ≤ 2 * Q := by
  have hu : Tendsto (fun n => u (φ n)) atTop (nhds s) :=
    hthreshold.comp hφ.tendsto_atTop
  have htwo : Tendsto
      (fun n => 2 * Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (2 * Q)) :=
    hspectral.const_mul 2
  exact le_of_tendsto_of_tendsto hu htwo
    (Filter.Eventually.of_forall fun n => (hfeasible (φ n)).le)

theorem compactified_certificate_residual_threshold_le
    {r j : ℕ} {u : ℕ → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ}
    {A : Fin (j + 1) → ℝ} {B : Fin j → ℝ}
    {φ : ℕ → ℕ} {s c : ℝ}
    (hφ : StrictMono φ)
    (hthreshold : Tendsto u atTop (nhds s))
    (hfeasible : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hspectral : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B))) :
    s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) := by
  have h := compactified_certificate_threshold_le
    hφ hthreshold hfeasible hspectral
  nlinarith

private def FixedLevelForwardCompactifiedResidualLimit (r : ℕ) : Prop :=
  ∀ {C : ℝ}
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ),
    (∀ n, Interlacing (a n) (b n)) →
    (∀ n, Phi (a n) (b n) ≤ C) →
    ∃ (j : ℕ) (c : ℝ)
      (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
      (φ : ℕ → ℕ),
      StrictMono φ ∧ 0 < c ∧ c ≤ 1 ∧ Interlacing A B ∧
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) ∧
      Tendsto (fun n => Gamma (a (φ n)) (b (φ n)))
        atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B)) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
        atTop (nhds (Phi A B - Real.logb 2 c))

theorem fixedLevelCompactifiedCertificateClosure_of_forward_residual_and_realization
    {r : ℕ}
    (hforward : FixedLevelForwardCompactifiedResidualLimit r)
    (hrealize : ∀ {j : ℕ} {s c : ℝ}
      (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ),
      0 < s → s < 1 → 0 < c → c ≤ 1 →
      Interlacing A B →
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) →
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) →
      levelRate r s ≤ Phi A B - Real.logb 2 c) :
    FixedLevelCompactifiedCertificateClosure r := by
  intro s R hs hs' u a b hu hinter hgap hPhi
  have huniform : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    calc
      Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1) := hPhi n
      _ ≤ R + 1 := by
        apply add_le_add (le_refl R)
        apply (div_le_iff₀ (by positivity)).2
        norm_num
  obtain ⟨j, c, A, B, φ, hφ, hc, hc', hAB,
    hlevels, hGamma, hentropy⟩ := hforward a b hinter huniform
  have hclosed := compactified_certificate_residual_threshold_le
    hφ hu hgap hGamma
  have hbound := compactified_certificate_entropy_le
    hφ hPhi hentropy
  exact (hrealize A B hs hs' hc hc' hAB hclosed hlevels).trans hbound

theorem fixedLevelCompactifiedCertificateClosure_of_forward_residual
    {r : ℕ}
    (hforward : FixedLevelForwardCompactifiedResidualLimit r) :
    FixedLevelCompactifiedCertificateClosure r := by
  apply fixedLevelCompactifiedCertificateClosure_of_forward_residual_and_realization
    hforward
  intro j s c A B hs hs' hc hc' hAB hclosed hlevels
  exact levelRate_le_compactified_boundary_datum
    hs hs' hc hc' A B hAB hclosed hlevels

theorem fixedLevelForwardCompactifiedResidualLimit
    (r : ℕ) : FixedLevelForwardCompactifiedResidualLimit r := by
  intro C a b hinter hbound
  have hnegative : ∀ n, (-1 : ℝ) < 2 * Gamma (a n) (b n) := by
    intro n
    linarith [(hinter n).Gamma_nonneg]
  have herror : ∀ n : ℕ,
      Phi (a n) (b n) ≤ C + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith [hbound n]
  obtain ⟨L, X, Y, d, φ, k, j, hkj, q, A, B, c,
      hφ, hLnonneg, hLC, hX, hY, hXlim, hYlim,
      hthreshold, hnegativeφ, hPhilim, hd, hdlim,
      hpaired, hescape, hq, hAB, hprefix, hzero,
      hpositiveX, hpositiveY, hweak,
      hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop,
      hPhiidentity⟩ :=
    exists_forward_residual_entropy_of_closure_sequence
      (fun _ : ℕ => (-1 : ℝ)) a b
      (tendsto_const_nhds (x := (-1 : ℝ)))
      hinter hnegative herror
  have hGamma : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B)) := by
    exact tendsto_Gamma_of_compactified_suffix
      hkj (fun n => a (φ n)) (fun n => b (φ n)) X Y d A B c
      (fun n => hinter (φ n)) hAB hX hXlim hYlim hdlim
      (fun i hi => (hprefix i hi).1)
      (fun i => (hpositiveX i).1)
      (fun i => (hpositiveY i).1)
      hstieltjes hc
  have hlevels : (c = 1 ∧ q ≤ r) ∨ (c < 1 ∧ q + 1 ≤ r) := by
    rcases hcle.lt_or_eq with hc_lt | hc_one
    · exact Or.inr ⟨hc_lt, by have hqr := hdrop hc_lt; omega⟩
    · exact Or.inl ⟨hc_one, by omega⟩
  refine ⟨q, c, A, B, φ, hφ, hcpos, hcle, hAB, hlevels, hGamma, ?_⟩
  simpa only [hPhiidentity] using hPhilim

theorem fixedLevelCompactifiedCertificateClosure
    (r : ℕ) : FixedLevelCompactifiedCertificateClosure r :=
  fixedLevelCompactifiedCertificateClosure_of_forward_residual
    (fixedLevelForwardCompactifiedResidualLimit r)

end

section

theorem levelRate_succ_lt_of_compactified_positive_minimizer
    {r j : ℕ} {s c : ℝ}
    {a : Fin (j + 1) → ℝ} {b : Fin j → ℝ}
    (hj : j ≤ r) (hc : 0 < c) (hc' : c ≤ 1)
    (hdrop : c < 1 → j < r)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last j))
    (hfeasible : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hmin : levelRate r s = Phi a b - Real.logb 2 c)
    (htransfer : ∀ {k j' : ℕ}
      (A : Fin (j' + 1) → ℝ) (B : Fin j' → ℝ),
      Interlacing A B →
      s < 1 - c ^ 2 * (1 - 2 * Gamma A B) →
      ((c = 1 ∧ j' ≤ k) ∨ (c < 1 ∧ j' + 1 ≤ k)) →
      levelRate k s ≤ Phi A B - Real.logb 2 c) :
    levelRate (r + 1) s < levelRate r s := by
  obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
    exists_nextLevel_strict_refinement h hlast
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hgap : s < 1 - c ^ 2 * (1 - 2 * Gamma A B) := by
    nlinarith
  have hlevels :
      (c = 1 ∧ j + 1 ≤ r + 1) ∨
        (c < 1 ∧ (j + 1) + 1 ≤ r + 1) := by
    rcases lt_or_eq_of_le hc' with hlt | rfl
    · have hjdrop := hdrop hlt
      exact Or.inr ⟨hlt, by omega⟩
    · exact Or.inl ⟨rfl, by omega⟩
  calc
    levelRate (r + 1) s ≤ Phi A B - Real.logb 2 c :=
      htransfer A B hAB hgap hlevels
    _ < Phi a b - Real.logb 2 c := by linarith
    _ = levelRate r s := hmin.symm

end

section


theorem log_inv_lt_half_inv_sub_self {t : ℝ}
    (ht : 0 < t) (ht' : t < 1) :
    Real.log (1 / t) < (1 / t - t) / 2 := by
  let x : ℝ := (1 - t) / (1 + t)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx' : x < 1 := by
    dsimp [x]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hratio : (1 + x) / (1 - x) = 1 / t := by
    dsimp [x]
    field_simp [ht.ne']
    ring
  have hseries :
      Real.log (1 / t) ≤ MetricCodes.Numerics.logSeriesUpper x 2 := by
    rw [← hratio]
    exact MetricCodes.Numerics.log_ratio_upper hx.le hx' 2
  have hstrict :
      MetricCodes.Numerics.logSeriesUpper x 2 <
        2 * x / (1 - x ^ 2) := by
    have hgap : 2 * x / (1 - x ^ 2) -
        MetricCodes.Numerics.logSeriesUpper x 2 =
          (4 / 3 : ℝ) * x ^ 3 := by
      unfold MetricCodes.Numerics.logSeriesUpper
        MetricCodes.Numerics.logSeriesLower
      norm_num [Finset.sum_range_succ]
      field_simp [hden.ne']
      ring
    exact sub_pos.mp (by rw [hgap]; positivity)
  have hvalue : 2 * x / (1 - x ^ 2) = (1 / t - t) / 2 := by
    dsimp [x]
    field_simp [ht.ne']
    rw [show (1 + t) ^ 2 - (1 - t) ^ 2 = 4 * t by ring]
    field_simp [ht.ne']
    ring
  exact hseries.trans_lt (hstrict.trans_eq hvalue)

theorem lt_log_one_add_add_half_log_one_add_sq {t : ℝ}
    (ht : 0 < t) (ht' : t < 1) :
    t < Real.log (1 + t) + (1 / 2 : ℝ) * Real.log (1 + t ^ 2) := by
  let x : ℝ := t / (2 + t)
  let y : ℝ := t ^ 2 / (2 + t ^ 2)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx' : x < 1 := by
    dsimp [x]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y < 1 := by
    dsimp [y]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hxratio : (1 + x) / (1 - x) = 1 + t := by
    dsimp [x]
    field_simp
    ring
  have hyratio : (1 + y) / (1 - y) = 1 + t ^ 2 := by
    dsimp [y]
    field_simp
    ring
  have hxlog : 2 * x ≤ Real.log (1 + t) := by
    have h := MetricCodes.Numerics.log_ratio_lower hx hx' 1
    rw [hxratio] at h
    simpa only [ge_iff_le, Numerics.logSeriesLower, Finset.range_one, Finset.sum_singleton,
      mul_zero, zero_add, pow_one, CharP.cast_eq_zero, div_one] using h
  have hylog : 2 * y ≤ Real.log (1 + t ^ 2) := by
    have h := MetricCodes.Numerics.log_ratio_lower hy hy' 1
    rw [hyratio] at h
    simpa only [ge_iff_le, Numerics.logSeriesLower, Finset.range_one, Finset.sum_singleton,
      mul_zero, zero_add, pow_one, CharP.cast_eq_zero, div_one] using h
  have hrational : t < 2 * x + y := by
    dsimp [x, y]
    have hden₁ : 0 < 2 + t := by linarith
    have hden₂ : 0 < 2 + t ^ 2 := by positivity
    apply sub_pos.mp
    have hidentity :
        2 * (t / (2 + t)) + t ^ 2 / (2 + t ^ 2) - t =
          t ^ 3 * (1 - t) / ((2 + t) * (2 + t ^ 2)) := by
      field_simp
      ring
    rw [hidentity]
    exact div_pos
      (mul_pos (pow_pos ht 3) (sub_pos.mpr ht'))
      (mul_pos hden₁ hden₂)
  nlinarith

theorem classicalThreshold_entropy_lt_half_neg_logb
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) <
      -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
  let u : ℝ := Real.sqrt (1 - s ^ 2)
  let t : ℝ := s / (1 + u)
  let a : ℝ := MetricCodes.classicalThreshold s
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.mpr hrad
  have hu_sq : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrad.le
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : t < 1 := by
    dsimp [t]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have htden : 0 < 1 - t ^ 2 := by nlinarith
  have hsparam : s = 2 * t / (1 + t ^ 2) := by
    dsimp [t]
    field_simp
    nlinarith [hu_sq]
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have ht_sq : t ^ 2 = (1 - u) / (1 + u) := by
    dsimp [t]
    field_simp
    nlinarith [hu_sq]
  have haparam : a = t ^ 2 / (1 - t ^ 2) := by
    change (1 / u - 1) / 2 = t ^ 2 / (1 - t ^ 2)
    rw [ht_sq]
    field_simp [hu.ne', (by positivity : 1 + u ≠ 0)]
    ring
  have hones : 1 - s = (1 - t) ^ 2 / (1 + t ^ 2) := by
    rw [hsparam]
    field_simp
    ring
  have honea : 1 + a = 1 / (1 - t ^ 2) := by
    rw [haparam]
    field_simp [htden.ne']
    ring
  have hratio : (1 + a) / a = (1 / t) ^ 2 := by
    rw [haparam]
    field_simp [ht.ne', htden.ne']
    ring
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hentropy :
      Real.log 2 * MetricCodes.sphericalEntropy a =
        Real.log (1 + a) + a * Real.log ((1 + a) / a) := by
    rw [MetricCodes.sphericalEntropy_eq_log_add ha]
    unfold Real.logb
    field_simp [hlogtwo.ne']
  have hlogones :
      Real.log (1 - s) =
        2 * Real.log (1 - t) - Real.log (1 + t ^ 2) := by
    rw [hones, Real.log_div (by positivity) (by positivity),
      Real.log_pow]
    norm_num
  have hlogonea :
      Real.log (1 + a) =
        -(Real.log (1 - t) + Real.log (1 + t)) := by
    rw [honea, one_div, Real.log_inv]
    have hfactor : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
    rw [hfactor, Real.log_mul (by linarith) (by linarith)]
  have hlogratio :
      Real.log ((1 + a) / a) = 2 * Real.log (1 / t) := by
    rw [hratio, Real.log_pow]
    norm_num
  have hfirst :
      t < Real.log (1 + t) +
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2) :=
    lt_log_one_add_add_half_log_one_add_sq ht ht'
  have hlast :
      2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) < t := by
    have hcoefficient : 0 < 2 * t ^ 2 / (1 - t ^ 2) := by positivity
    calc
      2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) <
          2 * t ^ 2 / (1 - t ^ 2) * ((1 / t - t) / 2) :=
        mul_lt_mul_of_pos_left (log_inv_lt_half_inv_sub_self ht ht')
          hcoefficient
      _ = t := by
        field_simp [ht.ne', htden.ne']
  have hgap : 0 < Real.log (1 + t) +
      (1 / 2 : ℝ) * Real.log (1 + t ^ 2) -
        2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) := by
    linarith
  have hidentity :
      Real.log 2 *
          (-(1 / 2 : ℝ) * Real.logb 2 (1 - s) -
            MetricCodes.sphericalEntropy a) =
        Real.log (1 + t) +
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2) -
            2 * t ^ 2 / (1 - t ^ 2) * Real.log (1 / t) := by
    calc
      _ = -(1 / 2 : ℝ) * Real.log (1 - s) -
          Real.log 2 * MetricCodes.sphericalEntropy a := by
        unfold Real.logb
        field_simp [hlogtwo.ne']
      _ = -(1 / 2 : ℝ) * Real.log (1 - s) -
          (Real.log (1 + a) + a * Real.log ((1 + a) / a)) := by
        rw [hentropy]
      _ = _ := by
        rw [hlogones, hlogonea, hlogratio, haparam]
        ring
  have hpositive :
      0 < -(1 / 2 : ℝ) * Real.logb 2 (1 - s) -
        MetricCodes.sphericalEntropy a := by
    apply (mul_pos_iff_of_pos_left hlogtwo).mp
    rw [hidentity]
    exact hgap
  exact sub_pos.mp hpositive

end

section

theorem compactified_zero_residual_cost_le
    {s c : ℝ} (_hs : 0 < s) (_hs' : s < 1)
    (hc : 0 < c) (hfeasible : s ≤ 1 - c ^ 2) :
    -(1 / 2 : ℝ) * Real.logb 2 (1 - s) ≤ -Real.logb 2 c := by
  have hcsquare : 0 < c ^ 2 := sq_pos_of_pos hc
  have hsquare : c ^ 2 ≤ 1 - s := by linarith
  have hlog : Real.logb 2 (c ^ 2) ≤ Real.logb 2 (1 - s) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hcsquare hsquare
  rw [Real.logb_pow] at hlog
  norm_num at hlog ⊢
  linarith

theorem classicalThreshold_entropy_lt_neg_logb_of_compactified_zero
    {s c : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c) (hfeasible : s ≤ 1 - c ^ 2) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) <
      -Real.logb 2 c :=
  (classicalThreshold_entropy_lt_half_neg_logb hs hs').trans_le
    (compactified_zero_residual_cost_le hs hs' hc hfeasible)

end

section

open Filter Topology
open scoped Topology

theorem levelRate_zero_le_entropy_of_classicalThreshold_lt
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1)
    (ha : MetricCodes.classicalThreshold s < a) :
    levelRate 0 s ≤ MetricCodes.sphericalEntropy a := by
  have hthreshold := MetricCodes.classicalThreshold_pos hs hs'
  let A : Fin 1 → ℝ := fun _ => a
  let B : Fin 0 → ℝ := Fin.elim0
  have hA : Interlacing A B := by
    constructor
    · dsimp [A]
      linarith
    · intro i
      exact Fin.elim0 i
  have hboundary : spectralAtom (MetricCodes.classicalThreshold s) = s / 2 := by
    have h := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
    rw [MetricCodes.Spherical.Gamma_zero hthreshold] at h
    change 2 * spectralAtom (MetricCodes.classicalThreshold s) = s at h
    linarith
  have hmono := spectralAtom_strictMonoOn hthreshold.le
    (show 0 ≤ a by linarith) ha
  have hgap : s < 2 * Gamma A B := by
    rw [Gamma_zero]
    change s < 2 * spectralAtom a
    linarith
  simpa only [ge_iff_le, Phi_zero] using levelRate_le hA hgap

theorem levelRate_zero_eq_classical_of_pos
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    levelRate 0 s =
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  apply le_antisymm
  · let a : ℕ → ℝ := fun n =>
      MetricCodes.classicalThreshold s + 1 / ((n : ℝ) + 1)
    have ha : Tendsto a atTop (nhds (MetricCodes.classicalThreshold s)) := by
      simpa [a] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hentropy : Tendsto
        (fun n => MetricCodes.sphericalEntropy (a n)) atTop
        (nhds (MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s))) :=
      MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.tendsto.comp ha
    apply ge_of_tendsto hentropy
    exact Filter.Eventually.of_forall fun n =>
      levelRate_zero_le_entropy_of_classicalThreshold_lt hs hs'
        (by
          dsimp [a]
          exact lt_add_of_pos_right _ (by positivity))
  · exact classical_le_levelRate_zero hs hs'

theorem levelRate_zero_eq_classical
    {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    levelRate 0 s =
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  rcases eq_or_lt_of_le hs with hzero | hpositive
  · subst s
    simp only [levelRate_at_zero, classicalThreshold_zero, sphericalEntropy_zero]
  · exact levelRate_zero_eq_classical_of_pos hpositive hs'

theorem exists_compactified_levelRate_minimizer
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ (j : ℕ) (c : ℝ)
      (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ),
      0 < c ∧ c ≤ 1 ∧ Interlacing a b ∧
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) ∧
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b) ∧
      levelRate r s = Phi a b - Real.logb 2 c := by
  obtain ⟨a, b, hfeasible, hanti, hlimit⟩ :=
    exists_levelRate_minimizing_sequence
      (levelRateSet_nonempty_of_interior r hs hs')
  obtain ⟨j, c, A, B, φ, hφ, hc, hc', hAB,
      hlevels, hGamma, hPhi⟩ :=
    fixedLevelForwardCompactifiedResidualLimit r a b
      (fun n => (hfeasible n).1)
      (fun n => levelRate_minimizing_sequence_bddAbove hanti n)
  have hclosed : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) :=
    compactified_certificate_residual_threshold_le
      hφ (tendsto_const_nhds (x := s))
      (fun n => (hfeasible n).2) hGamma
  have hmin : levelRate r s = Phi A B - Real.logb 2 c :=
    tendsto_nhds_unique (hlimit.comp hφ.tendsto_atTop) hPhi
  exact ⟨j, c, A, B, hc, hc', hAB, hlevels, hclosed, hmin⟩

theorem exists_compactified_positive_levelRate_minimizer
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ (j : ℕ) (c : ℝ)
      (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ),
      j ≤ r ∧ 0 < c ∧ c ≤ 1 ∧ (c < 1 → j < r) ∧
      Interlacing a b ∧ 0 < a (Fin.last j) ∧
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b) ∧
      levelRate r s = Phi a b - Real.logb 2 c := by
  obtain ⟨j, c, a, b, hc, hc', h, hlevels, hfeasible, hmin⟩ :=
    exists_compactified_levelRate_minimizer hs hs'
  have hj : j ≤ r := by
    rcases hlevels with ⟨_, hj⟩ | ⟨_, hj⟩ <;> omega
  have hdrop : c < 1 → j < r := by
    intro hclt
    rcases hlevels with ⟨hcone, _⟩ | ⟨_, hj⟩
    · linarith
    · omega
  have hlast : 0 < a (Fin.last j) := by
    by_contra hnot
    have hzero : a (Fin.last j) = 0 :=
      le_antisymm (le_of_not_gt hnot) (h.ambient_nonneg (Fin.last j))
    cases j with
    | zero =>
        have ha : a 0 = 0 := by simpa only [Fin.isValue, Fin.last_zero] using hzero
        have hGamma : Gamma a b = 0 := by
          simp only [Gamma_zero, spectralAtom, Fin.isValue, ha, add_zero,
            mul_one, Real.sqrt_zero, mul_zero, div_one]
        have hPhi : Phi a b = 0 := by
          simp only [Phi_zero, Fin.isValue, ha, sphericalEntropy_zero]
        have hscaled : s ≤ 1 - c ^ 2 := by
          rw [hGamma] at hfeasible
          nlinarith
        have hclassical :=
          classicalThreshold_entropy_lt_neg_logb_of_compactified_zero
            hs hs' hc hscaled
        have hupper : levelRate r s ≤
            MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
          calc
            levelRate r s ≤ levelRate 0 s :=
              levelRate_le_levelRate_zero hs hs'
            _ = MetricCodes.sphericalEntropy
                  (MetricCodes.classicalThreshold s) :=
              levelRate_zero_eq_classical hs.le hs'
        rw [hPhi] at hmin
        linarith
    | succ j =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos j) h hzero
        have hstrict :
            s < 1 - c ^ 2 * (1 - 2 * Gamma A b) := by
          nlinarith [sq_pos_of_pos hc]
        have hupper := levelRate_le_compactified_datum
          hs hs' hc A b hA hstrict hlevels
        linarith
  exact ⟨j, c, a, b, hj, hc, hc', hdrop, h,
    hlast, hfeasible, hmin⟩

theorem levelRate_succ_lt
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    levelRate (r + 1) s < levelRate r s := by
  obtain ⟨j, c, a, b, hj, hc, hc', hdrop, h,
      hlast, hfeasible, hmin⟩ :=
    exists_compactified_positive_levelRate_minimizer (r := r) hs hs'
  exact levelRate_succ_lt_of_compactified_positive_minimizer
    hj hc hc' hdrop h hlast hfeasible hmin
    (fun A B hAB hstrict hlevels =>
      levelRate_le_compactified_datum hs hs' hc A B hAB hstrict hlevels)

private def oneRowBoundaryObjective (s a : ℝ) : ℝ :=
  MetricCodes.sphericalEntropy a -
    MetricCodes.sphericalEntropy (MetricCodes.Spherical.boundaryDegree s a)

theorem oneRowBoundaryObjective_continuous (s : ℝ) :
    Continuous (fun a : ℝ => oneRowBoundaryObjective s a) := by
  have hquadratic :
      Continuous (fun a : ℝ =>
        MetricCodes.Spherical.boundaryQuadratic s a) := by
    unfold MetricCodes.Spherical.boundaryQuadratic
    fun_prop
  have hdegree :
      Continuous (fun a : ℝ => MetricCodes.Spherical.boundaryDegree s a) := by
    unfold MetricCodes.Spherical.boundaryDegree
    fun_prop
  exact MetricCodes.Spherical.sphericalEntropy_continuous.sub
    (MetricCodes.Spherical.sphericalEntropy_continuous.comp hdegree)

theorem boundaryQuadratic_classicalThreshold_eq_zero
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.Spherical.boundaryQuadratic s
      (MetricCodes.classicalThreshold s) = 0 := by
  let a : ℝ := MetricCodes.classicalThreshold s
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have hden : 0 < 1 + 2 * a := by positivity
  have hroot_sq := Real.sq_sqrt
    (show 0 ≤ a * (1 + a) by positivity)
  have hspectral := MetricCodes.Spherical.classicalThreshold_spectral hs hs'
  change 2 * MetricCodes.Gamma a 0 = s at hspectral
  rw [MetricCodes.Spherical.Gamma_zero ha,
    ← mul_div_assoc, div_eq_iff hden.ne'] at hspectral
  have hmult := congrArg
    (fun x : ℝ => x * Real.sqrt (a * (1 + a))) hspectral
  change MetricCodes.Spherical.boundaryQuadratic s a = 0
  unfold MetricCodes.Spherical.boundaryQuadratic
  nlinarith

theorem boundaryDegree_classicalThreshold_eq_zero
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.Spherical.boundaryDegree s
      (MetricCodes.classicalThreshold s) = 0 := by
  unfold MetricCodes.Spherical.boundaryDegree
  rw [boundaryQuadratic_classicalThreshold_eq_zero hs hs']
  norm_num

theorem oneRowBoundaryObjective_classicalThreshold
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    oneRowBoundaryObjective s (MetricCodes.classicalThreshold s) =
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  simp only [oneRowBoundaryObjective, boundaryDegree_classicalThreshold_eq_zero hs hs',
    sphericalEntropy_zero, sub_zero]

theorem boundaryDegree_spectral_eq
    {s a : ℝ} (ha : 0 < a)
    (hquadratic : 0 ≤ MetricCodes.Spherical.boundaryQuadratic s a) :
    2 * MetricCodes.Gamma a
      (MetricCodes.Spherical.boundaryDegree s a) = s := by
  have hden : 0 <
      (1 + 2 * a) * Real.sqrt (a * (1 + a)) := by positivity
  have hroot := MetricCodes.Spherical.boundaryDegree_mul_one_add hquadratic
  rw [MetricCodes.Gamma_eq_sub, ← mul_div_assoc,
    div_eq_iff hden.ne']
  unfold MetricCodes.Spherical.boundaryQuadratic at hroot
  nlinarith

theorem exists_variationalRate_boundary_minimizer_of_limit
    {s L : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlimit : Tendsto (fun a : ℝ => oneRowBoundaryObjective s a)
      atTop (𝓝 L))
    (hendpoint :
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) < L) :
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
  obtain ⟨u, b, hfeasible, himprove⟩ :=
    MetricCodes.Spherical.exists_strict_improving_spherical_feasible hs hs'
  have hdomain :=
    (MetricCodes.Spherical.feasible_iff_boundary hs hs').mp hfeasible
  have hu : 0 < u := hfeasible.1.trans hfeasible.2.1
  have hquadratic :=
    (MetricCodes.Spherical.boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' hu).mpr hdomain.1
  have hboundary :
      MetricCodes.sphericalEntropy b ≤
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree s u) :=
    MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      hdomain.2.1.le
      (MetricCodes.Spherical.boundaryDegree_pos hquadratic).le
      hdomain.2.2.le
  have hgood :
      oneRowBoundaryObjective s u <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    unfold oneRowBoundaryObjective
    linarith
  have hgood_limit : oneRowBoundaryObjective s u < L :=
    hgood.trans hendpoint
  obtain ⟨A, hA⟩ :=
    (eventually_atTop.1 (hlimit.eventually (lt_mem_nhds hgood_limit)))
  let T : ℝ := max A u
  have hT : MetricCodes.classicalThreshold s ≤ T :=
    hdomain.1.le.trans (le_max_right A u)
  obtain ⟨a, ha, hmin⟩ :=
    isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr hT)
      (oneRowBoundaryObjective_continuous s).continuousOn
  have hau :
      oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s u :=
    hmin ⟨hdomain.1.le, le_max_right A u⟩
  have haclassical :
      oneRowBoundaryObjective s a <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) :=
    hau.trans_lt hgood
  have hastrict : MetricCodes.classicalThreshold s < a := by
    by_contra hnot
    have heq : a = MetricCodes.classicalThreshold s :=
      le_antisymm (le_of_not_gt hnot) ha.1
    rw [heq, oneRowBoundaryObjective_classicalThreshold hs hs'] at haclassical
    exact (lt_irrefl _) haclassical
  have hglobal : ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
      oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
    intro t ht
    by_cases htT : t ≤ T
    · exact hmin ⟨ht.le, htT⟩
    · have htail : oneRowBoundaryObjective s u <
          oneRowBoundaryObjective s t :=
        hA t ((le_max_left A u).trans (le_of_not_ge htT))
      exact hau.trans htail.le
  refine ⟨a, hastrict, ?_, hglobal⟩
  rw [MetricCodes.Spherical.variationalRate_eq_boundaryVariationalRate hs hs']
  unfold MetricCodes.Spherical.boundaryVariationalRate
  apply le_antisymm
  · exact csInf_le (MetricCodes.Spherical.boundaryRateSet_bddBelow hs hs')
      ⟨a, hastrict, rfl⟩
  · refine le_csInf (s := MetricCodes.Spherical.boundaryRateSet s) ?_ ?_
    · exact ⟨oneRowBoundaryObjective s a, a, hastrict, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hglobal t ht

theorem exists_variationalRate_boundary_minimizer_of_boundary_limit
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlimit : Tendsto (fun a : ℝ => oneRowBoundaryObjective s a)
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s)))) :
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t :=
  exists_variationalRate_boundary_minimizer_of_limit hs hs' hlimit
    (classicalThreshold_entropy_lt_half_neg_logb hs hs')

theorem levelRate_one_lt_variationalRate_of_boundary_minimizer
    {s a : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hthreshold : MetricCodes.classicalThreshold s < a)
    (hmin : MetricCodes.Spherical.variationalRate s =
      oneRowBoundaryObjective s a) :
    levelRate 1 s < MetricCodes.Spherical.variationalRate s := by
  have ha : 0 < a :=
    (MetricCodes.classicalThreshold_pos hs hs').trans hthreshold
  have hquadratic :=
    (MetricCodes.Spherical.boundaryQuadratic_pos_iff_classicalThreshold_lt
      hs hs' ha).mpr hthreshold
  let b : ℝ := MetricCodes.Spherical.boundaryDegree s a
  have hb : 0 < b := MetricCodes.Spherical.boundaryDegree_pos hquadratic
  have hba : b < a :=
    MetricCodes.Spherical.boundaryDegree_lt_longitudinal hs ha hquadratic
  have hinterlacing :
      Interlacing (![a, 0]) (![b]) :=
    oneRowInterlacing_iff.mpr ⟨hb, hba⟩
  have hzero : ![a, 0] (Fin.last 1) = 0 := by
    simp only [Fin.reduceLast, Matrix.cons_val_one, Fin.isValue,
      Matrix.cons_val_fin_one]
  obtain ⟨A, _, hA, hgamma, hphi⟩ :=
    exists_sameLevel_opening_strict_refinement
      (by norm_num : 0 < (1 : ℕ)) hinterlacing hzero
  have heq : 2 * Gamma (![a, 0]) (![b]) = s := by
    rw [Gamma_oneRow ha]
    exact boundaryDegree_spectral_eq ha hquadratic.le
  have hspectral : s < 2 * Gamma A (![b]) := by
    linarith
  calc
    levelRate 1 s ≤ Phi A (![b]) :=
      levelRate_le hA hspectral
    _ < Phi (![a, 0]) (![b]) := hphi
    _ = oneRowBoundaryObjective s a := by
      rw [Phi_oneRow]
      rfl
    _ = MetricCodes.Spherical.variationalRate s := hmin.symm

theorem exists_variationalRate_boundary_minimizer
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
  apply exists_variationalRate_boundary_minimizer_of_boundary_limit hs hs'
  simpa only [oneRowBoundaryObjective, one_div, neg_mul] using
    (CompactificationEntropy.tendsto_entropy_sub_boundaryDegree hs')

theorem levelRate_one_lt_variationalRate
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    levelRate 1 s < MetricCodes.Spherical.variationalRate s := by
  obtain ⟨a, ha, hmin, _⟩ :=
    exists_variationalRate_boundary_minimizer hs hs'
  exact levelRate_one_lt_variationalRate_of_boundary_minimizer
    hs hs' ha hmin

end

section

theorem classicalHierarchyProfile_continuousOn_Icc
    {s : ℝ} (hs : s < 1) :
    ContinuousOn
      (fun t : ℝ => MetricCodes.sphericalEntropy
        (MetricCodes.classicalThreshold t))
      (Set.Icc (0 : ℝ) s) := by
  intro t ht
  exact
    (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.comp
      (MetricCodes.Spherical.classicalThreshold_continuousAt
        (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hs))).continuousWithinAt

theorem levelRate_zero_continuousOn_Icc
    {s : ℝ} (hs : s < 1) :
    ContinuousOn (levelRate 0) (Set.Icc (0 : ℝ) s) := by
  apply (classicalHierarchyProfile_continuousOn_Icc hs).congr
  intro t ht
  exact levelRate_zero_eq_classical ht.1
    (lt_of_le_of_lt ht.2 hs)

theorem levelRate_zero_lowerSemicontinuousOn_Icc
    {s : ℝ} (hs : s < 1) :
    LowerSemicontinuousOn (levelRate 0) (Set.Icc (0 : ℝ) s) :=
  (levelRate_zero_continuousOn_Icc hs).lowerSemicontinuousOn

theorem exists_positive_localized_classical_minimizer
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate 0) s =
        levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t :=
  exists_positive_localized_levelRate_minimizer_of_lsc hs hs'
    (levelRate_zero_lowerSemicontinuousOn_Icc hs')

theorem localizedEnvelope_lt_of_positive_minimizer
    {κ κ' : ℝ → ℝ} {s : ℝ}
    (hs' : s < 1)
    (hκ' : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ' t)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s, κ' t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ' s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  obtain ⟨t, ht, hmin⟩ := hmin
  exact localizedEnvelope_lt_of_minimizer hs'
    ⟨ht.1.le, ht.2⟩ hκ' hmin (hstrict t ht)

theorem localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s))
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      levelRate (r + 1) t < levelRate r t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate (r + 1)) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  exact localizedEnvelope_lt_of_positive_minimizer hs'
    (levelRate_nonnegOn_Icc (r + 1) s)
    (exists_positive_localized_levelRate_minimizer_of_lsc hs hs' hlsc)
    hstrict

theorem localizedEnvelope_levelRate_lt_profile_of_positive_minimizer
    {r : ℕ} {κ : ℝ → ℝ} {s : ℝ}
    (hs' : s < 1)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s, levelRate r t < κ t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s := by
  exact localizedEnvelope_lt_of_positive_minimizer hs'
    (levelRate_nonnegOn_Icc r s) hmin hstrict

end

section

open Filter Topology
open scoped Topology

theorem rowVariationalRate_nonneg_all (s : ℝ) :
    0 ≤ MetricCodes.Spherical.variationalRate s := by
  by_cases hnonempty : (MetricCodes.Spherical.rateSet s).Nonempty
  · unfold MetricCodes.Spherical.variationalRate
    apply le_csInf hnonempty
    rintro _ ⟨a, b, hfeasible, rfl⟩
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      hfeasible.1.le hfeasible.2.1.le
  · have hempty : MetricCodes.Spherical.rateSet s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [variationalRate, hempty, Real.sInf_empty, Std.le_refl]

theorem rowVariationalRate_zero :
    MetricCodes.Spherical.variationalRate 0 = 0 := by
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mono_left (nhdsWithin_le_nhds
        (s := Set.Ioi (0 : ℝ)))
  have hentropy : Tendsto
      (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [sphericalEntropy, Function.comp_def, add_zero, Real.logb_one, mul_zero,
      Real.logb_zero,
      sub_self] using (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt (x := (0 :
        ℝ))).tendsto.comp hsquare
  apply le_antisymm (ge_of_tendsto hentropy ?_)
    (rowVariationalRate_nonneg_all 0)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  let a : ℝ := t ^ 2
  let b : ℝ := a / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b]; linarith
  have hgamma : 0 < MetricCodes.Gamma a b :=
    MetricCodes.Gamma_pos hb.le hba
  have hfeasible : MetricCodes.Spherical.Feasible 0 a b :=
    ⟨hb, hba, by linarith⟩
  have hbound := MetricCodes.Spherical.variationalRate_le_of_feasible hfeasible
  have hbentropy := MetricCodes.sphericalEntropy_pos hb
  dsimp [a] at hbound ⊢
  linarith

theorem eventually_rowVariationalRate_le_squared_entropy :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      MetricCodes.Spherical.variationalRate t ≤
        MetricCodes.sphericalEntropy (t ^ 2) := by
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hupper,
    eventually_levelRate_zero_le_squared_entropy]
    with t (ht : 0 < t) ht' hzero
  calc
    MetricCodes.Spherical.variationalRate t ≤ levelRate 0 t := by
      rw [levelRate_zero_eq_classical ht.le ht']
      exact (MetricCodes.Spherical.variationalRate_lt_classical ht ht').le
    _ ≤ MetricCodes.sphericalEntropy (t ^ 2) := hzero

theorem exists_positive_localized_row_minimizer_of_lowerSemicontinuous
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn
      MetricCodes.Spherical.variationalRate (Set.Icc (0 : ℝ) s)) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          MetricCodes.Spherical.variationalRate s =
        MetricCodes.Spherical.variationalRate t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  exact exists_positive_localized_minimizer_of_lsc_and_smallEntropy
    hs hs' (fun t _ => rowVariationalRate_nonneg_all t)
    rowVariationalRate_zero
    eventually_rowVariationalRate_le_squared_entropy hlsc

theorem localized_level_one_lt_row_of_lowerSemicontinuous
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn
      MetricCodes.Spherical.variationalRate (Set.Icc (0 : ℝ) s)) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 1) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s := by
  apply localizedEnvelope_levelRate_lt_profile_of_positive_minimizer hs'
    (exists_positive_localized_row_minimizer_of_lowerSemicontinuous
      hs hs' hlsc)
  intro t ht
  exact levelRate_one_lt_variationalRate
    ht.1 (lt_of_le_of_lt ht.2 hs')

theorem localized_row_lt_level_zero_of_positive_minimizer
    {s : ℝ} (hs' : s < 1)
    (hmin : ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate 0) s =
        levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 0) s := by
  apply localizedEnvelope_lt_of_positive_minimizer hs'
    (fun t _ => rowVariationalRate_nonneg_all t) hmin
  intro t ht
  rw [levelRate_zero_eq_classical ht.1.le
    (lt_of_le_of_lt ht.2 hs')]
  exact MetricCodes.Spherical.variationalRate_lt_classical
    ht.1 (lt_of_le_of_lt ht.2 hs')

theorem localized_row_lt_level_zero
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        MetricCodes.Spherical.variationalRate s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate 0) s :=
  localized_row_lt_level_zero_of_positive_minimizer hs'
    (exists_positive_localized_classical_minimizer hs hs')

namespace CompactificationEntropy

theorem tendsto_boundaryDegree_div_of_tendsto
    {u a : ℕ → ℝ} {s : ℝ}
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto
      (fun n => MetricCodes.Spherical.boundaryDegree (u n) (a n) / a n)
      atTop (𝓝 (Real.sqrt (1 - s))) := by
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ha
  have hcontinuous : Continuous (fun p : ℝ × ℝ =>
      normalizedBoundaryDegree p.1 p.2) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    fun_prop
  have hzero : normalizedBoundaryDegree s 0 = Real.sqrt (1 - s) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    have hfactor : (0 : ℝ) ^ 2 +
        4 * (1 + 0 - (s / 2) * (0 + 2) * Real.sqrt (1 + 0)) =
          4 * (1 - s) := by
      norm_num
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hlimit := hcontinuous.continuousAt.tendsto.comp (hu.prodMk_nhds hinv)
  change Tendsto (fun n => normalizedBoundaryDegree (u n) (a n)⁻¹)
    atTop (𝓝 (normalizedBoundaryDegree s 0)) at hlimit
  rw [hzero] at hlimit
  apply hlimit.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  exact (boundaryDegree_div_eq_normalized hn).symm

theorem tendsto_boundaryDegree_atTop_of_tendsto
    {u a : ℕ → ℝ} {s : ℝ} (hs : s < 1)
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => MetricCodes.Spherical.boundaryDegree (u n) (a n))
      atTop atTop := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have hratio := tendsto_boundaryDegree_div_of_tendsto hu ha
  have hproduct := ha.atTop_mul_pos hroot hratio
  apply hproduct.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  field_simp

theorem tendsto_sphericalEntropy_sub_of_sequential_ratio
    {a b : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : Tendsto a atTop atTop)
    (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b n / a n) atTop (𝓝 c)) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (a n) -
        MetricCodes.sphericalEntropy (b n))
      atTop (𝓝 (-Real.logb 2 c)) := by
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ha
  have hnormalized : Tendsto
      (fun n => ((a n)⁻¹ + b n / a n) / ((a n)⁻¹ + 1))
      atTop (𝓝 c) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  have hshifted : Tendsto
      (fun n => (1 + b n) / (1 + a n)) atTop (𝓝 c) := by
    apply hnormalized.congr'
    filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn
    field_simp
  have hlog : Tendsto
      (fun n => Real.logb 2 ((1 + b n) / (1 + a n)))
      atTop (𝓝 (Real.logb 2 c)) :=
    (Real.continuousAt_logb hc.ne').tendsto.comp hshifted
  have hfirst := tendsto_sphericalEntropy_sub_logb_one_add.comp ha
  have hsecond := tendsto_sphericalEntropy_sub_logb_one_add.comp hb
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 c =
        -Real.logb 2 c := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ)),
    hb.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hbn
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring

theorem tendsto_entropy_sub_boundaryDegree_of_tendsto
    {u a : ℕ → ℝ} {s : ℝ} (_hs : 0 < s) (hs' : s < 1)
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (a n) -
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree (u n) (a n)))
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s))) := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs')
  have hratio := tendsto_boundaryDegree_div_of_tendsto hu ha
  have hboundary := tendsto_boundaryDegree_atTop_of_tendsto hs' hu ha
  have hlimit := tendsto_sphericalEntropy_sub_of_sequential_ratio
    hroot ha hboundary hratio
  have hconstant :
      -Real.logb 2 (Real.sqrt (1 - s)) =
        -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
    unfold Real.logb
    rw [Real.log_sqrt (sub_pos.mpr hs').le]
    ring
  rwa [hconstant] at hlimit

end CompactificationEntropy

end

section

open Set Filter Topology
open scoped Topology

private theorem rowProfile_nonneg_metriccodes2_a5c70490 (s : ℝ) :
    0 ≤ MetricCodes.Spherical.variationalRate s := by
  by_cases hnonempty : (MetricCodes.Spherical.rateSet s).Nonempty
  · unfold MetricCodes.Spherical.variationalRate
    apply le_csInf hnonempty
    rintro _ ⟨a, b, hfeasible, rfl⟩
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      hfeasible.1.le hfeasible.2.1.le
  · have hempty : MetricCodes.Spherical.rateSet s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [variationalRate, hempty, Real.sInf_empty, Std.le_refl]

private theorem rowProfile_zero_metriccodes2_a5c70490 :
    MetricCodes.Spherical.variationalRate 0 = 0 := by
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mono_left (nhdsWithin_le_nhds
        (s := Set.Ioi (0 : ℝ)))
  have hentropy : Tendsto
      (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [sphericalEntropy, Function.comp_def, add_zero, Real.logb_one, mul_zero,
      Real.logb_zero,
      sub_self] using (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt (x := (0 :
        ℝ))).tendsto.comp hsquare
  apply le_antisymm (ge_of_tendsto hentropy ?_)
    (rowProfile_nonneg_metriccodes2_a5c70490 0)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  let a : ℝ := t ^ 2
  let b : ℝ := a / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b]; linarith
  have hgamma : 0 < MetricCodes.Gamma a b :=
    MetricCodes.Gamma_pos hb.le hba
  have hfeasible : MetricCodes.Spherical.Feasible 0 a b :=
    ⟨hb, hba, by linarith⟩
  have hbound := MetricCodes.Spherical.variationalRate_le_of_feasible hfeasible
  have hbentropy := MetricCodes.sphericalEntropy_pos hb
  dsimp [a] at hbound ⊢
  linarith

theorem oneRowBoundaryObjective_joint_continuous :
    Continuous (fun p : ℝ × ℝ => oneRowBoundaryObjective p.1 p.2) := by
  have hdegree : Continuous
      (fun p : ℝ × ℝ => MetricCodes.Spherical.boundaryDegree p.1 p.2) := by
    unfold MetricCodes.Spherical.boundaryDegree
      MetricCodes.Spherical.boundaryQuadratic
    fun_prop
  exact (MetricCodes.Spherical.sphericalEntropy_continuous.comp
    continuous_snd).sub
      (MetricCodes.Spherical.sphericalEntropy_continuous.comp hdegree)

theorem variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hescape : ∀ {u a : ℕ → ℝ} {t : ℝ}, 0 < t → t < 1 →
      Tendsto u atTop (nhds t) → Tendsto a atTop atTop →
      Tendsto (fun n => oneRowBoundaryObjective (u n) (a n))
        atTop (nhds (-(1 / 2 : ℝ) * Real.logb 2 (1 - t)))) :
    LowerSemicontinuousOn MetricCodes.Spherical.variationalRate
      (Set.Icc (0 : ℝ) s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro R
  let V : Set ℝ := Set.Icc (0 : ℝ) s ∩
    (MetricCodes.Spherical.variationalRate) ⁻¹' Set.Iic R
  refine ⟨V, ?_, ?_⟩
  · apply IsSeqClosed.isClosed
    intro u x hu hux
    have hx : x ∈ Set.Icc (0 : ℝ) s :=
      isClosed_Icc.mem_of_tendsto hux
        (Filter.Eventually.of_forall fun n => (hu n).1)
    refine ⟨hx, ?_⟩
    change MetricCodes.Spherical.variationalRate x ≤ R
    by_cases hxzero : x = 0
    · rw [hxzero, rowProfile_zero_metriccodes2_a5c70490]
      exact (rowProfile_nonneg_metriccodes2_a5c70490 (u 0)).trans ((hu 0).2)
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
      have hxone : x < 1 := hx.2.trans_lt hs'
      have hevent : ∀ᶠ n : ℕ in atTop, 0 < u n ∧ u n < 1 :=
        (hux.eventually (Ioi_mem_nhds hxpos)).and
          (hux.eventually (Iio_mem_nhds hxone))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
      let v : ℕ → ℝ := fun n => u (n + N)
      have hvlim : Tendsto v atTop (nhds x) :=
        hux.comp (tendsto_add_atTop_nat N)
      have hvpos : ∀ n, 0 < v n :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).1
      have hvone : ∀ n, v n < 1 :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).2
      have hvrate : ∀ n, MetricCodes.Spherical.variationalRate (v n) ≤ R :=
        fun n => (hu (n + N)).2
      have hdata : ∀ n : ℕ,
          ∃ a : ℝ, MetricCodes.classicalThreshold (v n) < a ∧
            MetricCodes.Spherical.variationalRate (v n) =
              oneRowBoundaryObjective (v n) a := by
        intro n
        obtain ⟨a, ha, heq, _⟩ :=
          exists_variationalRate_boundary_minimizer (hvpos n) (hvone n)
        exact ⟨a, ha, heq⟩
      choose a hthreshold heq using hdata
      have ha : ∀ n, 0 < a n :=
        fun n => (MetricCodes.classicalThreshold_pos
          (hvpos n) (hvone n)).trans (hthreshold n)
      let z : ℕ → ℝ := fun n => compactifiedHierarchyCoordinate (a n)
      have hz : ∀ n, z n ∈ Set.Icc (0 : ℝ) 1 :=
        fun n => compactifiedHierarchyCoordinate_mem_Icc (ha n).le
      obtain ⟨q, hq, φ, hφ, hlim⟩ :=
        isCompact_Icc.tendsto_subseq hz
      have hvsub : Tendsto (fun n => v (φ n)) atTop (nhds x) :=
        hvlim.comp hφ.tendsto_atTop
      have hobjbound : ∀ n,
          oneRowBoundaryObjective (v (φ n)) (a (φ n)) ≤ R := by
        intro n
        rw [← heq (φ n)]
        exact hvrate (φ n)
      by_cases hqzero : q = 0
      · have hcompact : Tendsto
            (fun n => compactifiedHierarchyCoordinate (a (φ n)))
              atTop (nhds 0) := by
          simpa only [Function.comp_def, hqzero] using hlim
        have hatop : Tendsto (fun n => a (φ n)) atTop atTop :=
          tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
            (fun n => (ha (φ n)).le) hcompact
        have hlimit := hescape hxpos hxone hvsub hatop
        have hendpoint : -(1 / 2 : ℝ) * Real.logb 2 (1 - x) ≤ R :=
          le_of_tendsto hlimit (Filter.Eventually.of_forall hobjbound)
        have hstrict :=
          (MetricCodes.Spherical.variationalRate_lt_classical hxpos hxone).trans
            (classicalThreshold_entropy_lt_half_neg_logb hxpos hxone)
        exact hstrict.le.trans hendpoint
      · have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hqzero)
        let A : ℝ := q⁻¹ - 1
        have halim : Tendsto (fun n => a (φ n)) atTop (nhds A) := by
          apply tendsto_of_compactifiedHierarchyCoordinate_pos hqpos
          simpa only [Function.comp_def] using hlim
        have hthresholdlim : Tendsto
            (fun n => MetricCodes.classicalThreshold (v (φ n)))
              atTop (nhds (MetricCodes.classicalThreshold x)) :=
          (MetricCodes.Spherical.classicalThreshold_continuousAt
            (by linarith : -1 < x) hxone).tendsto.comp hvsub
        have hdiff := hthresholdlim.sub halim
        have hle : MetricCodes.classicalThreshold x ≤ A := by
          have hnonpos : MetricCodes.classicalThreshold x - A ≤ 0 :=
            le_of_tendsto hdiff (Filter.Eventually.of_forall
              (fun n => (sub_nonpos.mpr (hthreshold (φ n)).le)))
          linarith
        have hpair : Tendsto
            (fun n => (v (φ n), a (φ n))) atTop (nhds (x, A)) :=
          hvsub.prodMk_nhds halim
        have hobjective : Tendsto
            (fun n => oneRowBoundaryObjective (v (φ n)) (a (φ n)))
              atTop (nhds (oneRowBoundaryObjective x A)) := by
          simpa only [Function.comp_def] using
            oneRowBoundaryObjective_joint_continuous.continuousAt.tendsto.comp hpair
        have hAR : oneRowBoundaryObjective x A ≤ R :=
          le_of_tendsto hobjective (Filter.Eventually.of_forall hobjbound)
        have hrow : MetricCodes.Spherical.variationalRate x ≤
            oneRowBoundaryObjective x A := by
          rcases hle.eq_or_lt with heqA | hltA
          · rw [← heqA, oneRowBoundaryObjective_classicalThreshold
              hxpos hxone]
            exact (MetricCodes.Spherical.variationalRate_lt_classical
              hxpos hxone).le
          · exact MetricCodes.Spherical.variationalRate_le_boundaryObjective
              hxpos hxone hltA
        exact hrow.trans hAR
  · ext x
    simp only [mem_inter_iff, mem_Icc, mem_preimage, mem_Iic, and_self_left, V]

theorem variationalRate_lowerSemicontinuousOn_Icc
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    LowerSemicontinuousOn MetricCodes.Spherical.variationalRate
      (Set.Icc (0 : ℝ) s) := by
  apply variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape hs hs'
  intro u a t ht ht' hu ha
  simpa only [oneRowBoundaryObjective, one_div, neg_mul] using
    (CompactificationEntropy.tendsto_entropy_sub_boundaryDegree_of_tendsto ht ht' hu ha)

end

section

open Filter Topology
open scoped BigOperators Topology

private def closedHierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s ≤ 2 * Gamma a b ∧ z = Phi a b}

/-- The closed hierarchy variational rate used in the spherical-code argument. -/
def closedHierarchyVariationalRate (s : ℝ) : ℝ :=
  sInf (closedHierarchyRateSet s)

/-- The spherical code rate used in the spherical-code argument. -/
def sphericalCodeRate (s : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ))
    Filter.atTop

theorem hierarchyRateSet_subset_closedHierarchyRateSet (s : ℝ) :
    hierarchyRateSet s ⊆ closedHierarchyRateSet s := by
  rintro z ⟨r, a, b, hinterlacing, hspectral, rfl⟩
  exact ⟨r, a, b, hinterlacing, hspectral.le, rfl⟩

theorem closedHierarchyRateSet_bddBelow (s : ℝ) :
    BddBelow (closedHierarchyRateSet s) := by
  refine ⟨0, ?_⟩
  rintro z ⟨r, a, b, hinterlacing, _, rfl⟩
  exact hinterlacing.Phi_nonneg

theorem closedHierarchyRateSet_nonempty_of_interior
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (closedHierarchyRateSet s).Nonempty :=
  (hierarchyRateSet_nonempty_of_interior hs hs').mono
    (hierarchyRateSet_subset_closedHierarchyRateSet s)

theorem exists_strict_hierarchy_refinement_of_closed
    {r : ℕ} {s : ℝ} (hs : 0 < s)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s ≤ 2 * Gamma a b) :
    ∃ (r' : ℕ) (A : Fin (r' + 1) → ℝ) (B : Fin r' → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < Phi a b := by
  by_cases hlast : 0 < a (Fin.last r)
  · obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
      exists_nextLevel_strict_refinement hinterlacing hlast
    exact ⟨r + 1, A, B, hAB, by linarith, hPhi⟩
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast) hinterlacing.1
    cases r with
    | zero =>
        have ha0 : a 0 = 0 := by simpa only [Fin.isValue, Fin.last_zero] using hzero
        have hgamma : Gamma a b = 0 := by
          rw [Gamma_zero, ha0]
          norm_num [spectralAtom]
        rw [hgamma] at hspectral
        norm_num at hspectral
        linarith
    | succ r =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos r) hinterlacing hzero
        exact ⟨r + 1, A, b, hA, by linarith, hPhi⟩

theorem closedHierarchyVariationalRate_eq_hierarchyVariationalRate
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    closedHierarchyVariationalRate s = hierarchyVariationalRate s := by
  apply le_antisymm
  · exact csInf_le_csInf (closedHierarchyRateSet_bddBelow s)
      (hierarchyRateSet_nonempty_of_interior hs hs')
      (hierarchyRateSet_subset_closedHierarchyRateSet s)
  · unfold closedHierarchyVariationalRate
    apply le_csInf (closedHierarchyRateSet_nonempty_of_interior hs hs')
    rintro z ⟨r, a, b, hinterlacing, hspectral, rfl⟩
    obtain ⟨r', A, B, hAB, hGamma, hPhi⟩ :=
      exists_strict_hierarchy_refinement_of_closed
        hs a b hinterlacing hspectral
    exact (hierarchyVariationalRate_le_of_feasible hAB hGamma).trans hPhi.le

theorem sphericalCodeLogRate_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ) := by
  apply div_nonneg _ (Nat.cast_nonneg n)
  cases hcard : (SpherePacking.sphericalCodeNumber n s).toNat with
  | zero => simp only [CharP.cast_eq_zero, Real.logb_zero, Std.le_refl]
  | succ k =>
      apply Real.logb_nonneg (by norm_num)
      exact_mod_cast Nat.succ_pos k

theorem sphericalCodeRate_le_of_eventually_exponential
    {s R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
        (2 : ℝ) ^ (R * (n : ℝ))) :
    sphericalCodeRate s ≤ R := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (sphericalCodeLogRate_nonneg s))
  have hpoint : ∀ᶠ n : ℕ in atTop, w n ≤ R := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    by_cases hzero : (SpherePacking.sphericalCodeNumber n s).toNat = 0
    · simpa [w, hzero] using hR
    · have hcard :
          0 < ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hlog :
          Real.logb 2
            ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
              R * (n : ℝ) :=
        (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hcard).2 hn
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      exact (div_le_iff₀ hnreal).2 hlog.le
  have hconstant : Tendsto (fun _ : ℕ => R) atTop (nhds R) :=
    tendsto_const_nhds
  have hcomparison :
      Filter.limsup w atTop ≤ Filter.limsup (fun _ : ℕ => R) atTop :=
    Filter.limsup_le_limsup hpoint hlower.isCoboundedUnder_le
      hconstant.isBoundedUnder_le
  exact hcomparison.trans_eq hconstant.limsup_eq

/-- The fixed level hierarchy code bound used in the spherical-code argument. -/
def FixedLevelHierarchyCodeBound : Prop :=
  ∀ {r : ℕ} {s R : ℝ},
    0 < s → s < 1 →
    ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))

theorem eventually_sphericalCodeNumber_lt_hierarchyVariationalRate_of_code_bound
    (hcode : FixedLevelHierarchyCodeBound)
    {s ε : ℝ} (hs : 0 < s) (hs' : s < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
        (2 : ℝ) ^ ((hierarchyVariationalRate s + ε) * (n : ℝ)) := by
  have hnonempty := hierarchyRateSet_nonempty_of_interior hs hs'
  have hlt :
      sInf (hierarchyRateSet s) < hierarchyVariationalRate s + ε := by
    change hierarchyVariationalRate s < hierarchyVariationalRate s + ε
    linarith
  obtain ⟨z, ⟨r, a, b, hinterlacing, hspectral, rfl⟩, hrate⟩ :=
    exists_lt_of_csInf_lt hnonempty hlt
  filter_upwards [hcode hs hs' a b hinterlacing hspectral hrate]
    with n hn
  exact
    (MetricCodes.Spherical.MaximalCodeBounds.sphericalCodeNumber_toNat_lt_iff
      hs').2 hn

theorem sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by
  rw [closedHierarchyVariationalRate_eq_hierarchyVariationalRate hs hs']
  apply le_of_forall_pos_le_add
  intro ε hε
  exact sphericalCodeRate_le_of_eventually_exponential
    (by linarith [hierarchyVariationalRate_nonneg hs hs'])
    (eventually_sphericalCodeNumber_lt_hierarchyVariationalRate_of_code_bound
      hcode hs hs' hε)

end

section


private def compactificationCapFactor (s t : ℝ) : ℝ :=
  Real.sqrt ((1 - s) / (1 - t))

theorem compactificationCapFactor_pos
    {s t : ℝ} (hs : s < 1) (hts : t ≤ s) :
    0 < compactificationCapFactor s t := by
  unfold compactificationCapFactor
  apply Real.sqrt_pos.mpr
  exact div_pos (sub_pos.mpr hs)
    (sub_pos.mpr (lt_of_le_of_lt hts hs))

theorem compactificationCapFactor_sq
    {s t : ℝ} (hs : s < 1) (hts : t ≤ s) :
    compactificationCapFactor s t ^ 2 =
      (1 - s) / (1 - t) := by
  unfold compactificationCapFactor
  exact Real.sq_sqrt
    (div_nonneg (sub_nonneg.mpr hs.le)
      (sub_nonneg.mpr (le_trans hts hs.le)))

theorem compactificationCapFactor_lt_one
    {s t : ℝ} (hs : s < 1) (hts : t < s) :
    compactificationCapFactor s t < 1 := by
  have hden : 0 < 1 - t := by linarith
  have hratio : (1 - s) / (1 - t) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hsq := compactificationCapFactor_sq hs hts.le
  have hnonneg : 0 ≤ compactificationCapFactor s t :=
    (compactificationCapFactor_pos hs hts.le).le
  nlinarith

theorem neg_logb_compactificationCapFactor_eq_sliceCost
    {s t : ℝ} (hs : s < 1) (hts : t ≤ s) :
    -Real.logb 2 (compactificationCapFactor s t) =
      MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  have ht : t < 1 := lt_of_le_of_lt hts hs
  have hratio : 0 ≤ (1 - s) / (1 - t) := by
    exact div_nonneg (sub_nonneg.mpr hs.le) (sub_nonneg.mpr ht.le)
  unfold compactificationCapFactor
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost Real.logb
  rw [Real.log_sqrt hratio]
  rw [Real.log_div (by linarith : 1 - s ≠ 0)
    (by linarith : 1 - t ≠ 0),
    Real.log_div (by linarith : 1 - t ≠ 0)
      (by linarith : 1 - s ≠ 0)]
  ring

theorem compactificationCapFactor_scaled_spectral
    {r : ℕ} {s t : ℝ}
    (hs : s < 1) (hts : t ≤ s)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hgap : t < 2 * Gamma a b) :
    s < 1 - compactificationCapFactor s t ^ 2 *
      (1 - 2 * Gamma a b) := by
  have hden : 0 < 1 - t := by linarith
  rw [compactificationCapFactor_sq hs hts]
  have hrewrite :
      1 - (1 - s) / (1 - t) * (1 - 2 * Gamma a b) =
        (1 - t - (1 - s) * (1 - 2 * Gamma a b)) /
          (1 - t) := by
    field_simp [hden.ne']
  rw [hrewrite]
  apply (lt_div_iff₀ hden).2
  nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hgap)]

end

section


open Set Filter Topology
open scoped BigOperators Topology

theorem levelRateSet_nonempty_of_mem_source_interval
    {r : ℕ} {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1) (hts : t ≤ s) :
    (levelRateSet r t).Nonempty := by
  obtain ⟨R, a, b, h, hgap, hR⟩ :=
    levelRateSet_nonempty_of_interior r hs hs'
  exact ⟨R, a, b, h, lt_of_le_of_lt hts hgap, hR⟩

theorem hierarchyVariationalRate_le_levelRate
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤ levelRate r s := by
  unfold levelRate
  apply le_csInf (levelRateSet_nonempty_of_interior r hs hs')
  rintro _ ⟨a, b, h, hgap, rfl⟩
  exact hierarchyVariationalRate_le_of_feasible h hgap

theorem hierarchyVariationalRate_le_levelRate_add_sliceCost_of_transfer
    {r : ℕ} {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (hts : t ≤ s)
    (htransfer : ∀ {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ},
      Interlacing A B → t < 2 * Gamma A B →
        hierarchyVariationalRate s ≤
          Phi A B +
            MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    hierarchyVariationalRate s ≤
      levelRate r t +
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  have hnonempty : (levelRateSet r t).Nonempty :=
    levelRateSet_nonempty_of_mem_source_interval hs hs' hts
  have hlower :
      hierarchyVariationalRate s -
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t ≤
        levelRate r t := by
    unfold levelRate
    apply le_csInf hnonempty
    rintro _ ⟨A, B, hAB, hgap, rfl⟩
    linarith [htransfer hAB hgap]
  linarith

theorem hierarchyVariationalRate_le_localizedEnvelope_of_transfer
    {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (htransfer : ∀ {t : ℝ}, 0 ≤ t → t < s →
      ∀ {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ},
        Interlacing A B → t < 2 * Gamma A B →
          hierarchyVariationalRate s ≤
            Phi A B +
              MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    hierarchyVariationalRate s ≤
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  unfold MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_csInf
    (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs.le))
  rintro _ ⟨t, ⟨ht, hts⟩, rfl⟩
  rcases lt_or_eq_of_le hts with hlt | rfl
  · exact hierarchyVariationalRate_le_levelRate_add_sliceCost_of_transfer
      hs hs' hts (htransfer ht hlt)
  · simpa only [MetricCodes.Spherical.SidelnikovLocalization.sliceCost_self hs', add_zero] using
      (hierarchyVariationalRate_le_levelRate (r := r) hs hs')

end

section


private def GenuineCompactifiedHierarchyTransfer : Prop :=
  ∀ {r : ℕ} {s c : ℝ},
    0 < c → c < 1 →
    ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b →
        s < 1 - c ^ 2 * (1 - 2 * Gamma a b) →
          hierarchyVariationalRate s ≤ Phi a b - Real.logb 2 c

theorem hierarchyVariationalRate_le_localizedEnvelope_of_compactification
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  apply hierarchyVariationalRate_le_localizedEnvelope_of_transfer hs hs'
  intro t ht hts a b hab hgap
  have hfactor :
      0 < compactificationCapFactor s t :=
    compactificationCapFactor_pos hs' hts.le
  have hfactor' :
      compactificationCapFactor s t < 1 :=
    compactificationCapFactor_lt_one hs' hts
  have hscaled :
      s < 1 - compactificationCapFactor s t ^ 2 *
        (1 - 2 * Gamma a b) :=
    compactificationCapFactor_scaled_spectral hs' hts.le hgap
  calc
    hierarchyVariationalRate s ≤
        Phi a b - Real.logb 2 (compactificationCapFactor s t) :=
      hcompact hfactor hfactor' a b hab hscaled
    _ = Phi a b +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
      rw [← neg_logb_compactificationCapFactor_eq_sliceCost hs' hts.le]
      ring

theorem hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨r, rfl⟩
  exact hierarchyVariationalRate_le_localizedEnvelope_of_compactification
    hcompact hs hs'

theorem sphericalCodeRate_le_localizedHierarchyInf_of_compactification
    (hcode : FixedLevelHierarchyCodeBound)
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) := by
  calc
    sphericalCodeRate s ≤ closedHierarchyVariationalRate s :=
      sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
        hcode hs hs'
    _ = hierarchyVariationalRate s :=
      closedHierarchyVariationalRate_eq_hierarchyVariationalRate hs hs'
    _ ≤ sInf (Set.range fun r : ℕ =>
          MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
            (levelRate r) s) :=
      hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
        hcompact hs hs'

theorem genuineCompactifiedHierarchyTransfer :
    GenuineCompactifiedHierarchyTransfer := by
  intro r s c hc hc' a b h hscaled
  exact hierarchyVariationalRate_le_compactified_certificate_of_spectral_limit
    hc hc' a b h hscaled (tendsto_Gamma_prepend_scale h hc hc')

theorem sphericalCodeRate_le_localizedHierarchyInf
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) :=
  sphericalCodeRate_le_localizedHierarchyInf_of_compactification
    hcode genuineCompactifiedHierarchyTransfer hs hs'

end

section

/-- The localized level rate used in the spherical-code argument. -/
def localizedLevelRate (r : ℕ) (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (levelRate r) s

/-- The localized hierarchy rate used in the spherical-code argument. -/
def localizedHierarchyRate (s : ℝ) : ℝ :=
  sInf (Set.range fun r : ℕ => localizedLevelRate r s)

/-- The localized row rate used in the spherical-code argument. -/
def localizedRowRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    MetricCodes.Spherical.variationalRate s

/-- The classical localized rate used in the spherical-code argument. -/
def classicalLocalizedRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (fun t => MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t)) s

theorem localizedLevelRate_nonneg {r : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hs' : s < 1) :
    0 ≤ localizedLevelRate r s := by
  unfold localizedLevelRate
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_csInf (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs))
  rintro _ ⟨t, ht, rfl⟩
  exact add_nonneg (levelRate_nonneg_all r t)
    (MetricCodes.Spherical.SidelnikovLocalization.sliceCost_nonneg ht.2 hs')

theorem localizedHierarchyRate_le_level {r : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hs' : s < 1) :
    localizedHierarchyRate s ≤ localizedLevelRate r s := by
  unfold localizedHierarchyRate
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedLevelRate_nonneg hs hs'
  · exact ⟨r, rfl⟩

theorem localizedHierarchyRate_lt_level_one_of_level_two
    {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hstrict : localizedLevelRate 2 s < localizedLevelRate 1 s) :
    localizedHierarchyRate s < localizedLevelRate 1 s :=
  (localizedHierarchyRate_le_level (r := 2) hs hs').trans_lt hstrict

theorem sphericalCodeRate_le_localizedHierarchyRate_of_codeBound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤ localizedHierarchyRate s := by
  simpa only [localizedHierarchyRate, localizedLevelRate] using
    (sphericalCodeRate_le_localizedHierarchyInf hcode hs hs')

theorem localizedLevelRate_zero_eq_classicalLocalizedRate
    {s : ℝ} (_hs : 0 ≤ s) (hs' : s < 1) :
    localizedLevelRate 0 s = classicalLocalizedRate s := by
  unfold localizedLevelRate classicalLocalizedRate
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  congr 1
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    change
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t) +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t =
        levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t
    rw [levelRate_zero_eq_classical ht.1 (lt_of_le_of_lt ht.2 hs')]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    change
      levelRate 0 t +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t =
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t) +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t
    rw [levelRate_zero_eq_classical ht.1 (lt_of_le_of_lt ht.2 hs')]

theorem localizedLevelRate_one_lt_localizedRowRate
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    localizedLevelRate 1 s < localizedRowRate s := by
  unfold localizedLevelRate localizedRowRate
  exact localized_level_one_lt_row_of_lowerSemicontinuous hs hs'
    (variationalRate_lowerSemicontinuousOn_Icc hs hs')

theorem localizedRowRate_lt_localizedLevelRate_zero
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    localizedRowRate s < localizedLevelRate 0 s := by
  unfold localizedRowRate localizedLevelRate
  exact localized_row_lt_level_zero hs hs'

theorem strict_hierarchy_of_components
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlevel : ∀ r : ℕ, levelRate (r + 1) s < levelRate r s)
    (hlocalized : ∀ r : ℕ,
      localizedLevelRate (r + 1) s < localizedLevelRate r s)
    (hcode : sphericalCodeRate s ≤ localizedHierarchyRate s)
    (hrow : localizedLevelRate 1 s < localizedRowRate s)
    (hclassical : localizedRowRate s < localizedLevelRate 0 s) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  refine ⟨fun r => ⟨hlevel r, hlocalized r⟩,
    hcode, ?_, hrow, hclassical,
    localizedLevelRate_zero_eq_classicalLocalizedRate hs.le hs'⟩
  exact localizedHierarchyRate_lt_level_one_of_level_two hs.le hs'
    (hlocalized 1)

end

section


theorem localizedLevelRate_succ_lt_of_compactifiedCertificateClosure
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      levelRate (r + 1) t < levelRate r t)
    (hclosure : FixedLevelCompactifiedCertificateClosure r) :
    localizedLevelRate (r + 1) s < localizedLevelRate r s := by
  change
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate (r + 1)) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s
  exact localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous hs hs'
    (levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
      hs.le hs' hclosure)
    hstrict

theorem strict_hierarchy_of_codeBound_pointwiseStrict_and_compactifiedClosure
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hcode : FixedLevelHierarchyCodeBound)
    (hlevel : ∀ (r : ℕ) (t : ℝ), 0 < t → t ≤ s →
      levelRate (r + 1) t < levelRate r t)
    (hclosure : ∀ r : ℕ, FixedLevelCompactifiedCertificateClosure r) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  apply strict_hierarchy_of_components hs hs'
  · intro r
    exact hlevel r s hs le_rfl
  · intro r
    exact localizedLevelRate_succ_lt_of_compactifiedCertificateClosure
      hs hs' (fun t ht => hlevel r t ht.1 ht.2) (hclosure r)
  · exact sphericalCodeRate_le_localizedHierarchyRate_of_codeBound
      hcode hs hs'
  · exact localizedLevelRate_one_lt_localizedRowRate hs hs'
  · exact localizedRowRate_lt_localizedLevelRate_zero hs hs'

theorem strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
    (hcode : FixedLevelHierarchyCodeBound)
    (hlevel : ∀ (r : ℕ) {t : ℝ}, 0 < t → t < 1 →
      levelRate (r + 1) t < levelRate r t)
    (hclosure : ∀ r : ℕ, FixedLevelCompactifiedCertificateClosure r)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  apply strict_hierarchy_of_codeBound_pointwiseStrict_and_compactifiedClosure
    hs hs' hcode (hclosure := hclosure)
  intro r t ht hts
  exact hlevel r ht (lt_of_le_of_lt hts hs')

theorem strict_hierarchy_of_fixedLevelCodeBound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  exact strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
    hcode (fun r {t} ht ht' => levelRate_succ_lt (r := r) (s := t) ht ht')
    fixedLevelCompactifiedCertificateClosure hs hs'

end

section

open Filter Topology
open scoped Topology

theorem main_general_of_actualCodeBound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by
  constructor
  · intro r R a b hinter hspectral hR
    exact hcode hs hs' a b hinter hspectral hR
  · exact sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
      hcode hs hs'

theorem strict_hierarchy_of_actualCodeBound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s :=
  strict_hierarchy_of_fixedLevelCodeBound hcode hs hs'

end

end HigherHierarchy

end Spherical

end MetricCodes

end MetricCodesNoncomputable
