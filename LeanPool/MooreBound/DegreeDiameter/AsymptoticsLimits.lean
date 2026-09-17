/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.Asymptotics
import LeanPool.MooreBound.DegreeDiameter.MooreBound
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The asymptotic argument

This file derives Theorem 1.1 and Corollary 1.2 from
`AsymptoticHalvedWitnessHypothesis`.  Its only
number-theoretic input is `prime_between`, the prime-number-theorem consequence saying that a
prime lies in `(x,(1+ε)x)` for every sufficiently large `x`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Filter _root_.Set

namespace DegreeDiameter

noncomputable section

/-- Abstract form of the sole PNT consequence used in the analytic reduction. -/
def PrimeIntervalHypothesis : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + η) * x

/-- Taking a fixed positive integral root preserves divergence to infinity. -/
lemma tendsto_nthRoot_comp_atTop {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) : Tendsto (fun d ↦ Nat.nthRoot m (D d)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro a
  filter_upwards [hD.eventually_ge_atTop (a ^ m)] with d hd
  exact (Nat.le_nthRoot_iff hm.ne').2 hd

lemma tendsto_nat_sub_one_atTop : Tendsto (fun d : ℕ ↦ d - 1) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro a
  filter_upwards [eventually_ge_atTop (a + 1)] with d hd
  omega

/-- The quotient `r/(r+1)` tends to one when `r` is a fixed positive integral root of a
quantity tending to infinity. -/
lemma tendsto_nthRoot_div_add_one {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun d ↦ (Nat.nthRoot m (D d) : ℝ) /
      ((Nat.nthRoot m (D d) : ℝ) + 1)) atTop (nhds 1) := by
  have hrootNat := tendsto_nthRoot_comp_atTop hD hm
  have hrootReal : Tendsto (fun d ↦ (Nat.nthRoot m (D d) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrootNat
  have hadd : Tendsto (fun d ↦ (Nat.nthRoot m (D d) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hrootReal
  have hinv : Tendsto (fun d ↦ ((Nat.nthRoot m (D d) : ℝ) + 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hadd
  have hsub : Tendsto (fun d ↦ 1 - ((Nat.nthRoot m (D d) : ℝ) + 1)⁻¹)
      atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hinv
  simpa only [sub_zero] using hsub.congr' <| .of_forall fun d ↦ by
    have hne : (Nat.nthRoot m (D d) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- A positive multiplicative prime gap can be chosen so small that its fixed power loses less
than any prescribed amount. -/
lemma exists_pos_inv_one_add_pow_gt {M : ℕ} {y : ℝ} (hy : y < 1) :
    ∃ η : ℝ, 0 < η ∧ y < ((1 + η)⁻¹) ^ M := by
  have hlim : Tendsto (fun η : ℝ ↦ ((1 + η)⁻¹) ^ M) (nhds 0) (nhds 1) := by
    have hadd : Tendsto (fun η : ℝ ↦ 1 + η) (nhds 0) (nhds 1) := by
      have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (nhds 0) (nhds 1) :=
        tendsto_const_nhds
      simpa only [id_eq, add_zero] using hone.add tendsto_id
    simpa using (hadd.inv₀ one_ne_zero).pow M
  have hnear : {η : ℝ | y < ((1 + η)⁻¹) ^ M} ∈ nhds 0 :=
    hlim (Ioi_mem_nhds hy)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨δ / 2, half_pos hδ, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  linarith

/-- `prime_between` pulled back along a growing integral root.  The `+1` in the conclusion is
important: it is what makes the construction's degree cap fit under the ambient degree. -/
lemma eventually_prime_near_nthRoot (hprime : PrimeIntervalHypothesis)
    {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, ∃ p : ℕ, Nat.Prime p ∧
      (Nat.nthRoot m (D d) : ℝ) / (1 + η) < p ∧
      p + 1 ≤ Nat.nthRoot m (D d) := by
  have hrootNat := tendsto_nthRoot_comp_atTop hD hm
  have hrootReal : Tendsto (fun d ↦ (Nat.nthRoot m (D d) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrootNat
  have hx : Tendsto (fun d ↦ (Nat.nthRoot m (D d) : ℝ) / (1 + η))
      atTop atTop := hrootReal.atTop_div_const (by linarith)
  filter_upwards [hx.eventually (hprime hη)] with d hd
  obtain ⟨p, hp, hp_lower, hp_upper⟩ := hd
  refine ⟨p, hp, hp_lower, ?_⟩
  have hp_upper' : (p : ℝ) < Nat.nthRoot m (D d) := by
    calc
      (p : ℝ) < (1 + η) * ((Nat.nthRoot m (D d) : ℝ) / (1 + η)) := hp_upper
      _ = Nat.nthRoot m (D d) := by field_simp
  have hpNat : p < Nat.nthRoot m (D d) := by exact_mod_cast hp_upper'
  omega

/-- The real comparison used in both lower-bound arguments. -/
def rootComparison (D : ℕ → ℕ) (m t : ℕ) (η : ℝ) (d : ℕ) : ℝ :=
  ((Nat.nthRoot m (D d) : ℝ) /
    ((Nat.nthRoot m (D d) : ℝ) + 1) / (1 + η)) ^ (m * t)

lemma tendsto_rootComparison {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) (t : ℕ) {η : ℝ} (_hη : 0 < η) :
    Tendsto (rootComparison D m t η) atTop (nhds (((1 + η)⁻¹) ^ (m * t))) := by
  change Tendsto (fun d ↦ ((Nat.nthRoot m (D d) : ℝ) /
    ((Nat.nthRoot m (D d) : ℝ) + 1) / (1 + η)) ^ (m * t))
      atTop (nhds (((1 + η)⁻¹) ^ (m * t)))
  have hr := tendsto_nthRoot_div_add_one hD hm
  have hc : Tendsto (fun d ↦
      ((Nat.nthRoot m (D d) : ℝ) /
        ((Nat.nthRoot m (D d) : ℝ) + 1)) * (1 + η)⁻¹)
      atTop (nhds (1 * (1 + η)⁻¹)) := hr.mul tendsto_const_nhds
  simpa only [div_eq_mul_inv, one_mul] using hc.pow (m * t)

/-- The elementary comparison which turns a prime near an integral root into a lower bound for
an extremal ratio. -/
lemma rootComparison_lt_ratio {m t r p F d : ℕ} (hm : 0 < m) (ht : 0 < t)
    {η : ℝ} (hη : 0 < η)
    (hp : (r : ℝ) / (1 + η) < p)
    (hd : d ≤ (r + 1) ^ m) (hdpos : 0 < d)
    (hF : p ^ (m * t) ≤ F) :
    ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * t) <
      (F : ℝ) / (d : ℝ) ^ t := by
  have hM : m * t ≠ 0 := Nat.mul_ne_zero hm.ne' ht.ne'
  have hnum : ((r : ℝ) / (1 + η)) ^ (m * t) < (p : ℝ) ^ (m * t) := by
    exact pow_lt_pow_left₀ hp (by positivity) hM
  have hden : (0 : ℝ) < (d : ℝ) ^ t := by positivity
  have hupperden : (d : ℝ) ^ t ≤ (((r : ℝ) + 1) ^ m) ^ t := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hd
  have hid :
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * t) =
        ((r : ℝ) / (1 + η)) ^ (m * t) /
          (((r : ℝ) + 1) ^ m) ^ t := by
    have hpow : (((r : ℝ) + 1) ^ m) ^ t = ((r : ℝ) + 1) ^ (m * t) := by
      rw [← pow_mul]
    rw [hpow, div_pow, div_pow]
    ring
  rw [hid]
  calc
    ((r : ℝ) / (1 + η)) ^ (m * t) / (((r : ℝ) + 1) ^ m) ^ t <
        (p : ℝ) ^ (m * t) / (((r : ℝ) + 1) ^ m) ^ t :=
      (div_lt_div_iff_of_pos_right (by positivity)).2 hnum
    _ ≤ (p : ℝ) ^ (m * t) / (d : ℝ) ^ t :=
      div_le_div_of_nonneg_left (by positivity) hden hupperden
    _ ≤ (F : ℝ) / (d : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hF

/-- Every number below one is eventually below the vertex-extremum ratio. -/
lemma eventually_lt_orderRatio (hprime : PrimeIntervalHypothesis)
    (hw : AsymptoticHalvedWitnessHypothesis) {k : ℕ} (hk : 0 < k)
    {y : ℝ} (hy : y < 1) :
    ∀ᶠ d : ℕ in atTop, y < (nKD k d : ℝ) / (d : ℝ) ^ k := by
  let m := 2 * k
  have hm : 0 < m := Nat.mul_pos (by norm_num) hk
  obtain ⟨η, hη, hyη⟩ := exists_pos_inv_one_add_pow_gt (M := m * k) hy
  have hcomp := (tendsto_rootComparison tendsto_id hm k hη).eventually
    (Ioi_mem_nhds hyη)
  have hprimeRoot := eventually_prime_near_nthRoot hprime tendsto_id hm hη
  filter_upwards [hcomp, hprimeRoot] with d hdcomp hdprime
  obtain ⟨p, hp, hp_lower, hp_upper⟩ := hdprime
  let r := Nat.nthRoot m d
  have hcap : (p + 1) ^ m ≤ d :=
    (Nat.pow_le_pow_left hp_upper m).trans (Nat.pow_nthRoot_le (Or.inl hm.ne'))
  have hF : p ^ (m * k) ≤ nKD k d := by
    simpa [m, Nat.mul_assoc] using construction_order_lower (hw k p hk hp) hcap
  have hdupper : d ≤ (r + 1) ^ m := (Nat.lt_pow_nthRoot_add_one hm.ne' d).le
  have hdpos : 0 < d := by
    have hp1 : 0 < p + 1 := Nat.succ_pos p
    have hrpos : 0 < r := hp1.trans_le hp_upper
    exact (Nat.pow_pos hrpos).trans_le
      (Nat.pow_nthRoot_le (Or.inl hm.ne'))
  exact hdcomp.trans <| rootComparison_lt_ratio hm hk hη hp_lower hdupper hdpos hF

/-- Every number below one is eventually below the edge-extremum ratio. -/
lemma eventually_lt_edgeRatio (hprime : PrimeIntervalHypothesis)
    (hw : AsymptoticHalvedWitnessHypothesis) {k : ℕ} (hk : 0 < k)
    {y : ℝ} (hy : y < 1) :
    ∀ᶠ d : ℕ in atTop, y < (h (k + 1) d : ℝ) / (d : ℝ) ^ (k + 1) := by
  let m := 2 * k
  let t := k + 1
  have hm : 0 < m := Nat.mul_pos (by norm_num) hk
  have ht : 0 < t := Nat.succ_pos k
  obtain ⟨η, hη, hyη⟩ := exists_pos_inv_one_add_pow_gt (M := m * t) hy
  have hcomp := (tendsto_rootComparison tendsto_nat_sub_one_atTop hm t hη).eventually
    (Ioi_mem_nhds hyη)
  have hprimeRoot :=
    eventually_prime_near_nthRoot hprime tendsto_nat_sub_one_atTop hm hη
  filter_upwards [hcomp, hprimeRoot] with d hdcomp hdprime
  obtain ⟨p, hp, hp_lower, hp_upper⟩ := hdprime
  let r := Nat.nthRoot m (d - 1)
  have hcap0 : (p + 1) ^ m ≤ d - 1 :=
    (Nat.pow_le_pow_left hp_upper m).trans (Nat.pow_nthRoot_le (Or.inl hm.ne'))
  have hcapPos : 0 < (p + 1) ^ m := Nat.pow_pos (Nat.succ_pos p)
  have hcap : (p + 1) ^ m + 1 ≤ d := by omega
  have hF0 : p ^ (m * t) ≤ h (k + 1) d - 1 := by
    simpa [m, t, Nat.mul_assoc] using construction_edge_lower hk (hw k p hk hp) hcap
  have hF : p ^ (m * t) ≤ h (k + 1) d :=
    hF0.trans (Nat.sub_le _ _)
  have hrootUpper : d - 1 < (r + 1) ^ m := Nat.lt_pow_nthRoot_add_one hm.ne' (d - 1)
  have hdupper : d ≤ (r + 1) ^ m := by omega
  have hdpos : 0 < d := by omega
  exact hdcomp.trans <| rootComparison_lt_ratio hm ht hη hp_lower hdupper hdpos hF

lemma tendsto_orderRatio_upper (k : ℕ) :
    Tendsto (fun d : ℕ ↦ (1 + (d : ℝ)⁻¹) ^ k) atTop (nhds 1) := by
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa using (hone.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).pow k

/-- Theorem 1.1: for every fixed positive diameter, the vertex degree--diameter extremum has
leading term `d^k`. -/
theorem theorem_1_1_of_prime_intervals (hprime : PrimeIntervalHypothesis)
    (hw : AsymptoticHalvedWitnessHypothesis) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun d : ℕ ↦ (nKD k d : ℝ) / (d : ℝ) ^ k) atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    exact eventually_lt_orderRatio hprime hw hk hy
  · intro z hz
    have hupper : ∀ᶠ d : ℕ in atTop, (1 + (d : ℝ)⁻¹) ^ k < z :=
      (tendsto_orderRatio_upper k).eventually (Iio_mem_nhds hz)
    filter_upwards [hupper, eventually_gt_atTop 0] with d hupp hd
    have hdegree : (nKD k d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast (nKD_le_mooreBound k d).trans (mooreBound_le_add_one_pow k d)
    have hratioUpper : (nKD k d : ℝ) / (d : ℝ) ^ k ≤
        (1 + (d : ℝ)⁻¹) ^ k := by
      calc
        (nKD k d : ℝ) / (d : ℝ) ^ k ≤
            (((d + 1 : ℕ) : ℝ) ^ k) / (d : ℝ) ^ k :=
          div_le_div_of_nonneg_right hdegree (by positivity)
        _ = (1 + (d : ℝ)⁻¹) ^ k := by
          rw [← div_pow]
          congr 1
          norm_num
          field_simp
    exact hratioUpper.trans_lt hupp

lemma edgeRatio_isBoundedUnder_le (ell : ℕ) :
    atTop.IsBoundedUnder (· ≤ ·)
      (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) := by
  refine ⟨(3 : ℝ) ^ ell + 1, ?_⟩
  change ∀ᶠ d : ℕ in atTop,
    (h ell d : ℝ) / (d : ℝ) ^ ell ≤ (3 : ℝ) ^ ell + 1
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hhpos : 1 ≤ h ell d := by simp [h]
  have hbase : 2 * d + 1 ≤ 3 * d := by omega
  have hcoarse : h ell d - 1 ≤ (3 * d) ^ ell :=
    (h_sub_one_le_coarseBound ell d).trans (Nat.pow_le_pow_left hbase ell)
  have hrewrite : h ell d = (h ell d - 1) + 1 := by omega
  have hh : h ell d ≤ (3 * d) ^ ell + 1 := by
    rw [hrewrite]
    exact Nat.add_le_add_right hcoarse 1
  have hhReal : (h ell d : ℝ) ≤ ((3 * d) ^ ell + 1 : ℕ) := by
    exact_mod_cast hh
  have hden : (0 : ℝ) < (d : ℝ) ^ ell := by positivity
  calc
    (h ell d : ℝ) / (d : ℝ) ^ ell ≤
        (((3 * d) ^ ell + 1 : ℕ) : ℝ) / (d : ℝ) ^ ell :=
      div_le_div_of_nonneg_right hhReal hden.le
    _ = (3 : ℝ) ^ ell + 1 / (d : ℝ) ^ ell := by
      push_cast
      rw [mul_pow, add_div]
      field_simp
    _ ≤ (3 : ℝ) ^ ell + 1 := by
      gcongr
      exact (div_le_one hden).2 (one_le_pow₀ (by exact_mod_cast hd))

/-- Corollary 1.2: for every fixed `ell ≥ 2`, the edge extremum has lower limiting ratio at
least one. -/
theorem corollary_1_2_of_prime_intervals (hprime : PrimeIntervalHypothesis)
    (hw : AsymptoticHalvedWitnessHypothesis) {ell : ℕ} (hell : 2 ≤ ell) :
    1 ≤ liminf (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) atTop := by
  let k := ell - 1
  have hk : 0 < k := by omega
  have hkell : k + 1 = ell := by omega
  have hnonneg : atTop.IsBoundedUnder (· ≥ ·)
      (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ d : ℕ in atTop, (0 : ℝ) ≤ (h ell d : ℝ) / (d : ℝ) ^ ell
    exact .of_forall fun d ↦
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) ell)
  have hbounded := edgeRatio_isBoundedUnder_le ell
  rw [le_liminf_iff hbounded.isCoboundedUnder_ge hnonneg]
  intro y hy
  simpa [hkell] using eventually_lt_edgeRatio hprime hw hk hy

end

end DegreeDiameter

end MooreBound
