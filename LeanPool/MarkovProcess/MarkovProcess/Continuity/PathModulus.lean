/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicChaining
public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicPathChaining
public import LeanPool.MarkovProcess.MarkovProcess.Path.Basic


/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoEMetricSpace alpha]

/-- The paths whose oscillation over `[0, T]` at scale `delta` is at most `r`: any two times of
`[0, T]` within `delta` of each other carry values within `r` of each other. -/
def modulusSet (T : ℝ≥0) (delta r : ℝ≥0∞) : Set (ContinuousPath alpha) :=
  {omega | ∀ s t : ℝ≥0, s ≤ T → t ≤ T → edist s t ≤ delta → edist (omega s) (omega t) ≤ r}

theorem modulusSet_mono {T : ℝ≥0} {delta r r' : ℝ≥0∞} (hrr : r ≤ r') :
    modulusSet (alpha := alpha) T delta r ⊆ modulusSet T delta r' :=
  fun _ homega s t hs ht hd ↦ (homega s t hs ht hd).trans hrr

theorem isClosed_modulusSet (T : ℝ≥0) (delta r : ℝ≥0∞) :
    IsClosed (modulusSet (alpha := alpha) T delta r) := by
  have hrewrite : modulusSet (alpha := alpha) T delta r =
      ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ _ : s ≤ T, ⋂ _ : t ≤ T, ⋂ _ : edist s t ≤ delta,
        {omega : ContinuousPath alpha | edist (omega s) (omega t) ≤ r} := by
    ext omega
    simp only [modulusSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrewrite]
  refine isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_
  exact isClosed_le ((continuous_eval (alpha := alpha) s).edist (continuous_eval t))
    continuous_const

theorem measurableSet_modulusSet (T : ℝ≥0) (delta r : ℝ≥0∞) :
    MeasurableSet (modulusSet (alpha := alpha) T delta r) :=
  (isClosed_modulusSet T delta r).measurableSet

end ContinuousPath

section Estimate

variable {alpha : Type*} [PseudoEMetricSpace alpha]

/-- The chaining bound produced at base level `N`: twice the exact geometric tail above `N` plus
one coarse threshold. -/
private noncomputable def dyadicChainBound (gamma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  2 * (dyadicIncrementThreshold gamma (N + 1) *
      (1 - dyadicIncrementThresholdRatio gamma)⁻¹) + dyadicIncrementThreshold gamma N

private theorem tendsto_dyadicChainBound {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (dyadicChainBound gamma) atTop (nhds 0) := by
  have htail := tendsto_dyadicIncrementThreshold_ancestor_tail_zero hgamma
  have hthr : Tendsto (fun N : ℕ ↦ dyadicIncrementThreshold gamma N) atTop (nhds 0) := by
    simp_rw [dyadicIncrementThreshold_eq_ratio_pow]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (dyadicIncrementThresholdRatio_lt_one hgamma)
  have hdouble : Tendsto (fun N : ℕ ↦ 2 * (dyadicIncrementThreshold gamma (N + 1) *
      (1 - dyadicIncrementThresholdRatio gamma)⁻¹)) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr (by simp))
  simpa only [dyadicChainBound, add_zero] using! hdouble.add hthr

/-- The event that some adjacent increment of the level-`n` subdivision of `[0, T]` reaches the
level's Kolmogorov--Chentsov threshold. -/
private def badLevel (T : ℝ≥0) (p gamma : ℝ) (n : ℕ) : Set (ContinuousPath alpha) :=
  finiteGridBadIncrement (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t)
    (fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) p (dyadicIncrementThreshold gamma n)

private theorem coe_div_two_pow (T : ℝ≥0) (n : ℕ) :
    ((T / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ENNReal.coe_div (by positivity), div_eq_mul_inv, ENNReal.coe_pow, ENNReal.coe_ofNat]

private theorem measure_badLevel_le {p q : ℝ} {M : ℝ≥0} {mu : Measure (ContinuousPath alpha)}
    (hX : IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t) mu p q M)
    {gamma : ℝ} (hgamma : 0 < gamma) (T : ℝ≥0) (n : ℕ) :
    mu (badLevel T p gamma n) ≤
      (T : ℝ≥0∞) ^ q * ((M * dyadicIncrementDecayRatio p q gamma ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hgrid : ∀ i : Fin (2 ^ n),
      edist ((fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) i.castSucc)
          ((fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) i.succ) ≤
        ((T / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    intro i
    simpa only [Fin.val_castSucc, Fin.val_succ] using edist_dyadicTime_succ_le T n (i : ℕ)
  have hbound := IsKolmogorovProcess.measure_finiteGridBadIncrement_le hX
    (fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) _ _ hgrid
    (dyadicIncrementThreshold_ne_zero hgamma n) (dyadicIncrementThreshold_ne_top hgamma n)
  refine hbound.trans (le_of_eq ?_)
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [coe_div_two_pow, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top (by simp),
    ← dyadic_bound_normalization p q gamma M n]
  simp only [div_eq_mul_inv]
  ring

private theorem le_add_of_edist_le {s t c : ℝ≥0} (h : edist s t ≤ (c : ℝ≥0∞)) : t ≤ s + c := by
  have hd : dist s t ≤ (c : ℝ) := by
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff c.coe_nonneg).mp h
  rw [NNReal.dist_eq] at hd
  have hlow := (abs_le.mp hd).1
  rw [← NNReal.coe_le_coe]
  push_cast
  linarith

private theorem mem_modulusSet_of_notMem_badLevel {p gamma : ℝ} (hp : 0 < p)
    {T : ℝ≥0} (hT : 0 < T) (N : ℕ) {omega : ContinuousPath alpha}
    (homega : ∀ n, N ≤ n → omega ∉ badLevel T p gamma n) :
    omega ∈ ContinuousPath.modulusSet T ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞)
      (dyadicChainBound gamma N) := by
  have hadj : ∀ n, N ≤ n →
      HasDyadicAdjacentBound (fun t ↦ omega t) T n (dyadicIncrementThreshold gamma n) := by
    intro n hn i hi
    have hlt := edist_adjacent_lt_of_notMem_finiteGridBadIncrement
      (X := fun (t : ℝ≥0) (eta : ContinuousPath alpha) ↦ eta t)
      (grid := fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) hp (homega n hn)
      (⟨i, hi⟩ : Fin (2 ^ n))
    simpa only [Fin.val_castSucc, Fin.val_succ] using hlt.le
  have key : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → s ≤ t →
      edist s t ≤ ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) →
        edist (omega s) (omega t) ≤ dyadicChainBound gamma N := by
    intro s t hs ht hst hd
    have hd' : t ≤ s + T / 2 ^ (N + 1) := le_add_of_edist_le hd
    have hstep : ∀ u : ℕ,
        edist (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) s)))
          (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) t))) ≤
        dyadicChainBound gamma N := by
      intro u
      have hj := dyadicIndex_le hT ht (N + (u + 1))
      have hij := dyadicIndex_mono hT (N + (u + 1)) hst
      have hsub := dyadicIndex_sub_le (T := T) hT (n := N) (r := u + 1) (Nat.le_add_left 1 u) hd'
      have hchain := edist_dyadicTime_le_of_sub_le (f := fun v ↦ omega v) (T := T)
        (e := dyadicIncrementThreshold gamma) (n := N) (r := u + 1)
        (fun k hk _ ↦ hadj k hk) hij hj hsub
      refine hchain.trans ?_
      unfold dyadicChainBound
      gcongr
      exact sum_dyadicIncrementThreshold_ancestor_le_tail gamma N (u + 1)
    have hlevel : Tendsto (fun u : ℕ ↦ N + (u + 1)) atTop atTop :=
      tendsto_atTop_mono (fun u ↦ by simp only [id_eq]; omega) tendsto_id
    have htends : Tendsto
        (fun u : ℕ ↦ edist (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) s)))
          (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) t))))
        atTop (nhds (edist (omega s) (omega t))) := by
      refine Tendsto.edist ?_ ?_
      · exact (omega.continuous.tendsto s).comp
          ((tendsto_dyadicTime_dyadicIndex hT s).comp hlevel)
      · exact (omega.continuous.tendsto t).comp
          ((tendsto_dyadicTime_dyadicIndex hT t).comp hlevel)
    exact le_of_tendsto htends (Eventually.of_forall hstep)
  intro s t hs ht hd
  rcases le_total s t with hst | hst
  · exact key s t hs ht hst hd
  · rw [edist_comm]
    exact key t s ht hs hst (by rwa [edist_comm])

private theorem tendsto_badTail {p q gamma : ℝ} (hp : 0 < p) (hgamma : 0 < gamma)
    (hgammaq : gamma < (q - 1) / p) (M T : ℝ≥0) :
    Tendsto (fun N : ℕ ↦ (T : ℝ≥0∞) ^ q *
        ∑' k : ℕ, ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞))
      atTop (nhds 0) := by
  set rho : ℝ≥0 := dyadicIncrementDecayRatio p q gamma with hrhodef
  have hrho : (rho : ℝ≥0∞) < 1 := by
    exact_mod_cast dyadicIncrementDecayRatio_lt_one hp hgammaq
  have hsum : ∀ N : ℕ, (∑' k : ℕ, ((M * rho ^ (N + k) : ℝ≥0) : ℝ≥0∞)) =
      (M : ℝ≥0∞) * ((rho : ℝ≥0∞) ^ N * (1 - (rho : ℝ≥0∞))⁻¹) := by
    intro N
    have hrw : ∀ k : ℕ, ((M * rho ^ (N + k) : ℝ≥0) : ℝ≥0∞) =
        (M : ℝ≥0∞) * ((rho : ℝ≥0∞) ^ N * (rho : ℝ≥0∞) ^ k) := by
      intro k
      push_cast
      rw [pow_add]
    simp_rw [hrw]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hpow : Tendsto (fun N : ℕ ↦ ((rho : ℝ≥0∞)) ^ N) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrho
  have hq : 0 < q := by
    have hpos : 0 < (q - 1) / p := lt_trans hgamma hgammaq
    have := (div_pos_iff_of_pos_right hp).mp hpos
    linarith
  have hfinite : (T : ℝ≥0∞) ^ q * (M : ℝ≥0∞) * (1 - (rho : ℝ≥0∞))⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top
    · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hrho).ne'
  have hconst : Tendsto (fun N : ℕ ↦ ((T : ℝ≥0∞) ^ q * (M : ℝ≥0∞) * (1 - (rho : ℝ≥0∞))⁻¹) *
      ((rho : ℝ≥0∞)) ^ N) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hpow (Or.inr hfinite)
  refine hconst.congr fun N ↦ ?_
  rw [hsum N]
  ring

/-- **Quantitative modulus of continuity, uniform over the law.**  Fix Kolmogorov exponents
`0 < p`, an admissible Hölder exponent `0 < gamma < (q - 1) / p`, a constant `M`, a horizon `T`,
an oscillation tolerance `r` and a mass tolerance `eps`.  Then there is a single scale
`delta > 0` such that *every* probability law on continuous paths whose coordinate process is a
Kolmogorov process with these exponents and this constant gives mass at most `eps` to the paths
that oscillate by more than `r` at scale `delta` on `[0, T]`.

The scale `delta` is produced by the dyadic chaining of `Continuity/DyadicPathChaining.lean`
together with the geometric union bound of `Continuity/DyadicIncrements.lean`; both bounds depend
only on the displayed data, which is why the conclusion is uniform in the law. -/
theorem ContinuousPath.exists_measure_compl_modulusSet_le {p q : ℝ} {M : ℝ≥0} {gamma : ℝ}
    (hp : 0 < p) (hgamma : 0 < gamma) (hgammaq : gamma < (q - 1) / p) (T : ℝ≥0) {r : ℝ≥0∞}
    (hr : 0 < r) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧
      ∀ mu : Measure (ContinuousPath alpha),
        IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t) mu p q M →
          mu (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT | hT
  · refine ⟨1, one_pos, fun mu _ ↦ ?_⟩
    have hempty : (ContinuousPath.modulusSet (alpha := alpha) T 1 r)ᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro omega homega
      refine homega fun s t hs ht _ ↦ ?_
      have hs0 : s = 0 := le_antisymm (hT ▸ hs) (zero_le : (0 : ℝ≥0) ≤ s)
      have ht0 : t = 0 := le_antisymm (hT ▸ ht) (zero_le : (0 : ℝ≥0) ≤ t)
      subst hs0
      subst ht0
      simp
    rw [hempty]
    simp
  · have hchain := (tendsto_dyadicChainBound hgamma).eventually_le_const hr
    have htail := (tendsto_badTail hp hgamma hgammaq M T).eventually_le_const heps
    obtain ⟨N, hN1, hN2⟩ := (hchain.and htail).exists
    refine ⟨((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞), ?_, fun mu hX ↦ ?_⟩
    · exact_mod_cast div_pos hT (by positivity)
    · have hsubset : (ContinuousPath.modulusSet (alpha := alpha) T
          ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) r)ᶜ ⊆
            ⋃ k : ℕ, badLevel T p gamma (N + k) := by
        intro omega homega
        by_contra hcon
        refine homega (ContinuousPath.modulusSet_mono hN1 ?_)
        refine mem_modulusSet_of_notMem_badLevel hp hT N fun n hn hmem ↦ ?_
        exact hcon (Set.mem_iUnion.mpr ⟨n - N, by rwa [Nat.add_sub_cancel' hn]⟩)
      calc mu (ContinuousPath.modulusSet T ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) r)ᶜ
          ≤ mu (⋃ k : ℕ, badLevel T p gamma (N + k)) := measure_mono hsubset
        _ ≤ ∑' k : ℕ, mu (badLevel T p gamma (N + k)) := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, (T : ℝ≥0∞) ^ q *
              ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞) :=
            ENNReal.tsum_le_tsum fun k ↦ measure_badLevel_le hX hgamma T (N + k)
        _ = (T : ℝ≥0∞) ^ q *
              ∑' k : ℕ, ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞) :=
            ENNReal.tsum_mul_left
        _ ≤ eps := hN2

end Estimate

end MarkovProcess
