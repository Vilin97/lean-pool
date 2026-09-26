/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.PathModulus
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.UniformSpace.Ascoli


/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

@[expose] public section

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha]

section Chaining

/-- Chaining along an equally spaced subdivision of `[0, t]`: a modulus of continuity at scale
`d` on `[0, T]` bounds the displacement from the initial value by the number of steps times the
oscillation. -/
theorem edist_le_of_modulus {T d : ℝ≥0} (hd : 0 < d) {rho : ℝ≥0∞} {f : ℝ≥0 → alpha}
    (hf : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → edist s t ≤ (d : ℝ≥0∞) → edist (f s) (f t) ≤ rho)
    {t : ℝ≥0} (ht : t ≤ T) :
    edist (f 0) (f t) ≤ ((⌈(T : ℝ) / d⌉₊ + 1 : ℕ) : ℝ≥0∞) * rho := by
  set K : ℕ := ⌈(T : ℝ) / d⌉₊ + 1 with hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    rw [hK]
    push_cast
    positivity
  have hKne : (K : ℝ≥0) ≠ 0 := by
    simpa only [ne_eq, Nat.cast_eq_zero] using Nat.succ_ne_zero _
  set u : ℕ → ℝ≥0 := fun k ↦ t * k / K with hu
  have hu0 : u 0 = 0 := by simp [hu]
  have huK : u K = t := by
    change t * (K : ℝ≥0) / (K : ℝ≥0) = t
    rw [mul_div_assoc, div_self hKne, mul_one]
  have hule : ∀ k, k ≤ K → u k ≤ T := by
    intro k hk
    refine le_trans ?_ ht
    rw [← NNReal.coe_le_coe]
    push_cast [hu]
    rw [div_le_iff₀ hKpos]
    have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
    nlinarith [t.coe_nonneg, hkK]
  have hTK : (T : ℝ) / K < (d : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := hd
    have hceil : (T : ℝ) / d ≤ (⌈(T : ℝ) / d⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (T : ℝ) / d < (K : ℝ) := by
      rw [hK]
      push_cast
      linarith
    rw [div_lt_iff₀ hKpos]
    rw [div_lt_iff₀ hdpos] at hlt
    linarith
  have hstep : ∀ k : ℕ, edist (u k) (u (k + 1)) ≤ (d : ℝ≥0∞) := by
    intro k
    have hexp : ((u k : ℝ≥0) : ℝ) - ((u (k + 1) : ℝ≥0) : ℝ) = -((t : ℝ) / K) := by
      simp only [hu]
      push_cast
      rw [div_sub_div_same, ← mul_sub, show (k : ℝ) - ((k : ℝ) + 1) = -1 by ring]
      ring
    have hval : dist (u k) (u (k + 1)) = (t : ℝ) / K := by
      rw [NNReal.dist_eq, hexp, abs_neg, abs_of_nonneg (by positivity)]
    have htK : (t : ℝ) / K ≤ (d : ℝ) := by
      have hmono : (t : ℝ) / K ≤ (T : ℝ) / K := by gcongr
      linarith [hTK]
    rw [edist_dist, hval, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal htK
  have hchain : edist (f (u 0)) (f (u K)) ≤ ∑ _i ∈ Finset.Ico 0 K, rho :=
    edist_le_Ico_sum_of_edist_le (f := fun k ↦ f (u k)) (Nat.zero_le K)
      (d := fun _ ↦ rho) fun {k} _ hkK ↦
        hf (u k) (u (k + 1)) (hule k hkK.le) (hule (k + 1) hkK) (hstep k)
  rw [hu0, huK] at hchain
  simpa only [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] using hchain

end Chaining

section Moduli

/-- The paths that start in `K0` and, for every natural `n`, oscillate by at most `r n` at
scale `delta n` over `[0, n]`. -/
def moduliSet (K0 : Set alpha) (delta rho : ℕ → ℝ≥0∞) : Set (ContinuousPath alpha) :=
  {omega | omega 0 ∈ K0} ∩ ⋂ n : ℕ, modulusSet (n : ℝ≥0) (delta n) (rho n)

/-- The same conditions read on arbitrary, not necessarily continuous, functions of time. -/
def moduliFunSet (K0 : Set alpha) (delta rho : ℕ → ℝ≥0∞) : Set (ℝ≥0 → alpha) :=
  {f | f 0 ∈ K0} ∩ ⋂ n : ℕ, {f : ℝ≥0 → alpha |
    ∀ s t : ℝ≥0, s ≤ (n : ℝ≥0) → t ≤ (n : ℝ≥0) → edist s t ≤ delta n → edist (f s) (f t) ≤ rho n}

theorem isClosed_moduliFunSet {K0 : Set alpha} (hK0 : IsClosed K0) (delta rho : ℕ → ℝ≥0∞) :
    IsClosed (moduliFunSet K0 delta rho) := by
  refine IsClosed.inter (hK0.preimage (continuous_apply (0 : ℝ≥0))) (isClosed_iInter fun n ↦ ?_)
  have hrewrite : {f : ℝ≥0 → alpha | ∀ s t : ℝ≥0, s ≤ (n : ℝ≥0) → t ≤ (n : ℝ≥0) →
        edist s t ≤ delta n → edist (f s) (f t) ≤ rho n} =
      ⋂ s : ℝ≥0, ⋂ t : ℝ≥0, ⋂ _ : s ≤ (n : ℝ≥0), ⋂ _ : t ≤ (n : ℝ≥0),
        ⋂ _ : edist s t ≤ delta n, {f : ℝ≥0 → alpha | edist (f s) (f t) ≤ rho n} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrewrite]
  refine isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_
  exact isClosed_le ((continuous_apply s).edist (continuous_apply t)) continuous_const

/-- A vanishing oscillation sequence makes the family of functions obeying the moduli
equicontinuous. -/
theorem equicontinuous_moduliFunSet {K0 : Set alpha} {delta rho : ℕ → ℝ≥0∞}
    (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0)) :
    Equicontinuous fun f : moduliFunSet K0 delta rho ↦ (f : ℝ≥0 → alpha) := by
  intro t0
  rw [equicontinuousAt_iff]
  intro eps heps
  obtain ⟨n0, hn0⟩ := exists_nat_ge ((t0 : ℝ) + 1)
  obtain ⟨n, hnr, hnn⟩ :=
    ((hrho.eventually_lt_const (ENNReal.ofReal_pos.mpr heps)).and
      (eventually_ge_atTop n0)).exists
  set d : ℝ≥0∞ := min (delta n) 1 with hd
  have hdpos : 0 < d := lt_min (hdelta n) one_pos
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hdreal : 0 < d.toReal := ENNReal.toReal_pos hdpos.ne' hdtop
  have hdle1 : d.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (min_le_right (delta n) 1)
  have hnreal : (t0 : ℝ) + 1 ≤ (n : ℝ) := by
    refine hn0.trans ?_
    exact_mod_cast hnn
  have ht0n : t0 ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  refine ⟨d.toReal, hdreal, fun s hs f ↦ ?_⟩
  have hsdist : |(s : ℝ) - (t0 : ℝ)| < d.toReal := by
    rw [← NNReal.dist_eq]
    exact hs
  have hsn : s ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have := (abs_lt.mp hsdist).2
    linarith
  have hedist : edist t0 s ≤ delta n := by
    have hlt : edist t0 s < d := by
      rw [edist_comm, edist_dist, ← ENNReal.ofReal_toReal hdtop]
      exact (ENNReal.ofReal_lt_ofReal_iff hdreal).mpr hs
    exact hlt.le.trans (min_le_left _ _)
  have hmod := Set.mem_iInter.mp f.2.2 n (t0 : ℝ≥0) s ht0n hsn hedist
  have hkey : ENNReal.ofReal (dist ((f : ℝ≥0 → alpha) t0) ((f : ℝ≥0 → alpha) s)) <
      ENNReal.ofReal eps := by
    rw [← edist_dist]
    exact lt_of_le_of_lt hmod hnr
  exact (ENNReal.ofReal_lt_ofReal_iff heps).mp hkey

/-- Over a proper metric state space the moduli already confine every value of the path to one
compact set, because a chain of steps of length at most `delta n` reaches every time of `[0, n]`
from the starting point. -/
theorem exists_isCompact_eval_mem [ProperSpace alpha] {K0 : Set alpha} (hK0 : IsCompact K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0))
    (t : ℝ≥0) :
    ∃ Q : Set alpha, IsCompact Q ∧ ∀ f ∈ moduliFunSet K0 delta rho, f t ∈ Q := by
  rcases K0.eq_empty_or_nonempty with hempty | ⟨c, hc⟩
  · refine ⟨∅, isCompact_empty, fun f hf ↦ ?_⟩
    rw [hempty] at hf
    exact absurd hf.1 (Set.notMem_empty _)
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall c).mp hK0.isBounded
  obtain ⟨n0, hn0⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n, hnr, hnn⟩ :=
    ((hrho.eventually_lt_const (zero_lt_one (α := ℝ≥0∞))).and (eventually_ge_atTop n0)).exists
  set d : ℝ≥0 := (min (delta n) 1).toNNReal with hd
  have hdtop : min (delta n) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hdcoe : (d : ℝ≥0∞) = min (delta n) 1 := by
    rw [hd, ENNReal.coe_toNNReal hdtop]
  have hdpos : 0 < d := by
    rw [← ENNReal.coe_pos, hdcoe]
    exact lt_min (hdelta n) one_pos
  have hdle : (d : ℝ≥0∞) ≤ delta n := by
    rw [hdcoe]
    exact min_le_left _ _
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hn0.trans (by exact_mod_cast hnn)
  set C : ℝ≥0∞ := ((⌈((n : ℝ≥0) : ℝ) / d⌉₊ + 1 : ℕ) : ℝ≥0∞) * rho n with hC
  have hCtop : C ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ne_top_of_lt (lt_of_lt_of_le hnr le_top))
  refine ⟨closedBall c (R + C.toReal), isCompact_closedBall _ _, fun f hf ↦ ?_⟩
  have hmod : ∀ s u : ℝ≥0, s ≤ (n : ℝ≥0) → u ≤ (n : ℝ≥0) → edist s u ≤ (d : ℝ≥0∞) →
      edist (f s) (f u) ≤ rho n := fun s u hs hu hsu ↦
    Set.mem_iInter.mp hf.2 n s u hs hu (hsu.trans hdle)
  have hchain := edist_le_of_modulus hdpos hmod htn
  have hdist : dist (f 0) (f t) ≤ C.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hCtop, ← edist_dist]
    exact hchain
  have h0 : dist (f 0) c ≤ R := mem_closedBall.mp (hR hf.1)
  rw [mem_closedBall]
  calc dist (f t) c ≤ dist (f t) (f 0) + dist (f 0) c := dist_triangle _ _ _
    _ ≤ C.toReal + R := add_le_add (by rw [dist_comm]; exact hdist) h0
    _ = R + C.toReal := add_comm _ _

/-- **Compactness of a modulus class, with compact containment as a hypothesis.**  If the values
at each fixed time of the functions obeying the moduli stay in a compact set, then the continuous
paths obeying them form a compact subset of path space.  This is Arzelà--Ascoli: the moduli give
equicontinuity, and the pointwise hypothesis gives the pointwise relative compactness that no
modulus can supply on a general complete separable metric space. -/
theorem isCompact_moduliSet_of_forall_isCompact {K0 : Set alpha} (hK0 : IsClosed K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0))
    (hpoint : ∀ t : ℝ≥0, ∃ Q : Set alpha, IsCompact Q ∧
      ∀ f ∈ moduliFunSet K0 delta rho, f t ∈ Q) :
    IsCompact (moduliSet K0 delta rho) := by
  have hequi := equicontinuous_moduliFunSet (K0 := K0) hdelta hrho
  choose Q hQcompact hQmem using hpoint
  have hfun : IsCompact (moduliFunSet K0 delta rho) :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi hQcompact)
      (isClosed_moduliFunSet hK0 delta rho)
      fun f hf ↦ Set.mem_univ_pi.mpr fun t ↦ hQmem t f hf
  have himage : ContinuousMap.toFun '' moduliSet K0 delta rho = moduliFunSet K0 delta rho := by
    ext f
    constructor
    · rintro ⟨omega, homega, rfl⟩
      exact ⟨homega.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp homega.2 n⟩
    · intro hf
      exact ⟨⟨f, hequi.continuous ⟨f, hf⟩⟩,
        ⟨hf.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp hf.2 n⟩, rfl⟩
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · rw [himage]
    exact hfun
  · exact hequi.comp fun w : moduliSet K0 delta rho ↦
      (⟨((w : ContinuousPath alpha) : ℝ≥0 → alpha),
        ⟨w.2.1, Set.mem_iInter.mpr fun n ↦ Set.mem_iInter.mp w.2.2 n⟩⟩ :
          moduliFunSet K0 delta rho)

/-- **Compactness of a modulus class over a proper state space.**  Over a metric state space whose
closed balls are compact, the continuous paths starting in a compact set and obeying a vanishing
sequence of moduli form a compact subset of path space. -/
theorem isCompact_moduliSet [ProperSpace alpha] {K0 : Set alpha} (hK0 : IsCompact K0)
    {delta rho : ℕ → ℝ≥0∞} (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0)) :
    IsCompact (moduliSet K0 delta rho) :=
  isCompact_moduliSet_of_forall_isCompact hK0.isClosed hdelta hrho
    (exists_isCompact_eval_mem hK0 hdelta hrho)

end Moduli

section Tight

private theorem tsum_geometric_half (eps : ℝ≥0∞) :
    (∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) = eps := by
  have hsplit : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 2⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow]
    ring
  have hone : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
  rw [ENNReal.tsum_mul_left]
  simp_rw [hsplit]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hone, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- **Tightness from a uniform modulus estimate.**  Let `S` be a family of measures on continuous
paths over a proper metric state space.  Suppose every member gives full mass to the paths
starting in one fixed compact set `K0`, and suppose that for every horizon `T`, every oscillation
tolerance `r > 0` and every mass tolerance `eps > 0` there is a *single* scale `delta > 0` at
which every member of the family gives mass at most `eps` to the paths oscillating by more than
`r` at scale `delta` on `[0, T]`.  Then `S` is tight.

Properness of the state space enters only through `exists_isCompact_eval_mem`; on a general
complete separable metric space it is replaced by the compact containment condition, in the form
of the hypothesis of `isCompact_moduliSet_of_forall_isCompact`. -/
theorem isTightMeasureSet_of_measure_compl_modulusSet_le [ProperSpace alpha]
    {S : Set (Measure (ContinuousPath alpha))} {K0 : Set alpha} (hK0 : IsCompact K0)
    (hstart : ∀ mu ∈ S, mu {omega : ContinuousPath alpha | omega 0 ∉ K0} = 0)
    (hmod : ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ mu ∈ S, mu (modulusSet T delta r)ᶜ ≤ eps) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro eps heps
  set rho : ℕ → ℝ≥0∞ := fun n ↦ ((n : ℝ≥0∞))⁻¹ with hrho
  have hrhopos : ∀ n : ℕ, 0 < rho n := fun n ↦ ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  have hrhotendsto : Tendsto rho atTop (nhds 0) := ENNReal.tendsto_inv_nat_nhds_zero
  have hepsn : ∀ n : ℕ, 0 < eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ :=
    fun n ↦ ENNReal.mul_pos heps.ne' (by simp)
  choose delta hdelta hdeltaS using fun n : ℕ ↦
    hmod (n : ℝ≥0) (rho n) (hrhopos n) _ (hepsn n)
  refine ⟨moduliSet K0 delta rho, isCompact_moduliSet hK0 hdelta hrhotendsto, fun mu hmu ↦ ?_⟩
  have hcompl : (moduliSet K0 delta rho)ᶜ =
      {omega : ContinuousPath alpha | omega 0 ∉ K0} ∪
        ⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ := by
    ext omega
    simp only [moduliSet, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_union, Set.mem_iUnion, not_and_or, not_forall]
  rw [hcompl]
  calc mu ({omega : ContinuousPath alpha | omega 0 ∉ K0} ∪
          ⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ)
      ≤ mu {omega : ContinuousPath alpha | omega 0 ∉ K0} +
        mu (⋃ n : ℕ, (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ) := measure_union_le _ _
    _ ≤ 0 + ∑' n : ℕ, mu (modulusSet ((n : ℝ≥0)) (delta n) (rho n))ᶜ :=
        add_le_add (hstart mu hmu).le (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
        rw [zero_add]
        exact ENNReal.tsum_le_tsum fun n ↦ hdeltaS n mu hmu
    _ = eps := tsum_geometric_half eps

end Tight

end ContinuousPath

end MarkovProcess
