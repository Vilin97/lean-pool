/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SolenoidalDiagonal
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

/-!
# Quantitative jets of the actual diagonal sum

Local finiteness identifies derivatives of the actual `tsum` with finite sums
of actual `iteratedFDeriv`s. Pointwise stage estimates then give quantitative
tail estimates. The stage estimates themselves are explicit hypotheses, not
conclusions of the numerical cutoff selection. The prefix must depend on the
requested derivative order and decay power; no fixed tail is declared flat.
-/

noncomputable section

namespace NavierStokes.DiagonalJetBounds

open Set Filter Function
open scoped Topology BigOperators ContDiff

section LocalSums

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
/-- A common neighborhood kills all sufficiently late terms. This follows
from local finiteness of the supports; pointwise finiteness alone is weaker. -/
theorem eventually_zero_tail_of_locallyFinite {F : ℕ → E → V}
    (hF : LocallyFinite (fun j => support (F j))) (x : E) :
    ∃ K : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, K ≤ j → F j y = 0 := by
  obtain ⟨s, hs, hfin⟩ := hF x
  obtain ⟨K, hK⟩ := hfin.bddAbove
  refine ⟨K + 1, ?_⟩
  filter_upwards [hs] with y hy
  intro j hj
  by_contra hne
  have hle : j ≤ K := hK ⟨y, hne, hy⟩
  omega

private theorem finite_sum_jet {F : ℕ → E → V} {x : E}
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x) (K m : ℕ) :
    iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range K, F j y) x =
      ∑ j ∈ Finset.range K, iteratedFDeriv ℝ m (F j) x := by
  have hs : ∀ j ∈ Finset.range K, ContDiffWithinAt ℝ m (F j) univ x := by
    intro j _
    exact ((hF j).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffWithinAt
  simpa only [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) hs

/-- A common zero tail gives smoothness of the actual sum and termwise
derivative identities. Summability here is proved by finite support. -/
theorem tsum_jet_identity {F : ℕ → E → V} {x : E}
    (hloc : ∃ K : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, K ≤ j → F j y = 0)
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x) :
    ContDiffAt ℝ ∞ (fun y => ∑' j : ℕ, F j y) x ∧
      ∀ m : ℕ, Summable (fun j => iteratedFDeriv ℝ m (F j) x) ∧
        iteratedFDeriv ℝ m (fun y => ∑' j : ℕ, F j y) x =
          ∑' j : ℕ, iteratedFDeriv ℝ m (F j) x := by
  obtain ⟨K, hK⟩ := hloc
  have heq : (fun y => ∑' j : ℕ, F j y) =ᶠ[𝓝 x]
      (fun y => ∑ j ∈ Finset.range K, F j y) := by
    filter_upwards [hK] with y hy
    apply tsum_eq_sum
    intro j hj
    exact hy j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ j ∈ Finset.range K, F j y) x :=
    ContDiffAt.sum (fun j _ => hF j)
  refine ⟨hs.congr_of_eventuallyEq heq, fun m => ?_⟩
  have hzero : ∀ j : ℕ, K ≤ j → iteratedFDeriv ℝ m (F j) x = 0 := by
    intro j hj
    have hjzero : F j =ᶠ[𝓝 x] (fun _ => 0) := hK.mono (fun _ hy => hy j hj)
    have hjet := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hjzero m).self_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hjet
  have hsum : Summable (fun j => iteratedFDeriv ℝ m (F j) x) := by
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro j hj
    exact hzero j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))
  refine ⟨hsum, ?_⟩
  calc
    _ = iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range K, F j y) x :=
      (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds
    _ = ∑ j ∈ Finset.range K, iteratedFDeriv ℝ m (F j) x := finite_sum_jet hF K m
    _ = ∑' j : ℕ, iteratedFDeriv ℝ m (F j) x := by
      symm
      apply tsum_eq_sum
      intro j hj
      exact hzero j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))

/-- The jet of the actual sum minus a finite prefix is the sum of the actual
tail jets. The sum on the right is genuinely summable. -/
theorem tsum_sub_prefix_jet {F : ℕ → E → V} {x : E}
    (hloc : ∃ K : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, K ≤ j → F j y = 0)
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x) (J m : ℕ) :
    Summable (fun n : ℕ => iteratedFDeriv ℝ m (F (J + 1 + n)) x) ∧
      iteratedFDeriv ℝ m
        (fun y => (∑' j : ℕ, F j y) - ∑ j ∈ Finset.range (J + 1), F j y) x =
          ∑' n : ℕ, iteratedFDeriv ℝ m (F (J + 1 + n)) x := by
  obtain ⟨hsmooth, hjet⟩ := tsum_jet_identity hloc hF
  obtain ⟨hsum, hid⟩ := hjet m
  have htail : Summable (fun n : ℕ => iteratedFDeriv ℝ m (F (n + (J + 1))) x) :=
    (summable_nat_add_iff (f := fun j => iteratedFDeriv ℝ m (F j) x) (J + 1)).2 hsum
  refine ⟨by simpa only [Nat.add_comm] using htail, ?_⟩
  have hprefix : ContDiffAt ℝ ∞
      (fun y => ∑ j ∈ Finset.range (J + 1), F j y) x :=
    ContDiffAt.sum (fun j _ => hF j)
  have hm : (m : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  rw [fun_iteratedFDeriv_sub_apply (hsmooth.of_le hm) (hprefix.of_le hm),
    hid, finite_sum_jet hF (J + 1) m]
  calc
    _ = ∑' n : ℕ, iteratedFDeriv ℝ m (F (n + (J + 1))) x := by
      apply sub_eq_iff_eq_add.mpr
      exact (hsum.sum_add_tsum_nat_add (J + 1)).symm.trans (add_comm _ _)
    _ = _ := tsum_congr (fun n => congrArg
      (fun j => iteratedFDeriv ℝ m (F j) x) (Nat.add_comm n (J + 1)))

end LocalSums

section Scalar

/-- The scalar estimate from `DiagonalScale`, with the gain already denoting
the exponent retained after absorption of logarithmic factors. -/
theorem scalar_tail_bound (g : ℕ → ℝ) (hg : Monotone g) (L q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (J : ℕ) :
    Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) - L)) ∧
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) - L)) ≤
      (1 / 2 : ℝ) ^ J * q ^ (g (J + 1) - L) := by
  have hmono : Monotone (fun j => 2 * g j) := fun i j hij =>
    mul_le_mul_of_nonneg_left (hg hij) (by norm_num)
  have hcancel : ∀ j, 2 * g j / 2 = g j := fun _ => by ring
  simpa only [hcancel] using
    DiagonalScale.weighted_tail_bound (fun j => 2 * g j) hmono L q hq hq1 J

/-- One prefix can accommodate every derivative in a prescribed finite jet.
No monotonicity assumption is needed on the loss function. -/
theorem exists_prefix_gain (g L : ℕ → ℝ) (hgtop : Tendsto g atTop atTop)
    (M Jmin : ℕ) (N : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∀ m ≤ M, N ≤ g (J + 1) - L m := by
  let B : ℝ := (Finset.range (M + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos M)⟩ L
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (hgtop.eventually (eventually_ge_atTop (N + B)))
  refine ⟨max Jmin (max M K), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_left M K).trans (le_max_right _ _)
  · intro m hm
    have hmB : L m ≤ B :=
      Finset.le_sup' L (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have hgJ := hK (max Jmin (max M K) + 1) (by omega)
    linarith

end Scalar

section Quantitative

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bound for actual stage derivatives transfers to the actual remainder.
The conclusion includes the exact geometric tail coefficient. -/
theorem norm_tsum_sub_prefix_jet_le {F : ℕ → E → V} {x : E}
    (hloc : ∃ K : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, K ≤ j → F j y = 0)
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x)
    (g : ℕ → ℝ) (hg : Monotone g) (L q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (J m : ℕ)
    (hbound : ∀ j, J < j →
      ‖iteratedFDeriv ℝ m (F j) x‖ ≤ (1 / 2 : ℝ) ^ j * q ^ (g j - L)) :
    ‖iteratedFDeriv ℝ m
      (fun y => (∑' j : ℕ, F j y) - ∑ j ∈ Finset.range (J + 1), F j y) x‖ ≤
        (1 / 2 : ℝ) ^ J * q ^ (g (J + 1) - L) := by
  obtain ⟨hsum, hid⟩ := tsum_sub_prefix_jet hloc hF J m
  obtain ⟨hmajor, htail⟩ := scalar_tail_bound g hg L q hq hq1 J
  rw [hid]
  exact (hsum.hasSum.norm_le_of_bounded hmajor.hasSum
    (fun n => hbound (J + 1 + n) (by omega))).trans htail

/-- Direct version for any smooth family with locally finite supports. -/
theorem norm_tsum_sub_prefix_jet_le_of_locallyFinite {F : ℕ → E → V} {x : E}
    (hloc : LocallyFinite (fun j => support (F j)))
    (hF : ∀ j, ContDiffAt ℝ ∞ (F j) x)
    (g : ℕ → ℝ) (hg : Monotone g) (L q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (J m : ℕ)
    (hbound : ∀ j, J < j →
      ‖iteratedFDeriv ℝ m (F j) x‖ ≤ (1 / 2 : ℝ) ^ j * q ^ (g j - L)) :
    ‖iteratedFDeriv ℝ m
      (fun y => (∑' j : ℕ, F j y) - ∑ j ∈ Finset.range (J + 1), F j y) x‖ ≤
        (1 / 2 : ℝ) ^ J * q ^ (g (J + 1) - L) :=
  norm_tsum_sub_prefix_jet_le (eventually_zero_tail_of_locallyFinite hloc x)
    hF g hg L q hq hq1 J m hbound

/-- The stage estimates needed by the diagonal argument, stated on actual
cut potentials and their actual derivatives. Stage zero is exempt; stage `j`
controls the finite list of derivatives through `j+2`. -/
def CutStageBounds (a : ℕ → ℝ) (q : E → ℝ) (A : ℕ → E → V)
    (g L : ℕ → ℝ) (U : Set E) : Prop :=
  ∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ x ∈ U,
    ‖iteratedFDeriv ℝ m (SolenoidalDiagonal.cutStage a q A j) x‖ ≤
      (1 / 2 : ℝ) ^ j * (q x) ^ (g j - L m)

/-- The quantitative bound for the concrete cutoff-potential `tsum` already
constructed in `SolenoidalDiagonal`. -/
theorem potential_tail_jet_bound {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {g L : ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : CutStageBounds a q A g L U) {x : E} (hx : x ∈ U)
    (hqx : 0 < q x) (hqx1 : q x ≤ 1) (J m : ℕ) (hm : m ≤ J + 3) :
    ‖iteratedFDeriv ℝ m
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        SolenoidalDiagonal.partialPotential a q A (J + 1) y) x‖ ≤
      (1 / 2 : ℝ) ^ J * (q x) ^ (g (J + 1) - L m) := by
  have hqAt := hq.contDiffAt (hU.mem_nhds hx)
  have hAAt : ∀ j, ContDiffAt ℝ ∞ (A j) x :=
    fun j => (hA j).contDiffAt (hU.mem_nhds hx)
  exact norm_tsum_sub_prefix_jet_le
    (SolenoidalDiagonal.eventually_zero_tail ha hqAt.continuousAt hqx A)
    (SolenoidalDiagonal.cutStage_contDiffAt hqAt hAAt) g hg (L m) (q x) hqx hqx1
    J m (fun j hj => hb j (by omega) m (by omega) x hx)

/-- Given a finite derivative ceiling and a target power, choose one prefix
uniformly for every point in the positive unit-scale domain. -/
theorem exists_potential_tail_order {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {g L : ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hgtop : Tendsto g atTop atTop) (hb : CutStageBounds a q A g L U)
    (M Jmin : ℕ) (N : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∀ m ≤ M, ∀ x ∈ U,
      0 < q x → q x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.potentialSum a q A y -
          SolenoidalDiagonal.partialPotential a q A (J + 1) y) x‖ ≤
        (1 / 2 : ℝ) ^ J * (q x) ^ N := by
  obtain ⟨J, hJmin, hJM, hgain⟩ := exists_prefix_gain g L hgtop M Jmin N
  refine ⟨J, hJmin, hJM, ?_⟩
  intro m hm x hx hqx hqx1
  have htail := potential_tail_jet_bound ha hU hq hA hg hb hx hqx hqx1 J m (by omega)
  exact htail.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hqx hqx1 (hgain m hm)) (by positivity))

end Quantitative

section UncutPrefix

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The original finite stage, before multiplying its potentials by cutoffs. -/
def uncutPrefix (A : ℕ → E → V) (N : ℕ) (x : E) : V :=
  ∑ j ∈ Finset.range N, A j x

omit [NormedSpace ℝ E] in
/-- A single small-scale neighborhood makes the whole finite prefix equal
to the original prefix locally in the spatial variables. Consequently every
derivative order, not just the values at the point, agrees. -/
theorem partialPotential_eventuallyEq_uncut (a : ℕ → ℝ) (q : E → ℝ)
    (A : ℕ → E → V) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, ContinuousAt q x → |q x| < δ →
      SolenoidalDiagonal.partialPotential a q A N =ᶠ[𝓝 x] uncutPrefix A N := by
  obtain ⟨δ, hδ, hplateau⟩ := Metric.mem_nhds_iff.1
    (SmoothCutoffs.finite_scaledCutoffs_eventually_one (Finset.range N) a)
  refine ⟨δ, hδ, fun x hq hx => ?_⟩
  have hxball : q x ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hx
  filter_upwards [hq (Metric.isOpen_ball.mem_nhds hxball)] with y hy
  apply Finset.sum_congr rfl
  intro j hj
  change SmoothCutoffs.scaledCutoff (a j) (q y) • A j y = A j y
  rw [hplateau hy j hj, one_smul]

/-- The actual cut-sum remainder can be compared to the original uncut
finite stage for small `q`, with an arbitrary prescribed finite jet and power. -/
theorem exists_uncut_tail_order {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {g L : ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hgtop : Tendsto g atTop atTop) (hb : CutStageBounds a q A g L U)
    (M Jmin : ℕ) (N : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ m ≤ M, ∀ x ∈ U, 0 < q x → q x < δ →
        ‖iteratedFDeriv ℝ m
          (fun y => SolenoidalDiagonal.potentialSum a q A y -
            uncutPrefix A (J + 1) y) x‖ ≤ (1 / 2 : ℝ) ^ J * (q x) ^ N := by
  obtain ⟨J, hJmin, hJM, htail⟩ :=
    exists_potential_tail_order ha hU hq hA hg hgtop hb M Jmin N
  obtain ⟨δ, hδ, hprefix⟩ := partialPotential_eventuallyEq_uncut a q A (J + 1)
  refine ⟨J, hJmin, hJM, min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro m hm x hx hqx hsmall
  have hqx1 : q x ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  have hsmall' : |q x| < δ := by
    rw [abs_of_pos hqx]
    exact hsmall.trans_le (min_le_left _ _)
  have heq := hprefix x (hq.contDiffAt (hU.mem_nhds hx)).continuousAt hsmall'
  have hdiff :
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        SolenoidalDiagonal.partialPotential a q A (J + 1) y) =ᶠ[𝓝 x]
      (fun y => SolenoidalDiagonal.potentialSum a q A y - uncutPrefix A (J + 1) y) := by
    filter_upwards [heq] with y hy
    rw [hy]
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hdiff m).self_of_nhds]
  exact htail m hm x hx hqx hqx1

/-- Filter version of the small-scale comparison. The prefix depends on
the finite derivative ceiling and target power, never on the point. -/
theorem exists_uncut_tail_order_eventually {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {g L : ℕ → ℝ} {U : Set E}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hgtop : Tendsto g atTop atTop) (hb : CutStageBounds a q A g L U)
    {l : Filter E} (hlU : ∀ᶠ x in l, x ∈ U) (hlq : ∀ᶠ x in l, 0 < q x)
    (hqzero : Tendsto q l (𝓝 0)) (M Jmin : ℕ) (N : ℝ) :
    ∃ J : ℕ, Jmin ≤ J ∧ M ≤ J ∧ ∀ᶠ x in l, ∀ m ≤ M,
      ‖iteratedFDeriv ℝ m
        (fun y => SolenoidalDiagonal.potentialSum a q A y -
          uncutPrefix A (J + 1) y) x‖ ≤ (1 / 2 : ℝ) ^ J * (q x) ^ N := by
  obtain ⟨J, hJmin, hJM, δ, hδ, hbound⟩ :=
    exists_uncut_tail_order ha hU hq hA hg hgtop hb M Jmin N
  refine ⟨J, hJmin, hJM, ?_⟩
  filter_upwards [hlU, hlq, hqzero.eventually (gt_mem_nhds hδ)] with x hx hqx hsmall
  exact fun m hm => hbound m hm x hx hqx hsmall

end UncutPrefix

end NavierStokes.DiagonalJetBounds
