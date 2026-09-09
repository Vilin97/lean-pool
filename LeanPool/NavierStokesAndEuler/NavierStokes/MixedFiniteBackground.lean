/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalResidual

/-!
# Finite background bounds from the raw increments

The raw-stage interface starts at index one. A bound for the actual
initialized stage is therefore kept explicit. Together with the raw
increment bounds it controls every finite prefix with one derivative-loss
function, independent of the number of correction stages.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedFiniteBackground

open Set Filter DiagonalResidual ProblemStatement
open scoped ContDiff Topology BigOperators

section General

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem raw_jetRate {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {g L : ℕ → ℝ} {C : ℕ → ℕ → ℝ} {S : Set D}
    (hraw : CutStageEstimates.RawStageBounds q A g L C (fun _ _ => 0) S)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    JetRate l q (A j) m (g j - L m) := by
  refine ⟨max (C j m) 0, le_max_right _ _, ?_⟩
  filter_upwards [hS, hq] with x hx hqx
  have hb : ‖iteratedFDeriv ℝ m (A j) x‖ ≤ C j m * q x ^ (g j - L m) := by
    simpa only [Real.rpow_zero, mul_one] using hraw j hj m x hx hqx.2
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg hqx.1.le _))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ V] in
theorem uncutPrefix_succ (A : ℕ → D → V) (N : ℕ) :
    DiagonalJetBounds.uncutPrefix A (N + 1) =
      fun x => DiagonalJetBounds.uncutPrefix A N x + A N x := by
  funext x
  exact Finset.sum_range_succ (fun j => A j x) N

theorem nonemptyPrefix_jetRate {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {U : Set D} {m : ℕ} {r : ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hzero : JetRate l q (A 0) m r)
    (hpos : ∀ j, 1 ≤ j → JetRate l q (A j) m r) (J : ℕ) :
    JetRate l q (DiagonalJetBounds.uncutPrefix A (J + 1)) m r := by
  induction J with
  | zero =>
    have he : DiagonalJetBounds.uncutPrefix A (0 + 1) = A 0 := by
      funext x
      simp [DiagonalJetBounds.uncutPrefix]
    rw [he]
    exact hzero
  | succ J ih =>
    rw [show J.succ + 1 = (J + 1) + 1 from rfl, uncutPrefix_succ]
    exact ih.add (hpos (J + 1) (by omega)) hU hlU
      (ContDiffOn.sum (fun j _ => hA j)) (hA (J + 1))

theorem prefix_background {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {g L Lzero : ℕ → ℝ} {C : ℕ → ℕ → ℝ} {U S : Set D}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hraw : CutStageEstimates.RawStageBounds q A g L C (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzero : ∀ m, JetRate l q (A 0) m (-Lzero m)) (J m : ℕ) :
    JetRate l q (DiagonalJetBounds.uncutPrefix A (J + 1)) m (-max (L m) (Lzero m)) := by
  apply nonemptyPrefix_jetRate hU hlU hA
  · exact (hzero m).weaken hq (neg_le_neg (le_max_right _ _))
  · intro j hj
    apply (raw_jetRate hraw hS hq hj m).weaken hq
    have hmax := le_max_left (L m) (Lzero m)
    have hgain := hg j hj
    linarith

end General

/-- The one derivative needed for the potential is paid independently of
the correction index. The direct field pays no curl derivative. -/
noncomputable def backgroundLoss (LA LB LAzero LBzero : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))

theorem mixed_background {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {A B : ℕ → VelocityField} {g LA LB LAzero LBzero : ℕ → ℝ}
    {CA CB : ℕ → ℕ → ℝ} {U S : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA (fun _ _ => 0) S)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzeroA : ∀ m, JetRate l q (A 0) m (-LAzero m))
    (hzeroB : ∀ m, JetRate l q (B 0) m (-LBzero m)) (J m : ℕ) :
    JetRate l q (MixedDiagonalResidual.uncutVelocity A B J) m
      (-backgroundLoss LA LB LAzero LBzero m) := by
  have hpA := prefix_background hU hlU hS hq hA hrawA hg hzeroA J (m + 1)
  have hpB := prefix_background hU hlU hS hq hB hrawB hg hzeroB J m
  have hsA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have hsB : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix B (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hB j)
  have hc := (hpA.spatialCurl hU hlU hsA).weaken hq
    (neg_le_neg (le_max_left (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))))
  have hb := hpB.weaken hq
    (neg_le_neg (le_max_right (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))))
  have hsCurl : ContDiffOn ℝ ∞
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) U := by
    intro x hx
    exact (SpatialCurl.contDiffAt_spatialCurl (hsA.contDiffAt (hU.mem_nhds hx))
      (by simp)).contDiffWithinAt
  exact hc.add hb hU hlU hsCurl hsB

/-- Stage velocity, defined pointwise by `SpatialCurl.spatialCurl (A j) x + B j x`. -/
noncomputable def stageVelocity (A B : ℕ → VelocityField) (j : ℕ) : VelocityField :=
  fun x => SpatialCurl.spatialCurl (A j) x + B j x

theorem uncutVelocity_zero (A B : ℕ → VelocityField) :
    MixedDiagonalResidual.uncutVelocity A B 0 = stageVelocity A B 0 := by
  have hA : DiagonalJetBounds.uncutPrefix A (0 + 1) = A 0 := by
    funext x
    simp [DiagonalJetBounds.uncutPrefix]
  have hB : DiagonalJetBounds.uncutPrefix B (0 + 1) = B 0 := by
    funext x
    simp [DiagonalJetBounds.uncutPrefix]
  funext x
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (0 + 1)) x +
    DiagonalJetBounds.uncutPrefix B (0 + 1) x =
    SpatialCurl.spatialCurl (A 0) x + B 0 x
  rw [hA, hB]

theorem uncutVelocity_eq_stagePrefix {U : Set SpaceTime} (hU : IsOpen U)
    (A B : ℕ → VelocityField) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A B J)
      (DiagonalJetBounds.uncutPrefix (stageVelocity A B) (J + 1)) U := by
  intro x hx
  have hcurl := PhysicalParticularWave.spatialCurl_finset_sum (Finset.range (J + 1)) A
    (fun j _ => (hA j).contDiffAt (hU.mem_nhds hx) |>.differentiableAt (by simp))
  change SpatialCurl.spatialCurl (fun w => ∑ i ∈ Finset.range (J + 1), A i w) x +
    (∑ i ∈ Finset.range (J + 1), B i x) =
    ∑ i ∈ Finset.range (J + 1), (SpatialCurl.spatialCurl (A i) x + B i x)
  rw [hcurl]
  rw [Finset.sum_add_distrib]

/-- This version only needs a bound for the initialized physical velocity.
It imposes no growth assumption on the gauge of the initial potential. -/
noncomputable def initialBackgroundLoss (Lzero LA LB : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (Lzero m) (max (LA (m + 1)) (LB m))

theorem mixed_background_from_initial {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {A B : ℕ → VelocityField} {g LA LB Lzero : ℕ → ℝ}
    {CA CB : ℕ → ℕ → ℝ} {U S : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA (fun _ _ => 0) S)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzero : ∀ m, JetRate l q (MixedDiagonalResidual.uncutVelocity A B 0) m (-Lzero m))
    (J m : ℕ) :
    JetRate l q (MixedDiagonalResidual.uncutVelocity A B J) m
      (-initialBackgroundLoss Lzero LA LB m) := by
  have hLzero : Lzero m ≤ initialBackgroundLoss Lzero LA LB m := le_max_left _ _
  have hLA : LA (m + 1) ≤ initialBackgroundLoss Lzero LA LB m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hLB : LB m ≤ initialBackgroundLoss Lzero LA LB m :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hcurl (j : ℕ) : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (A j)) U := by
    intro x hx
    exact (SpatialCurl.contDiffAt_spatialCurl ((hA j).contDiffAt (hU.mem_nhds hx))
      (by simp)).contDiffWithinAt
  have hstage (j : ℕ) : ContDiffOn ℝ ∞ (stageVelocity A B j) U :=
    (hcurl j).add (hB j)
  have hinit : JetRate l q (stageVelocity A B 0) m
      (-initialBackgroundLoss Lzero LA LB m) := by
    have hz := (hzero m).weaken hq (neg_le_neg hLzero)
    rwa [uncutVelocity_zero] at hz
  have hpos (j : ℕ) (hj : 1 ≤ j) : JetRate l q (stageVelocity A B j) m
      (-initialBackgroundLoss Lzero LA LB m) := by
    have hgain := hg j hj
    have ha := ((raw_jetRate hrawA hS hq hj (m + 1)).spatialCurl hU hlU (hA j)).weaken hq
      (show -initialBackgroundLoss Lzero LA LB m ≤ g j - LA (m + 1) by linarith)
    have hb := (raw_jetRate hrawB hS hq hj m).weaken hq
      (show -initialBackgroundLoss Lzero LA LB m ≤ g j - LB m by linarith)
    exact ha.add hb hU hlU (hcurl j) (hB j)
  exact (nonemptyPrefix_jetRate hU hlU hstage hinit hpos J).congr_on hU hlU
    (uncutVelocity_eq_stagePrefix hU A B hA J).symm

end NavierStokes.MixedFiniteBackground
