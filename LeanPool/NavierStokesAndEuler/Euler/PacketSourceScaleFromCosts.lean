/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual

@[expose] public section

/-! Reconstruct the numerical source guards from a supplied common
finite cost budget, without making a second choice of the starting stage. -/

noncomputable section

namespace EulerPacketSourceScaleChoice

open Real EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleSequence EulerPacketSourceScaleActual

theorem uniformBounds_of_costs (J : ℕ) (hJ : 3 ≤ J) (C c δ : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (A : ℕ)
    (x : ℕ → ℝ) (hx1 : ∀ n, 1 ≤ x n)
    (hsmall : ∀ i : SourceCost,
      SmallSeries ((sourceCostSpec C c hC A i).cost J x) (δ/3)) :
    UniformBounds J C c A x δ := by
  have hJ1 : 1 ≤ J := by omega
  have hxp : ∀ n, 0 ≤ x n := fun n => zero_le_one.trans (hx1 n)
  let f := fun i : SourceCost => (sourceCostSpec C c hC A i).cost J x
  have hweak (i : SourceCost) : SmallSeries (f i) δ :=
    (hsmall i).weaken (by linarith only [hδ])
  have hsum : SmallSeries (fun n => f .shear n+f .prior n+f .neighbor n) δ := by
    have hs := ((hsmall .shear).summable.add (hsmall .prior).summable).add (hsmall
      .neighbor).summable
    refine ⟨fun n => add_nonneg (add_nonneg ((hsmall .shear).nonneg n)
      ((hsmall .prior).nonneg n)) ((hsmall .neighbor).nonneg n), hs, ?_⟩
    rw [Summable.tsum_add ((hsmall .shear).summable.add (hsmall .prior).summable)
        (hsmall .neighbor).summable,
      Summable.tsum_add (hsmall .shear).summable (hsmall .prior).summable]
    linarith only [(hsmall .shear).total_le,(hsmall .prior).total_le,(hsmall .neighbor).total_le]
  refine ⟨hsum.mono ?_ ?_, ?_, (hweak .width).mono ?_ ?_,
    (hweak .parent).mono ?_ ?_,(hweak .good).mono ?_ ?_⟩
  · intro n
    have hθ : 0 ≤ sourceTheta J C x n := zero_le_one.trans (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold coefficientCost sourceCoefficientError sourceEpsilon sourceOlderGradient
      sourcePriorError sourceNeighborError
    positivity
  · intro n
    exact sourceCoefficientError_bound J hJ C c hC hc A x hx1 n
  · intro a ha ha₂
    apply (hweak .extra).mono
    · intro n
      have hθ : 0 ≤ sourceTheta J C x n := zero_le_one.trans (sourceTheta_bounds hJ1 hC hx1 n).1
      unfold extraTimeCost sourceNextTimeWidth
      positivity
    · intro n
      exact sourceExtraTime_bound J hJ1 C hC A x hx1 n (a n) (ha n) (ha₂ n)
  · intro n
    unfold sourceTimeRatio
    positivity
  · intro n
    exact sourceTimeRatio_bound J hJ1 x n
  · intro n
    unfold parentSquareRatio
    positivity
  · intro n
    exact (sourceParentSquareRatio_eq J x n).le
  · intro n
    unfold goodCost
    positivity
  · intro n
    exact sourceGoodCost_bound J hJ x n (hxp n)

theorem actualBounds_of_uniform (J D : ℕ) (hJ : 3 ≤ J) (C c X δ : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (hX : 1 ≤ X) (hδ : 0 ≤ δ)
    (hbaseH : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7))
    (hbaseK : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4))
    (hbase : baseErrorCost J D C X ≤ δ/2)
    (hn : UniformBounds J C c 60 (scaleSequence J X) (δ/32)) :
    ActualBounds J D C c X δ := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw : δ/32 ≤ δ := by linarith only [hδ]
  refine ⟨⟨hn.coefficient.weaken hw,fun a ha ha₂ => (hn.extraTime a ha ha₂).weaken hw,
    hn.width.weaken hw,hn.parent.weaken hw,hn.good.weaken hw⟩,hbaseH,hbaseK,?_⟩
  intro a ha ha₂
  let f : ℕ → ℝ := fun n => 16*coefficientCost J C c 60 (scaleSequence J X) n
  let z : ℕ → ℝ := fun n => if n=0 then baseErrorCost J D C X else 0
  have hf : SmallSeries f (δ/2) := by
    refine ⟨fun n => mul_nonneg (by norm_num) (hn.coefficient.nonneg n),
      hn.coefficient.summable.mul_left 16,?_⟩
    change (∑' n,16*coefficientCost J C c 60 (scaleSequence J X) n) ≤ δ/2
    rw [tsum_mul_left]
    nlinarith only [hn.coefficient.total_le]
  have hz : SmallSeries z (δ/2) := by
    refine ⟨?_,(hasSum_ite_eq 0 (baseErrorCost J D C X)).summable,?_⟩
    · intro n
      exact ite_nonneg (baseErrorCost_nonneg J D C X (zero_le_one.trans hC) hXp.le) le_rfl
    · change (∑' n : ℕ,if n=0 then baseErrorCost J D C X else 0) ≤ δ/2
      rw [tsum_ite_eq]
      exact hbase
  have hsum : SmallSeries (fun n => f n+z n) δ := by
    refine ⟨fun n => add_nonneg (hf.nonneg n) (hz.nonneg n),hf.summable.add hz.summable,?_⟩
    rw [hf.summable.tsum_add hz.summable]
    linarith only [hf.total_le,hz.total_le]
  apply hsum.mono
  · intro n
    unfold geometryErrorCost
    exact mul_nonneg (geometryError_nonneg J D C c X a n (zero_le_one.trans hC) hXp)
      (pow_nonneg (by unfold sourceTheta; positivity) 60)
  · intro n
    exact geometryErrorCost_bound J D hJ C c X hC hX hc a ha ha₂ hbaseH hbaseK n

end EulerPacketSourceScaleChoice
