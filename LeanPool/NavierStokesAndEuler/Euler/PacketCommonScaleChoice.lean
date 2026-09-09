/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSeries
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleFromCosts

/-! One starting index and one final base scale suffice for the actual
geometric guards, pressure series, and any finite list of further packet
frequency comparisons. No independently chosen index is substituted. -/

@[expose] public section


noncomputable section

namespace EulerPacketCommonScaleChoice

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketSourceScaleGuards
  EulerPacketPressureScale EulerPacketGeometryLowBounds
open scoped Topology

theorem exists_common_guards {ι : Type*} [Finite ι] (s : ι → CostSpec)
    (D : ℕ) (hD : 1000 ≤ D) (C c K CM CMn CHn cP : ℝ)
    (hC : 4 ≤ C) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ η : ℝ, 0 < η → ∃ X₀ δ : ℝ,
      8 ≤ X₀ ∧ 0 < δ ∧ δ ≤ η ∧ δ ≤ 1/2 ∧
      ∀ X : ℝ, X₀ ≤ X →
        ActualBounds J D C c X δ ∧
        (∀ i, SmallSeries ((s i).cost J (scaleSequence J X)) δ) ∧
        SmallSeries (badCost J C CM CMn CHn cP (scaleSequence J X)) δ ∧
        SmallSeries (fun n => 2*CM*goodRatio*goodCost J (scaleSequence J X) n) δ ∧
        ∀ a β : ℕ → ℝ, (∀ n, 1/2 ≤ a n) → (∀ n, a n ≤ 2) →
          (∀ n, 1/2 ≤ β n*scaleSequence J X n^2) →
          (∀ n, β n*scaleSequence J X n^2 ≤ 2) →
          ∀ n, StageGuards J D C c X K a β n := by
  have hC1 : 1 ≤ C := by linarith only [hC]
  let specs : Sum SourceCost ι → CostSpec
    | .inl i => sourceCostSpec C c hC1 60 i
    | .inr i => s i
  obtain ⟨J,hJ,hchoice⟩ := literal_uniform_choice specs D C CM CMn CHn cP
    (zero_le_one.trans hC1) hCM hCMn hCHn
  refine ⟨J,hJ,?_⟩
  intro η hη
  let δ : ℝ := min η (min (1/2) (1/(1000000*K)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδK : 1000000*K*δ ≤ 1 := by
    have hh : δ ≤ 1/(1000000*K) := (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (show 0 < 1000000*K by positivity)).mp hh
    nlinarith only [hm]
  obtain ⟨Y,hY,hbounds⟩ := hchoice (δ/96) (by positivity)
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp
    ((baseErrorCost_tendsto_zero J D (by omega) hD C hC1).eventually_le_const
      (by positivity : 0 < δ/2))
  refine ⟨max Y Z,δ,hY.trans (le_max_left _ _),hδ,hδη,hδhalf,?_⟩
  intro X hX
  have hXY : Y ≤ X := (le_max_left _ _).trans hX
  have hXZ : Z ≤ X := (le_max_right _ _).trans hX
  have hX8 : 8 ≤ X := hY.trans hXY
  have hX1 : 1 ≤ X := by linarith only [hX8]
  have hb := hbounds X hXY
  have hx1 : ∀ n, 1 ≤ scaleSequence J X n := quadratic_growth_one_le J (by omega)
    (scaleSequence J X) hX1 (scaleSequence_succ J X)
  have hn : UniformBounds J C c 60 (scaleSequence J X) (δ/32) := by
    apply uniformBounds_of_costs J hJ C c (δ/32) hC1 hc (by positivity) 60
      (scaleSequence J X) hx1
    intro i
    have hi := hb.2.2.1 (Sum.inl i)
    convert hi using 1
    ring
  have ha := actualBounds_of_uniform J D hJ C c X δ hC1 hc hX1 hδ.le
    hb.1 hb.2.1 (hZ X hXZ) hn
  have hweaken : δ/96 ≤ δ := by linarith only [hδ]
  refine ⟨ha,fun i => (hb.2.2.1 (Sum.inr i)).weaken hweaken,
    hb.2.2.2.1.weaken hweaken,hb.2.2.2.2.weaken hweaken,?_⟩
  intro a β ha₁ ha₂ hβ₁ hβ₂ n
  exact stage_guards J D hJ C c X K δ hC hX8 hK hδhalf hδK ha
    a β ha₁ ha₂ hβ₁ hβ₂ n

end EulerPacketCommonScaleChoice
