/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryPressureCosts

@[expose] public section

/-! The pressure and initial-gradient costs allow one common scale choice
with any finite collection of the other source costs. Their finite partial
sums control the actual low-bound increments. -/

noncomputable section

namespace EulerPacketPressureScale

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceScaleBounds
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketGeometryLowBounds
open scoped Topology

def goodCostSpec (CM : ℝ) (hCM : 0 ≤ CM) : CostSpec where
  d := 1
  B := 5
  N := 3
  a := 3
  b := 1
  c := 2
  C := 1+2*CM*goodRatio
  p := 0
  q := 0
  d_le_two := by norm_num
  a_nonneg := by norm_num
  a_lt_B := by norm_num
  a_le_N := by norm_num
  b_pos := zero_lt_one
  C_pos := by positivity [goodRatio_pos]

theorem goodCost_le_spec (J : ℕ) (hJ : 3 ≤ J) (CM : ℝ) (hCM : 0 ≤ CM)
    (x : ℕ → ℝ) (n : ℕ) (hx : 0 ≤ x n) :
    2*CM*goodRatio*goodCost J x n ≤ (goodCostSpec CM hCM).cost J x n := by
  have h := sourceGoodCost_bound J hJ x n hx
  have hg : 0 ≤ goodCost J x n := by unfold goodCost; positivity
  have hm := monomialCost_nonneg J 1 5 3 1 2 1 0 0 x n zero_le_one hx
  calc
    _ ≤ (1+2*CM*goodRatio)*monomialCost J 1 5 3 1 2 1 0 0 x n := by
      apply mul_le_mul (by linarith) h hg
      positivity [goodRatio_pos]
    _ = _ := by
      simp only [goodCostSpec,CostSpec.cost,monomialCost,pow_zero,mul_one,one_mul]

theorem add_series {f g : ℕ → ℝ} {a b : ℝ} (hf : SmallSeries f a) (hg : SmallSeries g b) :
    SmallSeries (fun n => f n+g n) (a+b) := by
  refine ⟨fun n => add_nonneg (hf.nonneg n) (hg.nonneg n),hf.summable.add hg.summable,?_⟩
  rw [hf.summable.tsum_add hg.summable]
  exact add_le_add hf.total_le hg.total_le

theorem finite_sum_le {f : ℕ → ℝ} {a : ℝ} (hf : SmallSeries f a) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n ≤ a :=
  (hf.summable.sum_le_tsum (Finset.range N) (fun n _ => hf.nonneg n)).trans hf.total_le

theorem upper_increment_series {J : ℕ} {Cθ CM CMn CHn c : ℝ} {x : ℕ → ℝ}
    {increment error : ℕ → ℝ} {a b e : ℝ}
    (hg : SmallSeries (fun n => 2*CM*goodRatio*goodCost J x n) a)
    (hb : SmallSeries (badCost J Cθ CM CMn CHn c x) b) (he : SmallSeries error e)
    (h0 : ∀ n, 0 ≤ increment n)
    (h : ∀ n, increment n ≤ 2*CM*goodRatio*goodCost J x n+badCost J Cθ CM CMn CHn c x n+error n) :
    SmallSeries increment (a+b+e) :=
  (add_series (add_series hg hb) he).mono h0 h

theorem initial_increment_series {J : ℕ} {Cθ CM CMn CHn c : ℝ} {x : ℕ → ℝ}
    {increment error : ℕ → ℝ} {b e : ℝ}
    (hb : SmallSeries (badCost J Cθ CM CMn CHn c x) b) (he : SmallSeries error e)
    (h0 : ∀ n, 0 ≤ increment n)
    (h : ∀ n, increment n ≤ badCost J Cθ CM CMn CHn c x n+error n) :
    SmallSeries increment (b+e) := (add_series hb he).mono h0 h

/-- The added pressure costs share the stage index and base scale with
any finite list of the existing source costs. -/
theorem uniform_choice {ι : Type*} [Fintype ι] (s : ι → CostSpec)
    (Cθ CM CMn CHn c : ℝ) (hθ : 0 ≤ Cθ) (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 → (∀ n, x (n+1)=((J+n : ℕ) : ℝ)^2*x n) →
        (∀ i, SmallSeries ((s i).cost J x) η) ∧
        SmallSeries (badCost J Cθ CM CMn CHn c x) η ∧
        SmallSeries (fun n => 2*CM*goodRatio*goodCost J x n) η := by
  let t : Sum ι Bool → CostSpec
    | .inl i => s i
    | .inr false => goodCostSpec CM hM
    | .inr true => badCostSpec Cθ CM CMn CHn c hθ hM hMn hHn
  obtain ⟨J,hJ,hchoice⟩ := finite_uniform_choice t
  refine ⟨J,hJ,?_⟩
  intro η hη
  obtain ⟨X₀,hX₀,hX⟩ := hchoice η hη
  refine ⟨X₀,hX₀,?_⟩
  intro x hx0 hx
  have hxp := quadratic_growth_one_le J (by omega) x (by linarith only [hX₀,hx0]) hx
  have hs (i : Sum ι Bool) : SmallSeries ((t i).cost J x) η := by
    have hi := hX x hx0 hx i
    refine ⟨?_,hi.1,hi.2.1⟩
    intro n
    exact monomialCost_nonneg J (t i).d (t i).B (t i).a (t i).b (t i).c (t i).C
      (t i).p (t i).q x n (t i).C_pos.le (zero_le_one.trans (hxp n))
  refine ⟨fun i => hs (.inl i),hs (.inr true),?_⟩
  apply (hs (.inr false)).mono
  · intro n
    have hg := goodRatio_pos.le
    have hc : 0 ≤ goodCost J x n := by unfold goodCost; positivity
    positivity
  · intro n
    exact goodCost_le_spec J hJ CM hM x n (zero_le_one.trans (hxp n))

/-- The same choice covers the literal initial polynomial frequency and
shear and every subsequent recursively constructed scale. -/
theorem literal_uniform_choice {ι : Type*} [Fintype ι] (s : ι → CostSpec) (D : ℕ)
    (Cθ CM CMn CHn c : ℝ) (hθ : 0 ≤ Cθ) (hM : 0 ≤ CM) (hMn : 0 ≤ CMn) (hHn : 0 ≤ CHn) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, 8 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7) ∧ X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4) ∧
      (∀ i, SmallSeries ((s i).cost J (scaleSequence J X)) η) ∧
      SmallSeries (badCost J Cθ CM CMn CHn c (scaleSequence J X)) η ∧
      SmallSeries (fun n => 2*CM*goodRatio*goodCost J (scaleSequence J X) n) η := by
  obtain ⟨J,hJ,hchoice⟩ := uniform_choice s Cθ CM CMn CHn c hθ hM hMn hHn
  refine ⟨J,hJ,?_⟩
  intro η hη
  obtain ⟨Y,hY,hy⟩ := hchoice η hη
  have hp : (0 : ℝ) < (J-1 : ℕ) := by exact_mod_cast (show 0 < J-1 by omega)
  have hevent := (eventually_pow_le_exp 1000 (show 0 < ((J-1 : ℕ) : ℝ)^7 by positivity)).and
    (eventually_pow_le_exp D (show 0 < ((J-1 : ℕ) : ℝ)^4 by positivity))
  obtain ⟨Z,hZ⟩ := eventually_atTop.1 hevent
  refine ⟨max Y Z,hY.trans (le_max_left _ _),?_⟩
  intro X hX
  have hs := hy (scaleSequence J X) ((le_max_left Y Z).trans hX) (scaleSequence_succ J X)
  have hb := hZ X ((le_max_right Y Z).trans hX)
  exact ⟨hb.1,hb.2,hs.1,hs.2.1,hs.2.2⟩

end EulerPacketPressureScale
