/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFiniteScaleChoice
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
A common choice of the starting stage and base scale for the concrete
coefficient, time-width, and pressure costs in the outer construction.
-/

@[expose] public section


noncomputable section


namespace EulerPacketSourceScaleChoice

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
   EulerPacketFiniteScaleChoice EulerPacketSourceScaleBounds

open scoped Topology

/-- Cost spec data, collecting `d`, `B`, `N`, `a`, `b`, `c` and their compatibility conditions. -/
structure CostSpec where
  /-- D of `CostSpec`, of type `ℕ`. -/
  d : ℕ
  /-- Bound parameter of `CostSpec`, of type `ℕ`. -/
  B : ℕ
  /-- Truncation order of `CostSpec`, of type `ℕ`. -/
  N : ℕ
  /-- A of `CostSpec`, of type `ℝ`. -/
  a : ℝ
  /-- B of `CostSpec`, of type `ℝ`. -/
  b : ℝ
  /-- C of `CostSpec`, of type `ℝ`. -/
  c : ℝ
  /-- Bound coefficient of `CostSpec`, of type `ℝ`. -/
  C : ℝ
  /-- P of `CostSpec`, of type `ℕ`. -/
  p : ℕ
  /-- Q of `CostSpec`, of type `ℕ`. -/
  q : ℕ
  d_le_two : d ≤ 2
  a_nonneg : 0 ≤ a
  a_lt_B : a < B
  a_le_N : a ≤ N
  b_pos : 0 < b
  C_pos : 0 < C

/-- Cost, given by `monomialCost J s.d s.B s.a s.b s.c s.C s.p s.q x`. -/
def CostSpec.cost (s : CostSpec) (J : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  monomialCost J s.d s.B s.a s.b s.c s.C s.p s.q x

/-- A finite list of literal exponential costs has summable, uniformly
small terms and a small total, using one fixed stage and then one base scale. -/
theorem finite_uniform_choice {ι : Type*} [Finite ι] (s : ι → CostSpec) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n+1) = ((J+n : ℕ) : ℝ)^2*x n) →
        ∀ i, Summable ((s i).cost J x) ∧
          (∑' n, (s i).cost J x n) ≤ δ ∧ ∀ n, (s i).cost J x n ≤ δ := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨J, hJ, hchoice⟩ := finite_source_uniform_small_sum_choice
    (fun i => (s i).d) (fun i => (s i).B) (fun i => (s i).N)
    (fun i => (s i).a) (fun i => (s i).b) (fun i => (s i).c)
    (fun i => log (s i).C) (fun i => ((s i).p : ℝ)) (fun i => ((s i).q : ℝ))
    (fun i => (s i).a_lt_B) (fun i => (s i).a_le_N) (fun i => (s i).b_pos)
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice δ hδ
  refine ⟨max 8 X₀, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hstart : X₀ ≤ x 0 := (le_max_right _ _).trans hx0
  have hxp := quadratic_growth_pos J (by omega) x (lt_of_lt_of_le zero_lt_one (hX₀.trans hstart)) hx
  have hdJ : (s i).d < J := lt_of_le_of_lt (s i).d_le_two (by omega)
  have hsum : Summable ((s i).cost J x) :=
    polynomial_source_scale_summable J (s i).d (s i).B hdJ x (hxp 0) hx
      (s i).a (s i).b (s i).c (s i).C (s i).p (s i).q
      (s i).a_nonneg (s i).a_lt_B (s i).b_pos (s i).C_pos
  have hbound : (∑' n, (s i).cost J x n) ≤ δ := by
    convert! hX x hstart hx i using 1
    apply tsum_congr
    intro n
    exact monomialCost_eq_exp J (s i).d (s i).B (s i).a (s i).b (s i).c (s i).C
      (s i).p (s i).q x n (by omega) (s i).C_pos (hxp n)
  refine ⟨hsum, hbound, ?_⟩
  intro n
  apply le_trans (hsum.le_tsum n ?_) hbound
  intro m hm
  exact monomialCost_nonneg J (s i).d (s i).B (s i).a (s i).b (s i).c (s i).C
    (s i).p (s i).q x m (s i).C_pos.le (hxp m).le

/-- Source cost data, collecting `elems`. -/
inductive SourceCost
  | shear | prior | neighbor | extra | width | parent | good
  deriving DecidableEq

instance : Fintype SourceCost where
  elems := {.shear, .prior, .neighbor, .extra, .width, .parent, .good}
  complete c := by cases c <;> simp

/-- Source cost spec used in packet source scale choice. -/
def sourceCostSpec (C c : ℝ) (hC : 1 ≤ C) (A : ℕ) : SourceCost → CostSpec
  | .shear => {
      d := 2, B := 9, N := 7, a := 7, b := 1/2, c := 2,
      C := 128*(2*C)^(A+1), p := 2*(A+1), q := 2*(A+1),
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .prior => {
      d := 0, B := 5, N := 4, a := 4, b := 1/4, c := 0,
      C := 16*(2*C)^A, p := 2*A, q := 2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .neighbor => {
      d := 1, B := 4, N := 4, a := 7/2, b := 1, c := 2*c,
      C := 16*(2*C)^A, p := 2*A, q := 2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .extra => {
      d := 1, B := 7, N := 5, a := 5, b := 1/2, c := 1/2,
      C := 48*(2*C)^A, p := 6+2*A, q := 2+2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .width => {
      d := 1, B := 7, N := 5, a := 5, b := 1/2, c := 1/2,
      C := 4, p := 4, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }
  | .parent => {
      d := 1, B := 7, N := 5, a := 5, b := 1, c := 2,
      C := 1, p := 0, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }
  | .good => {
      d := 1, B := 5, N := 3, a := 3, b := 1, c := 2,
      C := 1, p := 0, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }

/-- Small series data, collecting `nonneg`, `summable`, `total_le`. -/
structure SmallSeries (f : ℕ → ℝ) (δ : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ f n
  summable : Summable f
  total_le : (∑' n, f n) ≤ δ

theorem SmallSeries.term_le {f : ℕ → ℝ} {δ : ℝ} (h : SmallSeries f δ) (n : ℕ) : f n ≤ δ :=
  (h.summable.le_tsum n (fun m _ => h.nonneg m)).trans h.total_le

theorem SmallSeries.weaken {f : ℕ → ℝ} {δ η : ℝ} (h : SmallSeries f δ) (hle : δ ≤ η) :
    SmallSeries f η := ⟨h.nonneg, h.summable, h.total_le.trans hle⟩

theorem SmallSeries.mono {f g : ℕ → ℝ} {δ : ℝ} (h : SmallSeries f δ)
    (hg : ∀ n, 0 ≤ g n) (hle : ∀ n, g n ≤ f n) : SmallSeries g δ := by
  have hs := h.summable.of_nonneg_of_le hg hle
  exact ⟨hg, hs, (hs.tsum_le_tsum hle h.summable).trans h.total_le⟩

/-- Coefficient cost, given by `sourceCoefficientError J C c x n * sourceTheta J C x n^A`. -/
def coefficientCost (J : ℕ) (C c : ℝ) (A : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  sourceCoefficientError J C c x n * sourceTheta J C x n^A

/-- Extra time cost, given by `2*sqrt (a n*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J
x n * sourceTheta J C x n^A`. -/
def extraTimeCost (J : ℕ) (C : ℝ) (A : ℕ) (x a : ℕ → ℝ) (n : ℕ) : ℝ :=
  2*sqrt (a n*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J x n *
    sourceTheta J C x n^A

/-- Parent square ratio, given by `exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5)`. -/
def parentSquareRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5)

/-- Good cost, given by `exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5) * exp (x
n/((J-1+n : ℕ) : ℝ)^7)`. -/
def goodCost (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5) *
    exp (x n/((J-1+n : ℕ) : ℝ)^7)

/-- Uniform bounds data, collecting `coefficient`, `extraTime`, `width`, `parent`, `good`. -/
structure UniformBounds (J : ℕ) (C c : ℝ) (A : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop where
  coefficient : SmallSeries (coefficientCost J C c A x) δ
  extraTime : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ n, a n ≤ 2) →
    SmallSeries (extraTimeCost J C A x a) δ
  width : SmallSeries (sourceTimeRatio J x) δ
  parent : SmallSeries (parentSquareRatio J x) δ
  good : SmallSeries (goodCost J x) δ

/-- One fixed choice of the starting stage makes all the actual normal-stage
coefficient, time, shear-separation and good-interval pressure series small.
The initial scale is chosen afterwards, and every later stage is covered. -/
theorem source_uniform_choice (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n+1) = ((J+n : ℕ) : ℝ)^2*x n) → UniformBounds J C c A x δ := by
  obtain ⟨J, hJ, hchoice⟩ := finite_uniform_choice (sourceCostSpec C c hC A)
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice (δ/3) (by positivity)
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx0 hx
  have hJ1 : 1 ≤ J := by omega
  have hx1 : ∀ n, 1 ≤ x n := quadratic_growth_one_le J hJ1 x
    (by linarith only [hX₀, hx0]) hx
  have hxp : ∀ n, 0 ≤ x n := fun n => le_trans zero_le_one (hx1 n)
  let f := fun i : SourceCost => (sourceCostSpec C c hC A i).cost J x
  have hsmall (i : SourceCost) : SmallSeries (f i) (δ/3) := by
    have hh := hX x hx0 hx i
    refine ⟨?_, hh.1, hh.2.1⟩
    intro n
    exact monomialCost_nonneg J _ _ _ _ _ _ _ _ x n
      (sourceCostSpec C c hC A i).C_pos.le (hxp n)
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
    linarith only [(hsmall .shear).total_le, (hsmall .prior).total_le, (hsmall .neighbor).total_le]
  refine ⟨hsum.mono ?_ ?_, ?_, (hweak .width).mono ?_ ?_,
    (hweak .parent).mono ?_ ?_, (hweak .good).mono ?_ ?_⟩
  · intro n
    have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold coefficientCost sourceCoefficientError sourceEpsilon sourceOlderGradient
        sourcePriorError sourceNeighborError
    positivity
  · intro n
    exact sourceCoefficientError_bound J hJ C c hC hc A x hx1 n
  · intro a ha ha₂
    apply (hweak .extra).mono
    · intro n
      have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
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

/-- The sequence in (37), now constructed rather than supplied. -/
def scaleSequence (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X
  | n+1 => ((J+n : ℕ) : ℝ)^2*scaleSequence J X n

@[simp] theorem scaleSequence_zero (J : ℕ) (X : ℝ) : scaleSequence J X 0 = X := rfl

theorem scaleSequence_succ (J : ℕ) (X : ℝ) (n : ℕ) :
    scaleSequence J X (n+1) = ((J+n : ℕ) : ℝ)^2*scaleSequence J X n := rfl

/-- In particular the explicit sequence allows the same simultaneous choice;
no recurrence or asymptotic conclusion remains as an input. -/
theorem explicit_sequence_uniform_choice (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → UniformBounds J C c A (scaleSequence J X) δ := by
  obtain ⟨J, hJ, hchoice⟩ := source_uniform_choice C c hC hc A
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice δ hδ
  exact ⟨X₀, hX₀, fun X hX' => hX (scaleSequence J X) hX' (scaleSequence_succ J X)⟩

end EulerPacketSourceScaleChoice
