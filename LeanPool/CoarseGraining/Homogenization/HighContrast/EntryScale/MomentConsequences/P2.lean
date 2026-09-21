/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Interval.Finset.Nat
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.HarmonicAndData
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.MomentConsequences.P1

/-! # P2 -/

open scoped BigOperators
open scoped Topology
open Filter

namespace Homogenization.HighContrast.EntryScale

/-- File-level typeclass cache: `Matrix` is a plain `def`, so blind instance
search for `PseudoMetrizableSpace (FullBlockMat d)` does not unfold it under
mathlib 4.33; the a.e.-measurability lemmas below need this instance directly. -/
private instance instPseudoMetrizableSpaceFullBlockMat (d : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (Homogenization.FullBlockMat d) :=
  inferInstanceAs
    (TopologicalSpace.PseudoMetrizableSpace
      (Homogenization.BlockCoord d → Homogenization.BlockCoord d → ℝ))

/--
Source label `M_m^st`: for a positive exponent, raising a finite ENNReal
maximum to that exponent commutes with the finite maximum.
-/
theorem finset_sup_rpow_of_pos {ι : Type*} (s : Finset ι) (x : ι → ENNReal)
    {q : ℝ} (hq : 0 < q) :
    (s.sup x) ^ q = s.sup (fun i => x i ^ q) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sup_empty, Finset.sup_empty]
    exact ENNReal.zero_rpow_of_pos hq
  · intro a s ha ih
    rw [Finset.sup_insert, Finset.sup_insert,
      ENNReal.max_rpow (le_of_lt hq), ih]

/--
Source label `l.union.bound`: deterministic finite-max step for `ENNReal`
integrands.
-/
theorem finset_sup_le_sum_ennreal {ι : Type*} (s : Finset ι) (x : ι → ENNReal) :
    s.sup x ≤ ∑ i ∈ s, x i := by
  refine Finset.sup_le ?_
  intro i hi
  exact Finset.single_le_sum (fun j _hj => zero_le) hi

/--
Source label `l.union.bound`: a.e. measurability of the finite maximum
appearing in the stochastic maximal union bound.
-/
theorem aemeasurable_finset_sup_ennreal
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (s : Finset ι) (X : ι → Ω → ENNReal)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
    AEMeasurable (fun ω => s.sup (fun i => X i ω)) μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      change AEMeasurable (fun _ω : Ω => (⊥ : ENNReal)) μ
      exact aemeasurable_const
  | insert a s _ha_not_mem ih =>
      have ha : AEMeasurable (X a) μ := hX a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, AEMeasurable (X i) μ := by
        intro i hi
        exact hX i (Finset.mem_insert_of_mem hi)
      have hsup : AEMeasurable (fun ω => s.sup (fun i => X i ω)) μ := ih hs
      simpa [Finset.sup_insert] using! ha.sup hsup

/--
Source label `l.union.bound`: finite-max lintegral bound, the measure-theoretic
core of the stochastic maximal union bound.
-/
theorem lintegral_finset_sup_le_sum_of_lintegral_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (s : Finset ι)
    (X : ι → Ω → ENNReal) (B : ι → ENNReal)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hB : ∀ i ∈ s, ∫⁻ ω, X i ω ∂ μ ≤ B i) :
    ∫⁻ ω, s.sup (fun i => X i ω) ∂ μ ≤ ∑ i ∈ s, B i := by
  calc
    ∫⁻ ω, s.sup (fun i => X i ω) ∂ μ
        ≤ ∫⁻ ω, ∑ i ∈ s, X i ω ∂ μ :=
      MeasureTheory.lintegral_mono fun ω =>
        finset_sup_le_sum_ennreal s fun i => X i ω
    _ = ∑ i ∈ s, ∫⁻ ω, X i ω ∂ μ :=
      MeasureTheory.lintegral_finsetSum' s hX
    _ ≤ ∑ i ∈ s, B i :=
      Finset.sum_le_sum hB

/--
Source label `l.union.bound`: weighted real-exponent finite-maximum bound.
This is the local real-`Q` replacement for the integer-moment finite-sup
pattern available in the library, with the weights kept explicit for the paper's
`3^{-\rho_M(m-j)}` factors.
-/
theorem lintegral_finset_sup_weighted_rpow_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (s : Finset ι)
    (w : ι → ENNReal) (X : ι → Ω → ENNReal) (B : ι → ENNReal) {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hX : ∀ i ∈ s, AEMeasurable (fun ω => X i ω ^ q) μ)
    (hB : ∀ i ∈ s, ∫⁻ ω, X i ω ^ q ∂ μ ≤ B i) :
    ∫⁻ ω, s.sup (fun i => (w i * X i ω) ^ q) ∂ μ ≤
      ∑ i ∈ s, w i ^ q * B i := by
  refine lintegral_finset_sup_le_sum_of_lintegral_le μ s
    (fun i ω => (w i * X i ω) ^ q)
    (fun i => w i ^ q * B i) ?_ ?_
  · intro i hi
    have hfun :
        (fun ω => (w i * X i ω) ^ q) =
          fun ω => w i ^ q * (X i ω ^ q) := by
      funext ω
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg]
    show AEMeasurable (fun ω => (w i * X i ω) ^ q) μ
    rw [hfun]
    exact (hX i hi).const_mul (w i ^ q)
  · intro i hi
    calc
      ∫⁻ ω, (w i * X i ω) ^ q ∂ μ
          = ∫⁻ ω, w i ^ q * (X i ω ^ q) ∂ μ := by
            congr 1
            ext ω
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg]
      _ = w i ^ q * ∫⁻ ω, X i ω ^ q ∂ μ :=
            MeasureTheory.lintegral_const_mul'' (w i ^ q) (hX i hi)
      _ ≤ w i ^ q * B i := mul_le_mul_right (hB i hi) (w i ^ q)

/--
Source label `l.union.bound`: weighted real-exponent finite-maximum bound
over the library's triadic descendants.  The factor `((3 ^ d) ^ n)` is exactly the
descendant count from `Homogenization.descendantsAtDepth_card`.
-/
theorem lintegral_sup_descendantsAtDepth_weighted_rpow_le_three_pow_mul
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) (n : ℕ)
    (w : Homogenization.TriadicCube d → ENNReal)
    (X : Homogenization.TriadicCube d → Ω → ENNReal) {B W : ENNReal} {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hX : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      AEMeasurable (fun ω => X R ω ^ q) μ)
    (hB : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      ∫⁻ ω, X R ω ^ q ∂ μ ≤ B)
    (hwB : ∀ R ∈ Homogenization.descendantsAtDepth Q n, w R ^ q * B ≤ W) :
    ∫⁻ ω, (Homogenization.descendantsAtDepth Q n).sup
        (fun R => (w R * X R ω) ^ q) ∂ μ ≤
      (((3 ^ d) ^ n : ℕ) : ENNReal) * W := by
  calc
    ∫⁻ ω, (Homogenization.descendantsAtDepth Q n).sup
        (fun R => (w R * X R ω) ^ q) ∂ μ
        ≤ ∑ R ∈ Homogenization.descendantsAtDepth Q n, w R ^ q * B :=
      lintegral_finset_sup_weighted_rpow_le_sum μ
        (Homogenization.descendantsAtDepth Q n) w X (fun _ => B)
        hq_nonneg hX hB
    _ ≤ ∑ R ∈ Homogenization.descendantsAtDepth Q n, W :=
      Finset.sum_le_sum hwB
    _ = (((3 ^ d) ^ n : ℕ) : ENNReal) * W := by
      simp [Homogenization.descendantsAtDepth_card Q n]

/--
Source label `l.union.bound`: one-scale descendant union estimate with the
paper's two inputs kept separate: a child high-moment bound and a deterministic
weight bound.  This is the step producing the factor
`3^{d(m-j)} 3^{-Q rho_M(m-j)} 3^{-Q gamma(j-N)}` before the convolution in
the proof.
-/
theorem lintegral_sup_descendantsAtDepth_weighted_rpow_le_card_mul_of_bounds
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) (n : ℕ)
    (w : Homogenization.TriadicCube d → ENNReal)
    (X : Homogenization.TriadicCube d → Ω → ENNReal) {B V : ENNReal} {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hX : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      AEMeasurable (fun ω => X R ω ^ q) μ)
    (hB : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      ∫⁻ ω, X R ω ^ q ∂ μ ≤ B)
    (hw : ∀ R ∈ Homogenization.descendantsAtDepth Q n, w R ^ q ≤ V) :
    ∫⁻ ω, (Homogenization.descendantsAtDepth Q n).sup
        (fun R => (w R * X R ω) ^ q) ∂ μ ≤
      (((3 ^ d) ^ n : ℕ) : ENNReal) * (V * B) := by
  refine lintegral_sup_descendantsAtDepth_weighted_rpow_le_three_pow_mul μ Q n
    w X hq_nonneg hX hB ?_
  intro R hR
  exact mul_le_mul_left (hw R hR) B

/--
Source labels `a.HM` and `l.union.bound`: high-moment-parameter version of the
one-scale descendant union estimate, using the real exponent `Q` from
Assumption `a.HM`.
-/
theorem lintegral_sup_descendantsAtDepth_weighted_highCenteredMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) (n : ℕ)
    (w : Homogenization.TriadicCube d → ENNReal)
    (X : Homogenization.TriadicCube d → Ω → ENNReal) {B V : ENNReal}
    (hX : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      AEMeasurable (fun ω => X R ω ^ hm.Q) μ)
    (hB : ∀ R ∈ Homogenization.descendantsAtDepth Q n,
      ∫⁻ ω, X R ω ^ hm.Q ∂ μ ≤ B)
    (hw : ∀ R ∈ Homogenization.descendantsAtDepth Q n, w R ^ hm.Q ≤ V) :
    ∫⁻ ω, (Homogenization.descendantsAtDepth Q n).sup
        (fun R => (w R * X R ω) ^ hm.Q) ∂ μ ≤
      (((3 ^ d) ^ n : ℕ) : ENNReal) * (V * B) :=
  lintegral_sup_descendantsAtDepth_weighted_rpow_le_card_mul_of_bounds
    μ Q n w X (le_of_lt (highCenteredMoment_Q_pos hm)) hX hB hw

/--
Source label `l.union.bound`: sum the one-scale descendant maximal estimates
over manuscript scales `j = N, ..., m`.  This is the stochastic union-bound
bridge immediately before substituting the explicit decay envelopes.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (w : ℕ → Homogenization.TriadicCube d → ENNReal)
    (X : ℕ → Homogenization.TriadicCube d → Ω → ENNReal)
    (B V : ℕ → ENNReal)
    (hX : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        AEMeasurable (fun ω => X j R ω ^ hm.Q) μ)
    (hB : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        ∫⁻ ω, X j R ω ^ hm.Q ∂ μ ≤ B j)
    (hw : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        (w j R) ^ hm.Q ≤ V j) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R => (w j R * X j R ω) ^ hm.Q)) ∂ μ ≤
      ∑ j ∈ Finset.Icc N m,
        (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) * (V j * B j) := by
  refine lintegral_finset_sup_le_sum_of_lintegral_le μ (Finset.Icc N m)
    (fun j ω => (Homogenization.descendantsAtDepth Q (m - j)).sup
      (fun R => (w j R * X j R ω) ^ hm.Q))
    (fun j => (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) * (V j * B j))
    ?_ ?_
  · intro j hj
    refine aemeasurable_finset_sup_ennreal
      (Homogenization.descendantsAtDepth Q (m - j))
      (fun R ω => (w j R * X j R ω) ^ hm.Q) ?_
    intro R hR
    have hq_nonneg : 0 ≤ hm.Q := le_of_lt (highCenteredMoment_Q_pos hm)
    have hfun :
        (fun ω => (w j R * X j R ω) ^ hm.Q) =
          fun ω => (w j R) ^ hm.Q * (X j R ω ^ hm.Q) := by
      funext ω
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg]
    show AEMeasurable (fun ω => (w j R * X j R ω) ^ hm.Q) μ
    rw [hfun]
    exact (hX j hj R hR).const_mul ((w j R) ^ hm.Q)
  · intro j hj
    exact lintegral_sup_descendantsAtDepth_weighted_highCenteredMoment_le
      hm μ Q (m - j) (w j) (X j) (hX j hj) (hB j hj) (hw j hj)

/--
the library's triadic geometry bridge used by `l.union.bound`: a descendant at depth
`m - j` of a terminal scale-`m` cube is a scale-`j` cube.
-/
theorem scale_eq_of_mem_descendantsAtDepth_terminal
    {d : ℕ} {Q R : Homogenization.TriadicCube d} {N j m : ℕ}
    (hj : j ∈ Finset.Icc N m) (hQ : Q.scale = (m : ℤ))
    (hR : R ∈ Homogenization.descendantsAtDepth Q (m - j)) :
    R.scale = (j : ℤ) := by
  have hscale := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR
  rw [hQ] at hscale
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  have hsub : (m : ℤ) - ((m - j : ℕ) : ℤ) = (j : ℤ) := by
    omega
  exact hscale.trans hsub

/--
Source labels `a.HM` and `l.union.bound`: substitute the scale-uniform
high centered-moment estimate into the scale-summed descendant union bridge.
This is still before terminal normalization losses and weak-norm envelopes are
specialized, so the deterministic weights remain an explicit input.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum_of_estimate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hQ : Q.scale = (m : ℤ))
    (w : ℕ → Homogenization.TriadicCube d → ENNReal)
    (X : ℕ → Homogenization.TriadicCube d → Ω → ENNReal)
    (hHM : HighCenteredMomentEstimate hm μ N X)
    (V : ℕ → ENNReal)
    (hw : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        (w j R) ^ hm.Q ≤ V j) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R => (w j R * X j R ω) ^ hm.Q)) ∂ μ ≤
      ∑ j ∈ Finset.Icc N m,
        (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
          (V j * highCenteredMomentEnvelope hm N j) := by
  refine lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum
    (N := N) (m := m) hm μ Q w X
    (fun j => highCenteredMomentEnvelope hm N j) V ?_ ?_ hw
  · intro j hj R hR
    exact hHM.measurable (Finset.mem_Icc.mp hj).1
      (scale_eq_of_mem_descendantsAtDepth_terminal hj hQ hR)
  · intro j hj R hR
    exact hHM.moment_le (Finset.mem_Icc.mp hj).1
      (scale_eq_of_mem_descendantsAtDepth_terminal hj hQ hR)

/--
Source labels `a.HM` and `l.union.bound`: substitute both the one-block
high-moment estimate and the deterministic terminal/weak-norm multiplier
`terminalCost * 3^{-rho_M(m-j)}` into the scale-summed descendant union bridge.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum_of_estimate_of_terminalWeak_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hQ : Q.scale = (m : ℤ))
    (w : ℕ → Homogenization.TriadicCube d → ENNReal)
    (X : ℕ → Homogenization.TriadicCube d → Ω → ENNReal)
    (hHM : HighCenteredMomentEstimate hm μ N X)
    (terminalCost : ENNReal)
    (hw : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        w j R ≤ terminalCost *
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R => (w j R * X j R ω) ^ hm.Q)) ∂ μ ≤
      ∑ j ∈ Finset.Icc N m,
        (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
          (terminalWeakMomentWeight hm terminalCost m j *
            highCenteredMomentEnvelope hm N j) := by
  refine
    lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum_of_estimate
      hm μ Q hQ w X hHM (fun j => terminalWeakMomentWeight hm terminalCost m j)
      ?_
  intro j hj R hR
  exact rpow_le_terminalWeakMomentWeight_of_le hm
    (m := m) (j := j)
    (w := fun R => w j R)
    (hw j hj R hR)

/--
Source labels `a.HM` and `l.union.bound`: full stochastic maximal lintegral
bridge through the manuscript's finite convolution envelope, still with the
terminal-normalization polynomial cost left as the explicit `terminalCost`.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_convolution_of_estimate_of_terminalWeak_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (w : ℕ → Homogenization.TriadicCube d → ENNReal)
    (X : ℕ → Homogenization.TriadicCube d → Ω → ENNReal)
    (hHM : HighCenteredMomentEstimate hm μ N X)
    (terminalCost : ENNReal)
    (hw : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        w j R ≤ terminalCost *
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R => (w j R * X j R ω) ^ hm.Q)) ∂ μ ≤
      terminalCost ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
  exact
    (lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_sum_of_estimate_of_terminalWeak_le
      hm μ Q hQ w X hHM terminalCost hw).trans
      (sum_Icc_terminalWeak_highCenteredMomentEnvelope_le_convolution
        hm terminalCost hNm)

/--
Source labels `a.HM` and `l.union.bound`: concrete full-block version of the
stochastic maximal union bound above the entry scale.  The high-moment
hypothesis is imposed on the intermediate-normalized centered full-block
deviation, while the displayed maximum uses the terminal-normalized deviation;
the deterministic comparison from `DeterministicAlgebra.lean` supplies the
factor `T = widetildeTheta_0`.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weak_terminalCenteredFullBlockDeviation_le_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (Y : ℕ → Homogenization.TriadicCube d → Ω → Homogenization.FullBlockMat d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCenteredFullBlockDeviation hP hStruct Y))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R =>
            (weak j R *
              terminalCenteredFullBlockDeviation hP hStruct m Y j R ω) ^ hm.Q)) ∂ μ ≤
      ENNReal.ofReal
          (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
  let T : ENNReal :=
    ENNReal.ofReal
      (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)
  let wTerminal : ℕ → Homogenization.TriadicCube d → ENNReal :=
    fun j R => T * weak j R
  let X : ℕ → Homogenization.TriadicCube d → Ω → ENNReal :=
    intermediateCenteredFullBlockDeviation hP hStruct Y
  have hQ_nonneg : 0 ≤ hm.Q := by
    linarith [hm.two_le_Q]
  have hpoint :
      ∀ ω,
        (Finset.Icc N m).sup
          (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
            (fun R =>
              (weak j R *
                terminalCenteredFullBlockDeviation hP hStruct m Y j R ω) ^ hm.Q)) ≤
        (Finset.Icc N m).sup
          (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
            (fun R => (wTerminal j R * X j R ω) ^ hm.Q)) := by
    intro ω
    refine Finset.sup_le ?_
    intro j hj
    refine Finset.sup_le ?_
    intro R hR
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    have hterminal :
        terminalCenteredFullBlockDeviation hP hStruct m Y j R ω ≤
          T * X j R ω := by
      simpa [T, X] using
        terminalCenteredFullBlockDeviation_le_initialWidetildeTheta_mul_intermediate_of_P4
          hP hStruct hP4 m Y hjm R ω
    have hmul :
        weak j R * terminalCenteredFullBlockDeviation hP hStruct m Y j R ω ≤
          wTerminal j R * X j R ω := by
      calc
        weak j R *
            terminalCenteredFullBlockDeviation hP hStruct m Y j R ω
            ≤ weak j R * (T * X j R ω) :=
              mul_le_mul_right hterminal (weak j R)
        _ = wTerminal j R * X j R ω := by
              simp [wTerminal, mul_assoc, mul_comm]
    have hpow := ENNReal.rpow_le_rpow hmul hQ_nonneg
    have hinner :
        (wTerminal j R * X j R ω) ^ hm.Q ≤
          (Homogenization.descendantsAtDepth Q (m - j)).sup
            (fun R => (wTerminal j R * X j R ω) ^ hm.Q) :=
      Finset.le_sup
        (s := Homogenization.descendantsAtDepth Q (m - j))
        (f := fun R => (wTerminal j R * X j R ω) ^ hm.Q) hR
    have houter :
        (Homogenization.descendantsAtDepth Q (m - j)).sup
            (fun R => (wTerminal j R * X j R ω) ^ hm.Q) ≤
          (Finset.Icc N m).sup
            (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
              (fun R => (wTerminal j R * X j R ω) ^ hm.Q)) :=
      Finset.le_sup
        (s := Finset.Icc N m)
        (f := fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R => (wTerminal j R * X j R ω) ^ hm.Q)) hj
    exact hpow.trans (hinner.trans houter)
  have hwTerminal :
      ∀ j ∈ Finset.Icc N m,
        ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
          wTerminal j R ≤ T *
            ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))) := by
    intro j hj R hR
    simpa [wTerminal] using
      mul_le_mul_right (hweak j hj R hR) T
  have hconv :=
    lintegral_sup_Icc_descendantsAtDepth_weighted_highCenteredMoment_le_convolution_of_estimate_of_terminalWeak_le
      hm μ Q hNm hQ wTerminal X hHM T hwTerminal
  calc
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R =>
            (weak j R *
              terminalCenteredFullBlockDeviation hP hStruct m Y j R ω) ^ hm.Q)) ∂ μ
        ≤ ∫⁻ ω, (Finset.Icc N m).sup
            (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
              (fun R => (wTerminal j R * X j R ω) ^ hm.Q)) ∂ μ :=
          MeasureTheory.lintegral_mono hpoint
    _ ≤ T ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := hconv
    _ =
      ENNReal.ofReal
          (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
          rfl

/--
Source labels `a.HM` and `l.union.bound`: the library's coarse-block specialization of
the terminal-normalized stochastic maximal union bound.  The high-moment
hypothesis is imposed on the concrete intermediate-normalized coarse-block
deviation from `a.HM`.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weak_terminalCoarseBlockDeviation_le_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R =>
            (weak j R *
              terminalCoarseBlockDeviation hP hStruct m a j R ω) ^ hm.Q)) ∂ μ ≤
      ENNReal.ofReal
          (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
  simpa [terminalCoarseBlockDeviation, intermediateCoarseBlockDeviation] using
    lintegral_sup_Icc_descendantsAtDepth_weak_terminalCenteredFullBlockDeviation_le_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak
      (coarseFullBlockMatrixAtCubeProcess a) hHM hweak

/--
Source labels `a.HM` and `l.union.bound`: polynomial form of the concrete
terminal coarse-block union bound.  The terminal normalization comparison gives
the manuscript polynomial exponent `A = 1`.
-/
theorem lintegral_sup_Icc_descendantsAtDepth_weak_terminalCoarseBlockDeviation_le_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R =>
            (weak j R *
              terminalCoarseBlockDeviation hP hStruct m a j R ω) ^ hm.Q)) ∂ μ ≤
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ))))) := by
  let Treal := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let envelope : ℝ :=
    hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
      (3 : ℝ) ^
        (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
          ((m - N : ℕ) : ℝ)))
  have hT : 1 ≤ Treal := by
    simpa [Treal] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hcost :
      ENNReal.ofReal Treal ≤ ENNReal.ofReal ((2 + Treal : ℝ) ^ (1 : ℝ)) :=
    ENNReal.ofReal_le_ofReal (by
      rw [Real.rpow_one]
      linarith)
  have hterminalQ :
      ENNReal.ofReal Treal ^ hm.Q ≤
        ENNReal.ofReal ((2 + Treal : ℝ) ^ ((1 : ℝ) * hm.Q)) :=
    terminalCost_rpow_le_polynomial_of_le
      (d := d) (hc := hc) hm (terminalCost := ENNReal.ofReal Treal)
      (T := Treal) (A := 1) hT hcost
  have hpoly_nonneg : 0 ≤ (2 + Treal : ℝ) ^ hm.Q := by
    have hbase_nonneg : 0 ≤ (2 + Treal : ℝ) := by linarith
    exact Real.rpow_nonneg hbase_nonneg hm.Q
  have hconv :=
    lintegral_sup_Icc_descendantsAtDepth_weak_terminalCoarseBlockDeviation_le_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak
  calc
    ∫⁻ ω, (Finset.Icc N m).sup
        (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun R =>
            (weak j R *
              terminalCoarseBlockDeviation hP hStruct m a j R ω) ^ hm.Q)) ∂ μ
        ≤ ENNReal.ofReal Treal ^ hm.Q * ENNReal.ofReal envelope := by
          simpa [Treal, envelope] using hconv
    _ ≤ ENNReal.ofReal ((2 + Treal : ℝ) ^ ((1 : ℝ) * hm.Q)) *
        ENNReal.ofReal envelope := by
          simpa [mul_comm] using
            mul_le_mul_right hterminalQ (ENNReal.ofReal envelope)
    _ = ENNReal.ofReal (((2 + Treal : ℝ) ^ hm.Q) * envelope) := by
          rw [one_mul]
          rw [← ENNReal.ofReal_mul hpoly_nonneg]
    _ =
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ))))) := by
          rfl

/--
Source label `M_m^st`: the weak-norm scale weight
`3^{-rho_M(m-j)}` from the stochastic maximal term.
-/
noncomputable def terminalStochasticWeakWeight
    {d : ℕ} (hc : HighContrastExponents d) (m : ℕ) :
    ℕ → Homogenization.TriadicCube d → ENNReal :=
  fun j _R =>
    ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))

/--
Source label `M_m^st`: the square of the inverse weak stochastic weight is
the expected positive power of the scale gap.
-/
theorem terminalStochasticWeakWeight_inv_sq_eq
    {d : ℕ} (hc : HighContrastExponents d) (m j : ℕ)
    (R : Homogenization.TriadicCube d) :
    (terminalStochasticWeakWeight (d := d) hc m j R)⁻¹ ^ 2 =
      ENNReal.ofReal
        ((3 : ℝ) ^ (2 * hc.rhoM * ((m - j : ℕ) : ℝ))) := by
  let gap : ℝ := ((m - j : ℕ) : ℝ)
  let x : ℝ := (3 : ℝ) ^ (-hc.rhoM * gap)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-hc.rhoM * gap)
  have hx_inv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hx_pos.le
  have hreal :
      x⁻¹ ^ 2 = (3 : ℝ) ^ (2 * hc.rhoM * gap) := by
    calc
      x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by
        rw [← Real.rpow_two x⁻¹, Real.inv_rpow hx_pos.le 2, Real.rpow_two]
      _ = ((3 : ℝ) ^ ((-hc.rhoM * gap) * (2 : ℝ)))⁻¹ := by
        dsimp [x]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)
          (-hc.rhoM * gap) 2]
        norm_num
      _ = (3 : ℝ) ^ (-((-hc.rhoM * gap) * (2 : ℝ))) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 : ℝ) ^ (2 * hc.rhoM * gap) := by
        congr 1
        ring
  calc
    (terminalStochasticWeakWeight (d := d) hc m j R)⁻¹ ^ 2 =
        (ENNReal.ofReal x)⁻¹ ^ 2 := by
          rfl
    _ = ENNReal.ofReal (x⁻¹ ^ 2) := by
          rw [← ENNReal.ofReal_inv_of_pos hx_pos,
            ← ENNReal.ofReal_pow hx_inv_nonneg 2]
    _ = ENNReal.ofReal
        ((3 : ℝ) ^ (2 * hc.rhoM * ((m - j : ℕ) : ℝ))) := by
          rw [hreal]

/--
Source label `M_m^st`: the unpowered ENNReal finite maximum over scales
`N <= j <= m` and the library's descendants of the terminal cube.
-/
noncomputable def terminalCoarseBlockStochasticEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (N m : ℕ) (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ENNReal :=
  fun ω => (Finset.Icc N m).sup
    (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
      (fun R =>
        weak j R *
          terminalCoarseBlockDeviation hP hStruct m a j R ω))

/--
Source label `M_m^st`: real-valued version of the terminal stochastic maximum
with a supplied weak-norm weight.  For the source weight
`terminalStochasticWeakWeight`, this is the finite maximum in the note written
with the library's descendants in place of `3^j Lat ∩ cu_m`.
-/
noncomputable def terminalCoarseBlockStochasticMaxOfWeak
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (N m : ℕ) (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ℝ :=
  fun ω =>
    (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω).toReal

/--
Source label `M_m^st`: the literal terminal stochastic maximum from the note,
using the source weak weight `3^{-rho_M(m-j)}`.
-/
noncomputable def terminalCoarseBlockStochasticMax
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ℝ :=
  terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q
    (terminalStochasticWeakWeight hc m) a

/--
Source label `M_m^st`: the ENNReal envelope appearing in the terminal
coarse-block union bound, with the `Q`-th power already inside the finite max.
-/
noncomputable def terminalCoarseBlockStochasticQEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ENNReal :=
  fun ω => (Finset.Icc N m).sup
    (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
      (fun R =>
        (weak j R *
          terminalCoarseBlockDeviation hP hStruct m a j R ω) ^ hm.Q))

private theorem measurable_terminalDeviationFunctional
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P) (j m : ℕ) :
    Measurable fun Y : Homogenization.FullBlockMat d =>
      ENNReal.ofReal
        (fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m)) := by
  refine Measurable.ennreal_ofReal ?_
  let L : Homogenization.FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (Homogenization.BlockCoord d) →L[ℝ]
        EuclideanSpace ℝ (Homogenization.BlockCoord d)) := {
    toFun := fun M =>
      Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) M
    map_add' := by
      intro A B
      exact map_add
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) A B
    map_smul' := by
      intro r A
      exact map_smul
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) r A
  }
  have hinner : Continuous fun Y : Homogenization.FullBlockMat d =>
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m := by
    dsimp [scalarCenteredFullBlockMatrixAtScale]
    fun_prop
  have hcont : Continuous fun Y : Homogenization.FullBlockMat d =>
      ‖L (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m)‖ :=
    (L.continuous_of_finiteDimensional.comp hinner).norm
  simpa [fullBlockOperatorNorm, L] using hcont.measurable
open scoped Matrix.Norms.Elementwise

/--
Source labels `M_m^st` and `l.S.and.J`: P4 integrability and stationarity give
a.e. measurability of each terminal-normalized concrete coarse-block deviation
over descendants of the terminal origin cube.
-/
theorem aemeasurable_terminalCoarseBlockDeviation_origin_descendant
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N j m : ℕ} (hj : j ∈ Finset.Icc N m)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtDepth
      (Homogenization.originCube d (m : ℤ)) (m - j)) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.RegCoeffField d => x) j R a) P := by
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  have hRscale :
      R ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d (m : ℤ)) (j : ℤ) := by
    have h := Homogenization.mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hscale :
        (Homogenization.originCube d (m : ℤ)).scale - ((m - j : ℕ) : ℤ) =
          (j : ℤ) := by
      simp only [Homogenization.originCube]
      omega
    simpa [hscale] using h
  have hOriginInt :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (j : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 j
  have hRInt :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
      hStruct.stationary (by exact_mod_cast Nat.zero_le j) (by exact_mod_cast hjm)
      hRscale hOriginInt
  have hbase :
      AEMeasurable (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R a) P :=
    hRInt.aestronglyMeasurable.aemeasurable
  have hcomp :=
    (measurable_terminalDeviationFunctional hP hStruct j m).comp_aemeasurable hbase
  simpa [terminalCoarseBlockDeviation, terminalCenteredFullBlockDeviation,
    coarseFullBlockMatrixAtCubeProcess, Function.comp_def] using! hcomp

/--
Source labels `M_m^st` and `l.S.and.J`: the source-weighted terminal ENNReal
stochastic envelope over the origin terminal cube is a.e. measurable under the
coefficient law.
-/
theorem aemeasurable_terminalCoarseBlockStochasticEnvelope_origin
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (N m : ℕ) :
    AEMeasurable
      (terminalCoarseBlockStochasticEnvelope hP hStruct N m
        (Homogenization.originCube d (m : ℤ))
        (terminalStochasticWeakWeight (d := d) hc m)
        (fun x : Homogenization.RegCoeffField d => x)) P := by
  classical
  unfold terminalCoarseBlockStochasticEnvelope
  refine aemeasurable_finset_sup_ennreal (Finset.Icc N m) _ ?_
  intro j hj
  refine aemeasurable_finset_sup_ennreal
    (Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - j))
    _ ?_
  intro R hR
  have hdev :=
    aemeasurable_terminalCoarseBlockDeviation_origin_descendant hP hStruct hP4 hj hR
  exact hdev.const_mul (terminalStochasticWeakWeight (d := d) hc m j R)

/--
Source labels `M_m^st` and `l.S.and.J`: the literal real terminal stochastic
maximum from the note is a.e. strongly measurable.  This discharges the
measurability surface needed for the Lyapunov step in the stochastic window
estimate.
-/
theorem aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (N m : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (terminalCoarseBlockStochasticMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x)) P := by
  have henv :=
    aemeasurable_terminalCoarseBlockStochasticEnvelope_origin hP hStruct hP4 hc N m
  have hreal := henv.ennreal_toReal
  unfold terminalCoarseBlockStochasticMax terminalCoarseBlockStochasticMaxOfWeak
  exact hreal.aestronglyMeasurable

theorem finset_sup_ne_top_of_forall_ne_top {ι : Type*} (s : Finset ι)
    (f : ι → ENNReal) (h : ∀ i ∈ s, f i ≠ ⊤) :
    s.sup f ≠ ⊤ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _h
    rw [Finset.sup_empty]
    exact bot_ne_top
  · intro a s ha ih h
    rw [Finset.sup_insert]
    exact max_ne_top
      (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Homogenization.HighContrast.EntryScale
