/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.TransferIdentity
public import LeanPool.BeyondBethe.BeyondBethe.SourceVontobel
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic

/-! # Optimizer -/

@[expose] public section

open scoped BigOperators Topology

namespace BeyondBethe

noncomputable section

/-- The barycenter of the Birkhoff polytope. -/
noncomputable def uniformBirkhoff (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ ↦ 1 / n

theorem uniformBirkhoff_doublyStochastic
    {n : ℕ} (hn : 0 < n) :
    IsDoublyStochastic (uniformBirkhoff n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
  · intro i
    simp [uniformBirkhoff, hn.ne']
  · intro j
    simp [uniformBirkhoff, hn.ne']

theorem uniformBirkhoff_interior
    {n : ℕ} (hn : 1 < n) :
    ∀ i, IsInteriorProbabilityVector (uniformBirkhoff n i) := by
  intro i
  have hn0 : 0 < n := by omega
  refine ⟨(uniformBirkhoff_doublyStochastic hn0).row_probability i, ?_⟩
  intro j
  constructor
  · exact div_pos (by norm_num) (by exact_mod_cast hn0)
  · rw [uniformBirkhoff]
    exact (div_lt_one (by exact_mod_cast hn0)).2 (by exact_mod_cast hn)

/-- The Birkhoff polytope is closed in the finite matrix space. -/
theorem isClosed_doublyStochastic
    {n : Type*} [Fintype n] :
    IsClosed {X : Matrix n n ℝ | IsDoublyStochastic X} := by
  have hnonneg : IsClosed
      {X : Matrix n n ℝ | ∀ i j, 0 ≤ X i j} := by
    simp only [show {X : Matrix n n ℝ | ∀ i j, 0 ≤ X i j} =
        ⋂ i, ⋂ j, {X | 0 ≤ X i j} by ext X; simp]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_le continuous_const (continuous_apply_apply i j)
  have hrow : IsClosed
      {X : Matrix n n ℝ | ∀ i, ∑ j, X i j = 1} := by
    simp only [show {X : Matrix n n ℝ | ∀ i, ∑ j, X i j = 1} =
        ⋂ i, {X | ∑ j, X i j = 1} by ext X; simp]
    exact isClosed_iInter fun i ↦ isClosed_eq
      (continuous_finsetSum Finset.univ fun j _ ↦
        continuous_apply_apply i j) continuous_const
  have hcol : IsClosed
      {X : Matrix n n ℝ | ∀ j, ∑ i, X i j = 1} := by
    simp only [show {X : Matrix n n ℝ | ∀ j, ∑ i, X i j = 1} =
        ⋂ j, {X | ∑ i, X i j = 1} by ext X; simp]
    exact isClosed_iInter fun j ↦ isClosed_eq
      (continuous_finsetSum Finset.univ fun i _ ↦
        continuous_apply_apply i j) continuous_const
  simpa [IsDoublyStochastic, Matrix.Nonnegative, Set.setOf_and] using
    hnonneg.inter (hrow.inter hcol)

/-- The Birkhoff polytope is compact. -/
theorem isCompact_doublyStochastic
    {n : Type*} [Fintype n] [DecidableEq n] :
    IsCompact {X : Matrix n n ℝ | IsDoublyStochastic X} := by
  let box : Set (Matrix n n ℝ) :=
    Set.univ.pi fun _i ↦ Set.univ.pi fun _j ↦ Set.Icc 0 1
  have hbox : IsCompact box :=
    isCompact_univ_pi fun _i ↦ isCompact_univ_pi fun _j ↦ isCompact_Icc
  apply hbox.of_isClosed_subset isClosed_doublyStochastic
  intro X hX i _ j _
  exact ⟨hX.nonnegative i j, hX.entry_le_one i j⟩

theorem regularizedBetheCoordinate_eq_continuousForm
    (τ a x : ℝ) :
    regularizedBetheCoordinate τ a x =
      x * Real.log a + (1 + τ) * Real.negMulLog x -
        Real.negMulLog (1 - x) := by
  rw [regularizedBetheCoordinate, Real.negMulLog_def]
  ring

/-- For a positive matrix the regularized objective is continuous even at
the boundary; `negMulLog` supplies the continuous extension at zero. -/
theorem continuous_regularizedBetheObjective
    {n : Type*} [Fintype n]
    (τ : ℝ) (A : Matrix n n ℝ) :
    Continuous (regularizedBetheObjective τ A) := by
  rw [show regularizedBetheObjective τ A = fun X ↦
      ∑ i, ∑ j, regularizedBetheCoordinate τ (A i j) (X i j) by
    funext X
    exact regularizedBetheObjective_eq_sum_coordinates τ A X]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  simp_rw [regularizedBetheCoordinate_eq_continuousForm]
  fun_prop

/-- A regularized maximizer exists on the Birkhoff polytope. -/
theorem exists_regularizedBetheMaximizer
    {n : ℕ} (τ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ X, IsDoublyStochastic X ∧
      ∀ Y, IsDoublyStochastic Y →
        regularizedBetheObjective τ A Y ≤
          regularizedBetheObjective τ A X := by
  have hne : ({X : Matrix (Fin n) (Fin n) ℝ |
      IsDoublyStochastic X} : Set _).Nonempty := by
    let I : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ if i = j then 1 else 0
    refine ⟨I, ?_⟩
    refine ⟨(fun i j ↦ by by_cases h : i = j <;> simp [I, h]), ?_, ?_⟩
    · intro i
      simp [I]
    · intro j
      simp [I]
  obtain ⟨X, hX, hmax⟩ := isCompact_doublyStochastic.exists_isMaxOn
    hne (continuous_regularizedBetheObjective τ A).continuousOn
  exact ⟨X, hX, fun Y hY ↦ hmax hY⟩

/-- Affine interpolation of two matrices. -/
def matrixSegment
    {n : Type*} (t : ℝ) (X Y : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j ↦ (1 - t) * X i j + t * Y i j

theorem matrixSegment_doublyStochastic
    {n : Type*} [Fintype n]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    {X Y : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y) :
    IsDoublyStochastic (matrixSegment t X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht₁) (hX.nonnegative i j))
      (mul_nonneg ht₀ (hY.nonnegative i j))
  · intro i
    simp_rw [matrixSegment, Finset.sum_add_distrib,
      ← Finset.mul_sum, hX.row_sum, hY.row_sum]
    ring
  · intro j
    simp_rw [matrixSegment, Finset.sum_add_distrib,
      ← Finset.mul_sum, hX.col_sum, hY.col_sum]
    ring

theorem negMulLog_segment_gap_nonneg
    {t x y : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ Real.negMulLog ((1 - t) * x + t * y) -
      ((1 - t) * Real.negMulLog x + t * Real.negMulLog y) := by
  have hconc := Real.concaveOn_negMulLog.2 hx hy
    (sub_nonneg.mpr ht₁) ht₀ (by ring : (1 - t) + t = 1)
  simpa [smul_eq_mul] using sub_nonneg.mpr hconc

theorem negMulLog_segment_gap_zero
    (t y : ℝ) :
    Real.negMulLog ((1 - t) * 0 + t * y) -
        ((1 - t) * Real.negMulLog 0 + t * Real.negMulLog y) =
      y * Real.negMulLog t := by
  rw [Real.negMulLog_zero]
  simp only [mul_zero, zero_add]
  rw [Real.negMulLog_mul]
  ring

/-- Quantitative entropy barrier at a zero coordinate.  Besides ordinary
concavity, mixing with the uniform matrix gains one copy of
`negMulLog t / n` from the chosen zero entry. -/
theorem totalRowEntropy_matrixSegment_uniform_bonus
    {n : ℕ} (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsDoublyStochastic X)
    {i₀ j₀ : Fin n} (hzero : X i₀ j₀ = 0)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1 - t) * totalRowEntropy X +
        t * totalRowEntropy (uniformBirkhoff n) +
        (1 / n) * Real.negMulLog t ≤
      totalRowEntropy (matrixSegment t X (uniformBirkhoff n)) := by
  let gap : Fin n → Fin n → ℝ := fun i j ↦
    Real.negMulLog (matrixSegment t X (uniformBirkhoff n) i j) -
      ((1 - t) * Real.negMulLog (X i j) +
        t * Real.negMulLog (uniformBirkhoff n i j))
  have hgap : ∀ i j, 0 ≤ gap i j := by
    intro i j
    exact negMulLog_segment_gap_nonneg ht₀ ht₁
      (hX.nonnegative i j)
      ((uniformBirkhoff_doublyStochastic hn).nonnegative i j)
  have hspecial : gap i₀ j₀ = (1 / n) * Real.negMulLog t := by
    dsimp [gap]
    rw [matrixSegment, hzero]
    calc
      Real.negMulLog ((1 - t) * 0 +
            t * uniformBirkhoff n i₀ j₀) -
          ((1 - t) * Real.negMulLog 0 +
            t * Real.negMulLog (uniformBirkhoff n i₀ j₀)) =
          uniformBirkhoff n i₀ j₀ * Real.negMulLog t :=
        negMulLog_segment_gap_zero t (uniformBirkhoff n i₀ j₀)
      _ = (1 / n) * Real.negMulLog t := by rfl
  have hrow : gap i₀ j₀ ≤ ∑ j, gap i₀ j :=
    Finset.single_le_sum (fun j _ ↦ hgap i₀ j) (Finset.mem_univ j₀)
  have hall : (∑ j, gap i₀ j) ≤ ∑ i, ∑ j, gap i j :=
    Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hgap i j)
      (Finset.mem_univ i₀)
  rw [hspecial] at hrow
  have hbonus := hrow.trans hall
  simp_rw [gap, totalRowEntropy, shannonEntropy,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hbonus ⊢
  simp_rw [matrixSegment] at hbonus ⊢
  linarith

theorem negMulLog_exp_neg (K : ℝ) :
    Real.negMulLog (Real.exp (-K)) = Real.exp (-K) * K := by
  change -Real.exp (-K) * Real.log (Real.exp (-K)) = _
  rw [Real.log_exp]
  ring

/-- Concavity of the Bethe objective plus the quantitative entropy barrier
rules out every zero coordinate of a regularized maximizer.  This proof
avoids coordinatewise asymptotic `O(t)` bookkeeping. -/
theorem regularizedBetheMaximizer_positive
    {n : ℕ} (hn : 1 < n)
    {τ : ℝ} (hτ : 0 < τ)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X) :
    ∀ i j, 0 < X i j := by
  have hn0 : 0 < n := by omega
  let W := uniformBirkhoff n
  have hW : IsDoublyStochastic W := uniformBirkhoff_doublyStochastic hn0
  intro i₀ j₀
  by_contra hnot
  have hzero : X i₀ j₀ = 0 :=
    le_antisymm (le_of_not_gt hnot) (hX.nonnegative i₀ j₀)
  let d := regularizedBetheObjective τ A X -
    regularizedBetheObjective τ A W
  let K := (n : ℝ) / τ * (|d| + 1)
  let t := Real.exp (-K)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (div_pos hnR hτ) (by positivity)
  have ht₀ : 0 < t := by
    dsimp [t]
    positivity
  have ht₁ : t < 1 := by
    dsimp [t]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos hK)
  let Z := matrixSegment t X W
  have hZ : IsDoublyStochastic Z :=
    matrixSegment_doublyStochastic ht₀.le ht₁.le hX hW
  have hentropy :
      (1 - t) * totalRowEntropy X + t * totalRowEntropy W +
          (1 / n) * Real.negMulLog t ≤ totalRowEntropy Z := by
    exact totalRowEntropy_matrixSegment_uniform_bonus hn0 hX hzero
      ht₀.le ht₁.le
  have hbeta :
      (1 - t) * betheObjective A X + t * betheObjective A W ≤
        betheObjective A Z := by
    have hc := betheObjective_segment_lower
      (ι := Fin n) (by simpa using hn) A X W hX hW ht₀.le ht₁.le
    have hseg : betheMatrixSegment t X W = Z := by
      ext i j
      simp [Z, matrixSegment, betheMatrixSegment, probabilitySegment]
    rw [← hseg]
    exact hc
  have hscale :
      τ * ((1 / n) * Real.negMulLog t) = t * (|d| + 1) := by
    rw [show Real.negMulLog t = t * K by
      simpa [t] using negMulLog_exp_neg K]
    dsimp [K]
    field_simp [hτ.ne', hnR.ne']
  have hgain :
      0 < t * (regularizedBetheObjective τ A W -
          regularizedBetheObjective τ A X) +
        τ * ((1 / n) * Real.negMulLog t) := by
    rw [hscale]
    have hd : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A W = d := by rfl
    have habs : d ≤ |d| := le_abs_self d
    rw [← hd] at habs
    have hbracket : 0 <
        (regularizedBetheObjective τ A W -
          regularizedBetheObjective τ A X) + (|d| + 1) := by
      linarith
    nlinarith [mul_pos ht₀ hbracket]
  have hbetter : regularizedBetheObjective τ A X <
      regularizedBetheObjective τ A Z := by
    have hentropyτ := mul_le_mul_of_nonneg_left hentropy hτ.le
    rw [regularizedBetheObjective, regularizedBetheObjective] at hgain
    rw [regularizedBetheObjective, regularizedBetheObjective]
    nlinarith
  exact (not_lt_of_ge (hmax Z hZ)) hbetter

theorem regularizedBetheMaximizer_interior
    {n : ℕ} (hn : 1 < n)
    {τ : ℝ} (hτ : 0 < τ)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X) :
    ∀ i, IsInteriorProbabilityVector (X i) := by
  have hpos := regularizedBetheMaximizer_positive hn hτ hA hX hmax
  intro i
  exact ⟨hX.row_probability i, fun j ↦
    ⟨hpos i j,
      hX.entry_lt_one_of_positive hpos (by simpa using hn) i j⟩⟩

/-- Coordinate derivative of the regularized Bethe objective. -/
noncomputable def regularizedBetheGradient
    {n : Type*} (τ : ℝ) (A X : Matrix n n ℝ) (i j : n) : ℝ :=
  Real.log (A i j) - (1 + τ) * Real.log (X i j) -
    Real.log (1 - X i j) - (2 + τ)

theorem hasDerivAt_regularizedBetheCoordinate
    {τ a x : ℝ} (hx₀ : x ≠ 0) (hx₁ : 1 - x ≠ 0) :
    HasDerivAt (regularizedBetheCoordinate τ a)
      (Real.log a - (1 + τ) * Real.log x -
        Real.log (1 - x) - (2 + τ)) x := by
  have hlinear : HasDerivAt (fun y : ℝ ↦ y * Real.log a)
      (Real.log a) x := by
    convert! (hasDerivAt_id x).mul_const (Real.log a) using 1 <;> simp
  have hentropy : HasDerivAt
      (fun y : ℝ ↦ (1 + τ) * Real.negMulLog y)
      ((1 + τ) * (-Real.log x - 1)) x := by
    convert! (Real.hasDerivAt_negMulLog hx₀).const_mul (1 + τ) using 1
  have hcomplementInner : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    convert! (hasDerivAt_neg' x).const_add 1 using 1
  have hcomplement : HasDerivAt
      (fun y : ℝ ↦ Real.negMulLog (1 - y))
      ((-Real.log (1 - x) - 1) * (-1)) x := by
    convert! (Real.hasDerivAt_negMulLog hx₁).comp x hcomplementInner using 1
  rw [show regularizedBetheCoordinate τ a = fun y ↦
      y * Real.log a + (1 + τ) * Real.negMulLog y -
        Real.negMulLog (1 - y) by
    funext y
    exact regularizedBetheCoordinate_eq_continuousForm τ a y]
  convert! (hlinear.add hentropy).sub hcomplement using 1 <;> ring

/-- An affine perturbation in a matrix direction. -/
def linearMatrixPerturb
    {n : Type*} (X D : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ :=
  fun i j ↦ X i j + t * D i j

theorem hasDerivAt_regularizedBetheObjective_line
    {n : Type*} [Fintype n]
    {τ : ℝ} {A X D : Matrix n n ℝ}
    (hXint : ∀ i, IsInteriorProbabilityVector (X i)) :
    HasDerivAt
      (fun t ↦ regularizedBetheObjective τ A
        (linearMatrixPerturb X D t))
      (∑ i, ∑ j, regularizedBetheGradient τ A X i j * D i j) 0 := by
  rw [show (fun t ↦ regularizedBetheObjective τ A
      (linearMatrixPerturb X D t)) = fun t ↦
        ∑ i, ∑ j, regularizedBetheCoordinate τ (A i j)
          (linearMatrixPerturb X D t i j) by
    funext t
    exact regularizedBetheObjective_eq_sum_coordinates τ A _]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hcoord := hasDerivAt_regularizedBetheCoordinate (τ := τ) (a := A i j)
    ((hXint i).2 j).1.ne'
    (sub_pos.mpr ((hXint i).2 j).2).ne'
  have hinner : HasDerivAt (fun t : ℝ ↦ X i j + t * D i j)
      (D i j) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (X i j)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (D i j)) using 1 <;> simp
  have hcoord' : HasDerivAt (regularizedBetheCoordinate τ (A i j))
      (Real.log (A i j) - (1 + τ) * Real.log (X i j) -
        Real.log (1 - X i j) - (2 + τ))
      ((fun t : ℝ ↦ X i j + t * D i j) 0) := by
    convert! hcoord using 1 <;> simp
  convert! hcoord'.comp 0 hinner using 1 <;>
    simp [linearMatrixPerturb, regularizedBetheGradient] <;> ring

/-- A strictly positive finite matrix remains nonnegative under all
sufficiently small affine perturbations. -/
theorem eventually_linearMatrixPerturb_nonnegative
    {n : Type*} [Fintype n]
    {X D : Matrix n n ℝ} (hXpos : ∀ i j, 0 < X i j) :
    ∀ᶠ t in 𝓝 (0 : ℝ), Matrix.Nonnegative (linearMatrixPerturb X D t) := by
  classical
  have hone : ∀ p : n × n,
      ∀ᶠ t in 𝓝 (0 : ℝ), 0 < linearMatrixPerturb X D t p.1 p.2 := by
    intro p
    have hcont : ContinuousAt
        (fun t : ℝ ↦ linearMatrixPerturb X D t p.1 p.2) 0 := by
      simp only [linearMatrixPerturb]
      fun_prop
    exact hcont.tendsto.eventually (Ioi_mem_nhds (by
      simpa [linearMatrixPerturb] using hXpos p.1 p.2))
  have hfin : ∀ s : Finset (n × n),
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p ∈ s,
        0 < linearMatrixPerturb X D t p.1 p.2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        filter_upwards [hone p, ih] with t hpt hst
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hpt
        · exact hst q hq
  filter_upwards [hfin Finset.univ] with t ht i j
  exact (ht (i, j) (Finset.mem_univ _)).le

theorem linearMatrixPerturb_doublyStochastic
    {n : Type*} [Fintype n]
    {X D : Matrix n n ℝ} {t : ℝ}
    (hX : IsDoublyStochastic X)
    (hDrow : ∀ i, ∑ j, D i j = 0)
    (hDcol : ∀ j, ∑ i, D i j = 0)
    (hnonneg : Matrix.Nonnegative (linearMatrixPerturb X D t)) :
    IsDoublyStochastic (linearMatrixPerturb X D t) := by
  refine ⟨hnonneg, ?_, ?_⟩
  · intro i
    simp_rw [linearMatrixPerturb, Finset.sum_add_distrib, ← Finset.mul_sum,
      hX.row_sum, hDrow]
    ring
  · intro j
    simp_rw [linearMatrixPerturb, Finset.sum_add_distrib, ← Finset.mul_sum,
      hX.col_sum, hDcol]
    ring

/-- First-order optimality on the tangent space of the Birkhoff polytope. -/
theorem regularizedBetheMaximizer_tangent_orthogonal
    {n : Type*} [Fintype n]
    {τ : ℝ} {A X D : Matrix n n ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X)
    (hDrow : ∀ i, ∑ j, D i j = 0)
    (hDcol : ∀ j, ∑ i, D i j = 0) :
    ∑ i, ∑ j, regularizedBetheGradient τ A X i j * D i j = 0 := by
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hfeasible : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsDoublyStochastic (linearMatrixPerturb X D t) :=
    (eventually_linearMatrixPerturb_nonnegative hXpos).mono fun _ ht ↦
      linearMatrixPerturb_doublyStochastic hX hDrow hDcol ht
  have hlocal : IsLocalMax
      (fun t ↦ regularizedBetheObjective τ A
        (linearMatrixPerturb X D t)) 0 :=
    hfeasible.mono fun t ht ↦ by
      have hzeroPerturb : linearMatrixPerturb X D 0 = X := by
        ext i j
        simp [linearMatrixPerturb]
      change regularizedBetheObjective τ A (linearMatrixPerturb X D t) ≤
        regularizedBetheObjective τ A (linearMatrixPerturb X D 0)
      rw [hzeroPerturb]
      exact hmax _ ht
  exact hlocal.hasDerivAt_eq_zero
    (hasDerivAt_regularizedBetheObjective_line hXint)

/-- Signed difference of two coordinate atoms. -/
def signedPair
    {ι : Type*} [DecidableEq ι] (a b : ι) (x : ι) : ℝ :=
  (if a = x then 1 else 0) - (if b = x then 1 else 0)

theorem sum_signedPair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) :
    ∑ x, signedPair a b x = 0 := by
  simp [signedPair, Finset.sum_sub_distrib]

theorem sum_signedPair_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (q : ι → ℝ) :
    ∑ x, signedPair a b x * q x = q a - q b := by
  simp [signedPair, sub_mul, Finset.sum_sub_distrib]

/-- The elementary four-cycle direction in the tangent space of the
Birkhoff polytope. -/
def rectangleDirection
    {ι : Type*} [DecidableEq ι]
    (i k j l : ι) : Matrix ι ι ℝ :=
  fun a b ↦ signedPair i k a * signedPair j l b

theorem rectangleDirection_row_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i k j l : ι} (hjl : j ≠ l) :
    ∀ a, ∑ b, rectangleDirection i k j l a b = 0 := by
  intro a
  rw [show (∑ b, rectangleDirection i k j l a b) =
      signedPair i k a * ∑ b, signedPair j l b by
    simp_rw [rectangleDirection, Finset.mul_sum]]
  rw [sum_signedPair hjl, mul_zero]

theorem rectangleDirection_col_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i k j l : ι} (hik : i ≠ k) :
    ∀ b, ∑ a, rectangleDirection i k j l a b = 0 := by
  intro b
  rw [show (∑ a, rectangleDirection i k j l a b) =
      (∑ a, signedPair i k a) * signedPair j l b by
    simp_rw [rectangleDirection, Finset.sum_mul]]
  rw [sum_signedPair hik, zero_mul]

theorem sum_mul_rectangleDirection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) {i k j l : ι}
    (hik : i ≠ k) (hjl : j ≠ l) :
    (∑ a, ∑ b, G a b * rectangleDirection i k j l a b) =
      G i j - G i l - G k j + G k l := by
  have hinner : ∀ a,
      (∑ b, G a b * rectangleDirection i k j l a b) =
        signedPair i k a * (G a j - G a l) := by
    intro a
    calc
      (∑ b, G a b * rectangleDirection i k j l a b) =
          signedPair i k a *
            ∑ b, signedPair j l b * G a b := by
        simp_rw [rectangleDirection]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = signedPair i k a * (G a j - G a l) := by
        rw [sum_signedPair_mul hjl]
  simp_rw [hinner]
  rw [sum_signedPair_mul hik]
  ring

/-- The gradient at an interior maximizer has vanishing alternating sum on
every four-cycle. -/
theorem regularizedGradient_rectangle_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {A X : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X)
    {i k j l : ι} (hik : i ≠ k) (hjl : j ≠ l) :
    regularizedBetheGradient τ A X i j -
        regularizedBetheGradient τ A X i l -
        regularizedBetheGradient τ A X k j +
        regularizedBetheGradient τ A X k l = 0 := by
  have htangent := regularizedBetheMaximizer_tangent_orthogonal
    hX hXint hmax
    (rectangleDirection_row_sum hjl)
    (rectangleDirection_col_sum hik)
  rw [sum_mul_rectangleDirection (regularizedBetheGradient τ A X) hik hjl] at htangent
  exact htangent

/-- Any matrix with zero alternating sum on every rectangle is a sum of a
row potential and a column potential. -/
theorem exists_rowColumnPotentials_of_rectangle_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G : Matrix ι ι ℝ)
    (hrect : ∀ {i k j l : ι}, i ≠ k → j ≠ l →
      G i j - G i l - G k j + G k l = 0) :
    ∃ r c : ι → ℝ, ∀ i j, G i j = r i + c j := by
  let i₀ : ι := Classical.choice inferInstance
  let j₀ : ι := Classical.choice inferInstance
  let r : ι → ℝ := fun i ↦ G i j₀
  let c : ι → ℝ := fun j ↦ G i₀ j - G i₀ j₀
  refine ⟨r, c, ?_⟩
  intro i j
  by_cases hi : i = i₀
  · subst i
    simp [r, c]
  by_cases hj : j = j₀
  · subst j
    simp [r, c]
  have h := hrect hi hj
  dsimp [r, c]
  linarith

/-- The logarithmic KKT factorization in paper Lemma 14. -/
theorem exists_logKKT_of_regularizedBetheMaximizer
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {τ : ℝ} {A X : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X) :
    ∃ r c : ι → ℝ, HasLogKKT τ A X r c := by
  obtain ⟨R, C, hRC⟩ := exists_rowColumnPotentials_of_rectangle_identity
    (fun i j ↦ regularizedBetheGradient τ A X i j)
    (fun hik hjl ↦ regularizedGradient_rectangle_identity
      hX hXint hmax hik hjl)
  let r : ι → ℝ := fun i ↦ R i + (2 + τ)
  refine ⟨r, C, ?_⟩
  intro i j
  have h := hRC i j
  dsimp [regularizedBetheGradient, r] at h ⊢
  linarith

theorem positiveMatrix_hasPerfectMatching
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : Matrix.Positive A) :
    Matrix.HasPerfectMatching A := by
  refine ⟨Equiv.refl ι, ?_⟩
  intro i
  exact (hA i i).ne'

/-- A regularized maximizer is within the entropy-regularization budget of
the variational Bethe value.  This proof uses the supremum definition and
does not assume that a separate unregularized maximizer has already been
chosen. -/
theorem betheLogValue_le_regularizedMaximizer
    {n : ℕ} (hn : 1 < n)
    {τ : ℝ} (hτ : 0 ≤ τ)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤
        regularizedBetheObjective τ A X) :
    betheLogValue A ≤ betheObjective A X +
      τ * (n * Real.log n) := by
  let W := uniformBirkhoff n
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hW : IsDoublyStochastic W := uniformBirkhoff_doublyStochastic hn0
  have hsetNonempty :
      ({v : ℝ | ∃ Y, BetheAdmissible A Y ∧
        betheObjective A Y = v} : Set ℝ).Nonempty := by
    refine ⟨betheObjective A W, W, ?_, rfl⟩
    exact ⟨hW, fun i j hzero ↦ False.elim ((hA i j).ne' hzero)⟩
  rw [betheLogValue]
  apply csSup_le hsetNonempty
  intro v hv
  obtain ⟨Y, hY, rfl⟩ := hv
  have hnear := regularized_near_bethe hτ A X Y hX hY.1 (hmax Y hY.1)
  simpa using hnear

/-- Every feasible value is bounded above by the variational Bethe value.
For positive matrices the support condition in `BetheAdmissible` is
automatic.  Compactness supplies a finite upper bound for the supremum. -/
theorem betheObjective_le_betheLogValue_of_positive
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A) (hX : IsDoublyStochastic X) :
    betheObjective A X ≤ betheLogValue A := by
  obtain ⟨M, hM, hmax⟩ := exists_regularizedBetheMaximizer 0 A
  have hmax' : ∀ Y, IsDoublyStochastic Y →
      betheObjective A Y ≤ betheObjective A M := by
    intro Y hY
    simpa [regularizedBetheObjective] using hmax Y hY
  have hbdd : BddAbove
      {v : ℝ | ∃ Y, BetheAdmissible A Y ∧ betheObjective A Y = v} := by
    refine ⟨betheObjective A M, ?_⟩
    rintro v ⟨Y, hY, rfl⟩
    exact hmax' Y hY.1
  rw [betheLogValue]
  apply le_csSup hbdd
  exact ⟨X, ⟨hX, fun i j hzero ↦ False.elim ((hA i j).ne' hzero)⟩, rfl⟩

/-- The regularized objective gap at an arbitrary feasible comparison point
is at most its unregularized Bethe suboptimality plus the entropy budget.
This is the optimization input used in the global transfer estimate. -/
theorem regularizedDifference_le_betheSuboptimality_add_budget
    {n : ℕ} (hn : 0 < n) {τ ξ : ℝ} (hτ : 0 ≤ τ)
    (hbudget : τ * (n * Real.log n) ≤ ξ * n)
    {A X P : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hP : IsDoublyStochastic P) :
    regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A P ≤
      betheSuboptimality (betheLogValue A) (betheObjective A P) + ξ * n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hbethe := betheObjective_le_betheLogValue_of_positive hA hX
  have hHX : totalRowEntropy X ≤ n * Real.log n := by
    simpa using totalRowEntropy_le hX
  have hHP : 0 ≤ totalRowEntropy P := totalRowEntropy_nonneg hP
  have hτHX := mul_le_mul_of_nonneg_left hHX hτ
  have hτHP : 0 ≤ τ * totalRowEntropy P := mul_nonneg hτ hHP
  rw [regularizedBetheObjective, regularizedBetheObjective,
    betheSuboptimality]
  linarith

/-- Paper Lemma 14, in the form consumed by the later transfer argument.
Existence, interiority, near-optimality, and the logarithmic KKT equations are
all proved; the only imported hypothesis is Vontobel's concavity theorem. -/
theorem exists_regularizedOptimizer_with_logKKT
    {n : ℕ} (hn : 1 < n)
    {τ ξ : ℝ} (hτ : 0 < τ)
    (hregularization : τ * (n * Real.log n) ≤ ξ * n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.Positive A) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      IsDoublyStochastic X ∧
      (∀ i, IsInteriorProbabilityVector (X i)) ∧
      (∀ Y, IsDoublyStochastic Y →
        regularizedBetheObjective τ A Y ≤
          regularizedBetheObjective τ A X) ∧
      (∃ r c : Fin n → ℝ, HasLogKKT τ A X r c) ∧
      Real.log (bethePermanent A) - ξ * n ≤ betheObjective A X := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  obtain ⟨X, hX, hmax⟩ := exists_regularizedBetheMaximizer τ A
  have hXint := regularizedBetheMaximizer_interior hn hτ hA hX hmax
  obtain ⟨r, c, hKKT⟩ :=
    exists_logKKT_of_regularizedBetheMaximizer hX hXint hmax
  have hvalue := betheLogValue_le_regularizedMaximizer
    hn hτ.le hA hX hmax
  have hmatch := positiveMatrix_hasPerfectMatching hA
  have hlog : Real.log (bethePermanent A) = betheLogValue A := by
    rw [bethePermanent, ite_eq_left hmatch, Real.log_exp]
  refine ⟨X, hX, hXint, hmax, ⟨r, c, hKKT⟩, ?_⟩
  rw [hlog]
  nlinarith

theorem regularization_budget_of_paper_scale
    {n : ℕ} {ell ξ τ : ℝ}
    (hell : 0 < ell)
    (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hτ : τ = ξ / (4 * ell)) :
    τ * (n * Real.log n) ≤ ξ * n := by
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hτlog : τ * Real.log n ≤ ξ := by
    calc
      τ * Real.log n ≤ τ * (ell * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogn hτpos.le
      _ = ξ * Real.log 2 / 4 := by
        rw [hτ]
        field_simp [hell.ne']
      _ ≤ ξ := by
        have := mul_le_mul_of_nonneg_left hlog2 hξ.le
        nlinarith
  calc
    τ * (n * Real.log n) = n * (τ * Real.log n) := by ring
    _ ≤ n * ξ := mul_le_mul_of_nonneg_left hτlog (Nat.cast_nonneg n)
    _ = ξ * n := by ring

theorem exists_regularizedOptimizer_at_paper_scale
    {n : ℕ} (hn : 1 < n)
    {ell ξ τ : ℝ} (hell : 0 < ell)
    (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hτ : τ = ξ / (4 * ell))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.Positive A) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ,
      IsDoublyStochastic X ∧
      (∀ i, IsInteriorProbabilityVector (X i)) ∧
      (∀ Y, IsDoublyStochastic Y →
        regularizedBetheObjective τ A Y ≤
          regularizedBetheObjective τ A X) ∧
      (∃ r c : Fin n → ℝ, HasLogKKT τ A X r c) ∧
      Real.log (bethePermanent A) - ξ * n ≤ betheObjective A X := by
  have hτpos : 0 < τ := by rw [hτ]; positivity
  exact exists_regularizedOptimizer_with_logKKT hn hτpos
    (regularization_budget_of_paper_scale hell hlogn hξ hτ) A hA
end
end BeyondBethe
