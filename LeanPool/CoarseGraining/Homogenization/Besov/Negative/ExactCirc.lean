/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms

/-!
# Exact concrete circ negative Besov kernel

This is the extended-valued source-facing circ lane from Chapter 1.  Its
natural depth `j` represents the manuscript scale `n = Q.scale - j`, and its
blocks are exactly the disjoint descendants at that depth.
-/

namespace Homogenization

open scoped BigOperators ENNReal

/-- Admissible finite-`q` circ parameters.  The real exponents are finite by
construction; the final implication is the source restriction at `s = 1`. -/
def ExactCircFiniteAdmissible (s p q : ℝ) : Prop :=
  0 < s ∧ s ≤ 1 ∧ 1 ≤ p ∧ 1 ≤ q ∧ (s = 1 → q = 1)

/-- Admissible `q = ∞` circ parameters. -/
def ExactCircTopAdmissible (s p : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ 1 ≤ p

/-- Finite-`q` parameters for the exact concrete circ seminorm. -/
structure ExactCircFiniteParameters where
  /-- Negative smoothness exponent. -/
  s : ℝ
  /-- Data integrability exponent. -/
  p : ℝ
  /-- Finite aggregation exponent. -/
  q : ℝ
  admissible : ExactCircFiniteAdmissible s p q

/-- `q = ∞` parameters for the exact concrete circ seminorm. -/
structure ExactCircTopParameters where
  /-- Negative smoothness exponent. -/
  s : ℝ
  /-- Data integrability exponent. -/
  p : ℝ
  admissible : ExactCircTopAdmissible s p

namespace ExactCircFiniteParameters

theorem s_pos (P : ExactCircFiniteParameters) : 0 < P.s :=
  P.admissible.1

theorem s_le_one (P : ExactCircFiniteParameters) : P.s ≤ 1 :=
  P.admissible.2.1

theorem p_one_le (P : ExactCircFiniteParameters) : 1 ≤ P.p :=
  P.admissible.2.2.1

theorem q_one_le (P : ExactCircFiniteParameters) : 1 ≤ P.q :=
  P.admissible.2.2.2.1

theorem q_eq_one_of_s_eq_one (P : ExactCircFiniteParameters) (hs : P.s = 1) :
    P.q = 1 :=
  P.admissible.2.2.2.2 hs

/-- The finite real `p` exponent as an `ENNReal` exponent. -/
noncomputable def pExponent (P : ExactCircFiniteParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.p

/-- The finite real `q` exponent as an `ENNReal` exponent. -/
noncomputable def qExponent (P : ExactCircFiniteParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.q

theorem pExponent_ne_top (P : ExactCircFiniteParameters) : P.pExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem qExponent_ne_top (P : ExactCircFiniteParameters) : P.qExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

end ExactCircFiniteParameters

namespace ExactCircTopParameters

theorem s_pos (P : ExactCircTopParameters) : 0 < P.s :=
  P.admissible.1

theorem s_lt_one (P : ExactCircTopParameters) : P.s < 1 :=
  P.admissible.2.1

theorem p_one_le (P : ExactCircTopParameters) : 1 ≤ P.p :=
  P.admissible.2.2

/-- The finite real `p` exponent as an `ENNReal` exponent. -/
noncomputable def pExponent (P : ExactCircTopParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.p

theorem pExponent_ne_top (P : ExactCircTopParameters) : P.pExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

end ExactCircTopParameters

/-- Integrability certificates for the normalized averages on every disjoint
block used by the source circ seminorm. -/
structure ExactCircIntegrable {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) where
  block : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
    MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)

/-- Canonical block-integrability data for the zero function. -/
theorem exactCircZeroIntegrable {d : ℕ} (Q : TriadicCube d) :
    ExactCircIntegrable Q (fun _ : Vec d => (0 : ℝ)) where
  block := fun _ _ _ => MeasureTheory.integrable_zero _ _ _

/-- The manuscript source index represented by a natural descendant depth. -/
def exactCircSourceDepth {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ℤ :=
  Q.scale - (j : ℤ)

theorem exactCircSourceDepth_eq {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    exactCircSourceDepth Q j = Q.scale - (j : ℤ) :=
  rfl

theorem exactCircSourceDepth_le_scale {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    exactCircSourceDepth Q j ≤ Q.scale := by
  unfold exactCircSourceDepth
  omega

theorem exists_exactCircDepth_of_le_scale {d : ℕ} (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) :
    ∃ j : ℕ, exactCircSourceDepth Q j = n := by
  refine ⟨Int.toNat (Q.scale - n), ?_⟩
  unfold exactCircSourceDepth
  have hnonneg : 0 ≤ Q.scale - n := sub_nonneg.mpr hn
  rw [Int.toNat_of_nonneg hnonneg]
  omega

/-- A depth-`j` descendant has exactly the source scale `n = Q.scale - j`. -/
theorem exactCirc_descendant_scale {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    R.scale = exactCircSourceDepth Q j := by
  simpa only [exactCircSourceDepth] using scale_eq_sub_of_mem_descendantsAtDepth hR

theorem exactCircDescendants_nonempty {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (descendantsAtDepth Q j).Nonempty :=
  descendantsAtDepth_nonempty Q j

/-- The normalized ordinary-cube average on a disjoint circ block. -/
noncomputable def exactCircBlockMean {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ)
    (_hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)) : ℝ :=
  ∫ x, f x ∂Homogenization.normalizedCubeMeasure R

/-- The exact source weight `3^(n s)` at descendant depth `j`. -/
noncomputable def exactCircDepthWeight {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (j : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ (((exactCircSourceDepth Q j : ℤ) : ℝ) * s)

/-- The exact normalized finite `ℓ^p` average of the absolute block means. -/
noncomputable def exactCircDepthAverage {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) : ℝ≥0∞ :=
  let D := descendantsAtDepth Q j
  (D.card : ℝ≥0∞)⁻¹ * D.attach.sum fun R =>
    (ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^ p

/-- The weighted source depth term of the concrete circ seminorm. -/
noncomputable def exactCircDepthTerm {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) : ℝ≥0∞ :=
  exactCircDepthWeight Q s j * (exactCircDepthAverage Q p f hf j) ^ p⁻¹

/-- The exact finite-`q` concrete circ negative Besov seminorm. -/
noncomputable def exactCircFiniteSeminorm {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) : ℝ≥0∞ :=
  (∑' j : ℕ, (exactCircDepthTerm Q P.s P.p f hf j) ^ P.q) ^ P.q⁻¹

/-- The exact `q = ∞` concrete circ negative Besov seminorm. -/
noncomputable def exactCircTopSeminorm {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) : ℝ≥0∞ :=
  ⨆ j : ℕ, exactCircDepthTerm Q P.s P.p f hf j

/-- Evaluation of the certified normalized disjoint block mean. -/
theorem exactCircBlockMean_eq {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)) :
    exactCircBlockMean R f hf = ∫ x, f x ∂Homogenization.normalizedCubeMeasure R :=
  rfl

theorem exactCircBlockMean_zero {d : ℕ} (R : TriadicCube d)
    (hf : MeasureTheory.Integrable (fun _ : Vec d => (0 : ℝ))
      (Homogenization.normalizedCubeMeasure R)) :
    exactCircBlockMean R (fun _ => (0 : ℝ)) hf = 0 := by
  simp only [exactCircBlockMean, MeasureTheory.integral_zero]

theorem exactCircBlockMean_congr_ae {d : ℕ} (R : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R))
    (hg : MeasureTheory.Integrable g (Homogenization.normalizedCubeMeasure R))
    (hfg : f =ᵐ[Homogenization.normalizedCubeMeasure R] g) :
    exactCircBlockMean R f hf = exactCircBlockMean R g hg :=
  MeasureTheory.integral_congr_ae hfg

/-- A normalized disjoint-block depth average depends only on the a.e.
representatives on each ordinary descendant block. -/
theorem exactCircDepthAverage_congr_ae {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    {f g : Vec d → ℝ} (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (hfg : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      f =ᵐ[Homogenization.normalizedCubeMeasure R] g)
    (j : ℕ) :
    exactCircDepthAverage Q p f hf j = exactCircDepthAverage Q p g hg j := by
  unfold exactCircDepthAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro R _
  rw [exactCircBlockMean_congr_ae R.1 (hf.block j R.1 R.2)
    (hg.block j R.1 R.2) (hfg j R.1 R.2)]

/-- A weighted circ depth term depends only on the a.e. representatives on
each ordinary descendant block. -/
theorem exactCircDepthTerm_congr_ae {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    {f g : Vec d → ℝ} (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (hfg : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      f =ᵐ[Homogenization.normalizedCubeMeasure R] g)
    (j : ℕ) :
    exactCircDepthTerm Q s p f hf j = exactCircDepthTerm Q s p g hg j := by
  unfold exactCircDepthTerm
  rw [exactCircDepthAverage_congr_ae Q p hf hg hfg j]

/-- The finite-`q` exact circ seminorm depends only on the a.e.
representatives on every ordinary descendant block. -/
theorem exactCircFiniteSeminorm_congr_ae {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (hfg : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      f =ᵐ[Homogenization.normalizedCubeMeasure R] g) :
    exactCircFiniteSeminorm P Q f hf = exactCircFiniteSeminorm P Q g hg := by
  unfold exactCircFiniteSeminorm
  congr 1
  apply tsum_congr
  intro j
  rw [exactCircDepthTerm_congr_ae Q P.s P.p hf hg hfg j]

/-- The `q = ∞` exact circ seminorm depends only on the a.e.
representatives on every ordinary descendant block. -/
theorem exactCircTopSeminorm_congr_ae {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (hfg : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      f =ᵐ[Homogenization.normalizedCubeMeasure R] g) :
    exactCircTopSeminorm P Q f hf = exactCircTopSeminorm P Q g hg := by
  unfold exactCircTopSeminorm
  apply iSup_congr
  intro j
  exact exactCircDepthTerm_congr_ae Q P.s P.p hf hg hfg j

private theorem exactCircDepthAverage_zero_of_pos {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (hp : 0 < p) (j : ℕ) :
    exactCircDepthAverage Q p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 := by
  simp only [exactCircDepthAverage, exactCircBlockMean_zero, abs_zero, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos hp, Finset.sum_const_zero, mul_zero]

private theorem exactCircDepthTerm_zero_of_pos {d : ℕ} (Q : TriadicCube d)
    (s p : ℝ) (hp : 0 < p) (j : ℕ) :
    exactCircDepthTerm Q s p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 := by
  unfold exactCircDepthTerm
  rw [exactCircDepthAverage_zero_of_pos Q p hp j,
    ENNReal.zero_rpow_of_pos (inv_pos.mpr hp), mul_zero]

/-- The depth average vanishes for zero data at every admissible finite-`q`
exponent. -/
theorem exactCircFiniteDepthAverage_zero {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactCircDepthAverage Q P.p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 :=
  exactCircDepthAverage_zero_of_pos Q P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The depth average vanishes for zero data at every admissible `q = ∞`
exponent. -/
theorem exactCircTopDepthAverage_zero {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactCircDepthAverage Q P.p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 :=
  exactCircDepthAverage_zero_of_pos Q P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The weighted depth term vanishes for zero data at every admissible
finite-`q` exponent. -/
theorem exactCircFiniteDepthTerm_zero {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactCircDepthTerm Q P.s P.p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 :=
  exactCircDepthTerm_zero_of_pos Q P.s P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The weighted depth term vanishes for zero data at every admissible
`q = ∞` exponent. -/
theorem exactCircTopDepthTerm_zero {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactCircDepthTerm Q P.s P.p (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) j = 0 :=
  exactCircDepthTerm_zero_of_pos Q P.s P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- Evaluation of the finite normalized disjoint block average. -/
theorem exactCircDepthAverage_eq {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    exactCircDepthAverage Q p f hf j =
      ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (descendantsAtDepth Q j).attach.sum fun R =>
          (ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^ p :=
  rfl

/-- Evaluation of the weighted concrete circ depth term. -/
theorem exactCircDepthTerm_eq {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    exactCircDepthTerm Q s p f hf j = exactCircDepthWeight Q s j *
      (exactCircDepthAverage Q p f hf j) ^ p⁻¹ :=
  rfl

/-- Evaluation of the infinite finite-`q` aggregation. -/
theorem exactCircFiniteSeminorm_eq {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    exactCircFiniteSeminorm P Q f hf =
      (∑' j : ℕ, (exactCircDepthTerm Q P.s P.p f hf j) ^ P.q) ^ P.q⁻¹ :=
  rfl

/-- Evaluation of the `q = ∞` aggregation. -/
theorem exactCircTopSeminorm_eq {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    exactCircTopSeminorm P Q f hf =
      ⨆ j : ℕ, exactCircDepthTerm Q P.s P.p f hf j :=
  rfl

/-- The exact finite-`q` circ seminorm vanishes on the zero function. -/
theorem exactCircFiniteSeminorm_zero {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) :
    exactCircFiniteSeminorm P Q (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) = 0 := by
  rw [exactCircFiniteSeminorm_eq]
  have hq : 0 < P.q := lt_of_lt_of_le zero_lt_one P.q_one_le
  simp_rw [exactCircFiniteDepthTerm_zero P Q, ENNReal.zero_rpow_of_pos hq]
  rw [tsum_zero, ENNReal.zero_rpow_of_pos]
  exact inv_pos.mpr hq

/-- The exact `q = ∞` circ seminorm vanishes on the zero function. -/
theorem exactCircTopSeminorm_zero {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) :
    exactCircTopSeminorm P Q (fun _ => (0 : ℝ)) (exactCircZeroIntegrable Q) = 0 := by
  rw [exactCircTopSeminorm_eq]
  simp_rw [exactCircTopDepthTerm_zero P Q]
  exact iSup_const

/-- All extended values in the exact concrete circ kernel are nonnegative. -/
theorem exactCircDepthAverage_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    0 ≤ exactCircDepthAverage Q p f hf j :=
  bot_le

theorem exactCircFiniteSeminorm_nonneg {d : ℕ} (P : ExactCircFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    0 ≤ exactCircFiniteSeminorm P Q f hf :=
  bot_le

theorem exactCircTopSeminorm_nonneg {d : ℕ} (P : ExactCircTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    0 ≤ exactCircTopSeminorm P Q f hf :=
  bot_le

end Homogenization
