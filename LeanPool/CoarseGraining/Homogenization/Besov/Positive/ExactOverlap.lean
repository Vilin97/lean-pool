/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp

/-!
# Exact overlapping positive-order Besov kernel

This module is the extended-norm realization of the Chapter 1 positive Besov
definition.  A natural depth `j` represents the manuscript scale
`n = Q.scale - j`; thus all `n ∈ (-∞, Q.scale]` occur exactly once.  The
overlapping centers are `ScalarOverlap.centersAtDepth Q j`.
-/

namespace Homogenization

open scoped BigOperators ENNReal

/-- Admissible finite-`q` positive Besov parameters.  The real-valued
exponents are finite by construction, and their `ENNReal` embeddings are used
only where `eLpNorm` requires an extended exponent. -/
def ExactOverlapFiniteAdmissible (s p q : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ 1 ≤ p ∧ 1 ≤ q

/-- Admissible `q = ∞` positive Besov parameters. -/
def ExactOverlapTopAdmissible (s p : ℝ) : Prop :=
  0 < s ∧ s ≤ 1 ∧ 1 ≤ p

/-- Finite-`q` parameters for the exact Chapter 1 overlap Besov kernel. -/
structure ExactOverlapFiniteParameters where
  /-- The positive regularity exponent. -/
  s : ℝ
  /-- The finite local-integrability exponent. -/
  p : ℝ
  /-- The finite depth-aggregation exponent. -/
  q : ℝ
  admissible : ExactOverlapFiniteAdmissible s p q

/-- `q = ∞` parameters for the exact Chapter 1 overlap Besov kernel. -/
structure ExactOverlapTopParameters where
  /-- The positive regularity exponent. -/
  s : ℝ
  /-- The finite local-integrability exponent. -/
  p : ℝ
  admissible : ExactOverlapTopAdmissible s p

namespace ExactOverlapFiniteParameters

theorem s_pos (P : ExactOverlapFiniteParameters) : 0 < P.s :=
  P.admissible.1

theorem s_lt_one (P : ExactOverlapFiniteParameters) : P.s < 1 :=
  P.admissible.2.1

theorem p_one_le (P : ExactOverlapFiniteParameters) : 1 ≤ P.p :=
  P.admissible.2.2.1

theorem q_one_le (P : ExactOverlapFiniteParameters) : 1 ≤ P.q :=
  P.admissible.2.2.2

/-- The finite real `p` exponent as an `ENNReal` exponent for `eLpNorm`. -/
noncomputable def pExponent (P : ExactOverlapFiniteParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.p

/-- The finite real `q` exponent as an `ENNReal` exponent. -/
noncomputable def qExponent (P : ExactOverlapFiniteParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.q

theorem pExponent_ne_top (P : ExactOverlapFiniteParameters) : P.pExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem qExponent_ne_top (P : ExactOverlapFiniteParameters) : P.qExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem one_le_pExponent (P : ExactOverlapFiniteParameters) : 1 ≤ P.pExponent := by
  rw [pExponent, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal P.p_one_le

theorem one_le_qExponent (P : ExactOverlapFiniteParameters) : 1 ≤ P.qExponent := by
  rw [qExponent, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal P.q_one_le

end ExactOverlapFiniteParameters

namespace ExactOverlapTopParameters

theorem s_pos (P : ExactOverlapTopParameters) : 0 < P.s :=
  P.admissible.1

theorem s_le_one (P : ExactOverlapTopParameters) : P.s ≤ 1 :=
  P.admissible.2.1

theorem p_one_le (P : ExactOverlapTopParameters) : 1 ≤ P.p :=
  P.admissible.2.2

/-- The finite real `p` exponent as an `ENNReal` exponent for `eLpNorm`. -/
noncomputable def pExponent (P : ExactOverlapTopParameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.p

theorem pExponent_ne_top (P : ExactOverlapTopParameters) : P.pExponent ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem one_le_pExponent (P : ExactOverlapTopParameters) : 1 ≤ P.pExponent := by
  rw [pExponent, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal P.p_one_le

end ExactOverlapTopParameters

/-- The integrability data needed to form the source-style root mean and every
overlap-local mean.  The two measures are kept explicit to prevent the native
small cube of a center from being confused with its enlarged overlap cube. -/
structure ExactOverlapIntegrable {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) where
  root : MeasureTheory.Integrable u (Homogenization.normalizedCubeMeasure Q)
  overlap : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
    MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)

/-- Canonical root and overlap-local integrability data for the zero function. -/
theorem exactOverlapZeroIntegrable {d : ℕ} (Q : TriadicCube d) :
    ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ)) where
  root := MeasureTheory.integrable_zero _ _ _
  overlap := fun _ _ _ => MeasureTheory.integrable_zero _ _ _

/-- The manuscript depth index represented by a natural overlap depth. -/
def exactOverlapSourceDepth {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ℤ :=
  Q.scale - (j : ℤ)

theorem exactOverlapSourceDepth_le_scale {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    exactOverlapSourceDepth Q j ≤ Q.scale := by
  unfold exactOverlapSourceDepth
  omega

theorem exactOverlapCenters_nonempty {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (ScalarOverlap.centersAtDepth Q j).Nonempty :=
  ScalarOverlap.centersAtDepth_nonempty Q j

theorem exists_exactOverlapDepth_of_le_scale {d : ℕ} (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) :
    ∃ j : ℕ, exactOverlapSourceDepth Q j = n := by
  refine ⟨Int.toNat (Q.scale - n), ?_⟩
  unfold exactOverlapSourceDepth
  have hnonneg : 0 ≤ Q.scale - n := sub_nonneg.mpr hn
  rw [Int.toNat_of_nonneg hnonneg]
  omega

/-- The exact source factor `3^(-n s)` at natural depth `j`, where
`n = Q.scale - j`. -/
noncomputable def exactOverlapDepthWeight {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (j : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ (-((exactOverlapSourceDepth Q j : ℤ) : ℝ) * s)

/-- The source root-scale factor `3^(-s m)`, where `m = Q.scale`. -/
noncomputable def exactOverlapRootWeight {d : ℕ} (Q : TriadicCube d) (s : ℝ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ (-((Q.scale : ℤ) : ℝ) * s)

theorem exactOverlapDepthWeight_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    exactOverlapDepthWeight Q s 0 = exactOverlapRootWeight Q s := by
  simp only [exactOverlapDepthWeight, exactOverlapRootWeight, exactOverlapSourceDepth,
    Nat.cast_zero, sub_zero]

/-- The source root mean on the ordinary normalized root cube. -/
noncomputable def exactOverlapRootMean {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ)
    (_hu : MeasureTheory.Integrable u (Homogenization.normalizedCubeMeasure Q)) : ℝ :=
  ∫ x, u x ∂Homogenization.normalizedCubeMeasure Q

/-- The source local mean on the enlarged scalar-overlap cube associated to a
center.  Its integrability certificate prevents any undefined-mean fallback. -/
noncomputable def exactOverlapLocalMean {d : ℕ} (S : TriadicCube d) (u : Vec d → ℝ)
    (_hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) : ℝ :=
  ∫ x, u x ∂ScalarOverlap.normalizedCubeMeasure S

/-- The extended normalized local `L^p` oscillation around the certified cube
mean. -/
noncomputable def exactOverlapLocalOscillation {d : ℕ} (S : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm (fun x => u x - exactOverlapLocalMean S u hu) p
    (ScalarOverlap.normalizedCubeMeasure S)

/-- Exact finite normalized `ℓ^p` average of the local overlap oscillations. -/
noncomputable def exactOverlapDepthAverage {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (j : ℕ) : ℝ≥0∞ :=
  let D := ScalarOverlap.centersAtDepth Q j
  (D.card : ℝ≥0∞)⁻¹ * D.attach.sum fun S =>
    (exactOverlapLocalOscillation S.1 (ENNReal.ofReal p) u (hu.overlap j S.1 S.2)) ^ p

/-- The weighted source depth term.  The overlap centers at `j` encode the
source scale `n = Q.scale - j`. -/
noncomputable def exactOverlapDepthTerm {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (j : ℕ) : ℝ≥0∞ :=
  exactOverlapDepthWeight Q s j *
    (exactOverlapDepthAverage Q p u hu j) ^ p⁻¹

/-- The exact finite-`q` positive Besov seminorm: the infinite `ℓ^q`
aggregation of the source depth terms, retaining the value `∞`. -/
noncomputable def exactOverlapFiniteSeminorm {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) : ℝ≥0∞ :=
  (∑' j : ℕ, (exactOverlapDepthTerm Q P.s P.p u hu j) ^ P.q) ^ P.q⁻¹

/-- The exact `q = ∞` positive Besov seminorm. -/
noncomputable def exactOverlapTopSeminorm {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) : ℝ≥0∞ :=
  ⨆ j : ℕ, exactOverlapDepthTerm Q P.s P.p u hu j

/-- The exact finite-`q` inhomogeneous positive Besov norm, including the
source root mean term `3^(-s m) |(u)_Q|`. -/
noncomputable def exactOverlapFiniteNorm {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) : ℝ≥0∞ :=
  exactOverlapFiniteSeminorm P Q u hu + exactOverlapRootWeight Q P.s *
    ENNReal.ofReal |exactOverlapRootMean Q u hu.root|

/-- The exact `q = ∞` inhomogeneous positive Besov norm, including the source
root mean term. -/
noncomputable def exactOverlapTopNorm {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) : ℝ≥0∞ :=
  exactOverlapTopSeminorm P Q u hu + exactOverlapRootWeight Q P.s *
    ENNReal.ofReal |exactOverlapRootMean Q u hu.root|

/-- Evaluation of the certified local overlap mean on the enlarged overlap
cube. -/
theorem exactOverlapLocalMean_eq {d : ℕ} (S : TriadicCube d) (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalMean S u hu = ∫ x, u x ∂ScalarOverlap.normalizedCubeMeasure S :=
  rfl

theorem exactOverlapRootMean_zero {d : ℕ} (Q : TriadicCube d)
    (hu : MeasureTheory.Integrable (fun _ : Vec d => (0 : ℝ))
      (Homogenization.normalizedCubeMeasure Q)) :
    exactOverlapRootMean Q (fun _ => (0 : ℝ)) hu = 0 := by
  simp only [exactOverlapRootMean, MeasureTheory.integral_zero]

/-- Evaluation of the certified local overlap oscillation. -/
theorem exactOverlapLocalOscillation_eq {d : ℕ} (S : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S p u hu =
      MeasureTheory.eLpNorm (fun x => u x - exactOverlapLocalMean S u hu) p
        (ScalarOverlap.normalizedCubeMeasure S) :=
  rfl

theorem exactOverlapLocalMean_zero {d : ℕ} (S : TriadicCube d)
    (hu : MeasureTheory.Integrable (fun _ : Vec d => (0 : ℝ))
      (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalMean S (fun _ => (0 : ℝ)) hu = 0 := by
  simp only [exactOverlapLocalMean, MeasureTheory.integral_zero]

theorem exactOverlapLocalOscillation_zero {d : ℕ} (S : TriadicCube d) (p : ℝ≥0∞)
    (hu : MeasureTheory.Integrable (fun _ : Vec d => (0 : ℝ))
      (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S p (fun _ => (0 : ℝ)) hu = 0 := by
  unfold exactOverlapLocalOscillation
  rw [exactOverlapLocalMean_zero]
  simpa only [zero_sub, neg_zero] using!
    (MeasureTheory.eLpNorm_zero (α := Vec d) (ε := ℝ) (p := p)
      (μ := ScalarOverlap.normalizedCubeMeasure S))

theorem exactOverlapLocalOscillation_congr_ae {d : ℕ} (S : TriadicCube d)
    (p : ℝ≥0∞) {u v : Vec d → ℝ}
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S))
    (hv : MeasureTheory.Integrable v (ScalarOverlap.normalizedCubeMeasure S))
    (huv : u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v) :
    exactOverlapLocalOscillation S p u hu = exactOverlapLocalOscillation S p v hv := by
  have hmean : exactOverlapLocalMean S u hu = exactOverlapLocalMean S v hv := by
    exact MeasureTheory.integral_congr_ae huv
  unfold exactOverlapLocalOscillation
  rw [hmean]
  apply MeasureTheory.eLpNorm_congr_ae
  filter_upwards [huv] with x hx
  exact congrArg (fun t => t - exactOverlapLocalMean S v hv) hx

/-- The certified normalized root mean depends only on the root-cube a.e.
representative. -/
theorem exactOverlapRootMean_congr_ae {d : ℕ} (Q : TriadicCube d)
    {u v : Vec d → ℝ}
    (hu : MeasureTheory.Integrable u (Homogenization.normalizedCubeMeasure Q))
    (hv : MeasureTheory.Integrable v (Homogenization.normalizedCubeMeasure Q))
    (huv : u =ᵐ[Homogenization.normalizedCubeMeasure Q] v) :
    exactOverlapRootMean Q u hu = exactOverlapRootMean Q v hv :=
  MeasureTheory.integral_congr_ae huv

/-- A normalized overlap depth average depends only on the a.e. representatives
on its enlarged overlap cubes. -/
theorem exactOverlapDepthAverage_congr_ae {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    {u v : Vec d → ℝ} (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (huv : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v)
  (j : ℕ) :
    exactOverlapDepthAverage Q p u hu j = exactOverlapDepthAverage Q p v hv j := by
  unfold exactOverlapDepthAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  rw [exactOverlapLocalOscillation_congr_ae S.1 (ENNReal.ofReal p)
    (hu.overlap j S.1 S.2) (hv.overlap j S.1 S.2) (huv j S.1 S.2)]

/-- A weighted overlap depth term depends only on the a.e. representatives on
its enlarged overlap cubes. -/
theorem exactOverlapDepthTerm_congr_ae {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    {u v : Vec d → ℝ} (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (huv : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v)
    (j : ℕ) :
    exactOverlapDepthTerm Q s p u hu j = exactOverlapDepthTerm Q s p v hv j := by
  unfold exactOverlapDepthTerm
  rw [exactOverlapDepthAverage_congr_ae Q p hu hv huv j]

/-- The finite-`q` exact overlap seminorm depends only on the a.e.
representatives on every enlarged overlap cube. -/
theorem exactOverlapFiniteSeminorm_congr_ae {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) {u v : Vec d → ℝ}
    (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (huv : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v) :
    exactOverlapFiniteSeminorm P Q u hu = exactOverlapFiniteSeminorm P Q v hv := by
  unfold exactOverlapFiniteSeminorm
  congr 1
  apply tsum_congr
  intro j
  rw [exactOverlapDepthTerm_congr_ae Q P.s P.p hu hv huv j]

/-- The `q = ∞` exact overlap seminorm depends only on the a.e.
representatives on every enlarged overlap cube. -/
theorem exactOverlapTopSeminorm_congr_ae {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) {u v : Vec d → ℝ}
    (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (huv : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v) :
    exactOverlapTopSeminorm P Q u hu = exactOverlapTopSeminorm P Q v hv := by
  unfold exactOverlapTopSeminorm
  apply iSup_congr
  intro j
  exact exactOverlapDepthTerm_congr_ae Q P.s P.p hu hv huv j

/-- The finite-`q` exact overlap norm depends only on the root and overlap-cube
a.e. representatives. -/
theorem exactOverlapFiniteNorm_congr_ae {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) {u v : Vec d → ℝ}
    (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (hroot : u =ᵐ[Homogenization.normalizedCubeMeasure Q] v)
    (hoverlap : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v) :
    exactOverlapFiniteNorm P Q u hu = exactOverlapFiniteNorm P Q v hv := by
  unfold exactOverlapFiniteNorm
  rw [exactOverlapFiniteSeminorm_congr_ae P Q hu hv hoverlap,
    exactOverlapRootMean_congr_ae Q hu.root hv.root hroot]

/-- The `q = ∞` exact overlap norm depends only on the root and overlap-cube
a.e. representatives. -/
theorem exactOverlapTopNorm_congr_ae {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) {u v : Vec d → ℝ}
    (hu : ExactOverlapIntegrable Q u) (hv : ExactOverlapIntegrable Q v)
    (hroot : u =ᵐ[Homogenization.normalizedCubeMeasure Q] v)
    (hoverlap : ∀ (j : ℕ) (S : TriadicCube d), S ∈ ScalarOverlap.centersAtDepth Q j →
      u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v) :
    exactOverlapTopNorm P Q u hu = exactOverlapTopNorm P Q v hv := by
  unfold exactOverlapTopNorm
  rw [exactOverlapTopSeminorm_congr_ae P Q hu hv hoverlap,
    exactOverlapRootMean_congr_ae Q hu.root hv.root hroot]

private theorem exactOverlapDepthAverage_zero_of_pos {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (hp : 0 < p) (j : ℕ) :
    exactOverlapDepthAverage Q p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 := by
  simp only [exactOverlapDepthAverage, exactOverlapLocalOscillation_zero,
    ENNReal.zero_rpow_of_pos hp, Finset.sum_const_zero, mul_zero]

private theorem exactOverlapDepthTerm_zero_of_pos {d : ℕ} (Q : TriadicCube d)
    (s p : ℝ) (hp : 0 < p) (j : ℕ) :
    exactOverlapDepthTerm Q s p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 := by
  unfold exactOverlapDepthTerm
  rw [exactOverlapDepthAverage_zero_of_pos Q p hp j,
    ENNReal.zero_rpow_of_pos (inv_pos.mpr hp), mul_zero]

/-- The local overlap depth average vanishes for zero data at every admissible
finite-`q` exponent. -/
theorem exactOverlapFiniteDepthAverage_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactOverlapDepthAverage Q P.p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 :=
  exactOverlapDepthAverage_zero_of_pos Q P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The local overlap depth average vanishes for zero data at every admissible
`q = ∞` exponent. -/
theorem exactOverlapTopDepthAverage_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactOverlapDepthAverage Q P.p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 :=
  exactOverlapDepthAverage_zero_of_pos Q P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The weighted overlap depth term vanishes for zero data at every admissible
finite-`q` exponent. -/
theorem exactOverlapFiniteDepthTerm_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactOverlapDepthTerm Q P.s P.p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 :=
  exactOverlapDepthTerm_zero_of_pos Q P.s P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- The weighted overlap depth term vanishes for zero data at every admissible
`q = ∞` exponent. -/
theorem exactOverlapTopDepthTerm_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (j : ℕ) :
    exactOverlapDepthTerm Q P.s P.p (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) j = 0 :=
  exactOverlapDepthTerm_zero_of_pos Q P.s P.p
    (lt_of_lt_of_le zero_lt_one P.p_one_le) j

/-- Evaluation of the finite overlap-center average at one source depth. -/
theorem exactOverlapDepthAverage_eq {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (j : ℕ) :
    exactOverlapDepthAverage Q p u hu j =
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum fun S =>
          (exactOverlapLocalOscillation S.1 (ENNReal.ofReal p) u
            (hu.overlap j S.1 S.2)) ^ p :=
  rfl

/-- Evaluation of the source-weighted depth term. -/
theorem exactOverlapDepthTerm_eq {d : ℕ} (Q : TriadicCube d) (s p : ℝ)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (j : ℕ) :
    exactOverlapDepthTerm Q s p u hu j = exactOverlapDepthWeight Q s j *
      (exactOverlapDepthAverage Q p u hu j) ^ p⁻¹ :=
  rfl

/-- Evaluation of the infinite finite-`q` aggregation. -/
theorem exactOverlapFiniteSeminorm_eq {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapFiniteSeminorm P Q u hu =
      (∑' j : ℕ, (exactOverlapDepthTerm Q P.s P.p u hu j) ^ P.q) ^ P.q⁻¹ :=
  rfl

/-- Evaluation of the `q = ∞` aggregation. -/
theorem exactOverlapTopSeminorm_eq {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapTopSeminorm P Q u hu =
      ⨆ j : ℕ, exactOverlapDepthTerm Q P.s P.p u hu j :=
  rfl

/-- Evaluation of the finite-`q` inhomogeneous norm. -/
theorem exactOverlapFiniteNorm_eq {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapFiniteNorm P Q u hu =
      exactOverlapFiniteSeminorm P Q u hu + exactOverlapRootWeight Q P.s *
        ENNReal.ofReal |exactOverlapRootMean Q u hu.root| :=
  rfl

/-- Evaluation of the `q = ∞` inhomogeneous norm. -/
theorem exactOverlapTopNorm_eq {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapTopNorm P Q u hu =
      exactOverlapTopSeminorm P Q u hu + exactOverlapRootWeight Q P.s *
        ENNReal.ofReal |exactOverlapRootMean Q u hu.root| :=
  rfl

/-- The exact finite-`q` overlap seminorm vanishes on the zero function. -/
theorem exactOverlapFiniteSeminorm_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) :
    exactOverlapFiniteSeminorm P Q (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) = 0 := by
  rw [exactOverlapFiniteSeminorm_eq]
  have hq : 0 < P.q := lt_of_lt_of_le zero_lt_one P.q_one_le
  simp_rw [exactOverlapFiniteDepthTerm_zero P Q, ENNReal.zero_rpow_of_pos hq]
  rw [tsum_zero, ENNReal.zero_rpow_of_pos]
  exact inv_pos.mpr hq

/-- The exact `q = ∞` overlap seminorm vanishes on the zero function. -/
theorem exactOverlapTopSeminorm_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) :
    exactOverlapTopSeminorm P Q (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) = 0 := by
  rw [exactOverlapTopSeminorm_eq]
  simp_rw [exactOverlapTopDepthTerm_zero P Q]
  exact iSup_const

/-- The exact finite-`q` inhomogeneous overlap norm vanishes on zero data. -/
theorem exactOverlapFiniteNorm_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) :
    exactOverlapFiniteNorm P Q (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) = 0 := by
  rw [exactOverlapFiniteNorm_eq, exactOverlapFiniteSeminorm_zero,
    exactOverlapRootMean_zero]
  simp only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero]

/-- The exact `q = ∞` inhomogeneous overlap norm vanishes on zero data. -/
theorem exactOverlapTopNorm_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) :
    exactOverlapTopNorm P Q (fun _ => (0 : ℝ)) (exactOverlapZeroIntegrable Q) = 0 := by
  rw [exactOverlapTopNorm_eq, exactOverlapTopSeminorm_zero, exactOverlapRootMean_zero]
  simp only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero]

/-- Every extended quantity in the exact overlap kernel is nonnegative. -/
theorem exactOverlapLocalOscillation_nonneg {d : ℕ} (S : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hu : MeasureTheory.Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    0 ≤ exactOverlapLocalOscillation S p u hu :=
  bot_le

theorem exactOverlapDepthAverage_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (j : ℕ) :
    0 ≤ exactOverlapDepthAverage Q p u hu j :=
  bot_le

theorem exactOverlapFiniteSeminorm_nonneg {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    0 ≤ exactOverlapFiniteSeminorm P Q u hu :=
  bot_le

theorem exactOverlapTopSeminorm_nonneg {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    0 ≤ exactOverlapTopSeminorm P Q u hu :=
  bot_le

theorem exactOverlapFiniteNorm_nonneg {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    0 ≤ exactOverlapFiniteNorm P Q u hu :=
  bot_le

theorem exactOverlapTopNorm_nonneg {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) :
    0 ≤ exactOverlapTopNorm P Q u hu :=
  bot_le

end Homogenization
