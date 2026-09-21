/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlap

/-!
# Exact dual-negative Besov kernel

This module records the three Chapter 1 negative Besov endpoint branches as
duals of the exact overlapping positive Besov kernel.  The source exponents
remain real; their `ENNReal` images are used only for `MemLp` and the extended
supremum which deliberately retains `∞`.
-/

namespace Homogenization

open scoped BigOperators ENNReal

/-- The finite real Hölder conjugate used by the exact dual branches. -/
noncomputable def exactDualConjExponent (p : ℝ) : ℝ :=
  Real.conjExponent p

theorem exactDualConjExponent_holder (p : ℝ) (hp : 1 < p) :
    p.HolderConjugate (exactDualConjExponent p) := by
  exact Real.HolderConjugate.conjExponent hp

theorem exactDualConjExponent_one_lt (p : ℝ) (hp : 1 < p) :
    1 < exactDualConjExponent p := by
  exact (exactDualConjExponent_holder p hp).symm.lt

theorem exactDualConjExponent_one_le (p : ℝ) (hp : 1 < p) :
    1 ≤ exactDualConjExponent p :=
  (exactDualConjExponent_one_lt p hp).le
private theorem exactDualHolderConjugateENNReal (p : ℝ) (hp : 1 < p) :
    ENNReal.HolderConjugate (ENNReal.ofReal p)
      (ENNReal.ofReal (exactDualConjExponent p)) := by
  let h := exactDualConjExponent_holder p hp
  exact h.ennrealOfReal

/-- The normalized absolute pairing used in the exact negative definitions.
Its integrability proof is an explicit argument: no totalized integral is
used as a substitute for the Hölder side condition. -/
noncomputable def exactDualNormalizedPairing {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ)
    (_hfg : MeasureTheory.Integrable (fun x => f x * g x)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ENNReal.ofReal |∫ x, f x * g x ∂Homogenization.normalizedCubeMeasure Q|

theorem exactDualNormalizedPairing_eq {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualNormalizedPairing Q f g hfg =
      ENNReal.ofReal |∫ x, f x * g x ∂Homogenization.normalizedCubeMeasure Q| :=
  rfl

/-- The normalized absolute pairing obtained from the displayed Hölder data. -/
noncomputable def exactDualPairingFromHolder {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f g : Vec d → ℝ)
    (hp : 1 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.ofReal (exactDualConjExponent p))
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  exactDualNormalizedPairing Q f g (by
    let : ENNReal.HolderConjugate (ENNReal.ofReal p)
        (ENNReal.ofReal (exactDualConjExponent p)) :=
      exactDualHolderConjugateENNReal p hp
    simpa only [Pi.mul_apply] using! hf.integrable_mul hg)

theorem exactDualPairingFromHolder_eq {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f g : Vec d → ℝ)
    (hp : 1 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.ofReal (exactDualConjExponent p))
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualPairingFromHolder Q p f g hp hf hg =
      ENNReal.ofReal |∫ x, f x * g x ∂Homogenization.normalizedCubeMeasure Q| :=
  rfl

theorem exactDualPairingFromHolder_congr_ae {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f f' g : Vec d → ℝ) (hp : 1 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (hf' : MeasureTheory.MemLp f' (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.ofReal (exactDualConjExponent p))
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualPairingFromHolder Q p f g hp hf hg =
      exactDualPairingFromHolder Q p f' g hp hf' hg := by
  rw [exactDualPairingFromHolder_eq, exactDualPairingFromHolder_eq]
  apply congrArg ENNReal.ofReal
  apply congrArg abs
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hff'] with x hx
  rw [hx]

/-- Negative `q = 1` source parameters.  The positive test space has
`q' = ∞`, including the allowed `s = 1` endpoint. -/
structure ExactDualQOneParameters where
  /-- Negative smoothness exponent. -/
  s : ℝ
  /-- Data integrability exponent. -/
  p : ℝ
  s_pos : 0 < s
  s_le_one : s ≤ 1
  p_one_lt : 1 < p

/-- Negative finite interior source parameters. -/
structure ExactDualFiniteParameters where
  /-- Negative smoothness exponent. -/
  s : ℝ
  /-- Data integrability exponent. -/
  p : ℝ
  /-- Finite negative aggregation exponent. -/
  q : ℝ
  s_pos : 0 < s
  s_lt_one : s < 1
  p_one_lt : 1 < p
  q_one_lt : 1 < q

/-- Negative `q = ∞` source parameters.  The positive test space has
`q' = 1`. -/
structure ExactDualTopParameters where
  /-- Negative smoothness exponent. -/
  s : ℝ
  /-- Data integrability exponent. -/
  p : ℝ
  s_pos : 0 < s
  s_lt_one : s < 1
  p_one_lt : 1 < p

/-- The exact positive `q' = infinity` parameters used to test this branch. -/
noncomputable def ExactDualQOneParameters.positiveParameters
    (P : ExactDualQOneParameters) : ExactOverlapTopParameters where
  s := P.s
  p := exactDualConjExponent P.p
  admissible := ⟨P.s_pos, P.s_le_one, exactDualConjExponent_one_le P.p P.p_one_lt⟩

/-- The exact finite positive Hölder-conjugate test parameters. -/
noncomputable def ExactDualFiniteParameters.positiveParameters
    (P : ExactDualFiniteParameters) : ExactOverlapFiniteParameters where
  s := P.s
  p := exactDualConjExponent P.p
  q := exactDualConjExponent P.q
  admissible := ⟨P.s_pos, P.s_lt_one,
    exactDualConjExponent_one_le P.p P.p_one_lt,
    exactDualConjExponent_one_le P.q P.q_one_lt⟩

/-- The exact positive `q' = 1` test parameters. -/
noncomputable def ExactDualTopParameters.positiveParameters
    (P : ExactDualTopParameters) : ExactOverlapFiniteParameters where
  s := P.s
  p := exactDualConjExponent P.p
  q := 1
  admissible := ⟨P.s_pos, P.s_lt_one,
    exactDualConjExponent_one_le P.p P.p_one_lt, le_rfl⟩

/-- A positive parent `MemLp` certificate supplies every certified root and
overlap-local integral required by the exact positive kernel. -/
theorem exactDualOverlapIntegrable {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (hp : 1 ≤ p) {g : Vec d → ℝ}
    (hg : MeasureTheory.MemLp g (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q)) : ExactOverlapIntegrable Q g where
  root := hg.integrable (ENNReal.one_le_ofReal.mpr hp)
  overlap := fun _ _ hS =>
    (ScalarOverlap.memLp_of_mem_centersAtDepth_of_memLp hS hg).integrable
      (ENNReal.one_le_ofReal.mpr hp)

/-- Full positive-top test functions for the negative `q = 1` branch. -/
structure ExactDualQOneFullTest {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  norm_le_one : exactOverlapTopNorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1

/-- Mean-zero positive-top test functions for the hatted negative `q = 1`
branch. -/
structure ExactDualQOneHattedTest {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  seminorm_le_one : exactOverlapTopSeminorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1
  root_mean_zero : exactOverlapRootMean Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp).root = 0

/-- Full finite positive tests for the negative finite interior branch. -/
structure ExactDualFiniteFullTest {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  norm_le_one : exactOverlapFiniteNorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1

/-- Mean-zero finite positive tests for the hatted negative finite branch. -/
structure ExactDualFiniteHattedTest {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  seminorm_le_one : exactOverlapFiniteSeminorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1
  root_mean_zero : exactOverlapRootMean Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp).root = 0

/-- Full finite positive tests with positive `q' = 1` for the negative
`q = ∞` branch. -/
structure ExactDualTopFullTest {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  norm_le_one : exactOverlapFiniteNorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1

/-- Mean-zero finite positive tests with `q' = 1` for the hatted negative
`q = ∞` branch. -/
structure ExactDualTopHattedTest {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) where
  /-- Test function. -/
  g : Vec d → ℝ
  parentMemLp : MeasureTheory.MemLp g
    (ENNReal.ofReal (exactDualConjExponent P.p))
    (Homogenization.normalizedCubeMeasure Q)
  seminorm_le_one : exactOverlapFiniteSeminorm P.positiveParameters Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp) ≤ 1
  root_mean_zero : exactOverlapRootMean Q g
    (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
      (exactDualConjExponent_one_le P.p P.p_one_lt) parentMemLp).root = 0

/-- The certified normalized pairing against a full `q = 1` test. -/
noncomputable def ExactDualQOneFullTest.pairing {d : ℕ} {P : ExactDualQOneParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualQOneFullTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- The certified normalized pairing against a hatted `q = 1` test. -/
noncomputable def ExactDualQOneHattedTest.pairing {d : ℕ} {P : ExactDualQOneParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualQOneHattedTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- The certified normalized pairing against a full finite test. -/
noncomputable def ExactDualFiniteFullTest.pairing {d : ℕ} {P : ExactDualFiniteParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualFiniteFullTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- The certified normalized pairing against a hatted finite test. -/
noncomputable def ExactDualFiniteHattedTest.pairing {d : ℕ} {P : ExactDualFiniteParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualFiniteHattedTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- The certified normalized pairing against a full `q = infinity` test. -/
noncomputable def ExactDualTopFullTest.pairing {d : ℕ} {P : ExactDualTopParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualTopFullTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- The certified normalized pairing against a hatted `q = infinity` test. -/
noncomputable def ExactDualTopHattedTest.pairing {d : ℕ} {P : ExactDualTopParameters}
    {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (T : ExactDualTopHattedTest P Q) : ℝ≥0∞ :=
  exactDualPairingFromHolder Q P.p f T.g P.p_one_lt hf T.parentMemLp

/-- Exact negative `q = 1` full dual norm. -/
noncomputable def exactDualQOneFullNorm {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualQOneFullTest P Q, T.pairing hf

/-- Exact hatted negative `q = 1` seminorm. -/
noncomputable def exactDualQOneHattedSeminorm {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualQOneHattedTest P Q, T.pairing hf

/-- Exact negative finite interior full dual norm. -/
noncomputable def exactDualFiniteFullNorm {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualFiniteFullTest P Q, T.pairing hf

/-- Exact hatted negative finite interior seminorm. -/
noncomputable def exactDualFiniteHattedSeminorm {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualFiniteHattedTest P Q, T.pairing hf

/-- Exact negative `q = ∞` full dual norm. -/
noncomputable def exactDualTopFullNorm {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualTopFullTest P Q, T.pairing hf

/-- Exact hatted negative `q = ∞` seminorm. -/
noncomputable def exactDualTopHattedSeminorm {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ⨆ T : ExactDualTopHattedTest P Q, T.pairing hf

theorem exactDualQOneFullNorm_eq {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualQOneFullNorm P Q f hf = ⨆ T : ExactDualQOneFullTest P Q, T.pairing hf := rfl

theorem exactDualQOneHattedSeminorm_eq {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualQOneHattedSeminorm P Q f hf =
      ⨆ T : ExactDualQOneHattedTest P Q, T.pairing hf := rfl

theorem exactDualFiniteFullNorm_eq {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualFiniteFullNorm P Q f hf = ⨆ T : ExactDualFiniteFullTest P Q, T.pairing hf := rfl

theorem exactDualFiniteHattedSeminorm_eq {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualFiniteHattedSeminorm P Q f hf =
      ⨆ T : ExactDualFiniteHattedTest P Q, T.pairing hf := rfl

theorem exactDualTopFullNorm_eq {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualTopFullNorm P Q f hf = ⨆ T : ExactDualTopFullTest P Q, T.pairing hf := rfl

theorem exactDualTopHattedSeminorm_eq {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualTopHattedSeminorm P Q f hf =
      ⨆ T : ExactDualTopHattedTest P Q, T.pairing hf := rfl

theorem exactDualQOneFullNorm_congr_ae {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualQOneFullNorm P Q f hf = exactDualQOneFullNorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualQOneFullNorm_eq, exactDualQOneFullNorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

theorem exactDualQOneHattedSeminorm_congr_ae {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualQOneHattedSeminorm P Q f hf =
      exactDualQOneHattedSeminorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualQOneHattedSeminorm_eq, exactDualQOneHattedSeminorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

theorem exactDualFiniteFullNorm_congr_ae {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualFiniteFullNorm P Q f hf = exactDualFiniteFullNorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualFiniteFullNorm_eq, exactDualFiniteFullNorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

theorem exactDualFiniteHattedSeminorm_congr_ae {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualFiniteHattedSeminorm P Q f hf =
      exactDualFiniteHattedSeminorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualFiniteHattedSeminorm_eq, exactDualFiniteHattedSeminorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

theorem exactDualTopFullNorm_congr_ae {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualTopFullNorm P Q f hf = exactDualTopFullNorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualTopFullNorm_eq, exactDualTopFullNorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

theorem exactDualTopHattedSeminorm_congr_ae {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) {f f' : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hff' : f =ᵐ[Homogenization.normalizedCubeMeasure Q] f') :
    exactDualTopHattedSeminorm P Q f hf =
      exactDualTopHattedSeminorm P Q f' (hf.ae_eq hff') := by
  rw [exactDualTopHattedSeminorm_eq, exactDualTopHattedSeminorm_eq]
  apply congrArg iSup
  funext T
  exact exactDualPairingFromHolder_congr_ae Q P.p f f' T.g P.p_one_lt hf
    (hf.ae_eq hff') T.parentMemLp hff'

private theorem exactDualDepthAverage_zero {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (hp : 0 < p) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ)))
    (j : ℕ) :
    exactOverlapDepthAverage Q p (fun _ => (0 : ℝ)) hu j = 0 := by
  simp only [exactOverlapDepthAverage_eq, exactOverlapLocalOscillation_zero,
    ENNReal.zero_rpow_of_pos hp, Finset.sum_const_zero, mul_zero]

private theorem exactDualDepthTerm_zero {d : ℕ} (Q : TriadicCube d)
    (s p : ℝ) (hp : 0 < p) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ)))
    (j : ℕ) :
    exactOverlapDepthTerm Q s p (fun _ => (0 : ℝ)) hu j = 0 := by
  unfold exactOverlapDepthTerm
  rw [exactDualDepthAverage_zero Q p hp hu j,
    ENNReal.zero_rpow_of_pos (inv_pos.mpr hp), mul_zero]

private theorem exactDualFiniteSeminorm_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ))) :
    exactOverlapFiniteSeminorm P Q (fun _ => (0 : ℝ)) hu = 0 := by
  rw [exactOverlapFiniteSeminorm_eq]
  have hq : 0 < P.q := lt_of_lt_of_le zero_lt_one P.q_one_le
  have hp : 0 < P.p := lt_of_lt_of_le zero_lt_one P.p_one_le
  simp_rw [exactDualDepthTerm_zero Q P.s P.p hp hu,
    ENNReal.zero_rpow_of_pos hq]
  rw [tsum_zero, ENNReal.zero_rpow_of_pos]
  exact inv_pos.mpr hq

private theorem exactDualTopSeminorm_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ))) :
    exactOverlapTopSeminorm P Q (fun _ => (0 : ℝ)) hu = 0 := by
  rw [exactOverlapTopSeminorm_eq]
  have hp : 0 < P.p := lt_of_lt_of_le zero_lt_one P.p_one_le
  simp_rw [exactDualDepthTerm_zero Q P.s P.p hp hu]
  exact iSup_const

private theorem exactDualFiniteNorm_zero {d : ℕ} (P : ExactOverlapFiniteParameters)
    (Q : TriadicCube d) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ))) :
    exactOverlapFiniteNorm P Q (fun _ => (0 : ℝ)) hu = 0 := by
  rw [exactOverlapFiniteNorm_eq, exactDualFiniteSeminorm_zero P Q hu,
    exactOverlapRootMean_zero]
  simp only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero]

private theorem exactDualTopNorm_zero {d : ℕ} (P : ExactOverlapTopParameters)
    (Q : TriadicCube d) (hu : ExactOverlapIntegrable Q (fun _ : Vec d => (0 : ℝ))) :
    exactOverlapTopNorm P Q (fun _ => (0 : ℝ)) hu = 0 := by
  rw [exactOverlapTopNorm_eq, exactDualTopSeminorm_zero P Q hu,
    exactOverlapRootMean_zero]
  simp only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero]

/-- The zero full test in the exact `q = 1` branch. -/
noncomputable def exactDualQOneFullZeroTest {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) : ExactDualQOneFullTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  norm_le_one := by
    rw [exactDualTopNorm_zero]
    exact zero_le_one

/-- The zero hatted test in the exact `q = 1` branch. -/
noncomputable def exactDualQOneHattedZeroTest {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) : ExactDualQOneHattedTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  seminorm_le_one := by
    rw [exactDualTopSeminorm_zero]
    exact zero_le_one
  root_mean_zero := exactOverlapRootMean_zero Q _

/-- The zero full test in the finite interior branch. -/
noncomputable def exactDualFiniteFullZeroTest {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) : ExactDualFiniteFullTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  norm_le_one := by
    rw [exactDualFiniteNorm_zero]
    exact zero_le_one

/-- The zero hatted test in the finite interior branch. -/
noncomputable def exactDualFiniteHattedZeroTest {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) : ExactDualFiniteHattedTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  seminorm_le_one := by
    rw [exactDualFiniteSeminorm_zero]
    exact zero_le_one
  root_mean_zero := exactOverlapRootMean_zero Q _

/-- The zero full test in the `q = infinity` branch. -/
noncomputable def exactDualTopFullZeroTest {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) : ExactDualTopFullTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  norm_le_one := by
    rw [exactDualFiniteNorm_zero]
    exact zero_le_one

/-- The zero hatted test in the `q = infinity` branch. -/
noncomputable def exactDualTopHattedZeroTest {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) : ExactDualTopHattedTest P Q where
  g := fun _ => 0
  parentMemLp := MeasureTheory.memLp_const (0 : ℝ)
  seminorm_le_one := by
    rw [exactDualFiniteSeminorm_zero]
    exact zero_le_one
  root_mean_zero := exactOverlapRootMean_zero Q _

theorem exactDualQOneFullTest_nonempty {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualQOneFullTest P Q) :=
  ⟨exactDualQOneFullZeroTest P Q⟩

theorem exactDualQOneHattedTest_nonempty {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualQOneHattedTest P Q) :=
  ⟨exactDualQOneHattedZeroTest P Q⟩

theorem exactDualFiniteFullTest_nonempty {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualFiniteFullTest P Q) :=
  ⟨exactDualFiniteFullZeroTest P Q⟩

theorem exactDualFiniteHattedTest_nonempty {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualFiniteHattedTest P Q) :=
  ⟨exactDualFiniteHattedZeroTest P Q⟩

theorem exactDualTopFullTest_nonempty {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualTopFullTest P Q) :=
  ⟨exactDualTopFullZeroTest P Q⟩

theorem exactDualTopHattedTest_nonempty {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) : Nonempty (ExactDualTopHattedTest P Q) :=
  ⟨exactDualTopHattedZeroTest P Q⟩

/-- The canonical parent-space certificate for zero data in any finite real
exponent used by the exact dual objects. -/
theorem exactDualZeroMemLp {d : ℕ} (Q : TriadicCube d) (p : ℝ) :
    MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ)) (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q) :=
  MeasureTheory.memLp_const (0 : ℝ)

theorem exactDualPairingFromHolder_zero_left {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (g : Vec d → ℝ) (hp : 1 < p)
    (hzero : MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ)) (ENNReal.ofReal p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.ofReal (exactDualConjExponent p))
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualPairingFromHolder Q p (fun _ => (0 : ℝ)) g hp hzero hg = 0 := by
  rw [exactDualPairingFromHolder_eq]
  simp only [zero_mul, MeasureTheory.integral_zero, abs_zero,
    ENNReal.ofReal_zero]

private theorem exactDual_iSup_zero {ι : Sort*} (a : ι → ℝ≥0∞)
    (ha : ∀ i, a i = 0) : (⨆ i, a i) = 0 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [ha i]
  · exact bot_le

theorem exactDualQOneFullNorm_zero {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) :
    exactDualQOneFullNorm P Q (fun _ => (0 : ℝ)) (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualQOneFullNorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

theorem exactDualQOneHattedSeminorm_zero {d : ℕ} (P : ExactDualQOneParameters)
    (Q : TriadicCube d) :
    exactDualQOneHattedSeminorm P Q (fun _ => (0 : ℝ)) (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualQOneHattedSeminorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

theorem exactDualFiniteFullNorm_zero {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) :
    exactDualFiniteFullNorm P Q (fun _ => (0 : ℝ)) (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualFiniteFullNorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

theorem exactDualFiniteHattedSeminorm_zero {d : ℕ} (P : ExactDualFiniteParameters)
    (Q : TriadicCube d) :
    exactDualFiniteHattedSeminorm P Q (fun _ => (0 : ℝ))
      (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualFiniteHattedSeminorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

theorem exactDualTopFullNorm_zero {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) :
    exactDualTopFullNorm P Q (fun _ => (0 : ℝ)) (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualTopFullNorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

theorem exactDualTopHattedSeminorm_zero {d : ℕ} (P : ExactDualTopParameters)
    (Q : TriadicCube d) :
    exactDualTopHattedSeminorm P Q (fun _ => (0 : ℝ)) (exactDualZeroMemLp Q P.p) = 0 := by
  rw [exactDualTopHattedSeminorm_eq]
  apply exactDual_iSup_zero
  intro T
  exact exactDualPairingFromHolder_zero_left Q P.p T.g P.p_one_lt
    (exactDualZeroMemLp Q P.p) T.parentMemLp

end Homogenization
