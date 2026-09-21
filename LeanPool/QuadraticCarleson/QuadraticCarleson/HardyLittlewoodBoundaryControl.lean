/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySharpSmoothAdapter
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximalLp
import LeanPool.QuadraticCarleson.QuadraticCarleson.ExtendedWeakL1Combinators
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximalProof
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleSparseAdapter
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleBlockWeak
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryOscillatoryScaling
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositivePrincipalValueEndpoints

/-!
# The Hardy--Littlewood boundary term in the sharp/smooth KL comparison

The smooth-to-sharp comparison produces one copy of the centered
Hardy--Littlewood maximal function, common to all modulations and truncation
radii.  This file packages that concrete boundary operator on `L0Infinity`.
In particular, its output is finite everywhere, measurable and locally
integrable, and it has the explicit weak `(1,1)` constant `4`.

This is also the operational reason that the boundary term need not be put
inside the individual Krause--Lacey sparse forms: after taking the finite
modulation maximum it is still a single maximal function, hence incurs no
cardinality loss.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace HardyLittlewoodBoundaryControl

open ExtendedWeakL1Combinators
open QuadraticHilbertMaximalMeasurable
open KrauseLaceyFiniteRadiusAdapter
open KrauseLaceySharpSmoothAdapter
open LacunaryMiddleSparseAdapter LacunaryMiddleRange
open LacunaryMiddleBlockWeak
open LacunaryOscillatoryScaling
open PositivePrincipalValueEndpoints HilbertPrincipalValueClosure


noncomputable section

/-- A pointwise bound passes through every positive centered average. -/
theorem centeredAverage_le_of_forall_le {F : ℝ → ℝ≥0∞} {D : ℝ≥0∞}
    (hF : ∀ x, F x ≤ D) {r x : ℝ} (hr : 0 < r) :
    centeredAverage r F x ≤ D := by
  have hd : ENNReal.ofReal (2 * r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have htop : ENNReal.ofReal (2 * r) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold centeredAverage
  calc
    (∫⁻ y in closedBall x r, F y) / ENNReal.ofReal (2 * r) ≤
        (∫⁻ _y in closedBall x r, D) / ENNReal.ofReal (2 * r) := by
      exact ENNReal.div_le_div_right (lintegral_mono hF) _
    _ = (D * ENNReal.ofReal (2 * r)) / ENNReal.ofReal (2 * r) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_closedBall]
    _ = D := ENNReal.mul_div_cancel_right hd htop

/-- The centered rational-radius maximal function preserves a uniform
pointwise bound.  In particular it never takes the value `∞` on a bounded
input. -/
theorem centeredHardyLittlewoodMaximal_le_of_forall_le
    {F : ℝ → ℝ≥0∞} {D : ℝ≥0∞} (hF : ∀ x, F x ≤ D) (x : ℝ) :
    centeredHardyLittlewoodMaximal F x ≤ D := by
  apply iSup_le
  intro q
  exact centeredAverage_le_of_forall_le hF (by exact_mod_cast q.property)

theorem centeredHardyLittlewoodMaximal_enorm_ne_top (f : L0Infinity) (x : ℝ) :
    centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x ≠ ∞ := by
  rcases f.bounded_toFun with ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hC 0)
  have hpoint (y : ℝ) : ‖f y‖ₑ ≤ ENNReal.ofReal C := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  exact ne_of_lt ((centeredHardyLittlewoodMaximal_le_of_forall_le hpoint x).trans_lt
    ENNReal.ofReal_lt_top)

/-- The real-valued Hardy--Littlewood boundary operator occurring in the
sharp/smooth comparison. -/
noncomputable def centeredHardyLittlewoodBoundaryOperator : TestOperator :=
  fun f x ↦ ((centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x).toReal : ℂ)

@[simp] theorem norm_centeredHardyLittlewoodBoundaryOperator
    (f : L0Infinity) (x : ℝ) :
    ‖centeredHardyLittlewoodBoundaryOperator f x‖ =
      (centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x).toReal := by
  simp [centeredHardyLittlewoodBoundaryOperator]

@[simp] theorem enorm_centeredHardyLittlewoodBoundaryOperator
    (f : L0Infinity) (x : ℝ) :
    ‖centeredHardyLittlewoodBoundaryOperator f x‖ₑ =
      centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [← ofReal_norm_eq_enorm, norm_centeredHardyLittlewoodBoundaryOperator,
    ENNReal.ofReal_toReal (centeredHardyLittlewoodMaximal_enorm_ne_top f x)]

theorem measurable_centeredHardyLittlewoodBoundaryOperator (f : L0Infinity) :
    Measurable (centeredHardyLittlewoodBoundaryOperator f) := by
  exact Complex.measurable_ofReal.comp
    ((measurable_centeredHardyLittlewoodMaximal f.measurable_toFun.enorm).ennreal_toReal)

private theorem eLpNorm_two_sq_lintegral_boundary {E : Type*} [ENorm E]
    (F : ℝ → E) :
    eLpNorm F 2 volume ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

/-- The boundary operator is locally integrable.  The proof uses the already
proved strong `L²` maximal theorem. -/
theorem centeredHardyLittlewoodBoundaryOperator_locallyIntegrable
    (f : L0Infinity) :
    LocallyIntegrable (centeredHardyLittlewoodBoundaryOperator f) volume := by
  rcases f.bounded_toFun with ⟨C, hC⟩
  have hf2 : MemLp f 2 volume :=
    f.hasCompactSupport_toFun.memLp_of_bound f.measurable_toFun.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hM2 : MemLp
      (fun x ↦ centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) 2 volume := by
    refine ⟨(measurable_centeredHardyLittlewoodMaximal
      f.measurable_toFun.enorm).aestronglyMeasurable, ?_⟩
    have hle := centeredHardyLittlewoodMaximal_rpow_lintegral_le
      f.measurable_toFun.enorm (fun _y ↦ enorm_ne_top) (p := 2) (by norm_num)
    have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
      have hp : eLpNorm f 2 volume ^ 2 < ∞ :=
        ENNReal.pow_lt_top (n := 2) hf2.eLpNorm_lt_top
      simpa only [eLpNorm_two_sq_lintegral_boundary, ENNReal.rpow_two] using hp.ne
    have hsq : (∫⁻ x,
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x ^ (2 : ℝ)) < ∞ :=
      hle.trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin))
    have hp : eLpNorm
        (fun x ↦ centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x)
          2 volume ^ 2 < ∞ := by
      simpa only [eLpNorm_two_sq_lintegral_boundary, enorm_eq_self,
        ENNReal.rpow_two] using hsq
    exact (ENNReal.pow_lt_top_iff.mp hp).resolve_right (by norm_num)
  have hcomplex : MemLp (centeredHardyLittlewoodBoundaryOperator f) 2 volume := by
    apply hM2.of_le_enorm
      (measurable_centeredHardyLittlewoodBoundaryOperator f).aestronglyMeasurable
    filter_upwards [] with x
    simpa only [enorm_centeredHardyLittlewoodBoundaryOperator, enorm_eq_self]
      using (le_refl (centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x))
  exact hcomplex.locallyIntegrable (by norm_num)

/-- Explicit weak `(1,1)` distribution bound for the concrete boundary
operator. -/
theorem centeredHardyLittlewoodBoundaryOperator_hasWeakOneOneBound :
    HasWeakOneOneBound 4
      (fun f x ↦ ‖centeredHardyLittlewoodBoundaryOperator f x‖) := by
  intro f a ha
  have htop (x : ℝ) :
      centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x ≠ ∞ :=
    centeredHardyLittlewoodMaximal_enorm_ne_top f x
  have hset :
      {x | a < ‖centeredHardyLittlewoodBoundaryOperator f x‖} =
        {x | ENNReal.ofReal a <
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x} := by
    ext x
    simp only [mem_setOf_eq, norm_centeredHardyLittlewoodBoundaryOperator]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ha.le (htop x)).symm
  rw [hset]
  simpa only [ENNReal.ofReal_ofNat] using
    centeredHardyLittlewoodMaximal_weak_bound
      (fun y ↦ ‖f y‖ₑ) (ENNReal.ofReal a)

/-- The sharp/smooth comparison written with the concrete boundary operator.
The rightmost term is independent of the finite radius family. -/
theorem finiteRadiusSharpMax_enorm_le_smoothHighPassMax_add_boundary
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ENNReal.ofReal
        ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖ ≤
      ENNReal.ofReal
          ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ +
        16 * ‖centeredHardyLittlewoodBoundaryOperator f x‖ₑ := by
  simpa only [enorm_centeredHardyLittlewoodBoundaryOperator] using
    finiteRadiusSharpMax_enorm_le_smoothHighPassMax_add_maximal
      lam s f x

/-- Operational endpoint transfer for one finite radius family.  A weak
bound for the smooth KL output plus the common Hardy--Littlewood boundary
term gives a weak bound for the genuine sharp truncation output, with no
dependence on the number of radii or modulations. -/
theorem finiteRadiusSharpMax_hasExtendedWeakL1Bound_of_smooth
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) {A : ℝ}
    (hSmooth : KaltonPaperApplication.HasExtendedWeakL1Bound volume A
      (fun x ↦ ENNReal.ofReal
        ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖)) :
    KaltonPaperApplication.HasExtendedWeakL1Bound volume
      (4 * A + 128 * (∫⁻ x, ‖f x‖ₑ).toReal)
      (fun x ↦ ENNReal.ofReal
        ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖) := by
  have hM := hasExtendedWeakL1Bound_centeredHardyLittlewoodMaximal_enorm
    f.measurable_toFun f.integrable
  have hpoint (x : ℝ) :
      ENNReal.ofReal
          ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖ ≤
        2 * ENNReal.ofReal
            ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
    exact (finiteRadiusSharpMax_enorm_le_smoothHighPassMax_add_maximal lam s f x).trans
      (add_le_add (by
        simpa only [two_mul] using
          (le_add_right (le_refl (ENNReal.ofReal
            ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖)))) le_rfl)
  have h := hasExtendedWeakL1Bound_of_le_two_mul_add_sixteen_mul
    hpoint hSmooth hM
  convert h using 1 <;> ring

/-- The finite smooth high-pass family indexed by one paper modulation block.
This is the family to which the genuine KL sparse recursion applies. -/
def finiteRadiusSmoothHighPassBlockFamily
    (B : ℕ) (tau : ℤ) (s : Finset densePositiveRadii) :
    Fin (Q B tau).card → TestOperator :=
  fun j ↦ finiteRadiusSmoothHighPassMaxTestOperator
    (dyadicModulation (modulationBlockIndex B tau j)) s

/-- Exact remaining smooth KL input.  Unlike the old sharp-truncation
interface, this contains no Hardy--Littlewood boundary term. -/
def HasUniformFiniteRadiusSmoothSparseBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (lam : ℝ), lam ≠ 0 → ∀ s : Finset densePositiveRadii,
    (∀ f : L0Infinity,
      LocallyIntegrable (finiteRadiusSmoothHighPassMaxTestOperator lam s f) volume) ∧
    ∀ p : ℝ, 1 < p → p < 2 →
      IsSparseOnePBounded p
          (absoluteValueOperator (finiteRadiusSmoothHighPassMaxTestOperator lam s)) ∧
        sparseOnePNorm p
            (absoluteValueOperator (finiteRadiusSmoothHighPassMaxTestOperator lam s)) ≤
          A * holderConjugate p

theorem finiteRadiusSmoothHighPassBlockFamily_sparseHypothesis
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A)
    (B : ℕ) (tau : ℤ) (s : Finset densePositiveRadii) :
    FiniteSparseMaximalHypothesis
      (finiteRadiusSmoothHighPassBlockFamily B tau s) A := by
  refine ⟨hA.1, ?_, ?_, ?_⟩
  · intro j f
    exact (hA.2 (dyadicModulation (modulationBlockIndex B tau j))
      (dyadicModulation_pos (modulationBlockIndex B tau j)).ne' s).1 f
  · intro j
    exact finiteRadiusSmoothHighPassMaxTestOperator_isSublinear _ _
  · intro p hp hp2 j
    exact (hA.2 (dyadicModulation (modulationBlockIndex B tau j))
      (dyadicModulation_pos (modulationBlockIndex B tau j)).ne' s).2 p hp hp2

/-- The proved finite sparse-maximal theorem applied to the smooth KL
family. -/
theorem finiteRadiusSmoothHighPassBlockFamily_hasWeakOneOneBound
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A)
    (B : ℕ) (tau : ℤ) (s : Finset densePositiveRadii) :
    HasWeakOneOneBound
      (finiteSparseMaximalUniversalConstant * A * paperLog 1 B ^ 2)
      (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s)) := by
  have h := finiteSparseMaximal_hasWeakOneOneBound
    (finiteRadiusSmoothHighPassBlockFamily B tau s) A
    (finiteRadiusSmoothHighPassBlockFamily_sparseHypothesis hA B tau s)
  simpa only [card_Q] using h

private theorem coe_nnreal_finset_sup_boundary {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (u : alpha → NNReal) :
    (↑(s.sup u) : ℝ≥0∞) = s.sup fun a ↦ (u a : ℝ≥0∞) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sup_insert, ih]

/-- A common extended-valued error can be moved outside a finite pointwise
maximum without being repeated once per member. -/
theorem ofReal_finiteMax_le_of_common_error {N : ℕ}
    (T U : Fin N → TestOperator) (f : L0Infinity) (x : ℝ) (E : ℝ≥0∞)
    (hTU : ∀ j, ENNReal.ofReal ‖T j f x‖ ≤ ENNReal.ofReal ‖U j f x‖ + E) :
    ENNReal.ofReal (finiteMax T f x) ≤
      ENNReal.ofReal (finiteMax U f x) + E := by
  classical
  simp only [finiteMax, ENNReal.ofReal_coe_nnreal]
  rw [coe_nnreal_finset_sup_boundary, coe_nnreal_finset_sup_boundary]
  apply Finset.sup_le
  intro j hj
  calc
    (↑‖T j f x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T j f x‖ := by
      rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    _ ≤ ENNReal.ofReal ‖U j f x‖ + E := hTU j
    _ = (↑‖U j f x‖₊ : ℝ≥0∞) + E := by
      rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    _ ≤ (Finset.univ.sup fun i : Fin N ↦ (↑‖U i f x‖₊ : ℝ≥0∞)) + E := by
      gcongr
      exact Finset.le_sup (s := Finset.univ)
        (f := fun i : Fin N ↦ (↑‖U i f x‖₊ : ℝ≥0∞)) (Finset.mem_univ j)

/-- The sharp modulation-block maximum is bounded by the smooth modulation-
block maximum plus one, not `B`, Hardy--Littlewood boundary term. -/
theorem finiteRadiusSharpBlock_finiteMax_le_smooth_add_boundary
    (B : ℕ) (tau : ℤ) (s : Finset densePositiveRadii)
    (f : L0Infinity) (x : ℝ) :
    ENNReal.ofReal (finiteMax
      (finiteRadiusQuadraticHilbertBlockFamily B tau s) f x) ≤
      ENNReal.ofReal (finiteMax
        (finiteRadiusSmoothHighPassBlockFamily B tau s) f x) +
        16 * ‖centeredHardyLittlewoodBoundaryOperator f x‖ₑ := by
  apply ofReal_finiteMax_le_of_common_error
  intro j
  exact finiteRadiusSharpMax_enorm_le_smoothHighPassMax_add_boundary
    (dyadicModulation (modulationBlockIndex B tau j)) s f x

/-- The full finite modulation maximum of genuine sharp truncations inherits
the logarithmic smooth sparse-maximal bound, plus one universal boundary
constant.  Crucially, `128` is not multiplied by the block cardinality. -/
theorem finiteRadiusSharpBlockFamily_hasWeakOneOneBound_of_smoothSparse
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A)
    (B : ℕ) (tau : ℤ) (s : Finset densePositiveRadii) :
    HasWeakOneOneBound
      (4 * (finiteSparseMaximalUniversalConstant * A * paperLog 1 B ^ 2) + 128)
      (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B tau s)) := by
  let C : ℝ := finiteSparseMaximalUniversalConstant * A * paperLog 1 B ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [finiteSparseMaximalUniversalConstant_pos, hA.1]
  have hsmooth : HasWeakOneOneBound C
      (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s)) := by
    simpa only [C] using
      finiteRadiusSmoothHighPassBlockFamily_hasWeakOneOneBound hA B tau s
  intro f a ha
  let mass : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ
  have hmass : mass ≠ ∞ := by
    simpa only [mass] using f.integrable.hasFiniteIntegral.ne
  have hsmoothExt : KaltonPaperApplication.HasExtendedWeakL1Bound volume
      (C * mass.toReal)
      (fun x ↦ ENNReal.ofReal
        (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s) f x)) := by
    refine ⟨mul_nonneg hC ENNReal.toReal_nonneg, ?_⟩
    intro b hb
    calc
      ENNReal.ofReal b * volume
          {x | ENNReal.ofReal b < ENNReal.ofReal
            (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s) f x)} =
          ENNReal.ofReal b * volume
            {x | b < finiteMax
              (finiteRadiusSmoothHighPassBlockFamily B tau s) f x} := by
        congr 2
        ext x
        simp only [mem_setOf_eq]
        rw [ENNReal.ofReal_lt_iff_lt_toReal hb.le ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by
            unfold finiteMax
            exact NNReal.coe_nonneg _)]
      _ ≤ ENNReal.ofReal C * mass := hsmooth f b hb
      _ = ENNReal.ofReal (C * mass.toReal) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hmass]
  have hmaximal := hasExtendedWeakL1Bound_centeredHardyLittlewoodMaximal_enorm
    f.measurable_toFun f.integrable
  have hpoint (x : ℝ) :
      ENNReal.ofReal
          (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B tau s) f x) ≤
        2 * ENNReal.ofReal
            (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s) f x) +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
    have hbase := finiteRadiusSharpBlock_finiteMax_le_smooth_add_boundary
      B tau s f x
    rw [enorm_centeredHardyLittlewoodBoundaryOperator] at hbase
    exact hbase.trans (add_le_add (by
        simpa only [two_mul] using
          (le_add_right (le_refl (ENNReal.ofReal
            (finiteMax (finiteRadiusSmoothHighPassBlockFamily B tau s) f x))))) le_rfl)
  have hcombined := hasExtendedWeakL1Bound_of_le_two_mul_add_sixteen_mul
    hpoint hsmoothExt hmaximal
  have hconstant : 4 * (C * mass.toReal) + 32 * (4 * mass.toReal) =
      (4 * C + 128) * mass.toReal := by ring
  have hout := hcombined.2 a ha
  rw [hconstant] at hout
  calc
    ENNReal.ofReal a * volume
        {x | a < finiteMax
          (finiteRadiusQuadraticHilbertBlockFamily B tau s) f x} =
      ENNReal.ofReal a * volume
        {x | ENNReal.ofReal a < ENNReal.ofReal
          (finiteMax (finiteRadiusQuadraticHilbertBlockFamily B tau s) f x)} := by
      congr 2
      ext x
      simp only [mem_setOf_eq]
      rw [ENNReal.ofReal_lt_iff_lt_toReal ha.le ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by
          unfold finiteMax
          exact NNReal.coe_nonneg _)]
    _ ≤ ENNReal.ofReal ((4 * C + 128) * mass.toReal) := hout
    _ = ENNReal.ofReal (4 * C + 128) * mass := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmass]
    _ = ENNReal.ofReal
          (4 * (finiteSparseMaximalUniversalConstant * A * paperLog 1 B ^ 2) + 128) *
        ∫⁻ x, ‖f x‖ₑ := by rfl

/-- The smooth KL sparse theorem supplies the all-radius frozen quadratic-
Hilbert block.  The common boundary constant is absorbed into the existing
`log₁(B)²` factor using `log₁(B) ≥ 1`. -/
theorem hasLogSquaredFrozenHilbertBlockWeakBounds_of_smoothSparse
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A)
    (f : L0Infinity) (B : ℕ → ℕ) (c : ℕ) :
    HasLogSquaredFrozenHilbertBlockWeakBounds (f : ℝ → ℂ) B c
      (4 * (finiteSparseMaximalUniversalConstant * A) + 128) := by
  have hK : 0 ≤ finiteSparseMaximalUniversalConstant :=
    finiteSparseMaximalUniversalConstant_pos.le
  have hKA : 0 ≤ finiteSparseMaximalUniversalConstant * A :=
    mul_nonneg hK hA.1
  refine ⟨by nlinarith, ?_⟩
  intro k tau
  let L : ℝ := paperLog 1 (B k : ℝ)
  let D : ℝ :=
    (4 * (finiteSparseMaximalUniversalConstant * A) + 128) * L ^ 2
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact PositiveEndpointOptimization.one_le_paperLog_one (by positivity)
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by nlinarith) (sq_nonneg _)
  apply
    hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_restrict_of_uniform_finiteRadii
      f k (B k) c tau hD
  intro s
  have hsmall := finiteRadiusSharpBlockFamily_hasWeakOneOneBound_of_smoothSparse
    hA (B k) tau s
  apply hsmall.mono
  dsimp only [D, L]
  have hA0 : 0 ≤ A := hA.1
  nlinarith [mul_nonneg hK hA0]

/-- Paper-facing uniform frozen-block conclusion with the finite sparse-
maximal lemma and both deterministic Hardy--Littlewood boundary passages
fully discharged.  Only the genuine smooth KL sparse estimate remains. -/
theorem hasUniformL0LogSquaredFrozenBlockWeakBounds_of_smoothSparse
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A) :
    HasUniformL0LogSquaredFrozenBlockWeakBounds
      (4 * (4 * (finiteSparseMaximalUniversalConstant * A) + 128) + 128) := by
  intro f
  exact logSquaredFrozenBlockWeakBounds_of_hilbert
    f.measurable_toFun f.integrable
    (hasLogSquaredFrozenHilbertBlockWeakBounds_of_smoothSparse
      hA f PositiveHighHeightEstimate.lacunaryHighCutoff 0)

/-- Strongest downstream lacunary endpoint exposed by this adapter.  Its only
remaining analytic inputs are the ordinary Hilbert maximal theorem and the
genuine smooth KL sparse estimate. -/
theorem lacunary_principalValue_endpoint_of_smoothSparse
    {CH : ℝ≥0∞} (hH : HasUniformHilbertMaximalWeakBound CH)
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  lacunary_principalValue_endpoint hH
    (hasUniformL0LogSquaredFrozenBlockWeakBounds_of_smoothSparse hA)


end
end HardyLittlewoodBoundaryControl
end QuadraticCarleson
