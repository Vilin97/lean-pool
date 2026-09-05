/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Sym.Card
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Ehrhart volume inequality: Foundations

Foundational convex, lattice, Bergman, and variational constructions.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

/-- The ambient real vector space in dimension `n`. -/
public
abbrev Space (n : ℕ) := Fin n → ℝ

/-- The real point associated to an integer lattice vector. -/
public
def integerPoint (n : ℕ) (z : Fin n → ℤ) : Space n :=
  fun i => (z i : ℝ)

/-- The standard closed simplex. -/
public
def standardSimplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

/-- The affine dilation taking the standard simplex to its centered extremal form. -/
public
def simplexDilation (n : ℕ) (x : Space n) : Space n :=
  fun i => ((n : ℝ) + 1) * x i - 1

/-- The centered simplex that attains the sharp Ehrhart volume bound. -/
public
def centeredSimplex (n : ℕ) : Set (Space n) :=
  simplexDilation n '' standardSimplex n

/-- Euclidean volume, converted from `ℝ≥0∞` to `ℝ`. -/
public
def normalizedVolume {n : ℕ} (K : Set (Space n)) : ℝ :=
  ((volume : Measure (Space n)) K).toReal

/-- The volume-normalized barycenter of a measurable body. -/
public
def barycenter {n : ℕ} (K : Set (Space n)) : Space n :=
  (normalizedVolume K)⁻¹ • ∫ x in K, x ∂(volume : Measure (Space n))

/-- The integer lattice points lying in the interior of a body. -/
public
def interiorLatticePoints {n : ℕ} (K : Set (Space n)) : Set (Fin n → ℤ) :=
  {z | integerPoint n z ∈ interior K}

/-- A compact full-dimensional convex body centered at its unique interior lattice point. -/
public
structure CenteredBody (n : ℕ) where
  /-- The underlying point set. -/
  carrier : Set (Space n)
  /-- Convexity of the body. -/
  convex : Convex ℝ carrier
  /-- Compactness of the body. -/
  compact : IsCompact carrier
  /-- Nonempty interior. -/
  fullDimensional : (interior carrier).Nonempty
  /-- The body has barycenter zero. -/
  centered : barycenter carrier = 0
  /-- The origin is the unique interior lattice point. -/
  uniqueInteriorLatticePoint : interiorLatticePoints carrier = {0}

private theorem CenteredBody.volume_pos {n : ℕ} (K : CenteredBody n) :
    0 < normalizedVolume K.carrier := by
  unfold normalizedVolume
  exact ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior
      (volume : Measure (Space n)) K.fullDimensional).ne'
    K.compact.measure_ne_top

/-- The sharp volume constant in dimension `n`. -/
public
def sharpConstant (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)

namespace BodyMeasure

open Set MeasureTheory
open scoped ENNReal

private theorem volume_interior_eq_volume {n : ℕ} (K : CenteredBody n) :
    (volume : Measure (Space n)) (interior K.carrier) =
      (volume : Measure (Space n)) K.carrier := by
  exact measure_interior_of_null_frontier
    (K.convex.addHaar_frontier (volume : Measure (Space n)))

end BodyMeasure

namespace LatticeAsymptotics

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Pointwise Topology

private def scaledIntegerLattice (n k : ℕ) : Set (Space n) :=
  (k : ℝ)⁻¹ •
    (↑(Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin n)))) : Set (Space n))

private def monomialIndex {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : Set (Space n) :=
  interior K.carrier ∩ scaledIntegerLattice n k

private theorem mem_scaledIntegerLattice_iff {n k : ℕ} (hk : 0 < k)
    (x : Space n) :
    x ∈ scaledIntegerLattice n k ↔
      ∀ i, (k : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
  exact BoxIntegral.unitPartition.mem_smul_span_iff
    (n := k) (v := x)

private theorem mem_monomialIndex_iff {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (x : Space n) :
    x ∈ monomialIndex K k ↔
      x ∈ interior K.carrier ∧
        ∀ i, (k : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) := by
  rw [monomialIndex, Set.mem_inter_iff,
    mem_scaledIntegerLattice_iff hk]

private theorem zero_mem_interior {n : ℕ}
    (K : CenteredBody n) :
    (0 : Space n) ∈ interior K.carrier := by
  have hz :
      (0 : Fin n → ℤ) ∈ interiorLatticePoints K.carrier := by
    rw [K.uniqueInteriorLatticePoint]
    exact Set.mem_singleton 0
  change integerPoint n (0 : Fin n → ℤ) ∈
    interior K.carrier at hz
  have hzero : integerPoint n (0 : Fin n → ℤ) =
      (0 : Space n) := by
    funext i
    simp only [integerPoint, Pi.zero_apply, Int.cast_zero]
  rwa [hzero] at hz

private theorem mem_monomialIndex_one_iff {n : ℕ}
    (K : CenteredBody n) (x : Space n) :
    x ∈ monomialIndex K 1 ↔ x = 0 := by
  classical
  constructor
  · intro hx
    obtain ⟨hxinterior, hxinteger⟩ :=
      (mem_monomialIndex_iff K (by decide) x).mp hx
    have hcoordinates : ∀ i, ∃ m : ℤ, (m : ℝ) = x i := by
      intro i
      obtain ⟨m, hm⟩ := hxinteger i
      refine ⟨m, ?_⟩
      simpa only [algebraMap_int_eq, eq_intCast, Nat.cast_one, one_mul] using hm
    choose z hz using hcoordinates
    have hreal : integerPoint n z = x := by
      funext i
      exact hz i
    have hmem : z ∈ interiorLatticePoints K.carrier := by
      change integerPoint n z ∈ interior K.carrier
      rwa [hreal]
    have hzero : z = 0 := by
      have hzsingleton : z ∈ ({0} : Set (Fin n → ℤ)) := by
        rw [← K.uniqueInteriorLatticePoint]
        exact hmem
      simpa only [mem_singleton_iff] using hzsingleton
    rw [← hreal, hzero]
    funext i
    simp only [integerPoint, Pi.zero_apply, Int.cast_zero]
  · rintro rfl
    refine (mem_monomialIndex_iff K (by decide) 0).mpr
      ⟨zero_mem_interior K, ?_⟩
    intro i
    refine ⟨0, ?_⟩
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_zero, Nat.cast_one, Pi.zero_apply, mul_zero]

private theorem monomial_count_div_pow_tendsto_volume {n : ℕ}
    (K : CenteredBody n) :
    Tendsto
      (fun k : ℕ =>
        (Nat.card (monomialIndex K k) : ℝ) / (k : ℝ) ^ n)
      atTop (𝓝 (normalizedVolume K.carrier)) := by
  have hbounded : Bornology.IsBounded (interior K.carrier) :=
    K.compact.isBounded.subset interior_subset
  have hmeas : MeasurableSet (interior K.carrier) :=
    isOpen_interior.measurableSet
  have hfront :
      (volume : Measure (Space n))
        (frontier (interior K.carrier)) = 0 :=
    K.convex.interior.addHaar_frontier
      (volume : Measure (Space n))
  have hvolume :
      (volume : Measure (Space n)).real
        (interior K.carrier) =
      normalizedVolume K.carrier := by
    unfold Measure.real normalizedVolume
    rw [BodyMeasure.volume_interior_eq_volume K]
  simpa only [monomialIndex, scaledIntegerLattice, Nat.card_coe_set_eq, Fintype.card_fin,
    hvolume] using
    (tendsto_card_div_pow_atTop_volume
      (s := interior K.carrier) hbounded hmeas hfront)

end LatticeAsymptotics

namespace SupportFunction

open Set
open scoped BigOperators

private def pairing {n : ℕ} (u x : Space n) : ℝ :=
  ∑ i, u i * x i

private def supportFunction {n : ℕ}
    (K : Set (Space n)) (x : Space n) : ℝ :=
  sSup ((fun y => pairing y x) '' K)

private theorem continuous_pairing_left {n : ℕ} (x : Space n) :
    Continuous (fun u : Space n => pairing u x) := by
  unfold pairing
  exact continuous_finsetSum Finset.univ
    (fun i _ => (continuous_apply i).mul continuous_const)

private theorem continuous_pairing_right {n : ℕ} (u : Space n) :
    Continuous (fun x : Space n => pairing u x) := by
  unfold pairing
  exact continuous_finsetSum Finset.univ
    (fun i _ => continuous_const.mul (continuous_apply i))

private theorem pairing_le_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) {u : Space n}
    (hu : u ∈ K) (x : Space n) :
    pairing u x ≤ supportFunction K x := by
  unfold supportFunction
  exact le_csSup
    (hcompact.bddAbove_image (continuous_pairing_left x).continuousOn)
    (Set.mem_image_of_mem _ hu)

private theorem supportFunction_le {n : ℕ}
    {K : Set (Space n)} (hnonempty : K.Nonempty)
    (x : Space n) {c : ℝ}
    (hbound : ∀ y ∈ K, pairing y x ≤ c) :
    supportFunction K x ≤ c := by
  unfold supportFunction
  apply csSup_le (hnonempty.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hbound y hy

private theorem supportFunction_attained {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty) (x : Space n) :
    ∃ y ∈ K, supportFunction K x = pairing y x := by
  obtain ⟨y, hy, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty
      (continuous_pairing_left x).continuousOn
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · exact supportFunction_le hnonempty x (fun z hz => hmax hz)
  · exact pairing_le_supportFunction hcompact hy x

private def signVector {n : ℕ} (x : Space n) : Space n :=
  fun i => if 0 ≤ x i then 1 else -1

private theorem norm_signVector_le_one {n : ℕ} (x : Space n) :
    ‖signVector x‖ ≤ (1 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [Real.norm_eq_abs]
  dsimp [signVector]
  split_ifs <;> norm_num

private theorem norm_le_sum_abs {n : ℕ} (x : Space n) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hnonneg : 0 ≤ ∑ i, |x i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum
    (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

private theorem pairing_signVector {n : ℕ} (x : Space n) :
    pairing (signVector x) x = ∑ i, |x i| := by
  unfold pairing signVector
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ x i
  · simp only [hi, ↓reduceIte, one_mul, abs_of_nonneg hi]
  · have hnegative : x i < 0 := lt_of_not_ge hi
    simp only [hi, ↓reduceIte, neg_mul, one_mul, abs_of_neg hnegative]

private theorem pairing_add_left {n : ℕ}
    (u v x : Space n) :
    pairing (u + v) x = pairing u x + pairing v x := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem pairing_smul_left {n : ℕ}
    (a : ℝ) (u x : Space n) :
    pairing (a • u) x = a * pairing u x := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem interior_gap {n : ℕ} {K : Set (Space n)}
    (hcompact : IsCompact K) {u : Space n}
    (hu : u ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      δ * ‖x‖ ≤ supportFunction K x - pairing u x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  have hhalf : 0 < r / 2 := half_pos hr
  refine ⟨r / 2, hhalf, ?_⟩
  intro x
  have hscaled_norm : ‖(r / 2) • signVector x‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf]
    exact mul_le_of_le_one_right hhalf.le (norm_signVector_le_one x)
  have hmem_ball : u + (r / 2) • signVector x ∈ Metric.ball u r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖u + (r / 2) • signVector x - u‖ ≤ r / 2 := by
      simpa only [add_sub_cancel_left] using hscaled_norm
    exact lt_of_le_of_lt hnorm (half_lt_self hr)
  have hmem : u + (r / 2) • signVector x ∈ K :=
    interior_subset (hball hmem_ball)
  have hsupport := pairing_le_supportFunction hcompact hmem x
  rw [pairing_add_left, pairing_smul_left, pairing_signVector] at hsupport
  have hnorm := norm_le_sum_abs x
  have hscaled := mul_le_mul_of_nonneg_left hnorm hhalf.le
  linarith

end SupportFunction

namespace MonomialIntegrability

open Set MeasureTheory
open scoped BigOperators

private theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|))
      (volume : Measure ℝ) := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)),
    integrableOn_union]
  constructor
  · have hpositive : IntegrableOn
        (fun x : ℝ => Real.exp (-a * x)) (Ioi (-(0 : ℝ)))
        (volume : Measure ℝ) := by
      simpa only [neg_zero] using exp_neg_integrableOn_Ioi (0 : ℝ) ha
    have h : IntegrableOn
        (fun x : ℝ => Real.exp (-a * (-x))) (Iio 0)
        (volume : Measure ℝ) :=
      hpositive.comp_neg_Iio (c := (0 : ℝ))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Iio
    rw [abs_of_neg (Set.mem_Iio.mp hx)]
  · have h : IntegrableOn (fun x : ℝ => Real.exp (-a * x))
        (Ici 0) (volume : Measure ℝ) :=
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun x : ℝ => Real.exp (-a * x))
        (b := (0 : ℝ))).mpr (exp_neg_integrableOn_Ioi 0 ha)
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ici
    rw [abs_of_nonneg (Set.mem_Ici.mp hx)]

private theorem sum_abs_le_dimension_mul_norm {n : ℕ} (x : Space n) :
    (∑ i, |x i|) ≤ (n : ℝ) * ‖x‖ := by
  calc
    (∑ i, |x i|) ≤ ∑ _i : Fin n, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = (n : ℝ) * ‖x‖ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

private theorem integrable_exp_neg_mul_sum_abs (n : ℕ) {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : Space n =>
      Real.exp (-a * ∑ i, |x i|))
      (volume : Measure (Space n)) := by
  have hprod :
      Integrable (fun x : Space n =>
        ∏ i, Real.exp (-a * |x i|))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_abs ha)
  rw [volume_pi]
  have hfun :
      (fun x : Space n => Real.exp (-a * ∑ i, |x i|)) =
        (fun x : Space n => ∏ i, Real.exp (-a * |x i|)) := by
    funext x
    rw [← Real.exp_sum, ← Finset.mul_sum]
  rw [hfun]
  exact hprod

private theorem integrable_exp_neg_mul_norm {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space n => Real.exp (-a * ‖x‖))
      (volume : Measure (Space n)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < a / (n : ℝ) := div_pos ha hnreal
  refine (integrable_exp_neg_mul_sum_abs n hb).mono'
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_norm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hsum := sum_abs_le_dimension_mul_norm x
  have hscaled :
      (a / (n : ℝ)) * (∑ i, |x i|) ≤ a * ‖x‖ := by
    calc
      (a / (n : ℝ)) * (∑ i, |x i|) ≤
          (a / (n : ℝ)) * ((n : ℝ) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsum hb.le
      _ = a * ‖x‖ := by
        field_simp
  linarith

private def monomialWeight {n : ℕ} (k : ℝ) (u : Space n)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (k * (SupportFunction.pairing u x - φ x))

private def monomialIntegral {n : ℕ} (k : ℝ) (u : Space n)
    (φ : Space n → ℝ) : ℝ :=
  ∫ x : Space n, monomialWeight k u φ x
    ∂(volume : Measure (Space n))

private theorem continuous_monomialWeight {n : ℕ} (k : ℝ)
    (u : Space n) {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    Continuous (monomialWeight k u φ) := by
  unfold monomialWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul
      ((SupportFunction.continuous_pairing_right u).sub hφ))

private theorem interior_sum_abs_gap {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      δ * (∑ i, |x i|) ≤
        SupportFunction.supportFunction K x -
          SupportFunction.pairing u x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  have hhalf : 0 < r / 2 := half_pos hr
  refine ⟨r / 2, hhalf, fun x => ?_⟩
  have hscaled :
      ‖(r / 2) • SupportFunction.signVector x‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf]
    exact mul_le_of_le_one_right hhalf.le
      (SupportFunction.norm_signVector_le_one x)
  have hmem_ball :
      u + (r / 2) • SupportFunction.signVector x ∈
        Metric.ball u r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm :
        ‖u + (r / 2) • SupportFunction.signVector x - u‖ ≤
          r / 2 := by
      simpa only [add_sub_cancel_left] using hscaled
    exact lt_of_le_of_lt hnorm (half_lt_self hr)
  have hmem :
      u + (r / 2) • SupportFunction.signVector x ∈ K :=
    interior_subset (hball hmem_ball)
  have hsupport := SupportFunction.pairing_le_supportFunction
    hcompact hmem x
  rw [SupportFunction.pairing_add_left,
    SupportFunction.pairing_smul_left,
    SupportFunction.pairing_signVector] at hsupport
  linarith

private theorem integrable_monomialWeight_of_support_le {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hpotential : ∀ x : Space n,
      SupportFunction.supportFunction K x ≤ φ x + C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  obtain ⟨δ, hδ, hgap⟩ := interior_sum_abs_gap hcompact hu
  have hdecay := integrable_exp_neg_mul_sum_abs n (mul_pos hk hδ)
  have hmajorant := hdecay.const_mul (Real.exp (k * C))
  refine hmajorant.mono'
    (continuous_monomialWeight k u hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold monomialWeight
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoercive :
      SupportFunction.pairing u x - φ x ≤
        C - δ * ∑ i, |x i| := by
    have hsupport := hpotential x
    have hinterior := hgap x
    linarith
  calc
    k * (SupportFunction.pairing u x - φ x) ≤
        k * (C - δ * ∑ i, |x i|) :=
      mul_le_mul_of_nonneg_left hcoercive hk.le
    _ = k * C + -(k * δ) * ∑ i, |x i| := by ring

private theorem integrable_monomialWeight_of_bounded_support {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  apply integrable_monomialWeight_of_support_le hcompact hu hφ
    (C := C) (k := k) (hk := hk)
  intro x
  have hlower := (abs_le.mp (hbounded x)).1
  linarith

private theorem monomialIntegral_pos_of_bounded_support {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    0 < monomialIntegral k u φ := by
  unfold monomialIntegral monomialWeight
  exact MeasureTheory.integral_exp_pos
    (integrable_monomialWeight_of_bounded_support
      hcompact hu hφ hbounded hk)

private theorem integrable_monomialWeight_of_centeredBody {n : ℕ}
    (K : CenteredBody n) {u : Space n}
    (hu : u ∈ interior K.carrier)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) :=
  integrable_monomialWeight_of_bounded_support
    K.compact hu hφ hbounded hk

end MonomialIntegrability

namespace MonomialDivergence

open Set MeasureTheory
open scoped BigOperators ENNReal

private def dualVector {n : ℕ}
    (f : Space n →L[ℝ] ℝ) : Space n :=
  fun i => f (Pi.single i (1 : ℝ))

private theorem dual_apply_eq_pairing {n : ℕ}
    (f : Space n →L[ℝ] ℝ) (x : Space n) :
    f x = SupportFunction.pairing x (dualVector f) := by
  classical
  have hexpansion :
      (∑ i : Fin n,
        x i • (Pi.single i (1 : ℝ) : Space n)) = x := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin n)).sum_repr x
  calc
    f x = f (∑ i : Fin n,
      x i • (Pi.single i (1 : ℝ) : Space n)) :=
      congrArg f hexpansion.symm
    _ = SupportFunction.pairing x (dualVector f) := by
      simp only [map_sum, map_smul, smul_eq_mul, SupportFunction.pairing, dualVector]

private theorem exists_separating_direction {n : ℕ}
    {K : Set (Space n)} (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {u : Space n} (hu : u ∉ interior K) :
    ∃ v : Space n, v ≠ 0 ∧
      ∀ y ∈ K, SupportFunction.pairing y v ≤
        SupportFunction.pairing u v := by
  obtain ⟨f, hf, hseparate⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      hconvex hu hinterior
  refine ⟨dualVector f, ?_, fun y hy => ?_⟩
  · intro hv
    apply hf
    ext x
    rw [dual_apply_eq_pairing, hv]
    simp only [SupportFunction.pairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_apply]
  · simpa only [dual_apply_eq_pairing] using hseparate y hy

private theorem pairing_sub_left {n : ℕ}
    (a b x : Space n) :
    SupportFunction.pairing (a - b) x =
      SupportFunction.pairing a x -
        SupportFunction.pairing b x := by
  simp only [SupportFunction.pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem pairing_add_right {n : ℕ}
    (a x y : Space n) :
    SupportFunction.pairing a (x + y) =
      SupportFunction.pairing a x +
        SupportFunction.pairing a y := by
  simp only [SupportFunction.pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem pairing_smul_right {n : ℕ} (c : ℝ)
    (a x : Space n) :
    SupportFunction.pairing a (c • x) =
      c * SupportFunction.pairing a x := by
  simp only [SupportFunction.pairing, Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum]

private theorem abs_pairing_le_sum_abs_mul_norm {n : ℕ}
    (a x : Space n) :
    |SupportFunction.pairing a x| ≤
      (∑ i, |a i|) * ‖x‖ := by
  unfold SupportFunction.pairing
  calc
    |∑ i, a i * x i| ≤ ∑ i, |a i * x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |x i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, |a i| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (abs_nonneg (a i))
    _ = (∑ i, |a i|) * ‖x‖ := by
      rw [Finset.sum_mul]

private theorem abs_pairing_le_dimension_mul_norm {n : ℕ}
    (a x : Space n) :
    |SupportFunction.pairing a x| ≤
      ((n : ℝ) * ‖a‖) * ‖x‖ := by
  calc
    |SupportFunction.pairing a x| ≤
        (∑ i, |a i|) * ‖x‖ :=
      abs_pairing_le_sum_abs_mul_norm a x
    _ ≤ ((n : ℝ) * ‖a‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (MonomialIntegrability.sum_abs_le_dimension_mul_norm a)
        (norm_nonneg x)

private def rayBall {n : ℕ} (v : Space n) (j : ℕ) :
    Set (Space n) :=
  Metric.ball ((j : ℝ) • v) (‖v‖ / 4)

private def rayTube {n : ℕ} (v : Space n) :
    Set (Space n) :=
  ⋃ j : ℕ, rayBall v j

private theorem one_le_abs_cast_sub {i j : ℕ} (hij : i ≠ j) :
    (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem rayBall_pairwise_disjoint {n : ℕ} (v : Space n) :
    Pairwise (Function.onFun Disjoint (rayBall v)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  change ‖v‖ / 4 + ‖v‖ / 4 ≤
    dist ((i : ℝ) • v) ((j : ℝ) • v)
  have hdist :
      ‖v‖ ≤ dist ((i : ℝ) • v) ((j : ℝ) • v) := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_abs_cast_sub hij) (norm_nonneg v)
  calc
    ‖v‖ / 4 + ‖v‖ / 4 ≤ ‖v‖ := by
      linarith [norm_nonneg v]
    _ ≤ dist ((i : ℝ) • v) ((j : ℝ) • v) := hdist

private theorem rayBall_volume {n : ℕ} (v : Space n)
    (hv : v ≠ 0) (j : ℕ) :
    (volume : Measure (Space n)) (rayBall v j) =
      ENNReal.ofReal ((2 * (‖v‖ / 4)) ^ n) := by
  have hr : 0 < ‖v‖ / 4 :=
    div_pos (norm_pos_iff.mpr hv) (by norm_num)
  unfold rayBall
  simpa only [Fintype.card_fin] using Real.volume_pi_ball ((j : ℝ) • v) hr

private theorem rayTube_volume_eq_top {n : ℕ}
    (v : Space n) (hv : v ≠ 0) :
    (volume : Measure (Space n)) (rayTube v) = ⊤ := by
  unfold rayTube
  rw [measure_iUnion (rayBall_pairwise_disjoint v)
    (fun j => (Metric.isOpen_ball.measurableSet :
      MeasurableSet (rayBall v j)))]
  simp_rw [rayBall_volume v hv]
  apply ENNReal.tsum_const_eq_top_of_ne_zero
  have hpositive : 0 < (2 * (‖v‖ / 4)) ^ n := by
    exact pow_pos (mul_pos (by norm_num)
      (div_pos (norm_pos_iff.mpr hv) (by norm_num))) n
  exact (ENNReal.ofReal_pos.mpr hpositive).ne'

private theorem supportFunction_le_pairing_add_on_rayTube {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v) :
    ∃ D : ℝ, ∀ x ∈ rayTube v,
      SupportFunction.supportFunction K x ≤
        SupportFunction.pairing u x + D := by
  obtain ⟨R, hR, hbound⟩ :=
    hcompact.isBounded.exists_pos_norm_le
  refine ⟨((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4),
    fun x hx => ?_⟩
  apply SupportFunction.supportFunction_le hnonempty x
  intro y hy
  have hx' : x ∈ ⋃ j : ℕ, rayBall v j := hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
  let w : Space n := x - (j : ℝ) • v
  have hw : ‖w‖ < ‖v‖ / 4 := by
    change ‖x - (j : ℝ) • v‖ < ‖v‖ / 4
    simpa only [rayBall, Metric.mem_ball, dist_eq_norm] using hj
  have hdiff : ‖y - u‖ ≤ R + ‖u‖ := by
    calc
      ‖y - u‖ ≤ ‖y‖ + ‖u‖ := norm_sub_le y u
      _ ≤ R + ‖u‖ := add_le_add (hbound y hy) (le_refl ‖u‖)
  have hpairw :
      SupportFunction.pairing (y - u) w ≤
        ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
    calc
      SupportFunction.pairing (y - u) w ≤
          |SupportFunction.pairing (y - u) w| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖y - u‖) * ‖w‖ :=
        abs_pairing_le_dimension_mul_norm (y - u) w
      _ ≤ ((n : ℝ) * (R + ‖u‖)) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n))
          (norm_nonneg w)
      _ ≤ ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
        apply mul_le_mul_of_nonneg_left hw.le
        positivity
  have hvsep : SupportFunction.pairing (y - u) v ≤ 0 := by
    rw [pairing_sub_left]
    linarith [hseparate y hy]
  have hray :
      SupportFunction.pairing (y - u)
        ((j : ℝ) • v) ≤ 0 := by
    rw [pairing_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) hvsep
  have hsplit : x = w + (j : ℝ) • v := by
    exact (sub_add_cancel x ((j : ℝ) • v)).symm
  have htotal :
      SupportFunction.pairing (y - u) x ≤
        ((n : ℝ) * (R + ‖u‖)) * (‖v‖ / 4) := by
    rw [hsplit, pairing_add_right]
    linarith
  rw [pairing_sub_left] at htotal
  linarith

private theorem monomialWeight_bounded_below_on_rayTube {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty)
    {u v : Space n}
    (hseparate : ∀ y ∈ K,
      SupportFunction.pairing y v ≤
        SupportFunction.pairing u v)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K x + C)
    {k : ℝ} (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ rayTube v,
      c ≤ MonomialIntegrability.monomialWeight k u φ x := by
  obtain ⟨D, hD⟩ :=
    supportFunction_le_pairing_add_on_rayTube
      hcompact hnonempty hseparate
  refine ⟨Real.exp (-(k * (D + C))), Real.exp_pos _,
    fun x hx => ?_⟩
  unfold MonomialIntegrability.monomialWeight
  apply Real.exp_le_exp.mpr
  have hsupport := hD x hx
  have hpotential := hupper x
  have hlower :
      -(D + C) ≤ SupportFunction.pairing u x - φ x := by
    linarith
  calc
    -(k * (D + C)) = k * (-(D + C)) := by ring
    _ ≤ k * (SupportFunction.pairing u x - φ x) :=
      mul_le_mul_of_nonneg_left hlower hk.le

private theorem not_integrable_monomialWeight_of_not_mem_interior {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {u : Space n} (hu : u ∉ interior K)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K x + C)
    {k : ℝ} (hk : 0 < k) :
    ¬ Integrable (MonomialIntegrability.monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  obtain ⟨v, hv, hseparate⟩ :=
    exists_separating_direction hconvex hinterior hu
  have hnonempty : K.Nonempty := hinterior.mono interior_subset
  obtain ⟨c, hc, hweight⟩ :=
    monomialWeight_bounded_below_on_rayTube
      hcompact hnonempty hseparate hupper hk
  intro hintegrable
  have hscaled :
      Integrable
        (fun x : Space n =>
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x)
        (volume : Measure (Space n)) :=
    hintegrable.const_mul c⁻¹
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure (Space n))]
        (fun x : Space n =>
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x) := by
    filter_upwards [] with x
    exact mul_nonneg (inv_nonneg.mpr hc.le)
      (Real.exp_pos _).le
  have hlarge :
      ∀ x ∈ rayTube v,
        (1 : ℝ) ≤
          c⁻¹ * MonomialIntegrability.monomialWeight k u φ x := by
    intro x hx
    calc
      (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ *
        MonomialIntegrability.monomialWeight k u φ x :=
        mul_le_mul_of_nonneg_left (hweight x hx)
          (inv_nonneg.mpr hc.le)
  have hmeasure := hscaled.measure_le_integral hnonnegative hlarge
  rw [rayTube_volume_eq_top v hv] at hmeasure
  exact ENNReal.ofReal_ne_top (top_unique hmeasure)

private theorem not_integrable_monomialWeight_of_centeredBody_not_mem_interior
    {n : ℕ} (K : CenteredBody n)
    {u : Space n} (hu : u ∉ interior K.carrier)
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K.carrier x + C)
    {k : ℝ} (hk : 0 < k) :
    ¬ Integrable (MonomialIntegrability.monomialWeight k u φ)
      (volume : Measure (Space n)) :=
  not_integrable_monomialWeight_of_not_mem_interior
    K.compact K.convex K.fullDimensional hu hupper hk

end MonomialDivergence

namespace BergmanMonomials

open Set MeasureTheory Filter
open scoped BigOperators Pointwise Topology

private def bergmanDimension {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℕ :=
  Nat.card (LatticeAsymptotics.monomialIndex K k)

private def monomialNormSquared {n : ℕ} (k : ℕ)
    (u : Space n) (φ : Space n → ℝ) : ℝ :=
  MonomialIntegrability.monomialIntegral (k : ℝ) u φ

private def normalizedMonomialDensity {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) : ℝ :=
  MonomialIntegrability.monomialWeight
    (k : ℝ) (u : Space n) φ x /
      monomialNormSquared k (u : Space n) φ

private def diagonalTerm {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) : ℝ :=
  Real.exp ((k : ℝ) *
    SupportFunction.pairing (u : Space n) x) /
      monomialNormSquared k (u : Space n) φ

private def diagonalKernel {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑' u : LatticeAsymptotics.monomialIndex K k,
    diagonalTerm K k φ u x

private def weightedDiagonalKernel {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑' u : LatticeAsymptotics.monomialIndex K k,
    normalizedMonomialDensity K k φ u x

private theorem monomialIndex_finite {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    (LatticeAsymptotics.monomialIndex K k).Finite := by
  classical
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  unfold LatticeAsymptotics.monomialIndex
    LatticeAsymptotics.scaledIntegerLattice
  rw [← Submodule.coe_pointwise_smul,
    ZSpan.smul _ (inv_ne_zero hkreal)]
  exact ZSpan.setFinite_inter _
    (K.compact.isBounded.subset interior_subset)

private theorem zero_mem_monomialIndex {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    (0 : Space n) ∈
      LatticeAsymptotics.monomialIndex K k := by
  apply (LatticeAsymptotics.mem_monomialIndex_iff
    K hk 0).mpr
  refine ⟨LatticeAsymptotics.zero_mem_interior K, ?_⟩
  intro i
  exact ⟨0, by simp only [algebraMap_int_eq, eq_intCast, Int.cast_zero, Pi.zero_apply, mul_zero]⟩

private theorem bergmanDimension_pos {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    0 < bergmanDimension K k := by
  let : Finite (LatticeAsymptotics.monomialIndex K k) :=
    (monomialIndex_finite K hk).to_subtype
  let : Nonempty (LatticeAsymptotics.monomialIndex K k) :=
    ⟨⟨0, zero_mem_monomialIndex K hk⟩⟩
  exact Nat.card_pos

private theorem weighted_diagonalTerm_eq_normalizedMonomialDensity
    {n k : ℕ} (K : CenteredBody n)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) :
    Real.exp (-(k : ℝ) * φ x) * diagonalTerm K k φ u x =
      normalizedMonomialDensity K k φ u x := by
  unfold diagonalTerm normalizedMonomialDensity
    MonomialIntegrability.monomialWeight
  rw [mul_div_assoc', ← Real.exp_add]
  congr 1
  ring_nf

private theorem weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ) (x : Space n) :
    weightedDiagonalKernel K k φ x =
      Real.exp (-(k : ℝ) * φ x) * diagonalKernel K k φ x := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel diagonalKernel
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact (weighted_diagonalTerm_eq_normalizedMonomialDensity
    K φ u x).symm

private theorem bergmanDimension_div_pow_tendsto_volume {n : ℕ}
    (K : CenteredBody n) :
    Tendsto
      (fun k : ℕ =>
        (bergmanDimension K k : ℝ) / (k : ℝ) ^ n)
      atTop (𝓝 (normalizedVolume K.carrier)) := by
  exact LatticeAsymptotics.monomial_count_div_pow_tendsto_volume K

end BergmanMonomials

namespace TorusCharacters

open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal Topology

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

private abbrev LogSpace (n : ℕ) := Fin n → ℂ

private abbrev AngularTorus (n : ℕ) := UnitAddTorus (Fin n)

private def characterExponent {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) : ℂ :=
  ∑ i, (m i : ℂ) * ζ i

private def torusCharacter {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) : ℂ :=
  Complex.exp (characterExponent m ζ)

private def imaginaryShift {n : ℕ}
    (q : Fin n → ℤ) : LogSpace n :=
  fun i => (q i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

private theorem differentiable_characterExponent {n : ℕ}
    (m : Fin n → ℤ) :
    Differentiable ℂ (characterExponent m) := by
  unfold characterExponent
  fun_prop

private theorem differentiable_torusCharacter {n : ℕ}
    (m : Fin n → ℤ) :
    Differentiable ℂ (torusCharacter m) := by
  unfold torusCharacter
  exact (differentiable_characterExponent m).cexp

private theorem characterExponent_add {n : ℕ}
    (m : Fin n → ℤ) (ζ η : LogSpace n) :
    characterExponent m (ζ + η) =
      characterExponent m ζ + characterExponent m η := by
  simp only [characterExponent, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem torusCharacter_zero {n : ℕ} (ζ : LogSpace n) :
    torusCharacter (0 : Fin n → ℤ) ζ = 1 := by
  simp only [torusCharacter, characterExponent, Pi.zero_apply, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, Complex.exp_zero]

private theorem torusCharacter_ne_zero {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) :
    torusCharacter m ζ ≠ 0 :=
  Complex.exp_ne_zero _

private theorem characterExponent_imaginaryShift {n : ℕ}
    (m q : Fin n → ℤ) :
    characterExponent m (imaginaryShift q) =
      ((∑ i, m i * q i : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I) := by
  unfold characterExponent imaginaryShift
  calc
    (∑ i, (m i : ℂ) *
        ((q i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) =
        ∑ i, ((m i * q i : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
            apply Finset.sum_congr rfl
            intro i _
            push_cast
            ring
    _ = ((∑ i, m i * q i : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [← Finset.sum_mul]
            norm_cast

private theorem torusCharacter_imaginaryShift {n : ℕ}
    (m q : Fin n → ℤ) (ζ : LogSpace n) :
    torusCharacter m (ζ + imaginaryShift q) =
      torusCharacter m ζ := by
  unfold torusCharacter
  rw [characterExponent_add,
    characterExponent_imaginaryShift, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

private def realLogSlice {n : ℕ}
    (x : Space n) : LogSpace n :=
  fun i => (x i : ℂ) / 2

private theorem characterExponent_realLogSlice_re {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) :
    (characterExponent m (realLogSlice x)).re =
      (∑ i, (m i : ℝ) * x i) / 2 := by
  unfold characterExponent realLogSlice
  simp only [← mul_div_assoc, Complex.re_sum, Complex.div_ofNat_re, Complex.mul_re,
    Complex.intCast_re, Complex.ofReal_re, Complex.intCast_im, Complex.ofReal_im, mul_zero,
    sub_zero, Finset.sum_div]

private theorem norm_sq_torusCharacter_realLogSlice {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) :
    ‖torusCharacter m (realLogSlice x)‖ ^ 2 =
      Real.exp (∑ i, (m i : ℝ) * x i) := by
  rw [torusCharacter, Complex.norm_exp,
    characterExponent_realLogSlice_re, pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem angular_characters_orthonormal (n : ℕ) :
    Orthonormal ℂ
      (UnitAddTorus.mFourierLp
        (d := Fin n) 2) :=
  UnitAddTorus.orthonormal_mFourier

end TorusCharacters

section

open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace

namespace WeightedTorusHilbert

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private abbrev LogTorus (n : ℕ) :=
  Space n × TorusCharacters.AngularTorus n

private def angularMeasure (n : ℕ) :
    Measure (TorusCharacters.AngularTorus n) :=
  volume

private instance angularMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (angularMeasure n) := by
  unfold angularMeasure
  infer_instance

private def radialWeight {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(k : ℝ) * φ x))

private def radialMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (radialWeight k φ)

private instance radialMeasure_sFinite {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : SFinite (radialMeasure k φ) := by
  unfold radialMeasure
  infer_instance

private def weightedTorusMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : Measure (LogTorus n) :=
  (radialMeasure k φ).prod (angularMeasure n)

private abbrev weightedHilbert {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  MeasureTheory.Lp ℂ 2 (weightedTorusMeasure k φ)

private theorem radialWeight_measurable {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Measurable (radialWeight k φ) := by
  unfold radialWeight
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp
      (continuous_const.mul hφ)).measurable

private theorem weightedTorusMeasure_eq_withDensity {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    weightedTorusMeasure k φ =
      ((volume : Measure (Space n)).prod
        (angularMeasure n)).withDensity
          (fun z : LogTorus n => radialWeight k φ z.1) := by
  unfold weightedTorusMeasure radialMeasure
  exact MeasureTheory.prod_withDensity_left
    (radialWeight_measurable k hφ)

private theorem angularCharacter_norm {n : ℕ} (m : Fin n → ℤ)
    (θ : TorusCharacters.AngularTorus n) :
    ‖UnitAddTorus.mFourier m θ‖ = 1 := by
  simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod]
  apply Finset.prod_eq_one
  intro b _
  exact (AddCircle.toCircle (m b • θ b)).norm_coe

private theorem angularCharacter_inner {n : ℕ} (m q : Fin n → ℤ) :
    (∫ θ : TorusCharacters.AngularTorus n,
      conj (UnitAddTorus.mFourier m θ) *
        UnitAddTorus.mFourier q θ
      ∂(angularMeasure n)) =
        if m = q then (1 : ℂ) else 0 := by
  have h := (orthonormal_iff_ite.mp
    (TorusCharacters.angular_characters_orthonormal n)) m q
  rw [ContinuousMap.inner_toLp] at h
  simpa only [angularMeasure, mul_comm] using h

private def radialCharacter {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  TorusCharacters.torusCharacter m
    (TorusCharacters.realLogSlice x)

private def torusMonomial {n : ℕ}
    (m : Fin n → ℤ) (z : LogTorus n) : ℂ :=
  radialCharacter m z.1 * UnitAddTorus.mFourier m z.2

private theorem continuous_torusMonomial {n : ℕ}
    (m : Fin n → ℤ) :
    Continuous (torusMonomial m) := by
  unfold torusMonomial radialCharacter
    TorusCharacters.torusCharacter
    TorusCharacters.characterExponent
    TorusCharacters.realLogSlice
  fun_prop

private theorem torusMonomial_norm_sq {n : ℕ}
    (m : Fin n → ℤ) (z : LogTorus n) :
    ‖torusMonomial m z‖ ^ 2 =
      Real.exp (SupportFunction.pairing
        (integerPoint n m) z.1) := by
  unfold torusMonomial
  rw [norm_mul, angularCharacter_norm, mul_one]
  exact TorusCharacters.norm_sq_torusCharacter_realLogSlice
    m z.1

private def integerExponent {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Fin n → ℤ :=
  fun i => Classical.choose
    (((LatticeAsymptotics.mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property).2 i)

private theorem integerPoint_integerExponent {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    integerPoint n (integerExponent K hk u) =
      (k : ℝ) • (u : Space n) := by
  funext i
  exact Classical.choose_spec
    (((LatticeAsymptotics.mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property).2 i)

private theorem integerExponent_injective {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    Function.Injective (integerExponent K hk) := by
  intro u v huv
  apply Subtype.ext
  have hscaled :
      (k : ℝ) • (u : Space n) =
        (k : ℝ) • (v : Space n) := by
    rw [← integerPoint_integerExponent K hk u,
      ← integerPoint_integerExponent K hk v, huv]
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  funext i
  apply mul_left_cancel₀ hkreal
  exact congrFun hscaled i

private theorem radialWeight_mul_exp_pairing {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (x : Space n) :
    (radialWeight k φ x).toReal *
      Real.exp (SupportFunction.pairing
        (integerPoint n m) x) =
      MonomialIntegrability.monomialWeight
        (k : ℝ) u φ x := by
  unfold radialWeight
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    hm, SupportFunction.pairing_smul_left]
  unfold MonomialIntegrability.monomialWeight
  rw [← Real.exp_add]
  congr 1
  ring

private theorem radial_exp_integral_eq_monomialIntegral {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    (∫ x : Space n,
      Real.exp (SupportFunction.pairing
        (integerPoint n m) x)
      ∂(radialMeasure k φ)) =
      MonomialIntegrability.monomialIntegral
        (k : ℝ) u φ := by
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
    MonomialIntegrability.monomialIntegral
  rw [integral_withDensity_eq_integral_toReal_smul
    (radialWeight_measurable k hφ) hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simpa only [smul_eq_mul] using
    radialWeight_mul_exp_pairing k φ m u hm x

private theorem radial_exp_integrable {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        Real.exp (SupportFunction.pairing
          (integerPoint n m) x))
      (radialMeasure k φ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
  apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (radialWeight_measurable k hφ) hfinite).2
  have hmono :=
    MonomialIntegrability.integrable_monomialWeight_of_centeredBody
      K hu hφ hbounded hkreal
  refine hmono.congr (Filter.Eventually.of_forall fun x => ?_)
  simpa only [smul_eq_mul] using
    (radialWeight_mul_exp_pairing k φ m u hm x).symm

private theorem torusMonomial_sq_integrable {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable (fun z : LogTorus n => ‖torusMonomial m z‖ ^ 2)
      (weightedTorusMeasure k φ) := by
  have hradial := radial_exp_integrable
    K hk hφ hbounded m u hu hm
  have hangular : Integrable
      (fun _ : TorusCharacters.AngularTorus n => (1 : ℝ))
      (angularMeasure n) := integrable_const _
  have hproduct := hradial.mul_prod hangular
  unfold weightedTorusMeasure
  convert hproduct using 1
  funext z
  simp only [torusMonomial_norm_sq, mul_one]

private theorem torusMonomial_memLp {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    MemLp (torusMonomial m) 2 (weightedTorusMeasure k φ) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_torusMonomial m).aestronglyMeasurable).2
  exact torusMonomial_sq_integrable
    K hk hφ hbounded m u hu hm

private theorem integral_torusMonomial_norm_sq_eq_monomialIntegral
    {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    (∫ z : LogTorus n, ‖torusMonomial m z‖ ^ 2
      ∂(weightedTorusMeasure k φ)) =
      MonomialIntegrability.monomialIntegral
        (k : ℝ) u φ := by
  unfold weightedTorusMeasure
  calc
    (∫ z : LogTorus n, ‖torusMonomial m z‖ ^ 2
      ∂(radialMeasure k φ).prod (angularMeasure n)) =
        ∫ z : LogTorus n,
          Real.exp (SupportFunction.pairing
            (integerPoint n m) z.1) * (1 : ℝ)
          ∂(radialMeasure k φ).prod (angularMeasure n) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with z
            simp only [torusMonomial_norm_sq, mul_one]
    _ = (∫ x : Space n,
          Real.exp (SupportFunction.pairing
            (integerPoint n m) x)
          ∂(radialMeasure k φ)) *
          (∫ _θ : TorusCharacters.AngularTorus n,
            (1 : ℝ) ∂(angularMeasure n)) :=
          MeasureTheory.integral_prod_mul
            (μ := radialMeasure k φ) (ν := angularMeasure n)
            (fun x : Space n =>
              Real.exp (SupportFunction.pairing
                (integerPoint n m) x))
            (fun _ : TorusCharacters.AngularTorus n =>
              (1 : ℝ))
    _ = MonomialIntegrability.monomialIntegral
          (k : ℝ) u φ := by
          rw [radial_exp_integral_eq_monomialIntegral
            k hφ m u hm]
          simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]

private theorem torusMonomial_inner_factor {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (m q : Fin n → ℤ) :
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(weightedTorusMeasure k φ)) =
      (∫ x : Space n,
        conj (radialCharacter m x) * radialCharacter q x
        ∂(radialMeasure k φ)) *
          if m = q then (1 : ℂ) else 0 := by
  unfold weightedTorusMeasure
  calc
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(radialMeasure k φ).prod (angularMeasure n)) =
        ∫ z : LogTorus n,
          (conj (radialCharacter m z.1) * radialCharacter q z.1) *
          (conj (UnitAddTorus.mFourier m z.2) *
            UnitAddTorus.mFourier q z.2)
          ∂(radialMeasure k φ).prod (angularMeasure n) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with z
            simp only [torusMonomial, map_mul]
            ring
    _ = (∫ x : Space n,
          conj (radialCharacter m x) * radialCharacter q x
          ∂(radialMeasure k φ)) *
        (∫ θ : TorusCharacters.AngularTorus n,
          conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ
          ∂(angularMeasure n)) :=
          MeasureTheory.integral_prod_mul
            (μ := radialMeasure k φ) (ν := angularMeasure n)
            (fun x : Space n =>
              conj (radialCharacter m x) * radialCharacter q x)
            (fun θ : TorusCharacters.AngularTorus n =>
              conj (UnitAddTorus.mFourier m θ) *
                UnitAddTorus.mFourier q θ)
    _ = _ := by rw [angularCharacter_inner]

private theorem torusMonomial_inner_eq_zero_of_ne {n : ℕ}
    (k : ℕ) (φ : Space n → ℝ)
    (m q : Fin n → ℤ) (hmq : m ≠ q) :
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(weightedTorusMeasure k φ)) = 0 := by
  rw [torusMonomial_inner_factor]
  simp only [hmq, ↓reduceIte, mul_zero]

private def indexedMonomialLp {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (u : LatticeAsymptotics.monomialIndex K k) :
    weightedHilbert k φ :=
  (torusMonomial_memLp K hk hφ hbounded
    (integerExponent K hk u) (u : Space n)
    u.property.1 (integerPoint_integerExponent K hk u)).toLp
      (torusMonomial (integerExponent K hk u))

private theorem indexedMonomialLp_ae {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (u : LatticeAsymptotics.monomialIndex K k) :
    (indexedMonomialLp K hk hφ hbounded u : LogTorus n → ℂ)
      =ᵐ[weightedTorusMeasure k φ]
        torusMonomial (integerExponent K hk u) := by
  unfold indexedMonomialLp
  exact MeasureTheory.MemLp.coeFn_toLp _

end WeightedTorusHilbert

namespace JetEnvelopeSlopeBridge

private theorem coeFn_finset_sum_ae
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (I : Finset ι)
    (f : ι → MeasureTheory.Lp ℂ 2 μ) :
    (fun x : α => (∑ i ∈ I, f i) x)
      =ᵐ[μ] (fun x : α => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2 μ]
        with x hx
      simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert i I hi hI =>
      rw [Finset.sum_insert hi]
      have hadd := MeasureTheory.Lp.coeFn_add (f i) (∑ j ∈ I, f j)
      filter_upwards [hadd, hI] with x hx hsum
      simpa only [AddSubgroup.coe_add, AddSubgroup.val_finsetSum, Finset.sum_insert hi] using
        hx.trans (congrArg (fun z : ℂ => f i x + z) hsum)

end JetEnvelopeSlopeBridge

namespace JetEnvelopeSlopeConvergence

private def sourceTorusBaseMeasure (n : ℕ) :
    Measure (WeightedTorusHilbert.LogTorus n) :=
  (volume : Measure (Space n)).prod
    (WeightedTorusHilbert.angularMeasure n)

end JetEnvelopeSlopeConvergence
end

namespace BergmanNormalization

open Set MeasureTheory
open scoped BigOperators ENNReal

private def normalizedDiagonalDensity {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  BergmanMonomials.weightedDiagonalKernel K k φ x /
    (BergmanMonomials.bergmanDimension K k : ℝ)

private def normalizedBergmanMeasure {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (normalizedDiagonalDensity K k φ x))

end BergmanNormalization

namespace BergmanJetSlope

open Set MeasureTheory
open scoped BigOperators ENNReal

private theorem continuous_normalizedMonomialDensity {n k : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Continuous
      (BergmanMonomials.normalizedMonomialDensity K k φ u) := by
  unfold BergmanMonomials.normalizedMonomialDensity
  exact
    (MonomialIntegrability.continuous_monomialWeight
      (k : ℝ) (u : Space n) hφ).div_const _

private theorem continuous_weightedDiagonalKernel {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous (BergmanMonomials.weightedDiagonalKernel K k φ) := by
  let := (BergmanMonomials.monomialIndex_finite K hk).fintype
  unfold BergmanMonomials.weightedDiagonalKernel
  simp_rw [tsum_fintype]
  exact continuous_finsetSum _
    (fun u _ => continuous_normalizedMonomialDensity K hφ u)

private theorem continuous_normalizedDiagonalDensity {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous
      (BergmanNormalization.normalizedDiagonalDensity K k φ) := by
  unfold BergmanNormalization.normalizedDiagonalDensity
  exact (continuous_weightedDiagonalKernel K hk hφ).div_const _

end BergmanJetSlope

namespace JetCounting

open scoped BigOperators

private def JetIndexLT (n j : ℕ) :=
  {α : Fin n → ℕ // (∑ i, α i) < j}

private def symSigmaEquivJetIndexLT (n j : ℕ) :
    (Σ r : Fin j, Sym (Fin n) (r : ℕ)) ≃ JetIndexLT n j :=
  (Equiv.sigmaCongr Fin.equivSubtype
    (fun r : Fin j => Sym.equivNatSumOfFintype (Fin n) (r : ℕ))).trans
      (Equiv.sigmaSubtypeFiberEquivSubtype
        (fun α : Fin n → ℕ => ∑ i, α i)
        (p := fun α : Fin n → ℕ => (∑ i, α i) < j)
        (q := fun r : ℕ => r < j)
        (fun _ => Iff.rfl))

private noncomputable instance instFintypeJetIndexLT (n j : ℕ) :
    Fintype (JetIndexLT n j) :=
  Fintype.ofEquiv (Σ r : Fin j, Sym (Fin n) (r : ℕ))
    (symSigmaEquivJetIndexLT n j)

private theorem card_jetIndexLT (n j : ℕ) (hj : 0 < j) :
    Fintype.card (JetIndexLT n j) = (n + j - 1).choose n := by
  rw [← Fintype.card_congr (symSigmaEquivJetIndexLT n j), Fintype.card_sigma]
  simp_rw [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]
  have hsum := Nat.sum_range_multichoose (j - 1) n
  rw [Nat.sub_add_cancel hj] at hsum
  convert hsum using 1
  congr 1
  omega

private theorem finrank_le_kernel_add_jetCount
    (𝕜 V : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V]
    (n j : ℕ) (hj : 0 < j)
    (jet : V →ₗ[𝕜] (JetIndexLT n j → 𝕜)) :
    Module.finrank 𝕜 V ≤
      Module.finrank 𝕜 (LinearMap.ker jet) + (n + j - 1).choose n := by
  have hrange : Module.finrank 𝕜 (LinearMap.range jet) ≤
      (n + j - 1).choose n := by
    calc
      Module.finrank 𝕜 (LinearMap.range jet) ≤
          Module.finrank 𝕜 (JetIndexLT n j → 𝕜) := Submodule.finrank_le _
      _ = (n + j - 1).choose n := by
        rw [Module.finrank_fintype_fun_eq_card, card_jetIndexLT n j hj]
  have hdimension := LinearMap.finrank_range_add_finrank_ker jet
  omega

end JetCounting

namespace BergmanJetFiltration

open Set MeasureTheory
open scoped BigOperators ENNReal

private theorem sum_range_jetCount (n N : ℕ) :
    (∑ j ∈ Finset.range N, (n + j).choose n) =
      (n + N).choose (n + 1) := by
  cases N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.choose_succ_self]
  | succ N =>
    simpa only [Nat.add_comm, Nat.add_assoc] using
      Nat.sum_range_add_choose N n

private theorem cast_sub_ge_real_sub (a b : ℕ) :
    (a : ℝ) - (b : ℝ) ≤ ((a - b : ℕ) : ℝ) := by
  exact sub_le_iff_le_add.mpr
    (by exact_mod_cast (show a ≤ a - b + b from le_tsub_add))

private theorem real_jetLayercake_le_nat_sum (n d N : ℕ) :
    (N : ℝ) * (d : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.range N,
        (d - (n + j).choose n)) : ℕ) := by
  calc
    (N : ℝ) * (d : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) =
      ∑ j ∈ Finset.range N,
        ((d : ℝ) - (((n + j).choose n : ℕ) : ℝ)) := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Nat.cast_sum,
            sum_range_jetCount]
    _ ≤ ∑ j ∈ Finset.range N,
          ((d - (n + j).choose n : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          exact cast_sub_ge_real_sub d ((n + j).choose n)
    _ = ((∑ j ∈ Finset.range N,
          (d - (n + j).choose n)) : ℕ) := by
          simp only [Nat.cast_sum]

end BergmanJetFiltration

namespace AdaptedBergmanBasis

open Set MeasureTheory Module
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace

private def monomialIndexEquivFin {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    LatticeAsymptotics.monomialIndex K k ≃
      Fin (BergmanMonomials.bergmanDimension K k) := by
  letI := (BergmanMonomials.monomialIndex_finite K hk).fintype
  apply Fintype.equivFinOfCardEq
  simp only [fintypeCard_eq_ncard, BergmanMonomials.bergmanDimension, Nat.card_eq_fintype_card]

private def normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (ζ : TorusCharacters.LogSpace n) : ℂ :=
  ((Real.sqrt (BergmanMonomials.monomialNormSquared
      k (u : Space n) φ) : ℂ)⁻¹) *
    TorusCharacters.torusCharacter
      (WeightedTorusHilbert.integerExponent K hk u) ζ

private theorem differentiable_normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Differentiable ℂ (normalizedHolomorphicMonomial K hk φ u) := by
  unfold normalizedHolomorphicMonomial
  exact (TorusCharacters.differentiable_torusCharacter _).const_mul _

private def multiIndexCoordinate {n : ℕ} (α : Fin n → ℕ) :
    Fin (∑ i, α i) → Fin n := by
  classical
  let e : ((i : Fin n) × Fin (α i)) ≃ Fin (∑ i, α i) :=
    Fintype.equivFinOfCardEq (by simp only [Fintype.card_sigma, Fintype.card_fin])
  exact fun q => (e.symm q).1

private def holomorphicMonomialJet {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (p : TorusCharacters.LogSpace n)
    (u : LatticeAsymptotics.monomialIndex K k)
    (α : Fin n → ℕ) : ℂ := by
  classical
  exact (iteratedFDeriv ℂ (∑ i, α i)
    (normalizedHolomorphicMonomial K hk φ u) p)
      (fun q => Pi.single (multiIndexCoordinate α q) (1 : ℂ))

end AdaptedBergmanBasis

namespace ArbitraryBodySmoothConvexPotentialBridge

open Set MeasureTheory
open scoped BigOperators Convolution Topology ContDiff

private theorem pairing_sub_right {n : ℕ}
    (u x y : Space n) :
    SupportFunction.pairing u (x - y) =
      SupportFunction.pairing u x -
        SupportFunction.pairing u y := by
  simp only [SupportFunction.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem supportFunction_lipschitzWith {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {R : ℝ} (hR : ∀ u ∈ K, ‖u‖ ≤ R) :
    LipschitzWith (Real.toNNReal ((n : ℝ) * R))
      (SupportFunction.supportFunction K) := by
  apply LipschitzWith.of_le_add_mul' ((n : ℝ) * R)
  intro x y
  obtain ⟨u, hu, hmax⟩ :=
    SupportFunction.supportFunction_attained
      hcompact hnonempty x
  have hy := SupportFunction.pairing_le_supportFunction
    hcompact hu y
  have hpair :
      SupportFunction.pairing u (x - y) ≤
        ((n : ℝ) * R) * dist x y := by
    calc
      SupportFunction.pairing u (x - y) ≤
          |SupportFunction.pairing u (x - y)| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖u‖) * ‖x - y‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          u (x - y)
      _ ≤ ((n : ℝ) * R) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR u hu) (Nat.cast_nonneg n))
          (norm_nonneg _)
      _ = ((n : ℝ) * R) * dist x y := by rw [dist_eq_norm]
  calc
    SupportFunction.supportFunction K x =
        SupportFunction.pairing u x := hmax
    _ = SupportFunction.pairing u y +
          SupportFunction.pairing u (x - y) := by
      rw [pairing_sub_right]
      ring
    _ ≤ SupportFunction.supportFunction K y +
          ((n : ℝ) * R) * dist x y :=
      add_le_add hy hpair

private theorem uniformContinuous_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    UniformContinuous (SupportFunction.supportFunction K) := by
  obtain ⟨R, hRpos, hR⟩ := hcompact.isBounded.exists_pos_norm_le
  exact (supportFunction_lipschitzWith hcompact hnonempty hR).uniformContinuous

private theorem continuous_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    Continuous (SupportFunction.supportFunction K) :=
  (uniformContinuous_supportFunction hcompact hnonempty).continuous

private theorem convexOn_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    ConvexOn ℝ Set.univ
      (SupportFunction.supportFunction K) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply SupportFunction.supportFunction_le hnonempty _
  intro u hu
  have hux :=
    SupportFunction.pairing_le_supportFunction hcompact hu x
  have huy :=
    SupportFunction.pairing_le_supportFunction hcompact hu y
  calc
    SupportFunction.pairing u (a • x + b • y) =
        a * SupportFunction.pairing u x +
          b * SupportFunction.pairing u y := by
      simp only [SupportFunction.pairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * SupportFunction.supportFunction K x +
          b * SupportFunction.supportFunction K y :=
      add_le_add (mul_le_mul_of_nonneg_left hux ha)
        (mul_le_mul_of_nonneg_left huy hb)
    _ = a • SupportFunction.supportFunction K x +
          b • SupportFunction.supportFunction K y := by
      simp only [smul_eq_mul]

private def mollifiedSupport {n : ℕ} (K : Set (Space n))
    (ρ : ContDiffBump (0 : Space n)) :
    Space n → ℝ :=
  ρ.normed (volume : Measure (Space n)) ⋆
    SupportFunction.supportFunction K

private theorem contDiff_mollifiedSupport {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    (ρ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ ∞ (mollifiedSupport K ρ) := by
  unfold mollifiedSupport
  exact ρ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ρ.contDiff_normed
    (continuous_supportFunction hcompact hnonempty).locallyIntegrable

private theorem convexOn_mollifiedSupport {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    (ρ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ Set.univ (mollifiedSupport K ρ) := by
  change ConvexOn ℝ Set.univ
    (fun x : Space n =>
      ∫ t : Space n,
        ρ.normed (volume : Measure (Space n)) t *
          SupportFunction.supportFunction K (x - t)
        ∂(volume : Measure (Space n)))
  apply MeasureTheory.integral_convexOn_of_integrand_ae convex_univ
  · filter_upwards [] with t
    have htranslate :
        ConvexOn ℝ Set.univ
          (fun x : Space n =>
            SupportFunction.supportFunction K (x - t)) := by
      simpa only [sub_eq_add_neg, add_comm, preimage_univ, Function.comp_def] using
        (convexOn_supportFunction hcompact hnonempty).translate_right (-t)
    simpa only [smul_eq_mul] using
      htranslate.smul
        (ρ.nonneg_normed (μ := (volume : Measure (Space n))) t)
  · intro x hx
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (ρ.hasCompactSupport_normed.convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.continuous_normed
        (continuous_supportFunction hcompact hnonempty).locallyIntegrable
        x).integrable

private theorem dist_mollifiedSupport_le {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {R : ℝ} (hRnonneg : 0 ≤ R)
    (hR : ∀ u ∈ K, ‖u‖ ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    dist (mollifiedSupport K ρ x)
      (SupportFunction.supportFunction K x) ≤
      ((n : ℝ) * R) * ρ.rOut := by
  unfold mollifiedSupport
  apply ρ.dist_normed_convolution_le
    (continuous_supportFunction hcompact hnonempty).aestronglyMeasurable
  intro y hy
  have hlip :=
    (supportFunction_lipschitzWith hcompact hnonempty hR).dist_le_mul y x
  have hcoe :
      ((Real.toNNReal ((n : ℝ) * R) : ℝ)) =
        (n : ℝ) * R := by
    rw [Real.coe_toNNReal]
    positivity
  rw [hcoe] at hlip
  exact hlip.trans (mul_le_mul_of_nonneg_left
    (Metric.mem_ball.mp hy).le (mul_nonneg (Nat.cast_nonneg n) hRnonneg))

private theorem exists_smooth_convex_potential_uniformly_close {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Space n → ℝ,
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ Set.univ φ ∧
        ∀ x : Space n,
          |φ x - SupportFunction.supportFunction K x| < ε := by
  obtain ⟨R, hRpos, hR⟩ := hcompact.isBounded.exists_pos_norm_le
  let L : ℝ := (n : ℝ) * R
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg n) hRpos.le
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let ρ : ContDiffBump (0 : Space n) :=
    ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨mollifiedSupport K ρ,
    contDiff_mollifiedSupport hcompact hnonempty ρ,
    convexOn_mollifiedSupport hcompact hnonempty ρ, ?_⟩
  intro x
  have hdist :=
    dist_mollifiedSupport_le hcompact hnonempty hRpos.le hR ρ x
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < L + 1)).mpr
    nlinarith
  rw [Real.dist_eq] at hdist
  exact lt_of_le_of_lt hdist (by simpa only [ρ, L] using hsmall)

private theorem exists_smooth_convex_potential_of_centeredBody {n : ℕ}
    (K : CenteredBody n) :
    ∃ φ : Space n → ℝ,
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ Set.univ φ ∧
        ∀ x : Space n,
          |φ x -
            SupportFunction.supportFunction K.carrier x| ≤ 1 := by
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  obtain ⟨φ, hφ, hconvex, hclose⟩ :=
    exists_smooth_convex_potential_uniformly_close
      K.compact hnonempty (show (0 : ℝ) < 1 by norm_num)
  exact ⟨φ, hφ, hconvex, fun x => (hclose x).le⟩

private def smoothConvexPotential {n : ℕ} (K : CenteredBody n) :
    Space n → ℝ :=
  (exists_smooth_convex_potential_of_centeredBody K).choose

private theorem smoothConvexPotential_contDiff {n : ℕ}
    (K : CenteredBody n) :
    ContDiff ℝ ∞ (smoothConvexPotential K) :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.1

private theorem smoothConvexPotential_convex {n : ℕ}
    (K : CenteredBody n) :
    ConvexOn ℝ Set.univ (smoothConvexPotential K) :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.2.1

private theorem smoothConvexPotential_bounded {n : ℕ}
    (K : CenteredBody n) (x : Space n) :
    |smoothConvexPotential K x -
      SupportFunction.supportFunction K.carrier x| ≤ 1 :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.2.2 x

end ArbitraryBodySmoothConvexPotentialBridge

namespace JetAdaptedOrthonormalBasis

open Set Module
open scoped BigOperators InnerProductSpace

private theorem starProjection_commute_of_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (U W : Submodule ℂ V) (hUW : U ≤ W) :
    Commute (U.starProjection : V →ₗ[ℂ] V)
      (W.starProjection : V →ₗ[ℂ] V) := by
  apply LinearMap.ext
  intro x
  change U.starProjection (W.starProjection x) =
    W.starProjection (U.starProjection x)
  have h := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le hUW) x
  rw [ContinuousLinearMap.comp_apply] at h
  rw [h]
  exact (Submodule.starProjection_eq_self_iff.mpr
    (hUW (U.starProjection_apply_mem x))).symm

private theorem exists_orthonormalBasis_simultaneously_adapted_finite
    {ι V : Type*} [Finite ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ι → Submodule ℂ V)
    (hchain : ∀ i j, F i ≤ F j ∨ F j ≤ F i) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∀ (j : ι) (i : Fin (Module.finrank ℂ V)),
        b i ∈ F j ∨ b i ∈ (F j)ᗮ := by
  classical
  let fintype : Fintype ι := Fintype.ofFinite ι
  let T : ι → V →ₗ[ℂ] V :=
    fun j => ((F j).starProjection : V →ₗ[ℂ] V)
  have hsym : ∀ j, (T j).IsSymmetric := fun j =>
    (F j).starProjection_isSymmetric
  have hcomm : Pairwise (fun i j => Commute (T i) (T j)) := by
    intro i j _
    rcases hchain i j with hij | hji
    · exact starProjection_commute_of_le (F i) (F j) hij
    · exact (starProjection_commute_of_le (F j) (F i) hji).symm
  let code : (ι → Fin 2) → (ι → ℂ) :=
    fun σ i => ((σ i).val : ℂ)
  have hcode : Function.Injective code := by
    intro σ τ hστ
    funext i
    apply Fin.ext
    have hi : ((σ i).val : ℂ) = ((τ i).val : ℂ) := by
      simpa [code] using congrFun hστ i
    exact_mod_cast hi
  let J : (ι → Fin 2) → Submodule ℂ V :=
    fun σ => ⨅ i, Module.End.eigenspace (T i) (code σ i)
  have horth :=
    (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym).comp hcode
  have hfull :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have htop : (⨆ σ : ι → Fin 2, J σ) = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply iSup_le
    intro χ
    let σ : ι → Fin 2 :=
      fun i => if χ i = 0 then 0 else 1
    refine le_trans ?_ (le_iSup (fun q => J q) σ)
    intro x hx
    change x ∈ (⨅ i, Module.End.eigenspace (T i) (χ i)) at hx
    change x ∈ (⨅ i, Module.End.eigenspace (T i) (code σ i))
    apply (Submodule.mem_iInf _).mpr
    intro i
    have heig := Module.End.mem_eigenspace_iff.mp
      (((Submodule.mem_iInf _).mp hx) i)
    apply Module.End.mem_eigenspace_iff.mpr
    by_cases hzero : χ i = 0
    · simpa [code, σ, hzero] using heig
    · have hscaled : χ i • x ∈ F i := by
        rw [← heig]
        exact (F i).starProjection_apply_mem x
      have hmem := (F i).smul_mem (χ i)⁻¹ hscaled
      have hxF : x ∈ F i := by
        simpa only [smul_smul, ne_eq, hzero, not_false_eq_true, inv_mul_cancel₀, one_smul] using
          hmem
      have hfix : (F i).starProjection x = x :=
        Submodule.starProjection_eq_self_iff.mpr hxF
      simpa [T, code, σ, hzero] using hfix
  have hinternal : DirectSum.IsInternal J := by
    apply horth.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff]
    exact htop
  let b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V :=
    hinternal.subordinateOrthonormalBasis rfl horth
  refine ⟨b, ?_⟩
  intro j i
  let σ : ι → Fin 2 :=
    hinternal.subordinateOrthonormalBasisIndex rfl i horth
  have hbi : b i ∈ J σ :=
    hinternal.subordinateOrthonormalBasis_subordinate rfl i horth
  have heig : T j (b i) = code σ j • b i :=
    Module.End.mem_eigenspace_iff.mp
      (((Submodule.mem_iInf _).mp hbi) j)
  by_cases hzero : code σ j = 0
  · right
    have hproj : (F j).starProjection (b i) = 0 := by
      simpa [T, hzero] using heig
    have hker : b i ∈ (F j).starProjection.ker :=
      (LinearMap.mem_ker).2 hproj
    simpa only [Submodule.ker_starProjection] using hker
  · left
    have hscaled : code σ j • b i ∈ F j := by
      rw [← heig]
      exact (F j).starProjection_apply_mem (b i)
    have hmem := (F j).smul_mem (code σ j)⁻¹ hscaled
    simpa only [smul_smul, ne_eq, hzero, not_false_eq_true, inv_mul_cancel₀, one_smul] using hmem

private theorem finite_range_antitone_submodule
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ℕ → Submodule ℂ V) (hF : Antitone F) :
    (Set.range F).Finite := by
  classical
  let d := Module.finrank ℂ V
  let rankFin : Submodule ℂ V → Fin (d + 1) := fun S =>
    ⟨Module.finrank ℂ S,
      Nat.lt_succ_of_le (Submodule.finrank_le S)⟩
  apply Set.Finite.of_finite_image (f := rankFin)
    (Set.toFinite (rankFin '' Set.range F))
  intro S hS W hW heq
  obtain ⟨i, rfl⟩ := hS
  obtain ⟨j, rfl⟩ := hW
  have hr : Module.finrank ℂ (F i) = Module.finrank ℂ (F j) := by
    simpa only using congrArg Fin.val heq
  rcases le_total i j with hij | hji
  · exact (Submodule.eq_of_le_of_finrank_eq (hF hij) hr.symm).symm
  · exact Submodule.eq_of_le_of_finrank_eq (hF hji) hr

private theorem exists_orthonormalBasis_simultaneously_adapted
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ℕ → Submodule ℂ V) (hF : Antitone F) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∀ (j : ℕ) (i : Fin (Module.finrank ℂ V)),
        b i ∈ F j ∨ b i ∈ (F j)ᗮ := by
  classical
  let s : Set (Submodule ℂ V) := Set.range F
  have hs : s.Finite := finite_range_antitone_submodule F hF
  let : Fintype s := hs.fintype
  let G : s → Submodule ℂ V := Subtype.val
  have hchain : ∀ a b : s, G a ≤ G b ∨ G b ≤ G a := by
    intro a b
    obtain ⟨i, hi⟩ := a.property
    obtain ⟨j, hj⟩ := b.property
    rcases le_total i j with hij | hji
    · right
      simpa [G, ← hi, ← hj] using hF hij
    · left
      simpa [G, ← hi, ← hj] using hF hji
  obtain ⟨b, hb⟩ :=
    exists_orthonormalBasis_simultaneously_adapted_finite G hchain
  refine ⟨b, ?_⟩
  intro j i
  exact hb ⟨F j, ⟨j, rfl⟩⟩ i

end JetAdaptedOrthonormalBasis

namespace GenuineJetAdaptedBasisCounting

open Set Module
open scoped BigOperators InnerProductSpace

private def adaptedIndices {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V) :
    Finset ι := by
  classical
  exact Finset.univ.filter (fun i => b i ∈ S)

private theorem span_adaptedIndices_eq {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V)
    (hb : ∀ i, b i ∈ S ∨ b i ∈ Sᗮ) :
    Submodule.span ℂ
      (Set.range (fun i : adaptedIndices b S => b (i : ι))) = S := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : (i : ι) ∈
        Finset.univ.filter (fun q => b q ∈ S) := i.property
    exact (Finset.mem_filter.mp hi).2
  · intro x hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : b i ∈ S
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨i, ?_⟩, rfl⟩
      simpa only [adaptedIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · have horth : b i ∈ Sᗮ := (hb i).resolve_left hi
      have hcoeff : b.repr x i = 0 := by
        rw [b.repr_apply_apply]
        exact (Submodule.mem_orthogonal' S (b i)).mp horth x hx
      simp only [hcoeff, zero_smul, zero_mem]

private theorem card_adaptedIndices_eq_finrank {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V)
    (hb : ∀ i, b i ∈ S ∨ b i ∈ Sᗮ) :
    (adaptedIndices b S).card = Module.finrank ℂ S := by
  classical
  have hindependent :
      LinearIndependent ℂ
        (fun i : adaptedIndices b S => b (i : ι)) := by
    exact b.orthonormal.linearIndependent.comp
      (fun i : adaptedIndices b S => (i : ι)) Subtype.val_injective
  have hcard := finrank_span_eq_card hindependent
  rw [span_adaptedIndices_eq b S hb] at hcard
  simpa only [Fintype.card_coe] using hcard.symm

end GenuineJetAdaptedBasisCounting

namespace LaurentJetSeparatedness

open Set Filter Module
open scoped BigOperators Topology

private def bodyRadius {n : ℕ} (K : CenteredBody n) : ℝ :=
  Classical.choose K.compact.isBounded.exists_pos_norm_le

private theorem bodyRadius_pos {n : ℕ} (K : CenteredBody n) :
    0 < bodyRadius K :=
  (Classical.choose_spec K.compact.isBounded.exists_pos_norm_le).1

private theorem norm_le_bodyRadius {n : ℕ} (K : CenteredBody n)
    (x : Space n) (hx : x ∈ K.carrier) :
    ‖x‖ ≤ bodyRadius K :=
  (Classical.choose_spec K.compact.isBounded.exists_pos_norm_le).2 x hx

private theorem analyticAt_torusCharacter {n : ℕ}
    (m : Fin n → ℤ)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ (TorusCharacters.torusCharacter m) p := by
  unfold TorusCharacters.torusCharacter
    TorusCharacters.characterExponent
  apply AnalyticAt.cexp'
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.fun_mul
    ((ContinuousLinearMap.proj i :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).analyticAt p)

private theorem analyticAt_normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ
      (AdaptedBergmanBasis.normalizedHolomorphicMonomial
        K hk φ u) p := by
  unfold AdaptedBergmanBasis.normalizedHolomorphicMonomial
  exact analyticAt_const.fun_mul
    (analyticAt_torusCharacter
      (WeightedTorusHilbert.integerExponent K hk u) p)

end LaurentJetSeparatedness

namespace LaplaceAsymptotics

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

private def phase {n : ℕ} (u : Space n)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  SupportFunction.pairing u x - φ x

private def legendreTransform {n : ℕ}
    (φ : Space n → ℝ) (u : Space n) : ℝ :=
  sSup (Set.range (phase u φ))

private theorem continuous_phase {n : ℕ} (u : Space n)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous (phase u φ) :=
  (SupportFunction.continuous_pairing_right u).sub hφ

private theorem exists_phase_le_const_sub_mul_sum_abs {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      phase u φ x ≤ C - δ * ∑ i, |x i| := by
  obtain ⟨δ, hδ, hgap⟩ :=
    MonomialIntegrability.interior_sum_abs_gap hcompact hu
  refine ⟨δ, hδ, fun x => ?_⟩
  have hsupport := (abs_le.mp (hbounded x)).1
  have hinterior := hgap x
  unfold phase
  linarith

private theorem exists_phase_maximizer {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ x : Space n, ∀ y : Space n,
      phase u φ y ≤ phase u φ x := by
  obtain ⟨δ, hδ, hcoercive⟩ :=
    exists_phase_le_const_sub_mul_sum_abs hcompact hu hbounded
  let R : ℝ := max 0 ((C - phase u φ 0) / δ)
  apply (continuous_phase u hφ).exists_forall_ge' 0
  filter_upwards [
    (isCompact_closedBall (0 : Space n) R).compl_mem_cocompact
  ] with x hx
  have hxnorm : R < ‖x‖ := by
    apply lt_of_not_ge
    intro h
    apply hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  have hR : C - phase u φ 0 ≤ δ * R := by
    have hrange : (C - phase u φ 0) / δ ≤ R :=
      le_max_right _ _
    have hscale := (div_le_iff₀ hδ).mp hrange
    nlinarith
  have hnorm := SupportFunction.norm_le_sum_abs x
  have hscale := mul_lt_mul_of_pos_left hxnorm hδ
  have hcoerce := hcoercive x
  nlinarith [mul_le_mul_of_nonneg_left hnorm hδ.le]

private theorem legendreTransform_eq_of_maximizer {n : ℕ}
    {u : Space n} {φ : Space n → ℝ}
    (x : Space n)
    (hmax : ∀ y : Space n,
      phase u φ y ≤ phase u φ x) :
    legendreTransform φ u = phase u φ x := by
  unfold legendreTransform
  apply le_antisymm
  · apply csSup_le
    · exact ⟨phase u φ x, ⟨x, rfl⟩⟩
    · rintro _ ⟨y, rfl⟩
      exact hmax y
  · apply le_csSup
    · exact ⟨phase u φ x, by
        rintro _ ⟨y, rfl⟩
        exact hmax y⟩
    · exact ⟨x, rfl⟩

private theorem exists_legendre_maximizer {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ x : Space n,
      phase u φ x = legendreTransform φ u ∧
      ∀ y : Space n, phase u φ y ≤ phase u φ x := by
  obtain ⟨x, hx⟩ :=
    exists_phase_maximizer hcompact hu hφ hbounded
  exact ⟨x, (legendreTransform_eq_of_maximizer x hx).symm, hx⟩

end LaplaceAsymptotics

namespace BergmanAsymptotics

open Set MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology

private def actualHessianBilinear {n : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    Space n →ₗ[ℝ] Space n →ₗ[ℝ] ℝ where
  toFun v := (fderiv ℝ (fderiv ℝ φ) x v).toLinearMap
  map_add' v w := by
    ext z
    simp only [map_add, ContinuousLinearMap.toLinearMap_add, LinearMap.coe_comp,
      LinearMap.coe_single,
      Function.comp_apply, LinearMap.add_apply, ContinuousLinearMap.coe_coe]
  map_smul' a v := by
    ext z
    simp only [map_smul, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_comp,
      LinearMap.coe_smul,
      ContinuousLinearMap.coe_coe, LinearMap.coe_single, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul, Real.ringHom_apply]

private def actualHessianMatrix {n : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂' ℝ (actualHessianBilinear φ x)

private def pairingLinear {n : ℕ}
    (u : Space n) : Space n →ₗ[ℝ] ℝ where
  toFun := SupportFunction.pairing u
  map_add' x y :=
    MonomialDivergence.pairing_add_right u x y
  map_smul' c x := by
    simpa only [Real.ringHom_apply, smul_eq_mul] using
      MonomialDivergence.pairing_smul_right c u x

end BergmanAsymptotics

namespace GlobalBergmanKernelBound

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

private theorem supportFunction_add_smul_le {n : ℕ}
    (K : CenteredBody n)
    (x v : Space n) {t : ℝ} (ht : 0 ≤ t) :
    SupportFunction.supportFunction K.carrier (x + t • v) ≤
      SupportFunction.supportFunction K.carrier x +
        t * SupportFunction.supportFunction K.carrier v := by
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  apply SupportFunction.supportFunction_le hnonempty _
  intro u hu
  have hx := SupportFunction.pairing_le_supportFunction
    K.compact hu x
  have hv := SupportFunction.pairing_le_supportFunction
    K.compact hu v
  calc
    SupportFunction.pairing u (x + t • v) =
        SupportFunction.pairing u x +
          t * SupportFunction.pairing u v := by
      simp only [SupportFunction.pairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        mul_left_comm, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ SupportFunction.supportFunction K.carrier x +
        t * SupportFunction.supportFunction K.carrier v :=
      add_le_add hx (mul_le_mul_of_nonneg_left hv ht)

private theorem convex_extrapolation_lower {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (x y : Space n) {t : ℝ} (ht : 1 ≤ t) :
    φ y + t * (φ x - φ y) ≤ φ (y + t • (x - y)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hinvnonneg : 0 ≤ (1 / t : ℝ) := by positivity
  have hinvle : (1 / t : ℝ) ≤ 1 := by
    apply (div_le_iff₀ htpos).mpr
    simpa only [one_mul] using ht
  have ha : 0 ≤ 1 - (1 / t : ℝ) := sub_nonneg.mpr hinvle
  have hsum : (1 - (1 / t : ℝ)) + 1 / t = 1 := by ring
  have hpoint :
      (1 - (1 / t : ℝ)) • y +
          (1 / t : ℝ) • (y + t • (x - y)) = x := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hconv := hφ.2
    (Set.mem_univ y)
    (Set.mem_univ (y + t • (x - y)))
    ha hinvnonneg hsum
  rw [hpoint] at hconv
  simp only [smul_eq_mul] at hconv
  have hscaled := mul_le_mul_of_nonneg_left hconv htpos.le
  have hcancel :
      t * ((1 - (1 / t : ℝ)) * φ y + (1 / t : ℝ) *
        φ (y + t • (x - y))) =
      (t - 1) * φ y + φ (y + t • (x - y)) := by
    field_simp
  rw [hcancel] at hscaled
  linarith

private theorem convex_supportCompatible_sub_le_support {n : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (x y : Space n) :
    φ x - φ y ≤
      SupportFunction.supportFunction K.carrier (x - y) := by
  by_contra hnot
  have hgap : 0 <
      φ x - φ y -
        SupportFunction.supportFunction K.carrier (x - y) := by
    have hstrict := lt_of_not_ge hnot
    linarith
  let gap : ℝ :=
    φ x - φ y -
      SupportFunction.supportFunction K.carrier (x - y)
  have hgappos : 0 < gap := hgap
  let D : ℝ :=
    SupportFunction.supportFunction K.carrier y + C - φ y
  let t : ℝ := max 1 (D / gap + 1)
  have ht : 1 ≤ t := le_max_left _ _
  have hlarge : D < t * gap := by
    have hmax : D / gap + 1 ≤ t := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hmax hgappos.le
    have hcancel : (D / gap + 1) * gap = D + gap := by
      field_simp
    rw [hcancel] at hmul
    linarith
  have hconv := convex_extrapolation_lower hconvex x y ht
  have hsupport := supportFunction_add_smul_le
    K y (x - y) (show 0 ≤ t from (zero_le_one.trans ht))
  have hupper := (abs_le.mp (hbounded (y + t • (x - y)))).2
  have hcombined :
      φ (y + t • (x - y)) ≤
        SupportFunction.supportFunction K.carrier y +
          t * SupportFunction.supportFunction K.carrier (x - y) + C := by
    linarith
  dsimp [D, gap] at hlarge
  linarith

private theorem convex_supportCompatible_lipschitz {n : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C) :
    LipschitzWith
      (Real.toNNReal ((n : ℝ) *
        LaurentJetSeparatedness.bodyRadius K)) φ := by
  apply LipschitzWith.of_le_add_mul'
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)
  intro x y
  have hrec := convex_supportCompatible_sub_le_support
    K hconvex hbounded x y
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  obtain ⟨u, hu, hmax⟩ :=
    SupportFunction.supportFunction_attained
      K.compact hnonempty (x - y)
  have hradius := LaurentJetSeparatedness.norm_le_bodyRadius
    K u hu
  have hpair :=
    MonomialDivergence.abs_pairing_le_dimension_mul_norm
      u (x - y)
  have hsupport :
      SupportFunction.supportFunction K.carrier (x - y) ≤
        ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y := by
    rw [hmax, dist_eq_norm]
    calc
      SupportFunction.pairing u (x - y) ≤
          |SupportFunction.pairing u (x - y)| := le_abs_self _
      _ ≤ ((n : ℝ) * ‖u‖) * ‖x - y‖ := hpair
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hradius (Nat.cast_nonneg n))
          (norm_nonneg _)
  linarith

private def phaseSlopeBound {n : ℕ} (K : CenteredBody n)
    (L : NNReal) : ℝ :=
  (n : ℝ) * LaurentJetSeparatedness.bodyRadius K + (L : ℝ)

private theorem phaseSlopeBound_nonneg {n : ℕ}
    (K : CenteredBody n) (L : NNReal) :
    0 ≤ phaseSlopeBound K L := by
  unfold phaseSlopeBound
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le)
    L.coe_nonneg

private def bodyPhaseSlopeBound {n : ℕ} (K : CenteredBody n) : ℝ :=
  2 * ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)

private theorem phaseSlopeBound_body {n : ℕ}
    (K : CenteredBody n) :
    phaseSlopeBound K
      (Real.toNNReal ((n : ℝ) *
        LaurentJetSeparatedness.bodyRadius K)) =
      bodyPhaseSlopeBound K := by
  have hnonneg : 0 ≤
      (n : ℝ) * LaurentJetSeparatedness.bodyRadius K :=
    mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  unfold phaseSlopeBound bodyPhaseSlopeBound
  rw [Real.coe_toNNReal _ hnonneg]
  ring

private theorem monomialExponent_norm_le_bodyRadius {n k : ℕ}
    (K : CenteredBody n)
    (u : LatticeAsymptotics.monomialIndex K k) :
    ‖(u : Space n)‖ ≤
      LaurentJetSeparatedness.bodyRadius K := by
  exact LaurentJetSeparatedness.norm_le_bodyRadius
    K u (interior_subset u.property.1)

private theorem phase_abs_sub_le {n k : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x y : Space n) :
    |LaplaceAsymptotics.phase (u : Space n) φ x -
      LaplaceAsymptotics.phase (u : Space n) φ y| ≤
      phaseSlopeBound K L * dist x y := by
  have hpair :
      |SupportFunction.pairing (u : Space n) x -
        SupportFunction.pairing (u : Space n) y| ≤
        ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          dist x y := by
    rw [← show
      SupportFunction.pairing (u : Space n) (x - y) =
        SupportFunction.pairing (u : Space n) x -
          SupportFunction.pairing (u : Space n) y by
        simp only [SupportFunction.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]]
    calc
      |SupportFunction.pairing (u : Space n) (x - y)| ≤
          ((n : ℝ) * ‖(u : Space n)‖) * ‖x - y‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u : Space n) (x - y)
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (monomialExponent_norm_le_bodyRadius K u)
            (Nat.cast_nonneg n))
          (norm_nonneg _)
      _ = ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y := by
        rw [dist_eq_norm]
  have hpot : |φ x - φ y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hφ.dist_le_mul x y
  calc
    |LaplaceAsymptotics.phase (u : Space n) φ x -
      LaplaceAsymptotics.phase (u : Space n) φ y| =
      |(SupportFunction.pairing (u : Space n) x -
        SupportFunction.pairing (u : Space n) y) -
        (φ x - φ y)| := by
      unfold LaplaceAsymptotics.phase
      congr 1
      ring
    _ ≤ |SupportFunction.pairing (u : Space n) x -
          SupportFunction.pairing (u : Space n) y| +
        |φ x - φ y| := abs_sub _ _
    _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y +
        (L : ℝ) * dist x y := add_le_add hpair hpot
    _ = phaseSlopeBound K L * dist x y := by
      unfold phaseSlopeBound
      ring

private theorem real_volume_ball_inv_nat {n k : ℕ}
    (hk : 0 < k) (x : Space n) :
    (volume : Measure (Space n)).real
      (Metric.ball x (k : ℝ)⁻¹) =
      (2 / (k : ℝ)) ^ n := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold Measure.real
  rw [Real.volume_pi_ball x (inv_pos.mpr hkreal)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [Fintype.card_fin, div_eq_mul_inv]

private theorem phase_lower_on_inv_nat_ball {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x v : Space n)
    (hv : v ∈ Metric.ball x (k : ℝ)⁻¹) :
    LaplaceAsymptotics.phase (u : Space n) φ x -
      phaseSlopeBound K L / (k : ℝ) ≤
      LaplaceAsymptotics.phase (u : Space n) φ v := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hdist : dist x v < (k : ℝ)⁻¹ := by
    simpa only [dist_comm] using Metric.mem_ball.mp hv
  have hS := phaseSlopeBound_nonneg K L
  have habs := phase_abs_sub_le K hφ u x v
  have hbound : phaseSlopeBound K L * dist x v ≤
      phaseSlopeBound K L / (k : ℝ) := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hdist.le hS
  have hdiff :
      LaplaceAsymptotics.phase (u : Space n) φ x -
        LaplaceAsymptotics.phase (u : Space n) φ v ≤
        |LaplaceAsymptotics.phase (u : Space n) φ x -
          LaplaceAsymptotics.phase (u : Space n) φ v| :=
    le_abs_self _
  linarith [hkreal]

private theorem eventually_bergmanDimension_le_volume_mul_pow
    {n : ℕ} (K : CenteredBody n) :
    ∀ᶠ k : ℕ in atTop,
      (BergmanMonomials.bergmanDimension K k : ℝ) ≤
        (normalizedVolume K.carrier + 1) * (k : ℝ) ^ n := by
  have hlimit := BergmanMonomials.bergmanDimension_div_pow_tendsto_volume K
  have hevent := hlimit.eventually
    (gt_mem_nhds (show normalizedVolume K.carrier <
      normalizedVolume K.carrier + 1 by linarith))
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with k hquot hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact (div_le_iff₀ (pow_pos hkreal n)).mp hquot.le

private def globalKernelPolynomialConstant {n : ℕ}
    (K : CenteredBody n) : ℝ :=
  (normalizedVolume K.carrier + 1) *
    Real.exp (bodyPhaseSlopeBound K) / (2 : ℝ) ^ n

private theorem globalKernelPolynomialConstant_pos {n : ℕ}
    (K : CenteredBody n) :
    0 < globalKernelPolynomialConstant K := by
  unfold globalKernelPolynomialConstant
  have hvolume := K.volume_pos
  positivity

private def globalKernelLogError {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℝ :=
  (Real.log (globalKernelPolynomialConstant K) +
    2 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)

private theorem tendsto_globalKernelLogError {n : ℕ}
    (K : CenteredBody n) :
    Tendsto (globalKernelLogError K) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun k : ℕ =>
        Real.log (globalKernelPolynomialConstant K) / (k : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_
      ((Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 one_ne_zero).comp hnat)
    exact Filter.Eventually.of_forall fun _ => by simp only [pow_one, one_mul, add_zero,
      Function.comp_apply]
  have hscaled := hlog.const_mul (2 * (n : ℝ))
  have hsum := hconst.add hscaled
  have hpoint : globalKernelLogError K =
      (fun k : ℕ =>
        Real.log (globalKernelPolynomialConstant K) / (k : ℝ) +
          2 * (n : ℝ) * (Real.log (k : ℝ) / (k : ℝ))) := by
    funext k
    unfold globalKernelLogError
    rw [add_div]
    ring
  rw [hpoint]
  simpa only [mul_zero, add_zero] using hsum

end GlobalBergmanKernelBound

namespace LaurentJetMultiplicityBridge

open Set Filter Module
open scoped BigOperators Topology

private def coordinateMultiplicity {n r : ℕ}
    (q : Fin r → Fin n) (i : Fin n) : ℕ := by
  classical
  exact Fintype.card {a : Fin r // q a = i}

private theorem sum_coordinateMultiplicity {n r : ℕ}
    (q : Fin r → Fin n) :
    (∑ i : Fin n, coordinateMultiplicity q i) = r := by
  classical
  unfold coordinateMultiplicity
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv q)).trans
    (Fintype.card_fin r)

private def multiIndexSigmaEquiv {n : ℕ} (α : Fin n → ℕ) :
    ((i : Fin n) × Fin (α i)) ≃ Fin (∑ i, α i) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_sigma, Fintype.card_fin])

private theorem multiIndexCoordinate_eq_sigma {n : ℕ}
    (α : Fin n → ℕ) (q : Fin (∑ i, α i)) :
    AdaptedBergmanBasis.multiIndexCoordinate α q =
      ((multiIndexSigmaEquiv α).symm q).1 := by
  rfl

private def multiIndexCoordinateFiberEquiv {n : ℕ}
    (α : Fin n → ℕ) (i : Fin n) :
    {q : Fin (∑ i, α i) //
      AdaptedBergmanBasis.multiIndexCoordinate α q = i} ≃
      Fin (α i) := by
  classical
  refine ((multiIndexSigmaEquiv α).symm.subtypeEquiv ?_).trans
    (Equiv.sigmaSubtype i)
  intro q
  exact ⟨fun h => (multiIndexCoordinate_eq_sigma α q).symm ▸ h,
    fun h => (multiIndexCoordinate_eq_sigma α q) ▸ h⟩

private theorem exists_multiIndexCoordinate_perm {n : ℕ}
    (α : Fin n → ℕ)
    (q : Fin (∑ i, α i) → Fin n)
    (hq : ∀ i : Fin n,
      Fintype.card {a : Fin (∑ i, α i) // q a = i} = α i) :
    ∃ σ : Equiv.Perm (Fin (∑ i, α i)),
      ∀ a, q a =
        AdaptedBergmanBasis.multiIndexCoordinate α (σ a) := by
  classical
  let e : ∀ i : Fin n,
      {a : Fin (∑ i, α i) // q a = i} ≃
        {a : Fin (∑ i, α i) //
          AdaptedBergmanBasis.multiIndexCoordinate α a = i} :=
    fun i => Fintype.equivOfCardEq (by
      calc
        Fintype.card {a : Fin (∑ i, α i) // q a = i} =
            α i := hq i
        _ = Fintype.card (Fin (α i)) :=
            (Fintype.card_fin (α i)).symm
        _ = Fintype.card
            {a : Fin (∑ i, α i) //
              AdaptedBergmanBasis.multiIndexCoordinate α a = i} :=
            (Fintype.card_congr
              (multiIndexCoordinateFiberEquiv α i)).symm)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  intro a
  exact (Equiv.ofFiberEquiv_map e a).symm

end LaurentJetMultiplicityBridge

namespace BergmanGeodesicConvexity

open Set Module
open scoped BigOperators InnerProductSpace

private def exponentialMoment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (r : ℕ) (t : ℝ) : ℝ :=
  ∑ i, w i * (order i : ℝ) ^ r *
    Real.exp (t * (order i : ℝ))

private def exponentialPartition {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (t : ℝ) : ℝ :=
  exponentialMoment w order 0 t

private theorem exponentialPartition_pos {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (t : ℝ) : 0 < exponentialPartition w order t := by
  classical
  obtain ⟨i, hi⟩ := hpositive
  unfold exponentialPartition exponentialMoment
  simp only [pow_zero, mul_one]
  apply lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    (Finset.mem_univ i)

private theorem hasDerivAt_exponentialMoment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (r : ℕ) (t : ℝ) :
    HasDerivAt (exponentialMoment w order r)
      (exponentialMoment w order (r + 1) t) t := by
  classical
  unfold exponentialMoment
  refine HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
    (fun i _ => ?_)
  exact ((((hasDerivAt_id t).mul_const (order i : ℝ)).exp).const_mul
    (w i * (order i : ℝ) ^ r)).congr_deriv (by
      simp only [id_eq, mul_comm, mul_one, mul_left_comm, mul_assoc, pow_succ])

private theorem hasDerivAt_exponentialPartition {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (t : ℝ) :
    HasDerivAt (exponentialPartition w order)
      (exponentialMoment w order 1 t) t := by
  change HasDerivAt (exponentialMoment w order 0)
    (exponentialMoment w order 1 t) t
  exact hasDerivAt_exponentialMoment w order 0 t

private theorem exponentialMoment_sq_le_partition_mul_second
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    exponentialMoment w order 1 t ^ 2 ≤
      exponentialPartition w order t *
        exponentialMoment w order 2 t := by
  classical
  let a : ι → ℝ := fun i =>
    w i * Real.exp (t * (order i : ℝ))
  have ha : ∀ i, 0 ≤ a i := fun i =>
    mul_nonneg (hw i) (Real.exp_pos _).le
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset ι)
    (r := fun i => a i * (order i : ℝ))
    (f := a)
    (g := fun i => a i * (order i : ℝ) ^ 2)
    (fun i _ => ha i)
    (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
    (fun i _ => (by ring : (a i * (order i : ℝ)) ^ 2 =
      a i * (a i * (order i : ℝ) ^ 2)).le)
  simpa [exponentialMoment, exponentialPartition, a,
    mul_assoc, mul_left_comm, mul_comm] using hcauchy

private def logarithmicPotential {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (k : ℝ) (t : ℝ) : ℝ :=
  Real.log (exponentialPartition w order t) / k

private theorem hasDerivAt_logarithmicPotential {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (k t : ℝ) :
    HasDerivAt (logarithmicPotential w order k)
      (exponentialMoment w order 1 t /
        exponentialPartition w order t / k) t := by
  unfold logarithmicPotential
  exact ((hasDerivAt_exponentialPartition w order t).log
    (exponentialPartition_pos w order hw hpositive t).ne').div_const k

private theorem hasDerivAt_logarithmicSlope {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (k t : ℝ) :
    HasDerivAt
      (fun q : ℝ => exponentialMoment w order 1 q /
        exponentialPartition w order q / k)
      ((exponentialMoment w order 2 t *
          exponentialPartition w order t -
        exponentialMoment w order 1 t *
        exponentialMoment w order 1 t) /
        (exponentialPartition w order t) ^ 2 / k) t := by
  exact ((hasDerivAt_exponentialMoment w order 1 t).fun_div
    (hasDerivAt_exponentialPartition w order t)
    (exponentialPartition_pos w order hw hpositive t).ne').div_const k

private theorem convexOn_logarithmicPotential {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) :
    ConvexOn ℝ Set.univ (logarithmicPotential w order k) := by
  have hderiv (t : ℝ) :
      deriv (logarithmicPotential w order k) t =
        exponentialMoment w order 1 t /
          exponentialPartition w order t / k :=
    (hasDerivAt_logarithmicPotential w order hw hpositive k t).deriv
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t =>
      (hasDerivAt_logarithmicPotential w order hw hpositive k t).differentiableAt
  · have heq : deriv (logarithmicPotential w order k) =
        fun t : ℝ => exponentialMoment w order 1 t /
          exponentialPartition w order t / k :=
        funext hderiv
    rw [heq]
    exact fun t =>
      (hasDerivAt_logarithmicSlope w order hw hpositive k t).differentiableAt
  · intro t
    change 0 ≤ deriv (deriv (logarithmicPotential w order k)) t
    have heq : deriv (logarithmicPotential w order k) =
        fun q : ℝ => exponentialMoment w order 1 q /
          exponentialPartition w order q / k :=
        funext hderiv
    rw [heq,
      (hasDerivAt_logarithmicSlope w order hw hpositive k t).deriv]
    apply div_nonneg
    · apply div_nonneg
      · have hvar :=
          exponentialMoment_sq_le_partition_mul_second
            w order hw t
        nlinarith
      · exact sq_nonneg _
    · exact hk.le

private theorem logarithmicPotential_deriv_nonneg {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 ≤ deriv (logarithmicPotential w order k) t := by
  rw [(hasDerivAt_logarithmicPotential
    w order hw hpositive k t).deriv]
  apply div_nonneg
  · apply div_nonneg
    · unfold exponentialMoment
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hw i) (by positivity))
          (Real.exp_pos _).le
    · exact (exponentialPartition_pos w order hw hpositive t).le
  · exact hk.le

private theorem logarithmicPotential_deriv_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) (J : ℕ)
    (horder : ∀ i, order i ≤ J) (t : ℝ) :
    deriv (logarithmicPotential w order k) t ≤
      (J : ℝ) / k := by
  rw [(hasDerivAt_logarithmicPotential
    w order hw hpositive k t).deriv]
  apply div_le_div_of_nonneg_right _ hk.le
  apply (div_le_iff₀
    (exponentialPartition_pos w order hw hpositive t)).mpr
  unfold exponentialMoment exponentialPartition
    exponentialMoment
  simp only [pow_one, pow_zero, mul_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (order i : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast horder i
  calc
    w i * (order i : ℝ) * Real.exp (t * (order i : ℝ)) ≤
        w i * (J : ℝ) * Real.exp (t * (order i : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (hw i))
        (Real.exp_pos _).le
    _ = (J : ℝ) * (w i * Real.exp (t * (order i : ℝ))) := by
      ring

end BergmanGeodesicConvexity

namespace BodyScale

open Set MeasureTheory

private def canonicalScale {n : ℕ} (K : CenteredBody n) : ℝ :=
  ((n.factorial : ℝ) * normalizedVolume K.carrier) ^
    ((n : ℝ)⁻¹)

private theorem factorial_mul_volume_pos {n : ℕ}
    (K : CenteredBody n) :
    0 < (n.factorial : ℝ) * normalizedVolume K.carrier := by
  exact mul_pos (by exact_mod_cast Nat.factorial_pos n) K.volume_pos

private theorem canonicalScale_pos {n : ℕ}
    (K : CenteredBody n) : 0 < canonicalScale K := by
  unfold canonicalScale
  exact Real.rpow_pos_of_pos (factorial_mul_volume_pos K) _

private theorem canonicalScale_pow {n : ℕ} (hn : 0 < n)
    (K : CenteredBody n) :
    canonicalScale K ^ n =
      (n.factorial : ℝ) * normalizedVolume K.carrier := by
  unfold canonicalScale
  exact Real.rpow_inv_natCast_pow
    (factorial_mul_volume_pos K).le (Nat.ne_of_gt hn)

end BodyScale

namespace JetAsymptotics

open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology

private theorem tendsto_floor_mul_div_nat {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun k : ℕ => (Nat.floor (t * (k : ℝ)) : ℝ) / (k : ℝ))
      atTop (𝓝 t) := by
  refine Filter.Tendsto.congr' ?_
    ((tendsto_nat_floor_mul_div_atTop ht).comp
      tendsto_natCast_atTop_atTop)
  exact Filter.Eventually.of_forall fun _ => rfl

private theorem tendsto_shifted_floor_mul_div_nat
    {t : ℝ} (ht : 0 ≤ t) (b : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 t) := by
  have h := (tendsto_floor_mul_div_nat ht).add
    (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
  simpa only [Nat.cast_add, add_div, add_zero] using h

private theorem tendsto_choose_floor_mul_div_pow
    (r b : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
          (k : ℝ) ^ r)
      atTop (𝓝 (t ^ r / (r.factorial : ℝ))) := by
  have hshift :
      Tendsto (fun k : ℕ => Nat.floor (t * (k : ℝ)) + b)
        atTop atTop :=
    (tendsto_add_atTop_nat b).comp
      (tendsto_nat_floor_mul_atTop t ht)
  have hequiv :
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ))
        ~[atTop]
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
          (r.factorial : ℝ))) := by
    simpa only [Nat.cast_add, Function.comp_def] using
      (isEquivalent_choose r).comp_tendsto hshift
  have hnonzero : ∀ᶠ k : ℕ in atTop,
      ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
        (r.factorial : ℝ) ≠ 0 := by
    filter_upwards [hshift.eventually (eventually_ge_atTop (1 : ℕ))]
      with k hk
    have hm : 0 < Nat.floor (t * (k : ℝ)) + b :=
      lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  have hratio :
      Tendsto
        (fun k : ℕ =>
          (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (r.factorial : ℝ)))
        atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hnonzero).mp hequiv
  have hscale := tendsto_shifted_floor_mul_div_nat ht.le b
  have hcombined := (hratio.mul (hscale.pow r)).div_const
    (r.factorial : ℝ)
  have htarget :
      Tendsto
        (fun k : ℕ =>
          (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (r.factorial : ℝ)) *
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (k : ℝ) ^ r) /
            (r.factorial : ℝ))
        atTop (𝓝 (t ^ r / (r.factorial : ℝ))) := by
    convert hcombined using 1 <;> simp [div_pow]
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hshift.eventually (eventually_ge_atTop (1 : ℕ))]
      with k hk hm
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hmne :
      ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ≠ 0 := by
    have hmpos : 0 < Nat.floor (t * (k : ℝ)) + b :=
      lt_of_lt_of_le Nat.zero_lt_one hm
    exact_mod_cast Nat.ne_of_gt hmpos
  have hfact : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem tendsto_normalized_jetLayercake_profile {n : ℕ}
    (K : CenteredBody n) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) : ℕ) : ℝ) *
            (BergmanMonomials.bergmanDimension K k : ℝ) -
          (((n + Nat.floor (t * (k : ℝ))).choose
            (n + 1) : ℕ) : ℝ)) /
          ((k : ℝ) *
            (BergmanMonomials.bergmanDimension K k : ℝ)))
      atTop
      (𝓝 (t - t ^ (n + 1) /
        (((n + 1).factorial : ℝ) *
          normalizedVolume K.carrier))) := by
  have hfloor := tendsto_floor_mul_div_nat ht.le
  have hchoose :
      Tendsto
        (fun k : ℕ =>
          (((n + Nat.floor (t * (k : ℝ))).choose
            (n + 1) : ℕ) : ℝ) / (k : ℝ) ^ (n + 1))
        atTop
        (𝓝 (t ^ (n + 1) / ((n + 1).factorial : ℝ))) := by
    simpa only [Nat.add_comm] using
      tendsto_choose_floor_mul_div_pow (n + 1) n ht
  have hdim :=
    BergmanMonomials.bergmanDimension_div_pow_tendsto_volume K
  have hquot := hchoose.div hdim K.volume_pos.ne'
  have htarget :
      Tendsto
        (fun k : ℕ =>
          (Nat.floor (t * (k : ℝ)) : ℝ) / (k : ℝ) -
            ((((n + Nat.floor (t * (k : ℝ))).choose
              (n + 1) : ℕ) : ℝ) / (k : ℝ) ^ (n + 1)) /
              ((BergmanMonomials.bergmanDimension K k : ℝ) /
                (k : ℝ) ^ n))
        atTop
        (𝓝 (t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier))) := by
    simpa only [div_div, Pi.div_apply] using hfloor.sub hquot
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkpos
  have hdne :
      (BergmanMonomials.bergmanDimension K k : ℝ) ≠ 0 := by
    exact_mod_cast
      (BergmanMonomials.bergmanDimension_pos K hkpos).ne'
  rw [pow_succ]
  field_simp

private theorem normalized_jetLayercake_value_at_bodyScale {n : ℕ}
    (K : CenteredBody n) {c : ℝ}
    (hscale : c ^ n = (n.factorial : ℝ) *
      normalizedVolume K.carrier) :
    c - c ^ (n + 1) /
      (((n + 1).factorial : ℝ) *
        normalizedVolume K.carrier) =
      (n : ℝ) * c / ((n : ℝ) + 1) := by
  have hvolume : normalizedVolume K.carrier ≠ 0 :=
    K.volume_pos.ne'
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsucc : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [pow_succ, hscale, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end JetAsymptotics

namespace Geometry

open Set MeasureTheory
open scoped BigOperators

private def coordinateSum (n : ℕ) : Space n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Real.ringHom_apply, Finset.mul_sum]

private theorem coordinateSum_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (coordinateSum n) := by
  classical
  intro t
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun j => if j = i then t else 0, ?_⟩
  simp only [coordinateSum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

private theorem continuous_coordinateSum (n : ℕ) :
    Continuous (coordinateSum n) := by
  exact continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)

private theorem mem_centeredSimplex_iff {n : ℕ} {y : Space n} :
    y ∈ centeredSimplex n ↔
      (∀ i, -(1 : ℝ) ≤ y i) ∧ (∑ i, y i) ≤ 1 := by
  classical
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (∀ i, -(1 : ℝ) ≤ ((n : ℝ) + 1) * x i - 1) ∧
      (∑ i, (((n : ℝ) + 1) * x i - 1)) ≤ 1
    constructor
    · intro i
      have hp := mul_nonneg hc.le (hx.1 i)
      linarith
    · have hsum : ((n : ℝ) + 1) * (∑ i, x i) ≤ (n : ℝ) + 1 :=
        (mul_le_mul_of_nonneg_left hx.2 hc.le).trans_eq (mul_one _)
      simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, tsub_le_iff_right, ge_iff_le] using
        (show ((n : ℝ) + 1) * (∑ i, x i) - (n : ℝ) ≤ 1 by linarith)
  · rintro ⟨hy, hsum⟩
    let x : Space n := fun i => (y i + 1) / ((n : ℝ) + 1)
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (by linarith [hy i]) hc.le
    · change (∑ i, (y i + 1) / ((n : ℝ) + 1)) ≤ 1
      rw [← Finset.sum_div, div_le_iff₀ hc]
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, one_mul] using
        (show (∑ i, y i) + (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
    · funext i
      change ((n : ℝ) + 1) * ((y i + 1) / ((n : ℝ) + 1)) - 1 = y i
      field_simp
      ring

private theorem isClosed_standardSimplex (n : ℕ) :
    IsClosed (standardSimplex n) := by
  have hcoords :
      IsClosed (⋂ i : Fin n, {x : Space n | 0 ≤ x i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {x : Space n | (∑ i, x i) ≤ 1} :=
    isClosed_le (continuous_coordinateSum n) continuous_const
  have hset : standardSimplex n =
      (⋂ i : Fin n, {x : Space n | 0 ≤ x i}) ∩
        {x : Space n | (∑ i, x i) ≤ 1} := by
    ext x
    simp only [standardSimplex, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [hset]
  exact hcoords.inter hsum

private theorem isCompact_standardSimplex (n : ℕ) :
    IsCompact (standardSimplex n) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (0 : Space n)) (b := 1))
    (isClosed_standardSimplex n)
  intro x hx
  constructor
  · exact hx.1
  · intro i
    change x i ≤ 1
    exact (Finset.single_le_sum (fun j _ => hx.1 j)
      (Finset.mem_univ i)).trans hx.2

private theorem continuous_simplexDilation (n : ℕ) :
    Continuous (simplexDilation n) := by
  apply continuous_pi
  intro i
  exact (continuous_const.mul (continuous_apply i)).sub continuous_const

private theorem isCompact_centeredSimplex (n : ℕ) :
    IsCompact (centeredSimplex n) := by
  exact (isCompact_standardSimplex n).image (continuous_simplexDilation n)

private theorem convex_centeredSimplex (n : ℕ) :
    Convex ℝ (centeredSimplex n) := by
  intro x hx y hy a b ha hb hab
  have hx' := mem_centeredSimplex_iff.mp hx
  have hy' := mem_centeredSimplex_iff.mp hy
  apply mem_centeredSimplex_iff.mpr
  constructor
  · intro i
    change -(1 : ℝ) ≤ a * x i + b * y i
    have hax : 0 ≤ a * (x i + 1) := mul_nonneg ha (by linarith [hx'.1 i])
    have hby : 0 ≤ b * (y i + 1) := mul_nonneg hb (by linarith [hy'.1 i])
    nlinarith
  · change (∑ i, (a * x i + b * y i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * (∑ i, x i) + b * (∑ i, y i)
          ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha)
              (mul_le_mul_of_nonneg_left hy'.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

private theorem isOpen_strict_centered_halfspaces (n : ℕ) :
    IsOpen {x : Space n |
      (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1} := by
  have hcoords :
      IsOpen (⋂ i : Fin n, {x : Space n | -(1 : ℝ) < x i}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hsum : IsOpen {x : Space n | (∑ i, x i) < 1} :=
    isOpen_lt (continuous_coordinateSum n) continuous_const
  have hset :
      {x : Space n |
        (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1} =
        (⋂ i : Fin n, {x : Space n | -(1 : ℝ) < x i}) ∩
          {x : Space n | (∑ i, x i) < 1} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [hset]
  exact hcoords.inter hsum

private theorem coordinate_lt_of_mem_interior_centeredSimplex
    {n : ℕ} {x : Space n}
    (hx : x ∈ interior (centeredSimplex n)) (i : Fin n) :
    -(1 : ℝ) < x i := by
  have hsub : centeredSimplex n ⊆
      (fun y : Space n => y i) ⁻¹' Ici (-(1 : ℝ)) := by
    intro y hy
    exact (mem_centeredSimplex_iff.mp hy).1 i
  have hi := interior_mono hsub hx
  have hopen : IsOpenMap (fun y : Space n => y i) :=
    isOpenMap_eval i
  rw [← hopen.preimage_interior_eq_interior_preimage
    (continuous_apply i) (Ici (-(1 : ℝ))), interior_Ici] at hi
  exact hi

private theorem coordinateSum_lt_of_mem_interior_centeredSimplex
    {n : ℕ} (hn : 0 < n) {x : Space n}
    (hx : x ∈ interior (centeredSimplex n)) :
    (∑ i, x i) < 1 := by
  have hsub : centeredSimplex n ⊆
      (coordinateSum n) ⁻¹' Iic (1 : ℝ) := by
    intro y hy
    exact (mem_centeredSimplex_iff.mp hy).2
  have hi := interior_mono hsub hx
  have hopen : IsOpenMap (coordinateSum n) :=
    (coordinateSum n).isOpenMap_of_finiteDimensional
      (coordinateSum_surjective n hn)
  rw [← hopen.preimage_interior_eq_interior_preimage
    (continuous_coordinateSum n) (Iic (1 : ℝ)), interior_Iic] at hi
  exact hi

private theorem mem_interior_centeredSimplex_iff {n : ℕ} (hn : 0 < n)
    {x : Space n} :
    x ∈ interior (centeredSimplex n) ↔
      (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1 := by
  constructor
  · intro hx
    exact ⟨coordinate_lt_of_mem_interior_centeredSimplex hx,
      coordinateSum_lt_of_mem_interior_centeredSimplex hn hx⟩
  · intro hx
    have hsub :
        {y : Space n |
          (∀ i, -(1 : ℝ) < y i) ∧ (∑ i, y i) < 1} ⊆
          centeredSimplex n := by
      intro y hy
      exact mem_centeredSimplex_iff.mpr
        ⟨fun i => (hy.1 i).le, hy.2.le⟩
    exact (interior_maximal hsub (isOpen_strict_centered_halfspaces n)) hx

private theorem zero_mem_interior_centeredSimplex (n : ℕ) (hn : 0 < n) :
    (0 : Space n) ∈ interior (centeredSimplex n) := by
  apply (mem_interior_centeredSimplex_iff hn).mpr
  constructor
  · intro i
    simp only [Pi.zero_apply, Left.neg_neg_iff, zero_lt_one]
  · simp only [Pi.zero_apply, Finset.sum_const_zero, zero_lt_one]

private theorem interior_centeredSimplex_nonempty (n : ℕ) (hn : 0 < n) :
    (interior (centeredSimplex n)).Nonempty :=
  ⟨0, zero_mem_interior_centeredSimplex n hn⟩

private theorem interior_integerPoint_eq_zero {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ)
    (hz : integerPoint n z ∈
      interior (centeredSimplex n)) :
    z = 0 := by
  classical
  have hstrict := (mem_interior_centeredSimplex_iff hn).mp hz
  have hstrict_coords : ∀ i, -(1 : ℝ) < (z i : ℝ) := by
    intro i
    simpa only [integerPoint] using hstrict.1 i
  have hstrict_sum : (∑ i, (z i : ℝ)) < 1 := by
    simpa only [integerPoint] using hstrict.2
  have hnonneg : ∀ i, (0 : ℤ) ≤ z i := by
    intro i
    have hi : (-1 : ℤ) < z i := by
      exact_mod_cast hstrict_coords i
    have hi' : (-1 : ℤ) + 1 ≤ z i := (Int.add_one_le_iff).mpr hi
    simpa only [ge_iff_le, Int.reduceNeg, neg_add_cancel] using hi'
  have hsum_lt : (∑ i, z i) < (1 : ℤ) := by
    exact_mod_cast hstrict_sum
  have hsum_le : (∑ i, z i) ≤ (0 : ℤ) := by
    apply (Int.lt_add_one_iff).mp
    simpa only [zero_add] using hsum_lt
  have hsum_nonneg : (0 : ℤ) ≤ ∑ i, z i :=
    Finset.sum_nonneg fun i _ => hnonneg i
  have hsum_zero : (∑ i, z i) = (0 : ℤ) :=
    le_antisymm hsum_le hsum_nonneg
  funext i
  have hi_le : z i ≤ ∑ j, z j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hi_zero : z i = (0 : ℤ) :=
    le_antisymm (hsum_zero ▸ hi_le) (hnonneg i)
  simpa only [Pi.zero_apply] using hi_zero

private theorem interiorLatticePoints_centeredSimplex (n : ℕ) (hn : 0 < n) :
    interiorLatticePoints (centeredSimplex n) = {0} := by
  ext z
  constructor
  · intro hz
    have hz' : integerPoint n z ∈
        interior (centeredSimplex n) := hz
    exact Set.mem_singleton_iff.mpr (interior_integerPoint_eq_zero hn z hz')
  · intro hz
    have hz' : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    change integerPoint n 0 ∈ interior (centeredSimplex n)
    have hzero : integerPoint n (0 : Fin n → ℤ) =
        (0 : Space n) := by
      funext i
      simp only [integerPoint, Pi.zero_apply, Int.cast_zero]
    rw [hzero]
    exact zero_mem_interior_centeredSimplex n hn

end Geometry

namespace SimplexVolume

open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

private def splitStandardSimplex (n : ℕ) : Set (ℝ × Space n) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + (∑ i, p.2 i) ≤ 1}

private theorem splitStandardSimplex_eq_preimage (n : ℕ) :
    splitStandardSimplex n =
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
          standardSimplex (n + 1) := by
  ext ⟨t, x⟩
  simp only [splitStandardSimplex, mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.zero_succAbove, Fin.insertNth_zero', Fin.removeNth_zero,
    Equiv.coe_fn_mk, standardSimplex, Fin.forall_fin_succ, Fin.sum_univ_succ, and_assoc,
    preimage_ofPred_eq, Fin.cons_zero, Fin.cons_succ]

private theorem measurableSet_splitStandardSimplex (n : ℕ) :
    MeasurableSet (splitStandardSimplex n) := by
  rw [splitStandardSimplex_eq_preimage]
  exact (Ehrhart.Geometry.isClosed_standardSimplex (n + 1)).measurableSet.preimage
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable

private theorem splitStandardSimplex_fiber_of_mem_Ico (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    Prod.mk t ⁻¹' splitStandardSimplex n =
      (1 - t) • standardSimplex n := by
  have hscale : 0 < 1 - t := sub_pos.mpr ht.2
  ext x
  change
    (0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1) ↔
      x ∈ (1 - t) • standardSimplex n
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hscale.ne']
  change
    (0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1) ↔
      (∀ i, 0 ≤ (1 - t)⁻¹ * x i) ∧
        (∑ i, (1 - t)⁻¹ * x i) ≤ 1
  constructor
  · rintro ⟨_, hx, hsum⟩
    refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hscale.le) (hx i), ?_⟩
    rw [← Finset.mul_sum, inv_mul_le_one₀ hscale]
    linarith
  · rintro ⟨hx, hsum⟩
    refine ⟨ht.1, fun i =>
      (mul_nonneg_iff_of_pos_left (inv_pos.mpr hscale)).mp (hx i), ?_⟩
    rw [← Finset.mul_sum, inv_mul_le_one₀ hscale] at hsum
    linarith

private theorem splitStandardSimplex_fiber_eq_empty (n : ℕ) {t : ℝ}
    (ht : t < 0 ∨ 1 < t) :
    Prod.mk t ⁻¹' splitStandardSimplex n = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  intro hx
  change 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + (∑ i, x i) ≤ 1 at hx
  rcases ht with ht | ht
  · linarith [hx.1]
  · have hsum : 0 ≤ ∑ i, x i :=
      Finset.sum_nonneg (fun i _ => hx.2.1 i)
    linarith [hx.2.2]

private theorem normalizedVolume_smul_standardSimplex (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) :
    normalizedVolume (r • standardSimplex n) =
      r ^ n * normalizedVolume (standardSimplex n) := by
  unfold normalizedVolume
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg
    (volume : Measure (Space n)) hr,
    Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr n)]

private theorem normalizedVolume_splitStandardSimplex_fiber_ae (n : ℕ) :
    (fun t : ℝ => normalizedVolume
      (Prod.mk t ⁻¹' splitStandardSimplex n)) =ᵐ[volume]
        (Set.Icc (0 : ℝ) 1).indicator
          (fun t => (1 - t) ^ n *
            normalizedVolume (standardSimplex n)) := by
  filter_upwards [(volume : Measure ℝ).ae_ne 1] with t ht
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t < 1
    · have hi : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
      rw [Set.indicator_of_mem hi,
        splitStandardSimplex_fiber_of_mem_Ico n ⟨ht0, ht1⟩,
        normalizedVolume_smul_standardSimplex n (1 - t)
          (sub_nonneg.mpr ht1.le)]
    · have hgt : 1 < t :=
        lt_of_le_of_ne (le_of_not_gt ht1) ht.symm
      have hnot : t ∉ Set.Icc (0 : ℝ) 1 := by
        intro h
        linarith [h.2]
      rw [Set.indicator_of_notMem hnot,
        splitStandardSimplex_fiber_eq_empty n (Or.inr hgt)]
      simp only [normalizedVolume, measure_empty, ENNReal.toReal_zero]
  · have hneg : t < 0 := lt_of_not_ge ht0
    have hnot : t ∉ Set.Icc (0 : ℝ) 1 := by
      intro h
      linarith [h.1]
    rw [Set.indicator_of_notMem hnot,
      splitStandardSimplex_fiber_eq_empty n (Or.inl hneg)]
    simp only [normalizedVolume, measure_empty, ENNReal.toReal_zero]

private theorem volume_splitStandardSimplex (n : ℕ) :
    (volume : Measure (ℝ × Space n)) (splitStandardSimplex n) =
      (volume : Measure (Space (n + 1)))
        (standardSimplex (n + 1)) := by
  rw [splitStandardSimplex_eq_preimage]
  exact
    ((MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm).measure_preimage_equiv
      (standardSimplex (n + 1))

private theorem normalizedVolume_standardSimplex_succ_eq_integral_fibers
    (n : ℕ) :
    normalizedVolume (standardSimplex (n + 1)) =
      ∫ t : ℝ, normalizedVolume
        (Prod.mk t ⁻¹' splitStandardSimplex n) := by
  have hmeas := measurableSet_splitStandardSimplex n
  have hfinite :
      (volume : Measure (ℝ × Space n))
          (splitStandardSimplex n) ≠ ∞ := by
    rw [volume_splitStandardSimplex n]
    exact (Ehrhart.Geometry.isCompact_standardSimplex (n + 1)).measure_ne_top
  unfold normalizedVolume
  calc
    ((volume : Measure (Space (n + 1)))
        (standardSimplex (n + 1))).toReal =
      ((volume : Measure (ℝ × Space n))
        (splitStandardSimplex n)).toReal := by
          rw [volume_splitStandardSimplex n]
    _ =
      (((volume : Measure ℝ).prod (volume : Measure (Space n)))
        (splitStandardSimplex n)).toReal := by
          rfl
    _ = (∫⁻ t : ℝ,
      (volume : Measure (Space n))
        (Prod.mk t ⁻¹' splitStandardSimplex n)).toReal := by
          rw [MeasureTheory.Measure.prod_apply hmeas]
    _ = ∫ t : ℝ,
      ((volume : Measure (Space n))
        (Prod.mk t ⁻¹' splitStandardSimplex n)).toReal := by
          symm
          exact MeasureTheory.integral_toReal
            (measurable_measure_prodMk_left hmeas).aemeasurable
            (MeasureTheory.Measure.ae_measure_lt_top hmeas hfinite)

private theorem integral_one_sub_pow_Icc (n : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) 1, (1 - t) ^ n) =
      1 / ((n : ℝ) + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) 1,
    integral_pow]
  norm_num

private theorem normalizedVolume_standardSimplex_succ (n : ℕ) :
    normalizedVolume (standardSimplex (n + 1)) =
      normalizedVolume (standardSimplex n) /
        ((n : ℝ) + 1) := by
  rw [normalizedVolume_standardSimplex_succ_eq_integral_fibers n]
  calc
    (∫ t : ℝ, normalizedVolume
      (Prod.mk t ⁻¹' splitStandardSimplex n)) =
      ∫ t : ℝ, (Set.Icc (0 : ℝ) 1).indicator
        (fun t => (1 - t) ^ n *
          normalizedVolume (standardSimplex n)) t :=
            MeasureTheory.integral_congr_ae
              (normalizedVolume_splitStandardSimplex_fiber_ae n)
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
        (1 - t) ^ n *
          normalizedVolume (standardSimplex n) :=
            MeasureTheory.integral_indicator measurableSet_Icc
    _ = (∫ t in Set.Icc (0 : ℝ) 1, (1 - t) ^ n) *
        normalizedVolume (standardSimplex n) := by
          exact MeasureTheory.integral_mul_const
            (normalizedVolume (standardSimplex n))
            (fun t : ℝ => (1 - t) ^ n)
    _ = normalizedVolume (standardSimplex n) /
        ((n : ℝ) + 1) := by
          rw [integral_one_sub_pow_Icc n]
          ring

private theorem normalizedVolume_standardSimplex (n : ℕ) :
    normalizedVolume (standardSimplex n) =
      1 / (n.factorial : ℝ) := by
  induction n with
  | zero =>
      have hz : (0 : Space 0) ∈ standardSimplex 0 := by
        simp only [standardSimplex, IsEmpty.forall_iff, Finset.univ_eq_empty, Finset.sum_empty,
          zero_le_one, and_self, ofPred_true, Matrix.zero_empty, mem_univ]
      unfold normalizedVolume
      rw [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Space 0),
        MeasureTheory.Measure.dirac_apply_of_mem hz]
      simp only [ENNReal.toReal_one, Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero,
        not_false_eq_true, div_self]
  | succ n ih =>
      rw [normalizedVolume_standardSimplex_succ n, ih,
        Nat.factorial_succ]
      push_cast
      have hfact : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hdenom : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp

private theorem normalizedVolume_centeredSimplex_eq_scale_mul (n : ℕ) :
    normalizedVolume (centeredSimplex n) =
      ((n : ℝ) + 1) ^ n *
        normalizedVolume (standardSimplex n) := by
  have hscale : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hset : centeredSimplex n =
      (fun x : Space n => x + (-1 : Space n)) ''
        (((n : ℝ) + 1) • standardSimplex n) := by
    unfold centeredSimplex
    rw [← Set.image_smul, Set.image_image]
    congr 1
  unfold normalizedVolume
  rw [hset]
  simp only [Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_smul_of_nonneg (volume : Measure (Space n)) hscale,
    Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hscale n)]

/-- The centered simplex has exactly the sharp normalized volume. -/
public
theorem normalizedVolume_centeredSimplex (n : ℕ) :
    normalizedVolume (centeredSimplex n) =
      sharpConstant n := by
  rw [normalizedVolume_centeredSimplex_eq_scale_mul n,
    normalizedVolume_standardSimplex n]
  simp only [div_eq_mul_inv, one_mul, sharpConstant]

private theorem centeredSimplex_coordinate_tail {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    {y : Space n | y ∈ T ∧ t ≤ y i + 1} =
      (fun x : Space n => x + (Pi.single i t - 1)) ''
        (((n : ℝ) + 1 - t) • standardSimplex n) := by
  classical
  let v : Space n := Pi.single i t
  let b : Space n := v - 1
  have hvsum : (∑ j, v j) = t := by simp only [Pi.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, v]
  have hbsum : (∑ j, b j) = t - n := by
    simp only [Pi.sub_apply, Pi.one_apply, Finset.sum_sub_distrib, hvsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, b]
  have hvnonneg (j : Fin n) : 0 ≤ v j := by
    by_cases hji : j = i
    · subst j
      simpa [v] using ht0
    · simp only [ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, Std.le_refl, v]
  have hp : 0 < (n : ℝ) + 1 - t := sub_pos.mpr ht1
  ext y
  change (y ∈ T ∧ t ≤ y i + 1) ↔
    y ∈ (fun x : Space n => x + b) ''
      (((n : ℝ) + 1 - t) • standardSimplex n)
  constructor
  · rintro ⟨hy, hyt⟩
    have hy' := (hT y).mp hy
    refine ⟨y - b, ?_, by ext j; simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hp.ne']
    change (∀ j, 0 ≤ ((n : ℝ) + 1 - t)⁻¹ * (y j - b j)) ∧
      (∑ j, ((n : ℝ) + 1 - t)⁻¹ * (y j - b j)) ≤ 1
    constructor
    · intro j
      refine mul_nonneg (inv_nonneg.mpr hp.le) ?_
      by_cases hji : j = i
      · subst j
        simp only [b, Pi.sub_apply, v, Pi.single_eq_same, Pi.one_apply]
        linarith
      · simp only [b, Pi.sub_apply, v, Pi.single_apply, ite_eq_right hji,
          Pi.one_apply]
        linarith [hy'.1 j]
    · rw [← Finset.mul_sum, Finset.sum_sub_distrib, hbsum,
        inv_mul_le_one₀ hp]
      linarith [hy'.2]
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hp.ne'] at hx
    change (∀ j, 0 ≤ ((n : ℝ) + 1 - t)⁻¹ * x j) ∧
      (∑ j, ((n : ℝ) + 1 - t)⁻¹ * x j) ≤ 1 at hx
    have hx0 (j : Fin n) : 0 ≤ x j :=
      (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp (hx.1 j)
    have hxsum : (∑ j, x j) ≤ (n : ℝ) + 1 - t := by
      rw [← Finset.mul_sum, inv_mul_le_one₀ hp] at hx
      exact hx.2
    refine ⟨(hT (x + b)).mpr ⟨?_, ?_⟩, ?_⟩
    · intro j
      change -(1 : ℝ) ≤ x j + (v j - 1)
      linarith [hx0 j, hvnonneg j]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hbsum]
      linarith
    · change t ≤ (x + b) i + 1
      simp only [Pi.add_apply, b, Pi.sub_apply, v, Pi.single_eq_same,
        Pi.one_apply]
      linarith [hx0 i]

private theorem centeredSimplex_coordinate_tail_measure {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    ((volume : Measure (Space n)).restrict T).real
        {y : Space n | t ≤ y i + 1} =
      ((n : ℝ) + 1 - t) ^ n *
        (volume : Measure (Space n)).real
          (standardSimplex n) := by
  have hm : MeasurableSet {y : Space n | t ≤ y i + 1} :=
    (isClosed_le continuous_const
      ((continuous_apply i).add continuous_const)).measurableSet
  rw [measureReal_def, Measure.restrict_apply hm]
  have hset : {y : Space n | t ≤ y i + 1} ∩ T =
      {y : Space n | y ∈ T ∧ t ≤ y i + 1} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, and_comm]
  rw [hset, centeredSimplex_coordinate_tail T hT i ht0 ht1]
  simp only [Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_smul_of_nonneg (volume : Measure (Space n))
      (sub_nonneg.mpr ht1.le), Module.finrank_fin_fun,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (pow_nonneg (sub_nonneg.mpr ht1.le) n)]
  rfl

private theorem centered_integral_zero_of_coordinate_tails
    {n : ℕ} (K : Set (Space n)) (hK : IsCompact K) (v : ℝ)
    (hT : ∀ y, y ∈ K ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (htail : ∀ (i : Fin n) {t : ℝ}, 0 ≤ t → t < (n : ℝ) + 1 →
      ((volume : Measure (Space n)).restrict K).real
        {y | t ≤ y i + 1} = (((n : ℝ) + 1) - t) ^ n * v) :
    (∫ y in K, y) = (0 : Space n) := by
  have hcoord : ∀ j : Fin n, Integrable (fun y : Space n => y j)
      ((volume : Measure (Space n)).restrict K) := fun j =>
    (continuous_apply j).continuousOn.integrableOn_compact hK
  have hone : Integrable (fun _ : Space n => (1 : ℝ))
      ((volume : Measure (Space n)).restrict K) :=
    continuous_const.continuousOn.integrableOn_compact hK
  ext i
  change (∫ y in K, y) i = 0
  rw [MeasureTheory.eval_integral hcoord i]
  have hsupport (y : Space n) (hy : y ∈ K) :
      0 ≤ y i + 1 ∧ y i + 1 ≤ (n : ℝ) + 1 := by
    have hy' := (hT y).mp hy
    have hnonneg (j : Fin n) : 0 ≤ y j + 1 := by linarith [hy'.1 j]
    refine ⟨hnonneg i, ?_⟩
    calc
      y i + 1 ≤ ∑ j, (y j + 1) :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ ≤ (n : ℝ) + 1 := by
        simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one] using
          (show (∑ j, y j) + (n : ℝ) ≤ n + 1 by linarith [hy'.2])
  have hzero : 0 ≤ᵐ[(volume : Measure (Space n)).restrict K]
      fun y => y i + 1 := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hsupport y hy).1
  have hbound : (fun y : Space n => y i + 1)
      ≤ᵐ[(volume : Measure (Space n)).restrict K]
        fun _ => (n : ℝ) + 1 := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hsupport y hy).2
  have hvol : (volume : Measure (Space n)).real K =
      ((n : ℝ) + 1) ^ n * v := by
    have h := htail i (t := 0) (by norm_num) (by positivity)
    have hsub : K ⊆ {y : Space n | 0 ≤ y i + 1} :=
      fun y hy => (hsupport y hy).1
    rw [measureReal_restrict_apply' hK.measurableSet,
      Set.inter_eq_right.mpr hsub] at h
    simpa only [sub_zero] using h
  have hplus : Integrable (fun y : Space n => y i + 1)
      ((volume : Measure (Space n)).restrict K) :=
    (hcoord i).add hone
  have hmoment : (∫ y in K, y i + 1) =
      ((n : ℝ) + 1) ^ n * v := by
    rw [hplus.integral_eq_integral_Ioc_meas_le hzero hbound]
    calc
      (∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
        ((volume : Measure (Space n)).restrict K).real
          {y | t ≤ y i + 1}) =
          ∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
            (((n : ℝ) + 1) - t) ^ n * v := by
              apply setIntegral_congr_ae measurableSet_Ioc
              filter_upwards [(volume : Measure ℝ).ae_ne ((n : ℝ) + 1)]
                with t ht hmem
              exact htail i hmem.1.le (lt_of_le_of_ne hmem.2 ht)
      _ = (∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
            (((n : ℝ) + 1) - t) ^ n) * v := by
              exact integral_mul_const v
                (fun t : ℝ => (((n : ℝ) + 1) - t) ^ n)
      _ = ((n : ℝ) + 1) ^ n * v := by
        rw [← intervalIntegral.integral_of_le (by positivity),
          intervalIntegral.integral_comp_sub_left
            (fun t : ℝ => t ^ n) ((n : ℝ) + 1), integral_pow]
        simp only [sub_zero, pow_succ, sub_self, mul_zero, isUnit_iff_ne_zero, ne_eq,
          (by positivity : (n : ℝ) + 1 ≠ 0), not_false_eq_true, IsUnit.mul_div_cancel_right]
  rw [integral_add (hcoord i) hone, integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul, mul_one, hvol] at hmoment
  linarith

/-- The centered simplex has barycenter zero. -/
public
theorem barycenter_centeredSimplex (n : ℕ) :
    barycenter (centeredSimplex n) = 0 := by
  have hzero : (∫ y in centeredSimplex n, y) =
      (0 : Space n) :=
    centered_integral_zero_of_coordinate_tails
      (centeredSimplex n)
      (Ehrhart.Geometry.isCompact_centeredSimplex n)
      ((volume : Measure (Space n)).real
        (standardSimplex n))
      (fun _ => Ehrhart.Geometry.mem_centeredSimplex_iff)
      (fun i _ ht0 ht1 => centeredSimplex_coordinate_tail_measure
        (centeredSimplex n)
        (fun _ => Ehrhart.Geometry.mem_centeredSimplex_iff) i ht0 ht1)
  simp only [barycenter, hzero, smul_zero]

/-- A centered body attaining the sharp volume bound exists in every positive dimension. -/
public
theorem exists_centeredBody_sharp (n : ℕ) (hn : 0 < n) :
    ∃ K : CenteredBody n,
      normalizedVolume K.carrier = sharpConstant n := by
  refine ⟨{
    carrier := centeredSimplex n
    convex := Ehrhart.Geometry.convex_centeredSimplex n
    compact := Ehrhart.Geometry.isCompact_centeredSimplex n
    fullDimensional := Ehrhart.Geometry.interior_centeredSimplex_nonempty n hn
    centered := barycenter_centeredSimplex n
    uniqueInteriorLatticePoint :=
      Ehrhart.Geometry.interiorLatticePoints_centeredSimplex n hn
  }, normalizedVolume_centeredSimplex n⟩

end SimplexVolume

namespace BergmanDiagonalBasisIndependence

open Set Filter MeasureTheory InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Topology

private def realLogCoordinate {n : ℕ}
    (z : TorusCharacters.LogSpace n) : Space n :=
  fun i => 2 * (z i).re

private theorem normSq_torusCharacter_eq_realLogSlice {n : ℕ}
    (m : Fin n → ℤ) (z : TorusCharacters.LogSpace n) :
    Complex.normSq (TorusCharacters.torusCharacter m z) =
      Complex.normSq (TorusCharacters.torusCharacter m
        (TorusCharacters.realLogSlice (realLogCoordinate z))) := by
  have hre :
      (TorusCharacters.characterExponent m z).re =
        (TorusCharacters.characterExponent m
          (TorusCharacters.realLogSlice
            (realLogCoordinate z))).re := by
    simp only [TorusCharacters.characterExponent,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
      TorusCharacters.realLogSlice, realLogCoordinate, Complex.ofReal_mul, Complex.ofReal_ofNat,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero]
  simp only [Complex.normSq_eq_norm_sq,
    TorusCharacters.torusCharacter, Complex.norm_exp, hre]

private theorem exponentialPartition_le_exp_mul_sum
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i)
    (J : ℕ) (horder : ∀ i, order i ≤ J)
    {t : ℝ} (ht : 0 ≤ t) :
    BergmanGeodesicConvexity.exponentialPartition w order t ≤
      Real.exp (t * (J : ℝ)) * ∑ i, w i := by
  classical
  unfold BergmanGeodesicConvexity.exponentialPartition
    BergmanGeodesicConvexity.exponentialMoment
  simp only [pow_zero, mul_one]
  calc
    (∑ i, w i * Real.exp (t * (order i : ℝ))) ≤
      ∑ i, w i * Real.exp (t * (J : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ ht
        exact_mod_cast horder i
    _ = Real.exp (t * (J : ℝ)) * ∑ i, w i := by
      rw [← Finset.sum_mul]
      ring

end BergmanDiagonalBasisIndependence

namespace ActualJetUpperEnvelope

open Set Filter MeasureTheory
open BergmanDiagonalBasisIndependence
open scoped BigOperators Topology

private def localUpperBounds {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) : Set ℝ :=
  {c | ∀ᶠ y : X in 𝓝 x, f y ≤ c}

private theorem localUpperBounds_bddBelow {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    BddBelow (localUpperBounds f x) := by
  refine ⟨f x, ?_⟩
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, f y ≤ c) at hc
  exact hc.self_of_nhds

private def upperRegularization {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) : ℝ :=
  sInf (localUpperBounds f x)

private theorem upperRegularization_le_of_eventually
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) {c : ℝ}
    (hc : ∀ᶠ y : X in 𝓝 x, f y ≤ c) :
    upperRegularization f x ≤ c := by
  exact csInf_le (localUpperBounds_bddBelow f x) hc

private theorem le_upperRegularization
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X)
    (hb : (localUpperBounds f x).Nonempty) :
    f x ≤ upperRegularization f x := by
  apply le_csInf hb
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, f y ≤ c) at hc
  exact hc.self_of_nhds

private theorem upperSemicontinuous_upperRegularization
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ)
    (hb : ∀ x : X, (localUpperBounds f x).Nonempty) :
    UpperSemicontinuous (upperRegularization f) := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change upperRegularization f x < a at hx
  obtain ⟨c, hc, hca⟩ :=
    exists_lt_of_csInf_lt (hb x) hx
  obtain ⟨U, hUsub, hUopen, hxU⟩ :=
    mem_nhds_iff.mp hc
  apply Filter.mem_of_superset (hUopen.mem_nhds hxU)
  intro y hy
  change upperRegularization f y < a
  have hlocal : ∀ᶠ w : X in 𝓝 y, f w ≤ c :=
    Filter.mem_of_superset (hUopen.mem_nhds hy) hUsub
  exact lt_of_le_of_lt
    (upperRegularization_le_of_eventually f y hlocal) hca

private theorem upperRegularization_le_of_continuous_majorant
    {X : Type*} [TopologicalSpace X]
    (f b : X → ℝ) (hb : Continuous b)
    (hpoint : ∀ x : X, f x ≤ b x) (x : X) :
    upperRegularization f x ≤ b x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ y : X in 𝓝 x,
      b y < b x + ε :=
    (hb.continuousAt.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε)))
  exact upperRegularization_le_of_eventually f x
    (hev.mono fun y hy => le_trans (hpoint y) hy.le)

private theorem localUpperBounds_nonempty_of_continuous_majorant
    {X : Type*} [TopologicalSpace X]
    (f b : X → ℝ) (hb : Continuous b)
    (hpoint : ∀ x : X, f x ≤ b x) (x : X) :
    (localUpperBounds f x).Nonempty := by
  refine ⟨b x + 1, ?_⟩
  change ∀ᶠ y : X in 𝓝 x, f y ≤ b x + 1
  have hev : ∀ᶠ y : X in 𝓝 x,
      b y < b x + 1 :=
    hb.continuousAt.eventually
      (Iio_mem_nhds (by linarith : b x < b x + 1))
  exact hev.mono fun y hy => le_trans (hpoint y) hy.le

private theorem upperRegularization_mono
    {X : Type*} [TopologicalSpace X]
    (f g : X → ℝ) (x : X)
    (hle : ∀ y : X, f y ≤ g y)
    (hg : (localUpperBounds g x).Nonempty) :
    upperRegularization f x ≤ upperRegularization g x := by
  apply csInf_le_csInf (localUpperBounds_bddBelow f x) hg
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, g y ≤ c) at hc
  change ∀ᶠ y : X in 𝓝 x, f y ≤ c
  exact hc.mono fun y hy => le_trans (hle y) hy

private abbrev PositiveJointLogSpace (n : ℕ) :=
  {q : TorusCharacters.LogSpace n × ℂ //
    1 < Complex.normSq q.2}

private def jointLogTime {n : ℕ}
    (q : PositiveJointLogSpace n) : ℝ :=
  Real.log (Complex.normSq q.val.2)

private theorem jointLogTime_pos {n : ℕ}
    (q : PositiveJointLogSpace n) :
    0 < jointLogTime q := by
  unfold jointLogTime
  exact Real.log_pos q.property

private def jointRealCoordinate {n : ℕ}
    (q : PositiveJointLogSpace n) : Space n :=
  realLogCoordinate q.val.1

private theorem continuous_jointRealCoordinate (n : ℕ) :
    Continuous (jointRealCoordinate (n := n)) := by
  unfold jointRealCoordinate realLogCoordinate
  fun_prop

private theorem continuous_jointLogTime (n : ℕ) :
    Continuous (jointLogTime (n := n)) := by
  unfold jointLogTime
  have hτ : Continuous
      (fun q : PositiveJointLogSpace n => q.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply (Complex.continuous_normSq.comp hτ).log
  intro q
  exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) q.property)

end ActualJetUpperEnvelope

namespace ActualJetPlurisubharmonicEnvelope

open Set Metric Filter Function MeasureTheory InnerProductSpace
open scoped BigOperators Topology InnerProductSpace ENNReal

private def positiveJointDomain (n : ℕ) :
    Set (TorusCharacters.LogSpace n × ℂ) :=
  {q | 1 < Complex.normSq q.2}

private theorem log_norm_le_circleAverage_of_differentiable
    {g : ℂ → ℂ}
    (hg : Differentiable ℂ g)
    (hzero : g 0 ≠ 0)
    (R : ℝ) :
    Real.log ‖g 0‖ ≤
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R := by
  let G : ℂ → ℂ := fun w => g ((R : ℂ) * w)
  have hG : Differentiable ℂ G := by
    exact hg.comp (by fun_prop)
  have hGanalytic : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) :=
    hG.differentiableOn.analyticOnNhd isOpen_univ
  have hGzero : G 0 ≠ 0 := by
    simpa [G] using hzero
  have hmeromorphic : Meromorphic G := by
    intro w
    exact (hG.analyticAt w).meromorphicAt
  have hdivisor :
      0 ≤ MeromorphicOn.divisor G (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hGanalytic
  have hcount :
      0 ≤ Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor G (Set.univ : Set ℂ)) 1 :=
    Function.locallyFinsuppWithin.logCounting_nonneg
      hdivisor (by norm_num)
  have hjensen :=
    Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      hmeromorphic (by norm_num : (1 : ℝ) ≠ 0)
  rw [(hG.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero
    hGzero] at hjensen
  have hjensen' :
      Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor G (Set.univ : Set ℂ)) 1 =
        Real.circleAverage
          (fun w : ℂ => Real.log ‖G w‖) 0 1 - Real.log ‖G 0‖ := by
    simpa only [top_eq_univ] using hjensen
  have hcenter :
      Real.log ‖G 0‖ ≤
        Real.circleAverage
          (fun w : ℂ => Real.log ‖G w‖) 0 1 := by
    rw [hjensen'] at hcount
    linarith
  simpa [G, Real.circleAverage_eq_circleAverage_zero_one] using hcenter

private theorem log_hilbert_norm_le_circleAverage_all_radius
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F : ℂ → H}
    (hF : Differentiable ℂ F)
    (hzero : F 0 ≠ 0)
    (R : ℝ)
    (hcircle : ∀ w ∈ Metric.sphere (0 : ℂ) |R|, F w ≠ 0) :
    Real.log ‖F 0‖ ≤
      Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
  by_cases hR : R = 0
  · simp only [hR, Real.circleAverage_zero, Std.le_refl]
  let g : ℂ → ℂ := fun w => inner ℂ (F 0) (F w)
  have hg : Differentiable ℂ g := by
    simpa only [coe_innerSL_apply, comp_def] using
      (innerSL ℂ (F 0)).differentiable.comp hF
  have hgzero : g 0 ≠ 0 := by
    change inner ℂ (F 0) (F 0) ≠ 0
    exact (inner_self_ne_zero (𝕜 := ℂ)).mpr hzero
  have hganalytic : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hglobal : ∀ᶠ w : ℂ in codiscrete ℂ, g w ≠ 0 := by
    change {w : ℂ | g w ≠ 0} ∈ codiscrete ℂ
    exact hganalytic.preimage_zero_mem_codiscrete hgzero
  have hnonzero :
      ∀ᶠ w : ℂ in codiscreteWithin (Metric.sphere (0 : ℂ) |R|),
        g w ≠ 0 := by
    exact hglobal.filter_mono
      (Filter.codiscreteWithin_mono
        (Set.subset_univ (Metric.sphere (0 : ℂ) |R|)))
  let corrected : ℂ → ℝ := fun w =>
    if g w = 0 then
      Real.log ‖F 0‖ + Real.log ‖F w‖
    else Real.log ‖g w‖
  have hcodiscrete :
      (fun w : ℂ => Real.log ‖g w‖) =ᶠ[
        codiscreteWithin (Metric.sphere (0 : ℂ) |R|)]
          corrected := by
    filter_upwards [hnonzero] with w hw
    simp only [hw, ↓reduceIte, corrected]
  have hgint : CircleIntegrable
      (fun w : ℂ => Real.log ‖g w‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro w _
    exact (hg.analyticAt w).meromorphicAt
  have hcorrectedint : CircleIntegrable corrected 0 R :=
    CircleIntegrable.congr_codiscreteWithin hcodiscrete hgint
  have hFint : CircleIntegrable
      (fun w : ℂ => Real.log ‖F w‖) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact hF.continuous.continuousOn.norm.log fun w hw =>
      norm_ne_zero_iff.mpr (hcircle w hw)
  have hconst : CircleIntegrable
      (fun _ : ℂ => Real.log ‖F 0‖) 0 R :=
    circleIntegrable_const (Real.log ‖F 0‖) 0 R
  have hboundint : CircleIntegrable
      (fun w : ℂ => Real.log ‖F 0‖ + Real.log ‖F w‖) 0 R := by
    exact hconst.fun_add hFint
  have hpoint :
      ∀ w ∈ Metric.sphere (0 : ℂ) |R|,
        corrected w ≤ Real.log ‖F 0‖ + Real.log ‖F w‖ := by
    intro w hw
    by_cases hgw : g w = 0
    · simp only [hgw, ↓reduceIte, Std.le_refl, corrected]
    · simp only [corrected, hgw, ↓reduceIte]
      calc
        Real.log ‖g w‖ ≤ Real.log (‖F 0‖ * ‖F w‖) := by
          apply Real.log_le_log (norm_pos_iff.mpr hgw)
          simpa only [g] using norm_inner_le_norm (F 0) (F w)
        _ = Real.log ‖F 0‖ + Real.log ‖F w‖ :=
          Real.log_mul (norm_ne_zero_iff.mpr hzero)
            (norm_ne_zero_iff.mpr (hcircle w hw))
  have hmean :
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R ≤
        Real.log ‖F 0‖ +
          Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
    calc
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R =
          Real.circleAverage corrected 0 R :=
        Real.circleAverage_congr_codiscreteWithin hcodiscrete hR
      _ ≤ Real.circleAverage
          (fun w : ℂ => Real.log ‖F 0‖ + Real.log ‖F w‖) 0 R :=
        Real.circleAverage_mono hcorrectedint hboundint hpoint
      _ = Real.log ‖F 0‖ +
          Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
        rw [Real.circleAverage_fun_add hconst hFint,
          Real.circleAverage_const]
  have hscalar :=
    log_norm_le_circleAverage_of_differentiable hg hgzero R
  have hcombined := hscalar.trans hmean
  have hcenter : ‖g 0‖ = ‖F 0‖ ^ 2 := by
    simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap, norm_pow, Complex.norm_real,
      norm_norm, g]
  rw [hcenter, Real.log_pow] at hcombined
  norm_num at hcombined
  linarith

private theorem log_hilbert_norm_sq_le_circleAverage_all_radius
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F : ℂ → H}
    (hF : Differentiable ℂ F)
    (hzero : F 0 ≠ 0)
    (R : ℝ)
    (hcircle : ∀ w ∈ Metric.sphere (0 : ℂ) |R|, F w ≠ 0) :
    Real.log (‖F 0‖ ^ 2) ≤
      Real.circleAverage
        (fun w : ℂ => Real.log (‖F w‖ ^ 2)) 0 R := by
  have h := log_hilbert_norm_le_circleAverage_all_radius
    hF hzero R hcircle
  simp_rw [Real.log_pow]
  change 2 * Real.log ‖F 0‖ ≤
    Real.circleAverage (fun w : ℂ => 2 * Real.log ‖F w‖) 0 R
  rw [show (fun w : ℂ => 2 * Real.log ‖F w‖) =
    (fun w : ℂ => (2 : ℝ) • Real.log ‖F w‖) by rfl,
    Real.circleAverage_fun_smul]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end ActualJetPlurisubharmonicEnvelope

namespace TranslatedGaussianLatticeAsymptotics

open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators

private def roundedLatticeExponent {n : ℕ} (k : ℕ)
    (u : Space n) : Space n :=
  fun i => (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ)

private theorem roundedLatticeExponent_mem_scaledIntegerLattice {n : ℕ}
    {k : ℕ} (hk : 0 < k) (u : Space n) :
    roundedLatticeExponent k u ∈
      LatticeAsymptotics.scaledIntegerLattice n k := by
  rw [LatticeAsymptotics.mem_scaledIntegerLattice_iff hk]
  intro i
  refine ⟨⌊(k : ℝ) * u i⌋, ?_⟩
  dsimp [roundedLatticeExponent]
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp

private theorem roundedLatticeExponent_coordinate_error {n : ℕ}
    {k : ℕ} (hk : 0 < k)
    (u : Space n) (i : Fin n) :
    roundedLatticeExponent k u i ≤ u i ∧
      u i - roundedLatticeExponent k u i < 1 / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfloor := Int.floor_le ((k : ℝ) * u i)
  have hnext := Int.lt_floor_add_one ((k : ℝ) * u i)
  constructor
  · apply (div_le_iff₀ hkreal).mpr
    change (⌊(k : ℝ) * u i⌋ : ℝ) ≤ u i * (k : ℝ)
    nlinarith
  · change u i - (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ) <
      1 / (k : ℝ)
    have heq :
        u i - (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ) =
          ((k : ℝ) * u i - (⌊(k : ℝ) * u i⌋ : ℝ)) /
            (k : ℝ) := by
      field_simp
    rw [heq]
    apply (div_lt_div_iff_of_pos_right hkreal).mpr
    linarith

private theorem roundedLatticeExponent_norm_sub_le {n : ℕ}
    {k : ℕ} (hk : 0 < k) (u : Space n) :
    ‖roundedLatticeExponent k u - u‖ ≤ 1 / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ))).mpr
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have h := roundedLatticeExponent_coordinate_error hk u i
  rw [abs_of_nonpos (sub_nonpos.mpr h.1)]
  linarith [h.2]

private theorem tendsto_roundedLatticeExponent {n : ℕ}
    (u : Space n) :
    Tendsto (fun k : ℕ => roundedLatticeExponent k u)
      atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => norm_nonneg _)
    ?_ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact roundedLatticeExponent_norm_sub_le
    (lt_of_lt_of_le Nat.zero_lt_one hk) u

private theorem eventually_roundedLatticeExponent_mem_monomialIndex
    {n : ℕ} (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∀ᶠ k : ℕ in atTop,
      roundedLatticeExponent k u ∈
        LatticeAsymptotics.monomialIndex K k := by
  have hnear :
      ∀ᶠ k : ℕ in atTop,
        roundedLatticeExponent k u ∈ interior K.carrier :=
    (tendsto_roundedLatticeExponent u).eventually
      (isOpen_interior.mem_nhds hu)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hnear] with k hk hinterior
  exact ⟨hinterior,
    roundedLatticeExponent_mem_scaledIntegerLattice
      (lt_of_lt_of_le Nat.zero_lt_one hk) u⟩

end TranslatedGaussianLatticeAsymptotics

namespace SpatialBergmanPointwiseAsymptotics

open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open TranslatedGaussianLatticeAsymptotics

private theorem zero_mem_monomialIndex_all_weights {n : ℕ}
    (K : CenteredBody n) (k : ℕ) :
    (0 : Space n) ∈
      LatticeAsymptotics.monomialIndex K k := by
  refine ⟨LatticeAsymptotics.zero_mem_interior K, ?_⟩
  unfold LatticeAsymptotics.scaledIntegerLattice
  exact Set.zero_mem_smul_set (Submodule.zero_mem _)

private def nearestMonomialIndex {n : ℕ}
    (K : CenteredBody n)
    (u : Space n) (k : ℕ) :
    LatticeAsymptotics.monomialIndex K k := by
  classical
  exact
    if h : roundedLatticeExponent k u ∈
        LatticeAsymptotics.monomialIndex K k then
      ⟨roundedLatticeExponent k u, h⟩
    else
      ⟨0, zero_mem_monomialIndex_all_weights K k⟩

private theorem eventually_nearestMonomialIndex_eq_rounded {n : ℕ}
    (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∀ᶠ k : ℕ in atTop,
      (nearestMonomialIndex K u k : Space n) =
        roundedLatticeExponent k u := by
  filter_upwards [eventually_roundedLatticeExponent_mem_monomialIndex
    K hu] with k hk
  simp only [nearestMonomialIndex, hk, ↓reduceDIte]

private theorem tendsto_nearestMonomialIndex {n : ℕ}
    (K : CenteredBody n)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    Tendsto (fun k : ℕ =>
      (nearestMonomialIndex K u k : Space n))
      atTop (𝓝 u) := by
  refine Filter.Tendsto.congr' ?_
    (tendsto_roundedLatticeExponent u)
  filter_upwards [eventually_nearestMonomialIndex_eq_rounded K hu]
    with k hk
  exact hk.symm

end SpatialBergmanPointwiseAsymptotics

namespace WeightedPoincare

open Set MeasureTheory Matrix
open scoped BigOperators ENNReal InnerProductSpace

private def partition {n : ℕ} (a : Space n → ℝ) : ℝ :=
  ∫ x : Space n, Real.exp (-a x)
    ∂(volume : Measure (Space n))

private def normalizedDensity {n : ℕ}
    (a : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (-a x) / partition a

private def normalizedMeasure {n : ℕ}
    (a : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (normalizedDensity a x))

private theorem partition_pos {n : ℕ} {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    0 < partition a := by
  exact MeasureTheory.integral_exp_pos ha

private theorem normalizedDensity_pos {n : ℕ} {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) (x : Space n) :
    0 < normalizedDensity a x := by
  exact div_pos (Real.exp_pos _) (partition_pos ha)

private theorem normalizedDensity_integrable {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    Integrable (normalizedDensity a)
      (volume : Measure (Space n)) := by
  exact ha.div_const _

private theorem integral_normalizedDensity {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    (∫ x : Space n, normalizedDensity a x
      ∂(volume : Measure (Space n))) = 1 := by
  unfold normalizedDensity
  rw [MeasureTheory.integral_div]
  exact div_self (partition_pos ha).ne'

private theorem normalizedMeasure_univ {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    normalizedMeasure a Set.univ = 1 := by
  unfold normalizedMeasure
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (normalizedDensity_integrable ha)
    (Filter.Eventually.of_forall
      (fun x => (normalizedDensity_pos ha x).le)),
    integral_normalizedDensity ha]
  exact ENNReal.ofReal_one

private theorem normalizedMeasure_isProbability {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    IsProbabilityMeasure (normalizedMeasure a) :=
  ⟨normalizedMeasure_univ ha⟩

private def coordinateGradient {n : ℕ}
    (f : Space n → ℝ)
    (x : Space n) : Space n :=
  fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))

end WeightedPoincare

namespace SpatialBergmanFatouScheffe

open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators ENNReal

private def actualGradient {n : ℕ}
    (φ : Space n → ℝ)
    (x : Space n) : Space n :=
  MonomialDivergence.dualVector (fderiv ℝ φ x)

private theorem pairing_actualGradient_eq_fderiv {n : ℕ}
    (φ : Space n → ℝ)
    (x v : Space n) :
    SupportFunction.pairing (actualGradient φ x) v =
      (fderiv ℝ φ x) v := by
  calc
    SupportFunction.pairing (actualGradient φ x) v =
        SupportFunction.pairing v (actualGradient φ x) := by
          simp only [SupportFunction.pairing, mul_comm]
    _ = (fderiv ℝ φ x) v := by
          exact (MonomialDivergence.dual_apply_eq_pairing
            (fderiv ℝ φ x) v).symm

end SpatialBergmanFatouScheffe

namespace MomentExistence

open Set Function Filter MeasureTheory
open ArbitraryBodySmoothConvexPotentialBridge LaplaceAsymptotics
open scoped BigOperators ENNReal Topology

private structure SourceMomentPotential {n : ℕ}
    (K : CenteredBody n) where
  potential : Space n → ℝ
  smooth : ContDiff ℝ 2 potential
  convex : ConvexOn ℝ Set.univ potential
  supportError : ℝ
  supportBound : ∀ x : Space n,
    |potential x -
      SupportFunction.supportFunction K.carrier x| ≤
        supportError

private def canonicalSourceMomentPotential {n : ℕ}
    (K : CenteredBody n) : SourceMomentPotential K where
  potential := smoothConvexPotential K
  smooth := (smoothConvexPotential_contDiff K).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  convex := smoothConvexPotential_convex K
  supportError := 1
  supportBound := smoothConvexPotential_bounded K

private theorem sourceMomentDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    Integrable
      (fun x : Space n => Real.exp (-D.potential x))
      (volume : Measure (Space n)) := by
  have h := MonomialIntegrability.integrable_monomialWeight_of_bounded_support
    K.compact (LatticeAsymptotics.zero_mem_interior K)
    D.smooth.continuous D.supportBound
    (k := (1 : ℝ)) (by norm_num)
  change Integrable
    (fun x : Space n =>
      Real.exp (1 *
        (SupportFunction.pairing
          (0 : Space n) x - D.potential x)))
    (volume : Measure (Space n)) at h
  simpa only [SupportFunction.pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub,
    mul_neg, one_mul] using h

private theorem sourceMomentDensity_integral_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < (∫ x : Space n,
      Real.exp (-D.potential x)
      ∂(volume : Measure (Space n))) := by
  have h := MonomialIntegrability.monomialIntegral_pos_of_bounded_support
    K.compact (LatticeAsymptotics.zero_mem_interior K)
    D.smooth.continuous D.supportBound
    (k := (1 : ℝ)) (by norm_num)
  simpa only [gt_iff_lt, MonomialIntegrability.monomialIntegral,
    MonomialIntegrability.monomialWeight, SupportFunction.pairing, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_sub, mul_neg, one_mul] using h

private theorem sourceMomentPhase_le_supportError {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier)
    (x : Space n) :
    phase p D.potential x ≤ D.supportError := by
  have hs := SupportFunction.pairing_le_supportFunction
    K.compact hp x
  have hb := (abs_le.mp (D.supportBound x)).1
  unfold phase
  linarith

private theorem sourceMomentPhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    BddAbove (Set.range (phase p D.potential)) := by
  refine ⟨D.supportError, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact sourceMomentPhase_le_supportError D hp x

private theorem sourceMomentLegendre_le_supportError {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    legendreTransform D.potential p ≤ D.supportError := by
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact sourceMomentPhase_le_supportError D hp x

private theorem neg_sourceMomentPotential_zero_le_legendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    -D.potential 0 ≤ legendreTransform D.potential p := by
  have h := le_csSup (sourceMomentPhase_bddAbove D hp)
    (show phase p D.potential 0 ∈
      Set.range (phase p D.potential) from ⟨0, rfl⟩)
  simpa only [legendreTransform, ge_iff_le, phase, SupportFunction.pairing, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_sub] using h

private theorem abs_sourceMomentLegendre_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    |legendreTransform D.potential p| ≤
      max D.supportError |D.potential 0| := by
  apply abs_le.mpr
  constructor
  · have hlow := neg_sourceMomentPotential_zero_le_legendre D hp
    have hφ := (le_abs_self (D.potential 0)).trans
      (le_max_right D.supportError |D.potential 0|)
    linarith
  · exact (sourceMomentLegendre_le_supportError D hp).trans
      (le_max_left D.supportError |D.potential 0|)

private theorem convexOn_sourceMomentLegendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ConvexOn ℝ K.carrier (legendreTransform D.potential) := by
  refine ⟨K.convex, ?_⟩
  intro p hp q hq a b ha hb hab
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hpmax : phase p D.potential x ≤
      sSup (Set.range (phase p D.potential)) :=
    le_csSup (sourceMomentPhase_bddAbove D hp) ⟨x, rfl⟩
  have hqmax : phase q D.potential x ≤
      sSup (Set.range (phase q D.potential)) :=
    le_csSup (sourceMomentPhase_bddAbove D hq) ⟨x, rfl⟩
  have hphase :
      phase (a • p + b • q) D.potential x =
        a * phase p D.potential x +
          b * phase q D.potential x := by
    have hpull :
        (∑ i : Fin n, (a * p i) * x i) =
          a * ∑ i : Fin n, p i * x i := by
      simp only [mul_assoc, Finset.mul_sum]
    have hqpull :
        (∑ i : Fin n, (b * q i) * x i) =
          b * ∑ i : Fin n, q i * x i := by
      simp only [mul_assoc, Finset.mul_sum]
    simp only [phase, SupportFunction.pairing,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib]
    rw [hpull, hqpull]
    linear_combination D.potential x * hab
  rw [hphase]
  simpa only [smul_eq_mul, ge_iff_le] using
    add_le_add (mul_le_mul_of_nonneg_left hpmax ha)
      (mul_le_mul_of_nonneg_left hqmax hb)

private theorem continuousOn_sourceMomentLegendre_interior {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ContinuousOn (legendreTransform D.potential)
      (interior K.carrier) :=
  (convexOn_sourceMomentLegendre D).continuousOn_interior

end MomentExistence

namespace MomentPotentialExistence

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence
open scoped BigOperators ENNReal Topology

private theorem sourceMomentLegendre_aestronglyMeasurable_restrict
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    AEStronglyMeasurable
      (legendreTransform D.potential)
      ((volume : Measure (Space n)).restrict K.carrier) := by
  have hrestrict :
      (volume : Measure (Space n)).restrict
        (interior K.carrier) =
      (volume : Measure (Space n)).restrict K.carrier :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  rw [← hrestrict]
  exact ContinuousOn.aestronglyMeasurable
    (continuousOn_sourceMomentLegendre_interior D)
    isOpen_interior.measurableSet

private theorem sourceMomentLegendre_integrableOn
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    IntegrableOn
      (legendreTransform D.potential)
      K.carrier (volume : Measure (Space n)) := by
  let B : ℝ := max D.supportError |D.potential 0|
  have hconst : Integrable
      (fun _ : Space n => B)
      ((volume : Measure (Space n)).restrict K.carrier) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  apply hconst.mono'
    (sourceMomentLegendre_aestronglyMeasurable_restrict D)
  filter_upwards [MeasureTheory.ae_restrict_mem
    K.compact.measurableSet] with p hp
  simpa [Real.norm_eq_abs, B] using
    abs_sourceMomentLegendre_le D hp

private def sourceMomentPartition {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  ∫ x : Space n,
    Real.exp (-D.potential x)
    ∂(volume : Measure (Space n))

private theorem sourceMomentPartition_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < sourceMomentPartition D :=
  sourceMomentDensity_integral_pos D

private def sourceMomentBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  (normalizedVolume K.carrier)⁻¹ *
    (∫ p in K.carrier,
      legendreTransform D.potential p
      ∂(volume : Measure (Space n)))

private def sourceMomentBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  Real.log (sourceMomentPartition D) -
    sourceMomentBodyEnergy D

private theorem exists_sourceMomentLegendre_maximizer
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    ∃ x : Space n,
      phase p D.potential x =
        legendreTransform D.potential p ∧
      ∀ z : Space n,
        phase p D.potential z ≤ phase p D.potential x :=
  LaplaceAsymptotics.exists_legendre_maximizer
    K.compact hp D.smooth.continuous D.supportBound

end MomentPotentialExistence

namespace MomentMinimizer

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence
open scoped BigOperators ENNReal NNReal Topology

private def sourceBodyLipschitzConstant {n : ℕ}
    (K : CenteredBody n) : ℝ≥0 :=
  Real.toNNReal ((n : ℝ) *
    LaurentJetSeparatedness.bodyRadius K)

private def normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) : Set (Space n → ℝ) :=
  {f | f 0 = 0 ∧
    ∀ x y : Space n,
      dist (f x) (f y) ≤
        (sourceBodyLipschitzConstant K : ℝ) * dist x y}

private theorem isClosed_normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) :
    IsClosed (normalizedSourcePointwiseFamily K) := by
  have hzero : IsClosed
      {f : Space n → ℝ | f 0 = 0} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hpair (x y : Space n) : IsClosed
      {f : Space n → ℝ |
        dist (f x) (f y) ≤
          (sourceBodyLipschitzConstant K : ℝ) * dist x y} :=
    isClosed_le ((continuous_apply x).dist (continuous_apply y))
      continuous_const
  have hforall : IsClosed
      {f : Space n → ℝ |
        ∀ x y : Space n,
          dist (f x) (f y) ≤
            (sourceBodyLipschitzConstant K : ℝ) * dist x y} := by
    have heq :
        {f : Space n → ℝ |
          ∀ x y : Space n,
            dist (f x) (f y) ≤
              (sourceBodyLipschitzConstant K : ℝ) * dist x y} =
          ⋂ x : Space n, ⋂ y : Space n,
            {f : Space n → ℝ |
              dist (f x) (f y) ≤
                (sourceBodyLipschitzConstant K : ℝ) * dist x y} := by
      ext f
      simp only [mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isClosed_iInter fun x => isClosed_iInter fun y => hpair x y
  exact hzero.inter hforall

private theorem isCompact_normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) :
    IsCompact (normalizedSourcePointwiseFamily K) := by
  let Q : Space n → Set ℝ := fun x =>
    Metric.closedBall 0
      ((sourceBodyLipschitzConstant K : ℝ) * dist x 0)
  have hQ : IsCompact (Set.univ.pi Q) :=
    isCompact_univ_pi (fun x => by
      simpa only [dist_zero_right, Q] using
        (isCompact_closedBall (0 : ℝ)
          ((sourceBodyLipschitzConstant K : ℝ) * dist x 0)))
  refine IsCompact.of_isClosed_subset hQ
    (isClosed_normalizedSourcePointwiseFamily K) ?_
  intro f hf
  rw [Set.mem_pi]
  intro x _
  change dist (f x) 0 ≤
    (sourceBodyLipschitzConstant K : ℝ) * dist x 0
  simpa only [dist_zero_right, Real.norm_eq_abs, hf.1] using hf.2 x 0

private def normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    Set C(Space n, ℝ) :=
  {f | f 0 = 0 ∧
    LipschitzWith (sourceBodyLipschitzConstant K) f}

private theorem normalizedSourceContinuousFamily_image {n : ℕ}
    (K : CenteredBody n) :
    ContinuousMap.toFun '' normalizedSourceContinuousFamily K =
      normalizedSourcePointwiseFamily K := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hg.1, fun x y => hg.2.dist_le_mul x y⟩
  · intro hf
    have hlip : LipschitzWith (sourceBodyLipschitzConstant K) f :=
      LipschitzWith.of_dist_le_mul hf.2
    let g : C(Space n, ℝ) := ⟨f, hlip.continuous⟩
    exact ⟨g, ⟨hf.1, hlip⟩, rfl⟩

private theorem equicontinuous_normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    Equicontinuous
      ((↑) : normalizedSourceContinuousFamily K →
        Space n → ℝ) := by
  apply Metric.equicontinuous_of_continuity_modulus
    (fun t : ℝ => (sourceBodyLipschitzConstant K : ℝ) * t)
    (by
      have hcontinuous : Continuous
          (fun t : ℝ => (sourceBodyLipschitzConstant K : ℝ) * t) := by
        fun_prop
      simpa only [mul_zero] using hcontinuous.tendsto (0 : ℝ))
  intro x y f
  exact f.property.2.dist_le_mul x y

private theorem isCompact_normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    IsCompact (normalizedSourceContinuousFamily K) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
    (normalizedSourceContinuousFamily K)
  · rw [normalizedSourceContinuousFamily_image]
    exact isCompact_normalizedSourcePointwiseFamily K
  · exact equicontinuous_normalizedSourceContinuousFamily K

private theorem sourceMomentBodyFenchel_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier)
    (x : Space n) :
    SupportFunction.pairing p x -
        legendreTransform D.potential p ≤
      D.potential x := by
  have h := le_csSup (sourceMomentPhase_bddAbove D hp)
    (show phase p D.potential x ∈
      Set.range (phase p D.potential) from ⟨x, rfl⟩)
  change SupportFunction.pairing p x - D.potential x ≤
    legendreTransform D.potential p at h
  linarith

end MomentMinimizer

namespace MomentCoercivityCompactness

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open scoped BigOperators ENNReal NNReal Topology

private def sourceMomentMinimumPoint {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : Space n :=
  (exists_sourceMomentLegendre_maximizer D
    (LatticeAsymptotics.zero_mem_interior K)).choose

private theorem sourceMomentMinimumPoint_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    D.potential (sourceMomentMinimumPoint D) ≤ D.potential x := by
  have h :=
    (exists_sourceMomentLegendre_maximizer D
      (LatticeAsymptotics.zero_mem_interior K)).choose_spec.2 x
  simpa only [sourceMomentMinimumPoint, phase, SupportFunction.pairing, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_sub, neg_le_neg_iff, ge_iff_le] using h

private def minimumNormalizedSourceContinuousMap {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    C(Space n, ℝ) where
  toFun x :=
    D.potential (x + sourceMomentMinimumPoint D) -
      D.potential (sourceMomentMinimumPoint D)
  continuous_toFun :=
    (D.smooth.continuous.comp
      (continuous_id.add continuous_const)).sub continuous_const

private theorem minimumNormalizedSourceContinuousMap_zero {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceContinuousMap D 0 = 0 := by
  simp only [minimumNormalizedSourceContinuousMap, ContinuousMap.coe_mk, zero_add, sub_self]

private theorem minimumNormalizedSourceContinuousMap_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    0 ≤ minimumNormalizedSourceContinuousMap D x := by
  change 0 ≤ D.potential (x + sourceMomentMinimumPoint D) -
    D.potential (sourceMomentMinimumPoint D)
  exact sub_nonneg.mpr
    (sourceMomentMinimumPoint_le D
      (x + sourceMomentMinimumPoint D))

private theorem minimumNormalizedSourceContinuousMap_le_support {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    minimumNormalizedSourceContinuousMap D x ≤
      SupportFunction.supportFunction K.carrier x := by
  have h :=
    GlobalBergmanKernelBound.convex_supportCompatible_sub_le_support
      K D.convex D.supportBound
      (x + sourceMomentMinimumPoint D)
      (sourceMomentMinimumPoint D)
  simpa only [minimumNormalizedSourceContinuousMap, ContinuousMap.coe_mk, tsub_le_iff_right,
    ge_iff_le, add_sub_cancel_right] using h

private theorem convexOn_minimumNormalizedSourceContinuousMap {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ConvexOn ℝ Set.univ (minimumNormalizedSourceContinuousMap D) := by
  let z := sourceMomentMinimumPoint D
  change ConvexOn ℝ Set.univ
    (fun x => D.potential (x + z) - D.potential z)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo :
      a • (x + z) + b • (y + z) =
        (a • x + b • y) + z := by
    calc
      a • (x + z) + b • (y + z) =
          (a • x + b • y) + (a • z + b • z) := by
        rw [smul_add, smul_add]
        abel
      _ = (a • x + b • y) + z := by
        rw [← add_smul, hab, one_smul]
  have h := D.convex.2 (Set.mem_univ (x + z))
    (Set.mem_univ (y + z)) ha hb hab
  rw [hcombo] at h
  change D.potential ((a • x + b • y) + z) ≤
    a * D.potential (x + z) + b * D.potential (y + z) at h
  change D.potential ((a • x + b • y) + z) - D.potential z ≤
    a * (D.potential (x + z) - D.potential z) +
      b * (D.potential (y + z) - D.potential z)
  calc
    D.potential ((a • x + b • y) + z) - D.potential z ≤
        (a * D.potential (x + z) +
          b * D.potential (y + z)) - D.potential z :=
      sub_le_sub_right h _
    _ = (a * D.potential (x + z) +
          b * D.potential (y + z)) - (a + b) * D.potential z := by
      simp only [hab, one_mul]
    _ = a * (D.potential (x + z) - D.potential z) +
          b * (D.potential (y + z) - D.potential z) := by
      ring

private theorem minimumNormalizedSourceContinuousMap_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (minimumNormalizedSourceContinuousMap D) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hD :=
    GlobalBergmanKernelBound.convex_supportCompatible_lipschitz
      K D.convex D.supportBound
  simpa only [minimumNormalizedSourceContinuousMap, ContinuousMap.coe_mk,
    dist_sub_eq_dist_add_right, sub_add_cancel, Real.dist_eq, sourceBodyLipschitzConstant,
    Real.coe_toNNReal', ge_iff_le, dist_add_right] using
    hD.dist_le_mul
      (x + sourceMomentMinimumPoint D)
      (y + sourceMomentMinimumPoint D)

private theorem minimumNormalizedSourceContinuousMap_mem {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceContinuousMap D ∈
      normalizedSourceContinuousFamily K :=
  ⟨minimumNormalizedSourceContinuousMap_zero D,
    minimumNormalizedSourceContinuousMap_lipschitz D⟩

private theorem convexOn_of_tendsto_minimumNormalizedSourceContinuousMap
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f)) :
    ConvexOn ℝ Set.univ f := by
  have hpoint (x : Space n) :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) x)
        atTop (𝓝 (f x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply le_of_tendsto_of_tendsto
    (hpoint (a • x + b • y))
    ((hpoint x).const_mul a |>.add ((hpoint y).const_mul b))
  filter_upwards with j
  simpa only [smul_eq_mul] using
    (convexOn_minimumNormalizedSourceContinuousMap (D (φ j))).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab

private theorem exists_minimumNormalizedSourceConvex_subsequence {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K) :
    ∃ (f : C(Space n, ℝ))
      (φ : ℕ → ℕ),
      f 0 = 0 ∧
      LipschitzWith (sourceBodyLipschitzConstant K) f ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x : Space n,
        0 ≤ f x ∧
          f x ≤ SupportFunction.supportFunction K.carrier x) ∧
      StrictMono φ ∧
      Tendsto (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 f) := by
  obtain ⟨f, hf, φ, hφ, hconv⟩ :=
    (isCompact_normalizedSourceContinuousFamily K).tendsto_subseq
      (x := fun j => minimumNormalizedSourceContinuousMap (D j))
      (fun j => minimumNormalizedSourceContinuousMap_mem (D j))
  refine ⟨f, φ, hf.1, hf.2,
    convexOn_of_tendsto_minimumNormalizedSourceContinuousMap
      D φ f hconv, ?_, hφ, hconv⟩
  intro x
  have hpoint :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) x)
        atTop (𝓝 (f x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  constructor
  · exact ge_of_tendsto hpoint
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceContinuousMap_nonneg (D (φ j)) x)
  · exact le_of_tendsto hpoint
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceContinuousMap_le_support (D (φ j)) x)

private theorem sourceCenteredBody_setIntegral_id_eq_zero {n : ℕ}
    (K : CenteredBody n) :
    (∫ p in K.carrier, p
      ∂(volume : Measure (Space n))) = 0 := by
  have hcenter :
      (normalizedVolume K.carrier)⁻¹ •
        (∫ p in K.carrier, p
          ∂(volume : Measure (Space n))) = 0 := by
    simpa only [smul_eq_zero, inv_eq_zero, barycenter] using K.centered
  exact (smul_eq_zero.mp hcenter).resolve_left
    (inv_ne_zero K.volume_pos.ne')

private def sourcePairingContinuousLinear {n : ℕ}
    (x : Space n) : Space n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (BergmanAsymptotics.pairingLinear x)

private theorem sourcePairingContinuousLinear_apply {n : ℕ}
    (x p : Space n) :
    sourcePairingContinuousLinear x p =
      SupportFunction.pairing p x := by
  change SupportFunction.pairing x p =
    SupportFunction.pairing p x
  simp only [SupportFunction.pairing, mul_comm]

private theorem sourceCenteredBody_pairing_integrableOn {n : ℕ}
    (K : CenteredBody n)
    (x : Space n) :
    IntegrableOn
      (fun p : Space n =>
        SupportFunction.pairing p x)
      K.carrier (volume : Measure (Space n)) := by
  simpa only [← sourcePairingContinuousLinear_apply] using
    (sourcePairingContinuousLinear x).continuous.continuousOn.integrableOn_compact
      K.compact

private theorem sourceCenteredBody_setIntegral_pairing_eq_zero {n : ℕ}
    (K : CenteredBody n)
    (x : Space n) :
    (∫ p in K.carrier,
      SupportFunction.pairing p x
      ∂(volume : Measure (Space n))) = 0 := by
  let L := sourcePairingContinuousLinear x
  have hid : IntegrableOn
      (fun p : Space n => p)
      K.carrier (volume : Measure (Space n)) :=
    continuous_id.continuousOn.integrableOn_compact K.compact
  calc
    (∫ p in K.carrier,
      SupportFunction.pairing p x
      ∂(volume : Measure (Space n))) =
        ∫ p in K.carrier, L p
          ∂(volume : Measure (Space n)) := by
            apply integral_congr_ae
            filter_upwards with p
            exact (sourcePairingContinuousLinear_apply x p).symm
    _ = L (∫ p in K.carrier, p
          ∂(volume : Measure (Space n))) :=
        L.integral_comp_comm hid
    _ = 0 := by
      rw [sourceCenteredBody_setIntegral_id_eq_zero]
      exact map_zero L

private def minimumNormalizedSourceBodyDual {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (p : Space n) : ℝ :=
  legendreTransform D.potential p -
    SupportFunction.pairing p
      (sourceMomentMinimumPoint D) +
    D.potential (sourceMomentMinimumPoint D)

private theorem minimumNormalizedSource_phase {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (p x : Space n) :
    phase p (minimumNormalizedSourceContinuousMap D) x =
      phase p D.potential
        (x + sourceMomentMinimumPoint D) -
      SupportFunction.pairing p
        (sourceMomentMinimumPoint D) +
      D.potential (sourceMomentMinimumPoint D) := by
  change
    SupportFunction.pairing p x -
        (D.potential (x + sourceMomentMinimumPoint D) -
          D.potential (sourceMomentMinimumPoint D)) =
      (SupportFunction.pairing p
          (x + sourceMomentMinimumPoint D) -
        D.potential (x + sourceMomentMinimumPoint D)) -
      SupportFunction.pairing p
        (sourceMomentMinimumPoint D) +
      D.potential (sourceMomentMinimumPoint D)
  rw [MonomialDivergence.pairing_add_right]
  ring

private theorem minimumNormalizedSourcePhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    BddAbove
      (Set.range (phase p (minimumNormalizedSourceContinuousMap D))) := by
  refine ⟨D.supportError -
    SupportFunction.pairing p
      (sourceMomentMinimumPoint D) +
    D.potential (sourceMomentMinimumPoint D), ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [minimumNormalizedSource_phase]
  linarith [sourceMomentPhase_le_supportError D hp
    (x + sourceMomentMinimumPoint D)]

private theorem minimumNormalizedSourceBodyDual_eq_legendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    minimumNormalizedSourceBodyDual D p =
      legendreTransform (minimumNormalizedSourceContinuousMap D) p := by
  apply le_antisymm
  · have hbdd := minimumNormalizedSourcePhase_bddAbove D hp
    have hupper :
        legendreTransform D.potential p ≤
          legendreTransform
              (minimumNormalizedSourceContinuousMap D) p +
            SupportFunction.pairing p
              (sourceMomentMinimumPoint D) -
            D.potential (sourceMomentMinimumPoint D) := by
      unfold legendreTransform
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨y, rfl⟩
      have h := le_csSup hbdd
        (show
          phase p (minimumNormalizedSourceContinuousMap D)
              (y - sourceMomentMinimumPoint D) ∈
            Set.range
              (phase p (minimumNormalizedSourceContinuousMap D))
          from ⟨y - sourceMomentMinimumPoint D, rfl⟩)
      rw [minimumNormalizedSource_phase] at h
      simp only [sub_add_cancel] at h
      linarith
    unfold minimumNormalizedSourceBodyDual
    linarith
  · change
      sSup (Set.range
        (phase p (minimumNormalizedSourceContinuousMap D))) ≤
        minimumNormalizedSourceBodyDual D p
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    rw [minimumNormalizedSource_phase]
    have h := le_csSup (sourceMomentPhase_bddAbove D hp)
      (show
        phase p D.potential
            (x + sourceMomentMinimumPoint D) ∈
          Set.range (phase p D.potential)
        from ⟨x + sourceMomentMinimumPoint D, rfl⟩)
    change
      phase p D.potential
          (x + sourceMomentMinimumPoint D) ≤
        legendreTransform D.potential p at h
    unfold minimumNormalizedSourceBodyDual
    linarith

private theorem minimumNormalizedSourceBodyDual_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    0 ≤ minimumNormalizedSourceBodyDual D p := by
  have h := sourceMomentBodyFenchel_le D hp
    (sourceMomentMinimumPoint D)
  unfold minimumNormalizedSourceBodyDual
  linarith

private theorem minimumNormalizedSourceBodyDual_integrableOn {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    IntegrableOn (minimumNormalizedSourceBodyDual D)
      K.carrier (volume : Measure (Space n)) := by
  have hleg := sourceMomentLegendre_integrableOn D
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (sourceMomentMinimumPoint D)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        D.potential (sourceMomentMinimumPoint D))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  exact (hleg.sub hpair).add hconst

private theorem minimumNormalizedSourceBodyDual_setIntegral {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier, legendreTransform D.potential p
        ∂(volume : Measure (Space n))) +
      normalizedVolume K.carrier *
        D.potential (sourceMomentMinimumPoint D) := by
  have hleg := sourceMomentLegendre_integrableOn D
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (sourceMomentMinimumPoint D)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        D.potential (sourceMomentMinimumPoint D))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  calc
    (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
      ∂(volume : Measure (Space n))) =
        (∫ p in K.carrier,
          legendreTransform D.potential p -
            SupportFunction.pairing p
              (sourceMomentMinimumPoint D)
          ∂(volume : Measure (Space n))) +
        (∫ _p in K.carrier,
          D.potential (sourceMomentMinimumPoint D)
          ∂(volume : Measure (Space n))) := by
            simpa only [minimumNormalizedSourceBodyDual, integral_const, MeasurableSet.univ,
              measureReal_restrict_apply, univ_inter, smul_eq_mul, Pi.sub_apply] using
              MeasureTheory.integral_add (hleg.sub hpair) hconst
    _ = (∫ p in K.carrier, legendreTransform D.potential p
          ∂(volume : Measure (Space n))) +
        normalizedVolume K.carrier *
          D.potential (sourceMomentMinimumPoint D) := by
            rw [MeasureTheory.integral_sub hleg hpair,
              sourceCenteredBody_setIntegral_pairing_eq_zero,
              MeasureTheory.setIntegral_const]
            simp only [sub_zero, measureReal_def, smul_eq_mul, normalizedVolume]

private theorem minimumNormalizedSourceBodyDual_energy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (normalizedVolume K.carrier)⁻¹ *
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
      sourceMomentBodyEnergy D +
        D.potential (sourceMomentMinimumPoint D) := by
  rw [minimumNormalizedSourceBodyDual_setIntegral]
  unfold sourceMomentBodyEnergy
  have hvol := K.volume_pos.ne'
  field_simp

private theorem sourceMomentBodyEnergy_add_minimum_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 ≤ sourceMomentBodyEnergy D +
      D.potential (sourceMomentMinimumPoint D) := by
  rw [← minimumNormalizedSourceBodyDual_energy]
  exact mul_nonneg
    (inv_nonneg.mpr K.volume_pos.le)
    (MeasureTheory.setIntegral_nonneg K.compact.measurableSet
      (fun p hp => minimumNormalizedSourceBodyDual_nonneg D hp))

end MomentCoercivityCompactness

namespace MomentFunctionalCoercivity

open Set Function Filter MeasureTheory TopologicalSpace
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open MomentCoercivityCompactness
open scoped BigOperators ENNReal NNReal Topology

private def sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ))
    (p : Space n) : ℝ≥0∞ :=
  ⨆ j : ℕ,
    ENNReal.ofReal
      (phase p f (TopologicalSpace.denseSeq (Space n) j))

private theorem measurable_sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ)) :
    Measurable (sourceExtendedBodyLegendre f) := by
  unfold sourceExtendedBodyLegendre
  apply Measurable.iSup
  intro j
  have hcontinuous : Continuous
      (fun p : Space n =>
        phase p f (TopologicalSpace.denseSeq (Space n) j)) := by
    unfold phase
    simp_rw [← sourcePairingContinuousLinear_apply]
    exact (sourcePairingContinuousLinear
      (TopologicalSpace.denseSeq (Space n) j)).continuous.fun_sub
        continuous_const
  exact hcontinuous.measurable.ennreal_ofReal

private theorem ofReal_phase_le_sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ))
    (p x : Space n) :
    ENNReal.ofReal (phase p f x) ≤
      sourceExtendedBodyLegendre f p := by
  refine (TopologicalSpace.denseRange_denseSeq
    (Space n)).induction_on x ?_ ?_
  · exact isClosed_le
      (ENNReal.continuous_ofReal.comp
        (continuous_phase p f.continuous))
      continuous_const
  · intro j
    exact le_iSup
      (fun k : ℕ =>
        ENNReal.ofReal
          (phase p f
            (TopologicalSpace.denseSeq (Space n) k))) j

private theorem sourceExtendedBodyLegendre_eq_of_bddAbove {n : ℕ}
    (f : C(Space n, ℝ))
    (p : Space n)
    (hbdd : BddAbove (Set.range (phase p f))) :
    sourceExtendedBodyLegendre f p =
      ENNReal.ofReal (legendreTransform f p) := by
  apply le_antisymm
  · unfold sourceExtendedBodyLegendre
    apply iSup_le
    intro j
    apply ENNReal.ofReal_le_ofReal
    exact le_csSup hbdd
      ⟨TopologicalSpace.denseSeq (Space n) j, rfl⟩
  · by_cases htop : sourceExtendedBodyLegendre f p = ⊤
    · simp only [htop, le_top]
    · have hreal :
          legendreTransform f p ≤
            (sourceExtendedBodyLegendre f p).toReal := by
        unfold legendreTransform
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨x, rfl⟩
        apply (ENNReal.ofReal_le_ofReal_iff
          ENNReal.toReal_nonneg).mp
        rw [ENNReal.ofReal_toReal htop]
        exact ofReal_phase_le_sourceExtendedBodyLegendre f p x
      simpa only [ge_iff_le, ENNReal.ofReal_toReal htop] using
        ENNReal.ofReal_le_ofReal hreal

private theorem sourceExtendedBodyLegendre_limit_le_liminf {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    {p : Space n}
    (hp : p ∈ K.carrier) :
    sourceExtendedBodyLegendre f p ≤
      Filter.liminf
        (fun j => ENNReal.ofReal
          (minimumNormalizedSourceBodyDual (D (φ j)) p))
        atTop := by
  unfold sourceExtendedBodyLegendre
  apply iSup_le
  intro k
  let q : Space n :=
    TopologicalSpace.denseSeq (Space n) k
  have hpoint :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) q)
        atTop (𝓝 (f q)) :=
    (continuous_eval_const q).continuousAt.tendsto.comp hconv
  have hphase :
      Tendsto
        (fun j => phase p
          (minimumNormalizedSourceContinuousMap (D (φ j))) q)
        atTop (𝓝 (phase p f q)) := by
    simpa only [phase] using
      (tendsto_const_nhds.sub hpoint)
  have hphaseENN :
      Tendsto
        (fun j => ENNReal.ofReal
          (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q))
        atTop (𝓝 (ENNReal.ofReal (phase p f q))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hphase
  have hmono :
      Filter.liminf
          (fun j => ENNReal.ofReal
            (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q))
          atTop ≤
        Filter.liminf
          (fun j => ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p))
          atTop := by
    have hpointle : ∀ j : ℕ,
        ENNReal.ofReal
            (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q) ≤
          ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p) := by
      intro j
      apply ENNReal.ofReal_le_ofReal
      have h := le_csSup
        (minimumNormalizedSourcePhase_bddAbove (D (φ j)) hp)
        (show
          phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q ∈
            Set.range
              (phase p (minimumNormalizedSourceContinuousMap (D (φ j))))
          from ⟨q, rfl⟩)
      change
        phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q ≤
          legendreTransform
            (minimumNormalizedSourceContinuousMap (D (φ j))) p at h
      rwa [← minimumNormalizedSourceBodyDual_eq_legendre (D (φ j)) hp]
        at h
    exact Filter.liminf_le_liminf (Eventually.of_forall hpointle)
  simpa only [q, hphaseENN.liminf_eq] using hmono

private theorem sourceExtendedBodyLegendre_lintegral_le_liminf {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f)) :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
      Filter.liminf
        (fun j =>
          ∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n)))
        atTop := by
  calc
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
        ∫⁻ p in K.carrier,
          Filter.liminf
            (fun j => ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p))
            atTop
          ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.lintegral_mono_ae
            filter_upwards
              [MeasureTheory.ae_restrict_mem
                K.compact.measurableSet] with p hp
            exact sourceExtendedBodyLegendre_limit_le_liminf
              D φ f hconv hp
    _ ≤ Filter.liminf
        (fun j =>
          ∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n)))
        atTop := by
          apply MeasureTheory.lintegral_liminf_le'
          intro j
          exact
            (minimumNormalizedSourceBodyDual_integrableOn
              (D (φ j))).aestronglyMeasurable.aemeasurable.ennreal_ofReal

private theorem minimumNormalizedSourceBodyDual_lintegral {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫⁻ p in K.carrier,
      ENNReal.ofReal (minimumNormalizedSourceBodyDual D p)
      ∂(volume : Measure (Space n))) =
      ENNReal.ofReal
        (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
  symm
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (minimumNormalizedSourceBodyDual_integrableOn D)
  filter_upwards
    [MeasureTheory.ae_restrict_mem K.compact.measurableSet]
    with p hp
  exact minimumNormalizedSourceBodyDual_nonneg D hp

private theorem sourceExtendedBodyLegendre_lintegral_le_of_uniformEnergy
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential
          (sourceMomentMinimumPoint (D j)) ≤ C) :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
      ENNReal.ofReal (normalizedVolume K.carrier * C) := by
  calc
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
        Filter.liminf
          (fun j =>
            ∫⁻ p in K.carrier,
              ENNReal.ofReal
                (minimumNormalizedSourceBodyDual (D (φ j)) p)
              ∂(volume : Measure (Space n)))
          atTop :=
        sourceExtendedBodyLegendre_lintegral_le_liminf
          D φ f hconv
    _ ≤ ENNReal.ofReal (normalizedVolume K.carrier * C) := by
      have hterm : ∀ j : ℕ,
          (∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n))) ≤
            ENNReal.ofReal
              (normalizedVolume K.carrier * C) := by
        intro j
        rw [minimumNormalizedSourceBodyDual_lintegral]
        apply ENNReal.ofReal_le_ofReal
        calc
          (∫ p in K.carrier,
            minimumNormalizedSourceBodyDual (D (φ j)) p
            ∂(volume : Measure (Space n))) =
              normalizedVolume K.carrier *
                (sourceMomentBodyEnergy (D (φ j)) +
                  (D (φ j)).potential
                    (sourceMomentMinimumPoint (D (φ j)))) := by
                  have h :=
                    minimumNormalizedSourceBodyDual_energy (D (φ j))
                  have hvol := K.volume_pos.ne'
                  field_simp at h
                  linarith
          _ ≤ normalizedVolume K.carrier * C :=
            mul_le_mul_of_nonneg_left
              (henergy (φ j)) K.volume_pos.le
      have hmono := Filter.liminf_le_liminf
        (show
          ∀ᶠ j : ℕ in atTop,
            (∫⁻ p in K.carrier,
              ENNReal.ofReal
                (minimumNormalizedSourceBodyDual (D (φ j)) p)
              ∂(volume : Measure (Space n))) ≤
              (fun _ : ℕ =>
                ENNReal.ofReal
                  (normalizedVolume K.carrier * C)) j
          from Eventually.of_forall hterm)
      have hconst :
          Tendsto
            (fun _ : ℕ =>
              ENNReal.ofReal
                (normalizedVolume K.carrier * C))
            atTop
            (𝓝 (ENNReal.ofReal
              (normalizedVolume K.carrier * C))) :=
        tendsto_const_nhds
      simpa only [hconst.liminf_eq] using hmono

private theorem exists_minimumNormalizedSourceFiniteEnergy_subsequence
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential
          (sourceMomentMinimumPoint (D j)) ≤ C) :
    ∃ (f : C(Space n, ℝ))
      (φ : ℕ → ℕ),
      f 0 = 0 ∧
      LipschitzWith (sourceBodyLipschitzConstant K) f ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x : Space n,
        0 ≤ f x ∧
          f x ≤ SupportFunction.supportFunction K.carrier x) ∧
      StrictMono φ ∧
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 f) ∧
      (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
        ∂(volume : Measure (Space n))) ≤
        ENNReal.ofReal (normalizedVolume K.carrier * C) := by
  obtain ⟨f, φ, hzero, hlip, hconvex, hbounds,
    hφ, hconv⟩ :=
    exists_minimumNormalizedSourceConvex_subsequence D
  exact ⟨f, φ, hzero, hlip, hconvex, hbounds, hφ, hconv,
    sourceExtendedBodyLegendre_lintegral_le_of_uniformEnergy
      D φ f hconv C henergy⟩

end MomentFunctionalCoercivity

namespace MomentNonlinearTightness

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentCoercivityCompactness
open scoped BigOperators ENNReal NNReal Topology

private theorem exists_uniform_inner_supportBall {n : ℕ}
    (K : CenteredBody n) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      ∀ x : Space n,
        ∃ c : Space n,
          Metric.ball c (ρ / 2) ⊆ K.carrier ∧
          ∀ p ∈ Metric.ball c (ρ / 2),
            δ * ‖x‖ ≤ SupportFunction.pairing p x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n)
      (LatticeAsymptotics.zero_mem_interior K)
  obtain ⟨d, hd, hgap⟩ :=
    SupportFunction.interior_gap K.compact
      (LatticeAsymptotics.zero_mem_interior K)
  let ρ : ℝ := min (r / 2) (d / (4 * ((n : ℝ) + 1)))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (half_pos hr)
      (div_pos hd (by positivity))
  have hρr : ρ < r :=
    (show ρ ≤ r / 2 from min_le_left _ _).trans_lt
      (half_lt_self hr)
  have hnrho : (n : ℝ) * ρ ≤ d / 4 := by
    have hfrac : ρ ≤ d / (4 * ((n : ℝ) + 1)) :=
      min_le_right _ _
    have hden : 0 < 4 * ((n : ℝ) + 1) := by
      positivity
    have hmul := (le_div_iff₀ hden).mp hfrac
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hρ.le]
  refine ⟨ρ, d / 4, hρ, by positivity, ?_⟩
  intro x
  obtain ⟨v, hv, hmax⟩ :=
    SupportFunction.supportFunction_attained
      K.compact (K.fullDimensional.mono interior_subset) x
  refine ⟨(2 : ℝ)⁻¹ • v, ?_, ?_⟩
  · intro p hp
    have hdist :
        ‖p - (2 : ℝ)⁻¹ • v‖ < ρ / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hp
    let z : Space n := (2 : ℝ) • p - v
    have hzform :
        z = (2 : ℝ) • (p - (2 : ℝ)⁻¹ • v) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, z]
      ring
    have hznorm : ‖z‖ < ρ := by
      rw [hzform, norm_smul, Real.norm_eq_abs]
      norm_num
      nlinarith
    have hzball : z ∈ Metric.ball (0 : Space n) r := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hznorm.trans hρr
    have hzK : z ∈ K.carrier :=
      interior_subset (hball hzball)
    have hpform :
        p = (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • z := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, z]
      ring
    rw [hpform]
    exact K.convex hv hzK (by norm_num) (by norm_num) (by norm_num)
  · intro p hp
    have hdist :
        ‖p - (2 : ℝ)⁻¹ • v‖ < ρ / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hp
    let z : Space n := (2 : ℝ) • p - v
    have hzform :
        z = (2 : ℝ) • (p - (2 : ℝ)⁻¹ • v) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, z]
      ring
    have hznorm : ‖z‖ < ρ := by
      rw [hzform, norm_smul, Real.norm_eq_abs]
      norm_num
      nlinarith
    have hzbound :
        |SupportFunction.pairing z x| ≤
          (d / 4) * ‖x‖ := by
      calc
        |SupportFunction.pairing z x| ≤
            ((n : ℝ) * ‖z‖) * ‖x‖ :=
          MonomialDivergence.abs_pairing_le_dimension_mul_norm
            z x
        _ ≤ ((n : ℝ) * ρ) * ‖x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hznorm.le
              (Nat.cast_nonneg n))
            (norm_nonneg x)
        _ ≤ (d / 4) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hnrho (norm_nonneg x)
    have hvbound :
        d * ‖x‖ ≤ SupportFunction.pairing v x := by
      have hg := hgap x
      simpa only [SupportFunction.pairing, ge_iff_le, hmax, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, sub_zero] using hg
    have hpform :
        p = (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • z := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, z]
      ring
    rw [hpform, SupportFunction.pairing_add_left,
      SupportFunction.pairing_smul_left,
      SupportFunction.pairing_smul_left]
    have hzlow := (abs_le.mp hzbound).1
    norm_num
    nlinarith [mul_nonneg hd.le (norm_nonneg x)]

private theorem realVolume_uniformInnerBall {n : ℕ}
    (c : Space n)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    (volume : Measure (Space n)).real
        (Metric.ball c (ρ / 2)) = ρ ^ n := by
  have h := congrArg ENNReal.toReal
    (Real.volume_pi_ball c (half_pos hρ))
  have htwo : (2 : ℝ) * (ρ / 2) = ρ := by
    ring
  simpa only [measureReal_def, htwo, Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg hρ.le n)] using h

private theorem minimumNormalizedSourceBodyFenchel_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier)
    (x : Space n) :
    SupportFunction.pairing p x -
        minimumNormalizedSourceContinuousMap D x ≤
      minimumNormalizedSourceBodyDual D p := by
  have h := le_csSup
    (minimumNormalizedSourcePhase_bddAbove D hp)
    (show
      phase p (minimumNormalizedSourceContinuousMap D) x ∈
        Set.range (phase p (minimumNormalizedSourceContinuousMap D))
      from ⟨x, rfl⟩)
  change
    SupportFunction.pairing p x -
        minimumNormalizedSourceContinuousMap D x ≤
      legendreTransform (minimumNormalizedSourceContinuousMap D) p at h
  rwa [← minimumNormalizedSourceBodyDual_eq_legendre D hp] at h

private theorem exists_minimumNormalizedSource_linear_coercivity {n : ℕ}
    (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (D : SourceMomentPotential K)
        (x : Space n),
        δ * ‖x‖ ≤
          minimumNormalizedSourceContinuousMap D x +
            B *
              (sourceMomentBodyEnergy D +
                D.potential (sourceMomentMinimumPoint D)) := by
  obtain ⟨ρ, δ, hρ, hδ, hball⟩ :=
    exists_uniform_inner_supportBall K
  have hpow : 0 < ρ ^ n := pow_pos hρ n
  refine ⟨δ, normalizedVolume K.carrier / ρ ^ n,
    hδ, div_pos K.volume_pos hpow, ?_⟩
  intro D x
  obtain ⟨c, hsubset, hpair⟩ := hball x
  have hfinite :
      (volume : Measure (Space n))
          (Metric.ball c (ρ / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top K.compact.measure_ne_top
      (measure_mono hsubset)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const hfinite
  have hdualK := minimumNormalizedSourceBodyDual_integrableOn D
  have hdualball : IntegrableOn
      (minimumNormalizedSourceBodyDual D)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    hdualK.mono_set hsubset
  have hdualmass :
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
        normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D)) := by
    have h := minimumNormalizedSourceBodyDual_energy D
    have hvol := K.volume_pos.ne'
    field_simp at h
    linarith
  have hbound :
      ρ ^ n *
          (δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x) ≤
        normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D)) := by
    calc
      ρ ^ n *
          (δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x) =
          (∫ _p in Metric.ball c (ρ / 2),
            δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x
            ∂(volume : Measure (Space n))) := by
              rw [MeasureTheory.setIntegral_const,
                realVolume_uniformInnerBall c hρ]
              simp only [smul_eq_mul]
      _ ≤ (∫ p in Metric.ball c (ρ / 2),
          minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_on
              hconst hdualball Metric.isOpen_ball.measurableSet
            intro p hp
            calc
              δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x ≤
                  SupportFunction.pairing p x -
                    minimumNormalizedSourceContinuousMap D x :=
                sub_le_sub_right (hpair p hp) _
              _ ≤ minimumNormalizedSourceBodyDual D p :=
                minimumNormalizedSourceBodyFenchel_le
                  D (hsubset hp) x
      _ ≤ (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_set hdualK
            · filter_upwards
                [MeasureTheory.ae_restrict_mem
                  K.compact.measurableSet] with p hp
              exact minimumNormalizedSourceBodyDual_nonneg D hp
            · exact Filter.Eventually.of_forall hsubset
      _ = normalizedVolume K.carrier *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D)) :=
          hdualmass
  have hdiv :
      δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x ≤
        (normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D))) /
          ρ ^ n := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [mul_comm] using hbound
  calc
    δ * ‖x‖ ≤
        minimumNormalizedSourceContinuousMap D x +
          (normalizedVolume K.carrier *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D))) /
            ρ ^ n := by
          linarith
    _ = minimumNormalizedSourceContinuousMap D x +
          (normalizedVolume K.carrier / ρ ^ n) *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D)) := by
          ring

private theorem exists_minimumNormalizedSource_gibbs_decay {n : ℕ}
    (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (D : SourceMomentPotential K)
        (x : Space n),
        Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
          Real.exp
              (B *
                (sourceMomentBodyEnergy D +
                  D.potential (sourceMomentMinimumPoint D))) *
            Real.exp (-δ * ‖x‖) := by
  obtain ⟨δ, B, hδ, hB, hcoerce⟩ :=
    exists_minimumNormalizedSource_linear_coercivity K
  refine ⟨δ, B, hδ, hB, ?_⟩
  intro D x
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hcoerce D x]

end MomentNonlinearTightness

namespace MomentMoserTrudinger

open Set Function Filter MeasureTheory
open MomentExistence MomentPotentialExistence MomentCoercivityCompactness MomentNonlinearTightness
open scoped BigOperators ENNReal NNReal Topology

private theorem integrable_exp_neg_mul_norm_all {n : ℕ} {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : Space n => Real.exp (-a * ‖x‖))
      (volume : Measure (Space n)) := by
  cases n with
  | zero =>
      rw [MeasureTheory.Measure.volume_pi_eq_dirac
        (0 : Space 0)]
      exact MeasureTheory.integrable_dirac (by simp only [Matrix.zero_empty, neg_mul, enorm_lt_top])
  | succ n =>
      exact MonomialIntegrability.integrable_exp_neg_mul_norm
        (Nat.zero_lt_succ n) ha

private def minimumNormalizedSourceBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  sourceMomentBodyEnergy D +
    D.potential (sourceMomentMinimumPoint D)

private def minimumNormalizedSourcePartition {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  ∫ x : Space n,
    Real.exp (-minimumNormalizedSourceContinuousMap D x)
    ∂(volume : Measure (Space n))

private theorem minimumNormalizedSourceDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    Integrable
      (fun x : Space n =>
        Real.exp (-minimumNormalizedSourceContinuousMap D x))
      (volume : Measure (Space n)) := by
  obtain ⟨δ, B, hδ, _hB, hdecay⟩ :=
    exists_minimumNormalizedSource_gibbs_decay K
  refine ((integrable_exp_neg_mul_norm_all hδ).const_mul
    (Real.exp (B * minimumNormalizedSourceBodyEnergy D))).mono'
    (Real.continuous_exp.comp
      (minimumNormalizedSourceContinuousMap D).continuous.neg).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hdecay D x

private theorem minimumNormalizedSourcePartition_eq {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourcePartition D =
      Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        sourceMomentPartition D := by
  unfold minimumNormalizedSourcePartition
  calc
    (∫ x : Space n,
      Real.exp (-minimumNormalizedSourceContinuousMap D x)
      ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          Real.exp (D.potential (sourceMomentMinimumPoint D)) *
            Real.exp
              (-D.potential (x + sourceMomentMinimumPoint D))
          ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [← Real.exp_add]
            congr 1
            change
              -(D.potential (x + sourceMomentMinimumPoint D) -
                D.potential (sourceMomentMinimumPoint D)) =
                D.potential (sourceMomentMinimumPoint D) +
                  -D.potential (x + sourceMomentMinimumPoint D)
            ring
    _ = Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        (∫ x : Space n,
          Real.exp
            (-D.potential (x + sourceMomentMinimumPoint D))
          ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul _ _
    _ = Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        sourceMomentPartition D := by
        rw [MeasureTheory.integral_add_right_eq_self
          (fun x : Space n => Real.exp (-D.potential x))
          (sourceMomentMinimumPoint D)]
        rfl

private theorem minimumNormalizedSourcePartition_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < minimumNormalizedSourcePartition D := by
  rw [minimumNormalizedSourcePartition_eq]
  exact mul_pos (Real.exp_pos _)
    (sourceMomentPartition_pos D)

private def minimumNormalizedSourceBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  Real.log (minimumNormalizedSourcePartition D) -
    minimumNormalizedSourceBodyEnergy D

private theorem minimumNormalizedSourceBermanFunctional_eq {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceBermanFunctional D =
      sourceMomentBermanFunctional D := by
  unfold minimumNormalizedSourceBermanFunctional
    minimumNormalizedSourceBodyEnergy sourceMomentBermanFunctional
  rw [minimumNormalizedSourcePartition_eq,
    Real.log_mul (Real.exp_pos _).ne'
      (sourceMomentPartition_pos D).ne',
    Real.log_exp]
  ring

private theorem minimumNormalizedSourceBodyEnergy_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 ≤ minimumNormalizedSourceBodyEnergy D :=
  sourceMomentBodyEnergy_add_minimum_nonneg D

private theorem exists_minimumNormalizedSource_strong_moser_trudinger
    {n : ℕ} (K : CenteredBody n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ,
      ∀ D : SourceMomentPotential K,
        Real.log (minimumNormalizedSourcePartition D) ≤
          ε * minimumNormalizedSourceBodyEnergy D + A := by
  obtain ⟨δ, B, hδ, hB, hcoerce⟩ :=
    exists_minimumNormalizedSource_linear_coercivity K
  let t : ℝ := min 1 (ε / B)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hε hB)
  have htone : t ≤ 1 := min_le_left _ _
  have htB : t * B ≤ ε := by
    calc
      t * B ≤ (ε / B) * B :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hB.le
      _ = ε := by field_simp
  let I : ℝ :=
    ∫ x : Space n,
      Real.exp (-(t * δ) * ‖x‖)
      ∂(volume : Measure (Space n))
  have hrad : Integrable
      (fun x : Space n => Real.exp (-(t * δ) * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all (mul_pos ht hδ)
  have hI : 0 < I := by
    dsimp [I]
    exact MeasureTheory.integral_exp_pos hrad
  refine ⟨Real.log I, ?_⟩
  intro D
  have henergy := minimumNormalizedSourceBodyEnergy_nonneg D
  have hpoint (x : Space n) :
      Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
        Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
          Real.exp (-(t * δ) * ‖x‖) := by
    have hφ := minimumNormalizedSourceContinuousMap_nonneg D x
    have htφ :
        t * minimumNormalizedSourceContinuousMap D x ≤
          minimumNormalizedSourceContinuousMap D x := by
      calc
        t * minimumNormalizedSourceContinuousMap D x ≤
            1 * minimumNormalizedSourceContinuousMap D x :=
          mul_le_mul_of_nonneg_right htone hφ
        _ = minimumNormalizedSourceContinuousMap D x := one_mul _
    have hc := hcoerce D x
    change
      δ * ‖x‖ ≤ minimumNormalizedSourceContinuousMap D x +
        B * minimumNormalizedSourceBodyEnergy D at hc
    have hscaled := mul_le_mul_of_nonneg_left hc ht.le
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbound :
      minimumNormalizedSourcePartition D ≤
        Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) * I := by
    unfold minimumNormalizedSourcePartition
    calc
      (∫ x : Space n,
        Real.exp (-minimumNormalizedSourceContinuousMap D x)
        ∂(volume : Measure (Space n))) ≤
          ∫ x : Space n,
            Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
              Real.exp (-(t * δ) * ‖x‖)
            ∂(volume : Measure (Space n)) :=
              MeasureTheory.integral_mono
                (minimumNormalizedSourceDensity_integrable D)
                (hrad.const_mul
                  (Real.exp
                    (t * B * minimumNormalizedSourceBodyEnergy D)))
                hpoint
      _ = Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
          I := by
            rw [MeasureTheory.integral_const_mul]
  calc
    Real.log (minimumNormalizedSourcePartition D) ≤
        Real.log
          (Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) * I) :=
      Real.log_le_log (minimumNormalizedSourcePartition_pos D) hbound
    _ = t * B * minimumNormalizedSourceBodyEnergy D + Real.log I := by
      rw [Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
    _ ≤ ε * minimumNormalizedSourceBodyEnergy D + Real.log I :=
      add_le_add
        (mul_le_mul_of_nonneg_right htB henergy)
        (le_refl _)

private theorem sourceMomentBermanFunctional_bddAbove {n : ℕ}
    (K : CenteredBody n) :
    BddAbove
      (Set.range
        (fun D : SourceMomentPotential K =>
          sourceMomentBermanFunctional D)) := by
  obtain ⟨A, hA⟩ :=
    exists_minimumNormalizedSource_strong_moser_trudinger
      K (1 / 2 : ℝ) (by norm_num)
  refine ⟨A, ?_⟩
  rintro _ ⟨D, rfl⟩
  change sourceMomentBermanFunctional D ≤ A
  rw [← minimumNormalizedSourceBermanFunctional_eq D]
  unfold minimumNormalizedSourceBermanFunctional
  linarith [hA D, minimumNormalizedSourceBodyEnergy_nonneg D]

private theorem exists_sourceMomentBerman_superlevel_uniformEnergy
    {n : ℕ} (K : CenteredBody n) (L : ℝ) :
    ∃ C : ℝ,
      ∀ D : SourceMomentPotential K,
        L ≤ sourceMomentBermanFunctional D →
          minimumNormalizedSourceBodyEnergy D ≤ C := by
  obtain ⟨A, hA⟩ :=
    exists_minimumNormalizedSource_strong_moser_trudinger
      K (1 / 2 : ℝ) (by norm_num)
  refine ⟨2 * (A - L), ?_⟩
  intro D hL
  have hfunctional := minimumNormalizedSourceBermanFunctional_eq D
  unfold minimumNormalizedSourceBermanFunctional at hfunctional
  nlinarith [hA D]

private theorem exists_sourceMomentBerman_maximizingSequence_uniformEnergy
    {n : ℕ} (K : CenteredBody n) :
    ∃ (D : ℕ → SourceMomentPotential K) (C : ℝ),
      (∀ j : ℕ, minimumNormalizedSourceBodyEnergy (D j) ≤ C) ∧
      Tendsto
        (fun j => sourceMomentBermanFunctional (D j))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun D : SourceMomentPotential K =>
                sourceMomentBermanFunctional D)))) := by
  obtain ⟨u, hmono, hlimit, hmem⟩ :=
    exists_seq_tendsto_sSup
      (show
        (Set.range
          (fun D : SourceMomentPotential K =>
            sourceMomentBermanFunctional D)).Nonempty from
        ⟨sourceMomentBermanFunctional
            (canonicalSourceMomentPotential K),
          canonicalSourceMomentPotential K, rfl⟩)
      (sourceMomentBermanFunctional_bddAbove K)
  have hchoose :
      ∀ j : ℕ, ∃ D : SourceMomentPotential K,
        sourceMomentBermanFunctional D = u j := by
    intro j
    exact hmem j
  choose D hD using hchoose
  obtain ⟨C, hC⟩ :=
    exists_sourceMomentBerman_superlevel_uniformEnergy K (u 0)
  refine ⟨D, C, ?_, ?_⟩
  · intro j
    apply hC
    rw [hD j]
    exact hmono (Nat.zero_le j)
  · have heq :
        (fun j => sourceMomentBermanFunctional (D j)) = u :=
      funext hD
    rw [heq]
    exact hlimit

end MomentMoserTrudinger

namespace MomentOptimizer

open Set Function Filter MeasureTheory
open MomentExistence MomentPotentialExistence MomentMinimizer MomentCoercivityCompactness
open MomentFunctionalCoercivity MomentNonlinearTightness MomentMoserTrudinger
open scoped BigOperators ENNReal NNReal Topology

private theorem exists_minimumNormalizedSource_uniform_gibbs_majorant_all
    {n : ℕ} (K : CenteredBody n) (C : ℝ) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      Integrable
        (fun x : Space n =>
          Real.exp (B * C) * Real.exp (-δ * ‖x‖))
        (volume : Measure (Space n)) ∧
      ∀ (D : SourceMomentPotential K),
        minimumNormalizedSourceBodyEnergy D ≤ C →
        ∀ x : Space n,
          Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
            Real.exp (B * C) * Real.exp (-δ * ‖x‖) := by
  obtain ⟨δ, B, hδ, hB, hdecay⟩ :=
    exists_minimumNormalizedSource_gibbs_decay K
  refine ⟨δ, B, hδ, hB,
    (integrable_exp_neg_mul_norm_all hδ).const_mul
      (Real.exp (B * C)), ?_⟩
  intro D henergy x
  calc
    Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
        Real.exp (B * minimumNormalizedSourceBodyEnergy D) *
          Real.exp (-δ * ‖x‖) := hdecay D x
    _ ≤ Real.exp (B * C) * Real.exp (-δ * ‖x‖) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left henergy hB.le))
        (Real.exp_pos _).le

private theorem tendsto_minimumNormalizedSourcePartition_of_uniformEnergy_all
    {n : ℕ} {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      minimumNormalizedSourceBodyEnergy (D j) ≤ C) :
    Tendsto
      (fun j => minimumNormalizedSourcePartition (D (φ j)))
      atTop
      (𝓝
        (∫ x : Space n, Real.exp (-f x)
          ∂(volume : Measure (Space n)))) := by
  obtain ⟨δ, B, _hδ, _hB, hG, hmajor⟩ :=
    exists_minimumNormalizedSource_uniform_gibbs_majorant_all K C
  unfold minimumNormalizedSourcePartition
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Space n =>
      Real.exp (B * C) * Real.exp (-δ * ‖x‖))
  · intro j
    exact (Real.continuous_exp.comp
      (minimumNormalizedSourceContinuousMap
        (D (φ j))).continuous.neg).aestronglyMeasurable
  · exact hG
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hmajor (D (φ j)) (henergy (φ j)) x
  · filter_upwards with x
    have hx :=
      (continuous_eval_const x).continuousAt.tendsto.comp hconv
    exact (Real.continuous_exp.tendsto _).comp hx.neg

private structure SourceFiniteEnergyPotential {n : ℕ}
    (K : CenteredBody n) where
  potential : C(Space n, ℝ)
  normalized : potential 0 = 0
  lipschitz : LipschitzWith (sourceBodyLipschitzConstant K) potential
  convex : ConvexOn ℝ Set.univ potential
  nonnegative : ∀ x : Space n, 0 ≤ potential x
  supportUpper : ∀ x : Space n,
    potential x ≤ SupportFunction.supportFunction K.carrier x
  legendreFinite :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre potential p
      ∂(volume : Measure (Space n))) < ⊤
  densityIntegrable :
    Integrable (fun x : Space n => Real.exp (-potential x))
      (volume : Measure (Space n))

private def finiteEnergySourcePartition {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  ∫ x : Space n, Real.exp (-F.potential x)
    ∂(volume : Measure (Space n))

private theorem finiteEnergySourcePartition_pos {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    0 < finiteEnergySourcePartition F :=
  MeasureTheory.integral_exp_pos F.densityIntegrable

private def finiteEnergySourceBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  (normalizedVolume K.carrier)⁻¹ *
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre F.potential p
      ∂(volume : Measure (Space n))).toReal

private def finiteEnergySourceBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  Real.log (finiteEnergySourcePartition F) -
    finiteEnergySourceBodyEnergy F

private theorem integrable_limit_gibbs_of_uniformEnergy_all
    {n : ℕ} {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      minimumNormalizedSourceBodyEnergy (D j) ≤ C) :
    Integrable (fun x : Space n => Real.exp (-f x))
      (volume : Measure (Space n)) := by
  obtain ⟨δ, B, _hδ, _hB, hG, hmajor⟩ :=
    exists_minimumNormalizedSource_uniform_gibbs_majorant_all K C
  refine hG.mono'
    (Real.continuous_exp.comp f.continuous.neg).aestronglyMeasurable
    ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hx :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  have hexp :
      Tendsto
        (fun j => Real.exp
          (-minimumNormalizedSourceContinuousMap (D (φ j)) x))
        atTop (𝓝 (Real.exp (-f x))) :=
    (Real.continuous_exp.tendsto _).comp hx.neg
  exact le_of_tendsto hexp
    (Eventually.of_forall fun j =>
      hmajor (D (φ j)) (henergy (φ j)) x)

private theorem minimumNormalizedSourceBodyDual_lintegral_eq_volume_mul_energy
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫⁻ p in K.carrier,
      ENNReal.ofReal (minimumNormalizedSourceBodyDual D p)
      ∂(volume : Measure (Space n))) =
      ENNReal.ofReal
        (normalizedVolume K.carrier *
          minimumNormalizedSourceBodyEnergy D) := by
  rw [minimumNormalizedSourceBodyDual_lintegral]
  congr 1
  have h := minimumNormalizedSourceBodyDual_energy D
  change
    (normalizedVolume K.carrier)⁻¹ *
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
      minimumNormalizedSourceBodyEnergy D at h
  have hvol := K.volume_pos.ne'
  field_simp at h
  linarith

private theorem exists_finiteEnergySourceBerman_optimizer {n : ℕ}
    (K : CenteredBody n) :
    ∃ (F : SourceFiniteEnergyPotential K)
      (D : ℕ → SourceMomentPotential K)
      (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 F.potential) ∧
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun G : SourceMomentPotential K =>
                sourceMomentBermanFunctional G)))) ∧
      (∀ G : SourceMomentPotential K,
        sourceMomentBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      sSup
        (Set.range
          (fun G : SourceMomentPotential K =>
            sourceMomentBermanFunctional G)) ≤
        finiteEnergySourceBermanFunctional F := by
  obtain ⟨D, C, henergy, hmax⟩ :=
    exists_sourceMomentBerman_maximizingSequence_uniformEnergy K
  have holdenergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential (sourceMomentMinimumPoint (D j)) ≤ C := by
    intro j
    exact henergy j
  obtain ⟨f, φ, hfzero, hflip, hfconvex, hfbounds,
    hφ, hconv, hfinite⟩ :=
    exists_minimumNormalizedSourceFiniteEnergy_subsequence
      D C holdenergy
  let F : SourceFiniteEnergyPotential K :=
    { potential := f
      normalized := hfzero
      lipschitz := hflip
      convex := hfconvex
      nonnegative := fun x => (hfbounds x).1
      supportUpper := fun x => (hfbounds x).2
      legendreFinite :=
        lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top
      densityIntegrable :=
        integrable_limit_gibbs_of_uniformEnergy_all
          D φ f hconv C henergy }
  let S : ℝ :=
    sSup
      (Set.range
        (fun G : SourceMomentPotential K =>
          sourceMomentBermanFunctional G))
  have hmaxsub :
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop (𝓝 S) := by
    change
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun G : SourceMomentPotential K =>
                sourceMomentBermanFunctional G))))
    exact (hmax.comp hφ.tendsto_atTop).congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hpartition :
      Tendsto
        (fun j => minimumNormalizedSourcePartition (D (φ j)))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa only [finiteEnergySourcePartition] using
      tendsto_minimumNormalizedSourcePartition_of_uniformEnergy_all
        D φ f hconv C henergy
  have hlog := hpartition.log (finiteEnergySourcePartition_pos F).ne'
  have henergyconv :
      Tendsto
        (fun j => minimumNormalizedSourceBodyEnergy (D (φ j)))
        atTop
        (𝓝 (Real.log (finiteEnergySourcePartition F) - S)) := by
    have hdiff := hlog.sub hmaxsub
    have heq :
        (fun j =>
          Real.log (minimumNormalizedSourcePartition (D (φ j))) -
            sourceMomentBermanFunctional (D (φ j))) =
        (fun j => minimumNormalizedSourceBodyEnergy (D (φ j))) := by
      funext j
      have h := minimumNormalizedSourceBermanFunctional_eq (D (φ j))
      unfold minimumNormalizedSourceBermanFunctional at h
      linarith
    rw [heq] at hdiff
    exact hdiff
  have hlimnonneg :
      0 ≤ Real.log (finiteEnergySourcePartition F) - S :=
    ge_of_tendsto henergyconv
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceBodyEnergy_nonneg (D (φ j)))
  have hmassconv :
      Tendsto
        (fun j => ENNReal.ofReal
          (normalizedVolume K.carrier *
            minimumNormalizedSourceBodyEnergy (D (φ j))))
        atTop
        (𝓝
          (ENNReal.ofReal
            (normalizedVolume K.carrier *
              (Real.log (finiteEnergySourcePartition F) - S)))) := by
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (henergyconv.const_mul (normalizedVolume K.carrier))).congr'
        (Filter.Eventually.of_forall fun _ => rfl)
  have hfatou :=
    sourceExtendedBodyLegendre_lintegral_le_liminf D φ f hconv
  have hmassfun :
      (fun j =>
        ∫⁻ p in K.carrier,
          ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p)
          ∂(volume : Measure (Space n))) =
      (fun j => ENNReal.ofReal
        (normalizedVolume K.carrier *
          minimumNormalizedSourceBodyEnergy (D (φ j)))) := by
    funext j
    exact minimumNormalizedSourceBodyDual_lintegral_eq_volume_mul_energy
      (D (φ j))
  rw [hmassfun, hmassconv.liminf_eq] at hfatou
  have hreal :
      (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
        ∂(volume : Measure (Space n))).toReal ≤
        normalizedVolume K.carrier *
          (Real.log (finiteEnergySourcePartition F) - S) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
    simpa only [ENNReal.toReal_ofReal
      (mul_nonneg K.volume_pos.le hlimnonneg)] using h
  have hFenergy :
      finiteEnergySourceBodyEnergy F ≤
        Real.log (finiteEnergySourcePartition F) - S := by
    unfold finiteEnergySourceBodyEnergy
    change
      (normalizedVolume K.carrier)⁻¹ *
          (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
            ∂(volume : Measure (Space n))).toReal ≤
        Real.log (finiteEnergySourcePartition F) - S
    calc
      (normalizedVolume K.carrier)⁻¹ *
          (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
            ∂(volume : Measure (Space n))).toReal ≤
        (normalizedVolume K.carrier)⁻¹ *
          (normalizedVolume K.carrier *
            (Real.log (finiteEnergySourcePartition F) - S)) :=
          mul_le_mul_of_nonneg_left hreal
            (inv_nonneg.mpr K.volume_pos.le)
      _ = Real.log (finiteEnergySourcePartition F) - S := by
        have hvol := K.volume_pos.ne'
        field_simp
  have hS : S ≤ finiteEnergySourceBermanFunctional F := by
    unfold finiteEnergySourceBermanFunctional
    linarith
  refine ⟨F, D, φ, hφ, ?_, ?_, ?_, ?_⟩
  · simpa only using hconv
  · exact hmaxsub
  · intro G
    exact
      (le_csSup
        (sourceMomentBermanFunctional_bddAbove K)
        (show
          sourceMomentBermanFunctional G ∈
            Set.range
              (fun H : SourceMomentPotential K =>
                sourceMomentBermanFunctional H)
          from ⟨G, rfl⟩)).trans hS
  · exact hS

end MomentOptimizer

namespace WeightedBochner

open Set MeasureTheory Matrix Filter
open scoped BigOperators ENNReal InnerProductSpace

private theorem continuous_normalizedDensity {n : ℕ}
    {a : Space n → ℝ} (ha : Continuous a) :
    Continuous (WeightedPoincare.normalizedDensity a) := by
  unfold WeightedPoincare.normalizedDensity
  exact (Real.continuous_exp.comp ha.neg).div_const _

private theorem integral_normalizedMeasure {n : ℕ}
    {a : Space n → ℝ}
    (ha : Continuous a)
    (hpart : Integrable
      (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n)))
    (f : Space n → ℝ) :
    (∫ x : Space n, f x
      ∂(WeightedPoincare.normalizedMeasure a)) =
      (∫ x : Space n, Real.exp (-a x) * f x
        ∂(volume : Measure (Space n))) /
        WeightedPoincare.partition a := by
  have hmeas : Measurable
      (fun x : Space n => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity a x)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_normalizedDensity ha).measurable
  have hfinite :
      ∀ᵐ x ∂(volume : Measure (Space n)),
        ENNReal.ofReal
          (WeightedPoincare.normalizedDensity a x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold WeightedPoincare.normalizedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal
      (WeightedPoincare.normalizedDensity_pos hpart _).le]
  calc
    (∫ x : Space n,
      WeightedPoincare.normalizedDensity a x * f x
        ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          (Real.exp (-a x) * f x) /
            WeightedPoincare.partition a
          ∂(volume : Measure (Space n)) := by
            congr 1
            funext x
            unfold WeightedPoincare.normalizedDensity
            ring
    _ = _ := MeasureTheory.integral_div _ _

private theorem fderiv_coordinate_eval {n : ℕ}
    {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x v w : Space n) :
    (fderiv ℝ (fun y : Space n =>
      (fderiv ℝ f y) v) x) w =
      ((fderiv ℝ (fderiv ℝ f) x) w) v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) |>.differentiableAt
  have heq := fderiv_clm_apply hdf
    (differentiableAt_const (c := v))
  have happly := congrArg
    (fun L : Space n →L[ℝ] ℝ => L w) heq
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using happly

end WeightedBochner

namespace MomentWeakFirstVariation

open Set Function Filter MeasureTheory Metric
open MomentOptimizer
open scoped ENNReal Topology

private def finiteEnergySourceGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measure (Space n) :=
  WeightedPoincare.normalizedMeasure F.potential

private theorem finiteEnergySourceGibbsProbability_isProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IsProbabilityMeasure (finiteEnergySourceGibbsProbability F) :=
  WeightedPoincare.normalizedMeasure_isProbability
    F.densityIntegrable

private theorem integral_finiteEnergySourceGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : Space n → ℝ) :
    (∫ x : Space n, v x
      ∂(finiteEnergySourceGibbsProbability F)) =
      (∫ x : Space n,
        v x * Real.exp (-F.potential x)
        ∂(volume : Measure (Space n))) /
        finiteEnergySourcePartition F := by
  unfold finiteEnergySourceGibbsProbability
  rw [WeightedBochner.integral_normalizedMeasure
    F.potential.continuous F.densityIntegrable v]
  congr 1
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring

end MomentWeakFirstVariation

namespace MomentConvexRecovery

open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics ArbitraryBodySmoothConvexPotentialBridge MomentExistence
open MomentPotentialExistence MomentMinimizer MomentFunctionalCoercivity MomentMoserTrudinger
open MomentOptimizer
open scoped BigOperators Convolution ENNReal Topology ContDiff

private def sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (x : Space n) : ℝ :=
  max (F.potential x)
    (SupportFunction.supportFunction K.carrier x - R)

private theorem continuous_sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (R : ℝ) :
    Continuous (sourceSupportClipping F R) := by
  unfold sourceSupportClipping
  exact F.potential.continuous.sup
    ((continuous_supportFunction K.compact
      (K.fullDimensional.mono interior_subset)).sub continuous_const)

private theorem convexOn_sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (R : ℝ) :
    ConvexOn ℝ Set.univ (sourceSupportClipping F R) := by
  have hsupport := convexOn_supportFunction K.compact
    (K.fullDimensional.mono interior_subset)
  have hshift :
      ConvexOn ℝ Set.univ
        (fun x : Space n =>
          SupportFunction.supportFunction K.carrier x - R) := by
    refine ⟨hsupport.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hsupport.2 hx hy ha hb hab
    change SupportFunction.supportFunction K.carrier
        (a • x + b • y) ≤
      a * SupportFunction.supportFunction K.carrier x +
        b * SupportFunction.supportFunction K.carrier y at h
    change SupportFunction.supportFunction K.carrier
        (a • x + b • y) - R ≤
      a * (SupportFunction.supportFunction K.carrier x - R) +
        b * (SupportFunction.supportFunction K.carrier y - R)
    calc
      SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R ≤
          (a * SupportFunction.supportFunction K.carrier x +
            b * SupportFunction.supportFunction K.carrier y) - R :=
        sub_le_sub_right h R
      _ = (a * SupportFunction.supportFunction K.carrier x +
            b * SupportFunction.supportFunction K.carrier y) -
            (a + b) * R := by simp only [hab, one_mul]
      _ = a * (SupportFunction.supportFunction K.carrier x - R) +
            b * (SupportFunction.supportFunction K.carrier y - R) := by
        ring
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change
    max (F.potential (a • x + b • y))
        (SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R) ≤
      a * max (F.potential x)
        (SupportFunction.supportFunction K.carrier x - R) +
      b * max (F.potential y)
        (SupportFunction.supportFunction K.carrier y - R)
  apply max_le
  · calc
      F.potential (a • x + b • y) ≤
          a * F.potential x + b * F.potential y :=
        F.convex.2 hx hy ha hb hab
      _ ≤ a * max (F.potential x)
            (SupportFunction.supportFunction K.carrier x - R) +
          b * max (F.potential y)
            (SupportFunction.supportFunction K.carrier y - R) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · calc
      SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R ≤
          a * (SupportFunction.supportFunction K.carrier x - R) +
            b * (SupportFunction.supportFunction K.carrier y - R) :=
        hshift.2 hx hy ha hb hab
      _ ≤ a * max (F.potential x)
            (SupportFunction.supportFunction K.carrier x - R) +
          b * max (F.potential y)
            (SupportFunction.supportFunction K.carrier y - R) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)

private theorem sourceSupportClipping_ge {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (x : Space n) :
    F.potential x ≤ sourceSupportClipping F R x :=
  le_max_left _ _

private theorem sourceSupportClipping_le_support {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (x : Space n) :
    sourceSupportClipping F R x ≤
      SupportFunction.supportFunction K.carrier x := by
  unfold sourceSupportClipping
  exact max_le (F.supportUpper x) (sub_le_self _ hR)

private theorem sourceSupportClipping_supportBound {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (x : Space n) :
    |sourceSupportClipping F R x -
      SupportFunction.supportFunction K.carrier x| ≤ R := by
  have hu := sourceSupportClipping_le_support F hR x
  have hl :
      SupportFunction.supportFunction K.carrier x - R ≤
        sourceSupportClipping F R x :=
    le_max_right _ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem sourceSupportClipping_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (sourceSupportClipping F R) := by
  exact GlobalBergmanKernelBound.convex_supportCompatible_lipschitz
    K (convexOn_sourceSupportClipping F R)
    (sourceSupportClipping_supportBound F hR)

private def mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    Space n → ℝ :=
  ρ.normed (volume : Measure (Space n)) ⋆
    sourceSupportClipping F R

private theorem contDiff_mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ ∞ (mollifiedSourceSupportClipping F R ρ) := by
  unfold mollifiedSourceSupportClipping
  exact ρ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ρ.contDiff_normed
    (continuous_sourceSupportClipping F R).locallyIntegrable

private theorem convexOn_mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ Set.univ
      (mollifiedSourceSupportClipping F R ρ) := by
  change ConvexOn ℝ Set.univ
    (fun x : Space n =>
      ∫ y : Space n,
        ρ.normed (volume : Measure (Space n)) y *
          sourceSupportClipping F R (x - y)
        ∂(volume : Measure (Space n)))
  apply MeasureTheory.integral_convexOn_of_integrand_ae convex_univ
  · filter_upwards with y
    have htranslate :
        ConvexOn ℝ Set.univ
          (fun x : Space n =>
            sourceSupportClipping F R (x - y)) := by
      simpa only [sub_eq_add_neg, add_comm, preimage_univ, comp_def] using
        (convexOn_sourceSupportClipping F R).translate_right (-y)
    simpa only [smul_eq_mul] using
      htranslate.smul
        (ρ.nonneg_normed (μ := (volume : Measure (Space n))) y)
  · intro x _hx
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (ρ.hasCompactSupport_normed.convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.continuous_normed
        (continuous_sourceSupportClipping F R).locallyIntegrable
        x).integrable

private theorem dist_mollifiedSourceSupportClipping_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    dist (mollifiedSourceSupportClipping F R ρ x)
      (sourceSupportClipping F R x) ≤
      ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
        ρ.rOut := by
  unfold mollifiedSourceSupportClipping
  apply ρ.dist_normed_convolution_le
    (continuous_sourceSupportClipping F R).aestronglyMeasurable
  intro y hy
  have h := (sourceSupportClipping_lipschitz F hR).dist_le_mul y x
  have hcoe :
      (sourceBodyLipschitzConstant K : ℝ) =
        (n : ℝ) * LaurentJetSeparatedness.bodyRadius K := by
    unfold sourceBodyLipschitzConstant
    rw [Real.coe_toNNReal]
    exact mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  rw [hcoe] at h
  exact h.trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le
      (mul_nonneg (Nat.cast_nonneg n)
        (LaurentJetSeparatedness.bodyRadius_pos K).le))

private theorem mollifiedSourceSupportClipping_supportBound {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    |mollifiedSourceSupportClipping F R ρ x -
      SupportFunction.supportFunction K.carrier x| ≤
      R +
        ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          ρ.rOut := by
  have hdist := dist_mollifiedSourceSupportClipping_le F hR ρ x
  rw [Real.dist_eq] at hdist
  have hclip := sourceSupportClipping_supportBound F hR x
  calc
    |mollifiedSourceSupportClipping F R ρ x -
      SupportFunction.supportFunction K.carrier x| ≤
        |mollifiedSourceSupportClipping F R ρ x -
            sourceSupportClipping F R x| +
          |sourceSupportClipping F R x -
            SupportFunction.supportFunction K.carrier x| := by
            simpa only [sub_add_sub_cancel] using abs_add_le
              (mollifiedSourceSupportClipping F R ρ x -
                sourceSupportClipping F R x)
              (sourceSupportClipping F R x -
                SupportFunction.supportFunction K.carrier x)
    _ ≤ ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          ρ.rOut + R := add_le_add hdist hclip
    _ = R +
          ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
            ρ.rOut := add_comm _ _

private def sourceClippedMollificationMoment {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n)) :
    SourceMomentPotential K where
  potential := mollifiedSourceSupportClipping F R ρ
  smooth := (contDiff_mollifiedSourceSupportClipping F R ρ).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  convex := convexOn_mollifiedSourceSupportClipping F R ρ
  supportError := R +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
      ρ.rOut
  supportBound := mollifiedSourceSupportClipping_supportBound F hR ρ

private theorem sourceSupportClippingDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp (-sourceSupportClipping F R x))
      (volume : Measure (Space n)) := by
  refine F.densityIntegrable.mono'
    (Real.continuous_exp.comp
      (continuous_sourceSupportClipping F R).neg).aestronglyMeasurable
    ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (sourceSupportClipping_ge F R x))

private theorem eventually_sourceSupportClipping_nat_eq {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    ∀ᶠ j : ℕ in atTop,
      sourceSupportClipping F (j : ℝ) x = F.potential x := by
  have hlarge :
      ∀ᶠ j : ℕ in atTop,
        SupportFunction.supportFunction K.carrier x -
            F.potential x ≤ (j : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Filter.eventually_ge_atTop
        (SupportFunction.supportFunction K.carrier x -
          F.potential x))
  filter_upwards [hlarge] with j hj
  unfold sourceSupportClipping
  exact max_eq_left (by linarith)

private theorem tendsto_sourceSupportClippingPartition {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Tendsto
      (fun j : ℕ =>
        ∫ x : Space n,
          Real.exp (-sourceSupportClipping F (j : ℝ) x)
          ∂(volume : Measure (Space n)))
      atTop (𝓝 (finiteEnergySourcePartition F)) := by
  unfold finiteEnergySourcePartition
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Space n => Real.exp (-F.potential x))
  · intro j
    exact (Real.continuous_exp.comp
      (continuous_sourceSupportClipping
        F (j : ℝ)).neg).aestronglyMeasurable
  · exact F.densityIntegrable
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (neg_le_neg (sourceSupportClipping_ge F (j : ℝ) x))
  · filter_upwards with x
    have heq := eventually_sourceSupportClipping_nat_eq F x
    exact tendsto_const_nhds.congr'
      (heq.mono fun j hj => by
        change
          Real.exp (-F.potential x) =
            Real.exp (-sourceSupportClipping F (j : ℝ) x)
        rw [hj])

private theorem finiteEnergySourceExtendedLegendre_integrableOn {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IntegrableOn
      (fun p : Space n =>
        (sourceExtendedBodyLegendre F.potential p).toReal)
      K.carrier (volume : Measure (Space n)) := by
  apply MeasureTheory.integrable_toReal_of_lintegral_ne_top
  · exact (measurable_sourceExtendedBodyLegendre
      F.potential).aemeasurable
  · exact F.legendreFinite.ne

private theorem finiteEnergySourceBodyEnergy_eq_setIntegral {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceBodyEnergy F =
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal
          ∂(volume : Measure (Space n))) := by
  unfold finiteEnergySourceBodyEnergy
  congr 1
  symm
  apply MeasureTheory.integral_toReal
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
  exact MeasureTheory.ae_lt_top'
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
    F.legendreFinite.ne

private theorem recoveryLegendre_le_extended {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (ε : ℝ)
    (hlower : ∀ x : Space n,
      F.potential x - ε ≤ D.potential x)
    (p : Space n)
    (hpfinite : sourceExtendedBodyLegendre F.potential p ≠ ⊤) :
    legendreTransform D.potential p ≤
      (sourceExtendedBodyLegendre F.potential p).toReal + ε := by
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hphaseENN :=
    ofReal_phase_le_sourceExtendedBodyLegendre F.potential p x
  rw [← ENNReal.ofReal_toReal hpfinite] at hphaseENN
  have hphase :=
    (ENNReal.ofReal_le_ofReal_iff
      ENNReal.toReal_nonneg).mp hphaseENN
  change
    SupportFunction.pairing p x - F.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal at hphase
  change
    SupportFunction.pairing p x - D.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal + ε
  linarith [hlower x]

private theorem sourceMomentBodyEnergy_le_finiteEnergy_add {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (ε : ℝ)
    (hlower : ∀ x : Space n,
      F.potential x - ε ≤ D.potential x) :
    sourceMomentBodyEnergy D ≤
      finiteEnergySourceBodyEnergy F + ε := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hconst : IntegrableOn
      (fun _ : Space n => ε)
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  have hfinite :
      ∀ᵐ p : Space n
          ∂((volume : Measure (Space n)).restrict K.carrier),
        sourceExtendedBodyLegendre F.potential p < ⊤ :=
    MeasureTheory.ae_lt_top'
      (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
      F.legendreFinite.ne
  have hmono :
      (∫ p in K.carrier, legendreTransform D.potential p
        ∂(volume : Measure (Space n))) ≤
      ∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal + ε
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.integral_mono_ae
      (sourceMomentLegendre_integrableOn D)
      (hdual.add hconst)
    filter_upwards [hfinite] with p hp
    exact recoveryLegendre_le_extended F D ε hlower p hp.ne
  unfold sourceMomentBodyEnergy
  calc
    (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier, legendreTransform D.potential p
          ∂(volume : Measure (Space n))) ≤
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal + ε
          ∂(volume : Measure (Space n))) :=
        mul_le_mul_of_nonneg_left hmono
          (inv_nonneg.mpr K.volume_pos.le)
    _ = finiteEnergySourceBodyEnergy F + ε := by
      rw [MeasureTheory.integral_add hdual hconst,
        MeasureTheory.setIntegral_const,
        finiteEnergySourceBodyEnergy_eq_setIntegral]
      simp only [normalizedVolume, measureReal_def, smul_eq_mul]
      have hvol :
          ((volume : Measure (Space n)) K.carrier).toReal ≠ 0 := by
        simpa only [ne_eq, normalizedVolume] using K.volume_pos.ne'
      field_simp [hvol]

private theorem exists_smooth_sourceSupportClipping_recovery {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : SourceMomentPotential K,
      (∀ x : Space n,
        |D.potential x - sourceSupportClipping F R x| < ε) ∧
      sourceMomentBodyEnergy D ≤
        finiteEnergySourceBodyEnergy F + ε := by
  let L : ℝ :=
    (n : ℝ) * LaurentJetSeparatedness.bodyRadius K
  have hL : 0 ≤ L :=
    mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let ρ : ContDiffBump (0 : Space n) :=
    ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let D := sourceClippedMollificationMoment F R hR ρ
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < L + 1)).mpr
    nlinarith
  have hclose : ∀ x : Space n,
      |D.potential x - sourceSupportClipping F R x| < ε := by
    intro x
    have hdist := dist_mollifiedSourceSupportClipping_le F hR ρ x
    rw [Real.dist_eq] at hdist
    exact hdist.trans_lt (by simpa only [ρ, L] using hsmall)
  refine ⟨D, hclose, ?_⟩
  apply sourceMomentBodyEnergy_le_finiteEnergy_add F D ε
  intro x
  have hclip := sourceSupportClipping_ge F R x
  have hnear := (abs_lt.mp (hclose x)).1
  linarith

private theorem sourceClippingRecovery_partition_bounds {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (R ε : ℝ)
    (hclose : ∀ x : Space n,
      |D.potential x - sourceSupportClipping F R x| ≤ ε) :
    Real.exp (-ε) *
        (∫ x : Space n,
          Real.exp (-sourceSupportClipping F R x)
          ∂(volume : Measure (Space n))) ≤
      sourceMomentPartition D ∧
    sourceMomentPartition D ≤
      Real.exp ε *
        (∫ x : Space n,
          Real.exp (-sourceSupportClipping F R x)
          ∂(volume : Measure (Space n))) := by
  have hclip := sourceSupportClippingDensity_integrable F R
  have hsource := sourceMomentDensity_integrable D
  constructor
  · calc
      Real.exp (-ε) *
          (∫ x : Space n,
            Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n))) =
          ∫ x : Space n,
            Real.exp (-ε) *
              Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n)) :=
            (MeasureTheory.integral_const_mul _ _).symm
      _ ≤ (∫ x : Space n,
            Real.exp (-D.potential x)
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.integral_mono
              (hclip.const_mul (Real.exp (-ε))) hsource
            intro x
            change
              Real.exp (-ε) *
                  Real.exp (-sourceSupportClipping F R x) ≤
                Real.exp (-D.potential x)
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h := (abs_le.mp (hclose x)).2
            linarith
      _ = sourceMomentPartition D := rfl
  · calc
      sourceMomentPartition D =
          (∫ x : Space n,
            Real.exp (-D.potential x)
            ∂(volume : Measure (Space n))) := rfl
      _ ≤ ∫ x : Space n,
            Real.exp ε *
              Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.integral_mono hsource
              (hclip.const_mul (Real.exp ε))
            intro x
            change
              Real.exp (-D.potential x) ≤
                Real.exp ε *
                  Real.exp (-sourceSupportClipping F R x)
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h := (abs_le.mp (hclose x)).1
            linarith
      _ = Real.exp ε *
          (∫ x : Space n,
            Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n))) :=
          MeasureTheory.integral_const_mul _ _

private theorem exists_smooth_finiteEnergySource_recovery_sequence {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∃ D : ℕ → SourceMomentPotential K,
      (∀ (j : ℕ) (x : Space n),
        |(D j).potential x - sourceSupportClipping F (j : ℝ) x| <
          1 / ((j : ℝ) + 1)) ∧
      (∀ j : ℕ,
        sourceMomentBodyEnergy (D j) ≤
          finiteEnergySourceBodyEnergy F + 1 / ((j : ℝ) + 1)) ∧
      Tendsto
        (fun j => sourceMomentPartition (D j))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : ∀ j : ℕ, 0 < ε j := by
    intro j
    dsimp [ε]
    positivity
  have hchoose :
      ∀ j : ℕ, ∃ D : SourceMomentPotential K,
        (∀ x : Space n,
          |D.potential x - sourceSupportClipping F (j : ℝ) x| <
            ε j) ∧
        sourceMomentBodyEnergy D ≤
          finiteEnergySourceBodyEnergy F + ε j := by
    intro j
    exact exists_smooth_sourceSupportClipping_recovery
      F (Nat.cast_nonneg j) (hε j)
  choose D hclose henergy using hchoose
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hclip := tendsto_sourceSupportClippingPartition F
  have hnegexp :
      Tendsto (fun j => Real.exp (-ε j)) atTop (𝓝 1) := by
    have hnegzero :
        Tendsto (fun j => -ε j) atTop (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using hεzero.neg
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp hnegzero
    rw [Real.exp_zero] at h
    exact h.congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hposexp :
      Tendsto (fun j => Real.exp (ε j)) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp hεzero
    rw [Real.exp_zero] at h
    exact h.congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hlower :
      Tendsto
        (fun j =>
          Real.exp (-ε j) *
            (∫ x : Space n,
              Real.exp (-sourceSupportClipping F (j : ℝ) x)
              ∂(volume : Measure (Space n))))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa only [one_mul] using hnegexp.mul hclip
  have hupper :
      Tendsto
        (fun j =>
          Real.exp (ε j) *
            (∫ x : Space n,
              Real.exp (-sourceSupportClipping F (j : ℝ) x)
              ∂(volume : Measure (Space n))))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa only [one_mul] using hposexp.mul hclip
  have hpart :
      Tendsto
        (fun j => sourceMomentPartition (D j))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower hupper
    · intro j
      exact
        (sourceClippingRecovery_partition_bounds F (D j)
          (j : ℝ) (ε j) (fun x => (hclose j x).le)).1
    · intro j
      exact
        (sourceClippingRecovery_partition_bounds F (D j)
          (j : ℝ) (ε j) (fun x => (hclose j x).le)).2
  refine ⟨D, ?_, ?_, hpart⟩
  · intro j x
    exact hclose j x
  · intro j
    exact henergy j

private theorem finiteEnergySourceBermanFunctional_le_sSup {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceBermanFunctional F ≤
      sSup
        (Set.range
          (fun D : SourceMomentPotential K =>
            sourceMomentBermanFunctional D)) := by
  obtain ⟨D, _hclose, henergy, hpartition⟩ :=
    exists_smooth_finiteEnergySource_recovery_sequence F
  let S : ℝ :=
    sSup
      (Set.range
        (fun G : SourceMomentPotential K =>
          sourceMomentBermanFunctional G))
  have hεzero :
      Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlog :=
    hpartition.log (finiteEnergySourcePartition_pos F).ne'
  have hlower :
      Tendsto
        (fun j =>
          Real.log (sourceMomentPartition (D j)) -
            (finiteEnergySourceBodyEnergy F +
              1 / ((j : ℝ) + 1)))
        atTop (𝓝 (finiteEnergySourceBermanFunctional F)) := by
    simpa only [one_div, finiteEnergySourceBermanFunctional, add_zero] using
      hlog.sub (tendsto_const_nhds.add hεzero)
  change finiteEnergySourceBermanFunctional F ≤ S
  apply le_of_tendsto hlower
  filter_upwards with j
  have hsup : sourceMomentBermanFunctional (D j) ≤ S :=
    le_csSup
      (sourceMomentBermanFunctional_bddAbove K)
      (show
        sourceMomentBermanFunctional (D j) ∈
          Set.range
            (fun G : SourceMomentPotential K =>
              sourceMomentBermanFunctional G)
        from ⟨D j, rfl⟩)
  unfold sourceMomentBermanFunctional at hsup
  linarith [henergy j]

private theorem exists_finiteEnergySourceBerman_exact_optimizer {n : ℕ}
    (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      ∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F := by
  obtain ⟨F, _D, _φ, _hmono, _hconv, _hmax, _hdom, hupper⟩ :=
    exists_finiteEnergySourceBerman_optimizer K
  have heq := le_antisymm
    (finiteEnergySourceBermanFunctional_le_sSup F) hupper
  refine ⟨F, heq, ?_⟩
  intro G
  rw [heq]
  exact finiteEnergySourceBermanFunctional_le_sSup G

end MomentConvexRecovery

namespace MomentFirstVariation

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentWeakFirstVariation
open scoped BigOperators ENNReal NNReal Topology

private theorem finiteEnergySourcePhase_actualGradient_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (z : Space n) :
    phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential z ≤
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential x := by
  let line : ℝ →ᵃ[ℝ] Space n := AffineMap.lineMap x z
  have hconv : ConvexOn ℝ Set.univ
      (fun t : ℝ => F.potential (line t)) := by
    simpa only [preimage_univ, comp_def] using F.convex.comp_affineMap line
  have hline : HasDerivAt
      (fun t : ℝ => line t) (z - x) 0 := by
    simpa [line, AffineMap.lineMap_apply, Function.comp_def] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (z - x)).add_const x
  have hlinezero : line (0 : ℝ) = x := by
    simp only [AffineMap.lineMap_apply_zero, line]
  have hderiv : HasDerivAt
      (fun t : ℝ => F.potential (line t))
      ((fderiv ℝ F.potential x) (z - x)) 0 := by
    simpa only [map_sub, comp_def] using
      hx.hasFDerivAt.comp_hasDerivAt_of_eq
        (0 : ℝ) hline hlinezero.symm
  have hslope := hconv.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hderiv
  have htangent :
      (fderiv ℝ F.potential x) (z - x) ≤
        F.potential z - F.potential x := by
    simpa [slope_def_field, line] using hslope
  rw [← SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    at htangent
  unfold phase
  have hpair :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) (z - x) =
        SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) z -
        SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) x := by
    simp only [SupportFunction.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hpair] at htangent
  linarith

private theorem finiteEnergySourceGradient_pairing_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (v : Space n) :
    SupportFunction.pairing
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x) v ≤
      SupportFunction.supportFunction K.carrier v := by
  by_contra hnot
  have hgap : 0 <
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) v -
        SupportFunction.supportFunction K.carrier v := by
    linarith [lt_of_not_ge hnot]
  let gap : ℝ :=
    SupportFunction.pairing
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x) v -
      SupportFunction.supportFunction K.carrier v
  let C : ℝ :=
    SupportFunction.supportFunction K.carrier x -
      F.potential x
  have hgap' : 0 < gap := hgap
  have hC : 0 ≤ C := sub_nonneg.mpr (F.supportUpper x)
  let t : ℝ := 1 + (C + 1) / gap
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hphase :=
    finiteEnergySourcePhase_actualGradient_le F x hx (x + t • v)
  have hpair :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) (x + t • v) =
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) x +
        t * SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) v := by
    rw [MonomialDivergence.pairing_add_right,
      MonomialDivergence.pairing_smul_right]
  unfold phase at hphase
  rw [hpair] at hphase
  have hsupp := GlobalBergmanKernelBound.supportFunction_add_smul_le
    K x v ht
  have hupper := F.supportUpper (x + t • v)
  have hbound : t * gap ≤ C := by
    dsimp [gap, C]
    linarith
  have heq : t * gap = gap + (C + 1) := by
    dsimp [t]
    field_simp
  linarith

private theorem finiteEnergySourceGradient_mem_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x ∈ K.carrier := by
  classical
  by_contra hnot
  obtain ⟨f, c, hbody, hpoint⟩ :=
    geometric_hahn_banach_closed_point
      K.convex K.compact.isClosed hnot
  let v : Space n := MonomialDivergence.dualVector f
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  have hsupport :
      SupportFunction.supportFunction K.carrier v ≤ c := by
    apply SupportFunction.supportFunction_le hnonempty v
    intro y hy
    have hf := hbody y hy
    rw [MonomialDivergence.dual_apply_eq_pairing] at hf
    exact hf.le
  have hgradient :=
    finiteEnergySourceGradient_pairing_le_support F x hx v
  rw [MonomialDivergence.dual_apply_eq_pairing] at hpoint
  exact (not_lt_of_ge (hgradient.trans hsupport)) hpoint

private theorem ae_differentiableAt_finiteEnergySource
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      DifferentiableAt ℝ
        (F.potential : Space n → ℝ) x := by
  exact F.lipschitz.ae_differentiableAt

private theorem measurable_finiteEnergySourceGradient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measurable
      (SpatialBergmanFatouScheffe.actualGradient
        (F.potential : Space n → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_fderiv_apply_const ℝ
    (F.potential : Space n → ℝ)
    (Pi.single i (1 : ℝ))

private theorem finiteEnergySourceGibbs_ae_of_volume
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (P : Space n → Prop)
    (hP : ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)), P x) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F), P x := by
  change ∀ᵐ x : Space n
    ∂((volume : Measure (Space n)).withDensity
      (fun y => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity F.potential y))), P x
  exact (MeasureTheory.withDensity_absolutelyContinuous
    (volume : Measure (Space n))
    (fun y => ENNReal.ofReal
      (WeightedPoincare.normalizedDensity F.potential y))).ae_le hP

private def finiteEnergySourceGradientPushforward
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measure (Space n) :=
  Measure.map
    (SpatialBergmanFatouScheffe.actualGradient
      (F.potential : Space n → ℝ))
    (finiteEnergySourceGibbsProbability F)

private theorem finiteEnergySourceGradientPushforward_univ
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceGradientPushforward F Set.univ = 1 := by
  let : IsProbabilityMeasure
      (finiteEnergySourceGibbsProbability F) :=
    finiteEnergySourceGibbsProbability_isProbability F
  unfold finiteEnergySourceGradientPushforward
  rw [Measure.map_apply (measurable_finiteEnergySourceGradient F)
    MeasurableSet.univ]
  simp only [preimage_univ, measure_univ]

private theorem finiteEnergySourceGradientPushforward_isProbability
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IsProbabilityMeasure
      (finiteEnergySourceGradientPushforward F) :=
  ⟨finiteEnergySourceGradientPushforward_univ F⟩

private theorem finiteEnergySourceExtendedLegendre_actualGradient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    sourceExtendedBodyLegendre F.potential
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) =
      ENNReal.ofReal
        (phase
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
          F.potential x) := by
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hmax : ∀ z : Space n,
      phase p F.potential z ≤ phase p F.potential x :=
    fun z => finiteEnergySourcePhase_actualGradient_le F x hx z
  have hbdd : BddAbove (Set.range (phase p F.potential)) := by
    refine ⟨phase p F.potential x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hmax z
  rw [sourceExtendedBodyLegendre_eq_of_bddAbove
    F.potential p hbdd]
  congr 1
  unfold legendreTransform
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact hmax z
  · exact le_csSup hbdd ⟨x, rfl⟩

private theorem finiteEnergySourcePhase_actualGradient_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    0 ≤ phase
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)
      F.potential x := by
  have h := finiteEnergySourcePhase_actualGradient_le
    F x hx (0 : Space n)
  simpa only [phase, SupportFunction.pairing, sub_nonneg, ge_iff_le, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, F.normalized, sub_self] using h

private theorem finiteEnergySourceExtendedLegendre_actualGradient_toReal
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    (sourceExtendedBodyLegendre F.potential
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)).toReal =
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential x := by
  rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx,
    ENNReal.toReal_ofReal
      (finiteEnergySourcePhase_actualGradient_nonneg F x hx)]

end MomentFirstVariation

namespace MomentTargetGeodesic

open Set Function Filter MeasureTheory TopologicalSpace
open LaplaceAsymptotics MomentFunctionalCoercivity MomentMinimizer MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation
open scoped BigOperators ENNReal NNReal Topology

private def normalizedTargetBodyMeasure {n : ℕ}
    (K : CenteredBody n) : Measure (Space n) :=
  ((volume : Measure (Space n)) K.carrier)⁻¹ •
    ((volume : Measure (Space n)).restrict K.carrier)

private theorem centeredBody_volume_ne_zero_top {n : ℕ}
    (K : CenteredBody n) :
    (volume : Measure (Space n)) K.carrier ≠ 0 ∧
      (volume : Measure (Space n)) K.carrier ≠ ⊤ := by
  refine ⟨?_, K.compact.measure_ne_top⟩
  intro hzero
  have hpos := K.volume_pos
  simp only [normalizedVolume, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hpos

private theorem normalizedTargetBodyMeasure_univ {n : ℕ}
    (K : CenteredBody n) :
    normalizedTargetBodyMeasure K Set.univ = 1 := by
  unfold normalizedTargetBodyMeasure
  rw [Measure.smul_apply, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel
    (centeredBody_volume_ne_zero_top K).1
    (centeredBody_volume_ne_zero_top K).2

private theorem normalizedTargetBodyMeasure_isProbability {n : ℕ}
    (K : CenteredBody n) :
    IsProbabilityMeasure (normalizedTargetBodyMeasure K) :=
  ⟨normalizedTargetBodyMeasure_univ K⟩

private theorem integral_normalizedTargetBodyMeasure {n : ℕ}
    (K : CenteredBody n)
    (v : Space n → ℝ) :
    (∫ p : Space n, v p
      ∂(normalizedTargetBodyMeasure K)) =
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier, v p
          ∂(volume : Measure (Space n))) := by
  unfold normalizedTargetBodyMeasure
  rw [MeasureTheory.integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, normalizedVolume]

private theorem integral_finiteEnergySourceGradientPushforward {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    (∫ p : Space n, v p
      ∂(finiteEnergySourceGradientPushforward F)) =
      (∫ x : Space n,
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        ∂(finiteEnergySourceGibbsProbability F)) := by
  unfold finiteEnergySourceGradientPushforward
  exact MeasureTheory.integral_map
    (measurable_finiteEnergySourceGradient F).aemeasurable
    v.continuous.aestronglyMeasurable

private theorem finiteEnergySourceExtendedLegendre_zero {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    sourceExtendedBodyLegendre F.potential
      (0 : Space n) = 0 := by
  apply le_antisymm
  · unfold sourceExtendedBodyLegendre
    apply iSup_le
    intro j
    have hphase :
        phase (0 : Space n) F.potential
          (TopologicalSpace.denseSeq (Space n) j) ≤ 0 := by
      simpa only [phase, SupportFunction.pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_sub, Left.neg_nonpos_iff] using
        neg_nonpos.mpr
          (F.nonnegative
            (TopologicalSpace.denseSeq (Space n) j))
    rw [ENNReal.ofReal_eq_zero.mpr hphase]
  · exact bot_le

private def finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Set (Space n) :=
  {p | p ∈ K.carrier ∧
    sourceExtendedBodyLegendre F.potential p ≠ ⊤}

private theorem zero_mem_finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (0 : Space n) ∈ finiteEnergyFiniteTargetSet F := by
  refine ⟨interior_subset
    (LatticeAsymptotics.zero_mem_interior K), ?_⟩
  rw [finiteEnergySourceExtendedLegendre_zero F]
  exact ENNReal.zero_ne_top

private theorem finiteEnergyFiniteTargetSet_nonempty {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (finiteEnergyFiniteTargetSet F).Nonempty :=
  ⟨0, zero_mem_finiteEnergyFiniteTargetSet F⟩

private theorem ae_mem_finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∀ᵐ p : Space n
      ∂((volume : Measure (Space n)).restrict K.carrier),
      p ∈ finiteEnergyFiniteTargetSet F := by
  have hfinite := MeasureTheory.ae_lt_top'
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
    F.legendreFinite.ne
  filter_upwards
    [MeasureTheory.ae_restrict_mem K.compact.measurableSet, hfinite]
    with p hp htop
  exact ⟨hp, ne_of_lt htop⟩

private theorem finiteEnergyFiniteTarget_fenchel {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal ≤
      F.potential x := by
  have hphase :=
    ofReal_phase_le_sourceExtendedBodyLegendre F.potential p x
  rw [← ENNReal.ofReal_toReal hp.2] at hphase
  have hreal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hphase
  change
    SupportFunction.pairing p x - F.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal at hreal
  linarith

private def finiteEnergyTargetTestBound {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ)) : ℝ :=
  max 0 (sSup ((fun p : Space n => |v p|) '' K.carrier))

private theorem finiteEnergyTargetTestBound_nonneg {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ)) :
    0 ≤ finiteEnergyTargetTestBound K v :=
  le_max_left _ _

private theorem abs_targetTest_le_finiteEnergyTargetTestBound {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ))
    {p : Space n} (hp : p ∈ K.carrier) :
    |v p| ≤ finiteEnergyTargetTestBound K v := by
  have hbdd : BddAbove
      ((fun q : Space n => |v q|) '' K.carrier) :=
    K.compact.bddAbove_image v.continuous.abs.continuousOn
  exact (le_csSup hbdd ⟨p, hp, rfl⟩).trans
    (le_max_right 0 _)

private def finiteEnergyTargetDualPhase {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (p x : Space n) : ℝ :=
  SupportFunction.pairing p x -
    (sourceExtendedBodyLegendre F.potential p).toReal - t * v p

private theorem finiteEnergyTargetDualPhase_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    finiteEnergyTargetDualPhase F v t p x ≤
      SupportFunction.supportFunction K.carrier x +
        |t| * finiteEnergyTargetTestBound K v := by
  have hpair := SupportFunction.pairing_le_supportFunction
    K.compact hp.1 x
  have htest := abs_targetTest_le_finiteEnergyTargetTestBound
    K v hp.1
  have ht : -t * v p ≤ |t| * finiteEnergyTargetTestBound K v := by
    calc
      -t * v p = -(t * v p) := by ring
      _ ≤ |t * v p| := neg_le_abs _
      _ = |t| * |v p| := abs_mul _ _
      _ ≤ |t| * finiteEnergyTargetTestBound K v :=
        mul_le_mul_of_nonneg_left htest (abs_nonneg t)
  have hdual := ENNReal.toReal_nonneg
    (a := sourceExtendedBodyLegendre F.potential p)
  unfold finiteEnergyTargetDualPhase
  linarith

private def finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) : ℝ :=
  sSup
    ((fun p : Space n =>
      finiteEnergyTargetDualPhase F v t p x) ''
        finiteEnergyFiniteTargetSet F)

private theorem finiteEnergyTargetDualPhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    BddAbove
      ((fun p : Space n =>
        finiteEnergyTargetDualPhase F v t p x) ''
          finiteEnergyFiniteTargetSet F) := by
  refine ⟨SupportFunction.supportFunction K.carrier x +
    |t| * finiteEnergyTargetTestBound K v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact finiteEnergyTargetDualPhase_le F v t hp x

private theorem finiteEnergyTargetDualPhase_le_geodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    finiteEnergyTargetDualPhase F v t p x ≤
      finiteEnergyTargetGeodesic F v t x := by
  exact le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t x)
    ⟨p, hp, rfl⟩

private theorem finiteEnergyTargetGeodesic_zero_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n) :
    finiteEnergyTargetGeodesic F v 0 x ≤ F.potential x := by
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  simpa only [finiteEnergyTargetDualPhase, zero_mul, sub_zero, tsub_le_iff_right] using
    finiteEnergyFiniteTarget_fenchel F hp x

private theorem finiteEnergyTargetGeodesic_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (finiteEnergyTargetGeodesic F v t) := by
  unfold sourceBodyLipschitzConstant
  apply LipschitzWith.of_le_add_mul'
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)
  intro x y
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  have hy := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t y)
    (show finiteEnergyTargetDualPhase F v t p y ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q y) ''
          finiteEnergyFiniteTargetSet F
      from ⟨p, hp, rfl⟩)
  have hpair :
      SupportFunction.pairing p x -
          SupportFunction.pairing p y ≤
        ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) *
            dist x y := by
    have hpbound :=
      LaurentJetSeparatedness.norm_le_bodyRadius
        K p hp.1
    have h :=
      MonomialDivergence.abs_pairing_le_dimension_mul_norm
        p (x - y)
    rw [dist_eq_norm]
    calc
      SupportFunction.pairing p x -
          SupportFunction.pairing p y =
        SupportFunction.pairing p (x - y) := by
          simp only [SupportFunction.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      _ ≤ |SupportFunction.pairing p (x - y)| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖p‖) * ‖x - y‖ := h
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) *
            ‖x - y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpbound
            (Nat.cast_nonneg n)) (norm_nonneg _)
  unfold finiteEnergyTargetDualPhase at hy ⊢
  linarith

private theorem continuous_finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Continuous (finiteEnergyTargetGeodesic F v t) :=
  (finiteEnergyTargetGeodesic_lipschitz F v t).continuous

private theorem convexOn_finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ConvexOn ℝ Set.univ (finiteEnergyTargetGeodesic F v t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  have hpx := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t x)
    (show finiteEnergyTargetDualPhase F v t p x ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q x) ''
          finiteEnergyFiniteTargetSet F from ⟨p, hp, rfl⟩)
  have hpy := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t y)
    (show finiteEnergyTargetDualPhase F v t p y ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q y) ''
          finiteEnergyFiniteTargetSet F from ⟨p, hp, rfl⟩)
  have hphase :
      finiteEnergyTargetDualPhase F v t p (a • x + b • y) =
        a * finiteEnergyTargetDualPhase F v t p x +
          b * finiteEnergyTargetDualPhase F v t p y := by
    unfold finiteEnergyTargetDualPhase
    rw [MonomialDivergence.pairing_add_right,
      MonomialDivergence.pairing_smul_right,
      MonomialDivergence.pairing_smul_right]
    linear_combination
      ((sourceExtendedBodyLegendre F.potential p).toReal +
        t * v p) * hab
  change
    finiteEnergyTargetDualPhase F v t p (a • x + b • y) ≤
      a * sSup
        ((fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q x) ''
            finiteEnergyFiniteTargetSet F) +
      b * sSup
        ((fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q y) ''
            finiteEnergyFiniteTargetSet F)
  rw [hphase]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hpx ha)
    (mul_le_mul_of_nonneg_left hpy hb)

private theorem finiteEnergyTargetGeodesic_zero_eq_of_differentiableAt
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    finiteEnergyTargetGeodesic F v 0 x = F.potential x := by
  apply le_antisymm (finiteEnergyTargetGeodesic_zero_le F v x)
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hpbody : p ∈ K.carrier :=
    finiteEnergySourceGradient_mem_carrier F x hx
  have hpfinite :
      sourceExtendedBodyLegendre F.potential p ≠ ⊤ := by
    rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
    exact ENNReal.ofReal_ne_top
  have hgeodesic := finiteEnergyTargetDualPhase_le_geodesic
    F v 0 (show p ∈ finiteEnergyFiniteTargetSet F
      from ⟨hpbody, hpfinite⟩) x
  have hleg :=
    finiteEnergySourceExtendedLegendre_actualGradient_toReal
      F x hx
  change
    SupportFunction.pairing p x -
      (sourceExtendedBodyLegendre F.potential p).toReal -
        0 * v p ≤ finiteEnergyTargetGeodesic F v 0 x at hgeodesic
  change
    (sourceExtendedBodyLegendre F.potential p).toReal =
      SupportFunction.pairing p x - F.potential x at hleg
  linarith

private theorem finiteEnergyTargetGeodesic_zero_eq {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n) :
    finiteEnergyTargetGeodesic F v 0 x = F.potential x := by
  apply le_antisymm (finiteEnergyTargetGeodesic_zero_le F v x)
  have hdense : Dense
      {y : Space n |
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y} :=
    MeasureTheory.Measure.dense_of_ae
      (ae_differentiableAt_finiteEnergySource F)
  have hclosed : IsClosed
      {y : Space n |
        F.potential y ≤ finiteEnergyTargetGeodesic F v 0 y} :=
    isClosed_le F.potential.continuous
      (continuous_finiteEnergyTargetGeodesic F v 0)
  have hsubset :
      {y : Space n |
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y} ⊆
      {y : Space n |
        F.potential y ≤ finiteEnergyTargetGeodesic F v 0 y} := by
    intro y hy
    exact le_of_eq
      (finiteEnergyTargetGeodesic_zero_eq_of_differentiableAt
        F v y hy).symm
  exact (closure_minimal hsubset hclosed) (hdense x)

private theorem finiteEnergyTargetGeodesic_uniform_error {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    |finiteEnergyTargetGeodesic F v t x - F.potential x| ≤
      |t| * finiteEnergyTargetTestBound K v := by
  apply abs_le.mpr
  constructor
  · have hzero : F.potential x ≤
        finiteEnergyTargetGeodesic F v t x +
          |t| * finiteEnergyTargetTestBound K v := by
      rw [← finiteEnergyTargetGeodesic_zero_eq F v x]
      change
        sSup
            ((fun p : Space n =>
              finiteEnergyTargetDualPhase F v 0 p x) ''
                finiteEnergyFiniteTargetSet F) ≤
          finiteEnergyTargetGeodesic F v t x +
            |t| * finiteEnergyTargetTestBound K v
      apply csSup_le
        ((finiteEnergyFiniteTargetSet_nonempty F).image _)
      rintro _ ⟨p, hp, rfl⟩
      have hphase := finiteEnergyTargetDualPhase_le_geodesic
        F v t hp x
      have htest := abs_targetTest_le_finiteEnergyTargetTestBound
        K v hp.1
      have ht : t * v p ≤
          |t| * finiteEnergyTargetTestBound K v := by
        calc
          t * v p ≤ |t * v p| := le_abs_self _
          _ = |t| * |v p| := abs_mul _ _
          _ ≤ |t| * finiteEnergyTargetTestBound K v :=
            mul_le_mul_of_nonneg_left htest (abs_nonneg t)
      unfold finiteEnergyTargetDualPhase at hphase
      change
        SupportFunction.pairing p x -
          (sourceExtendedBodyLegendre F.potential p).toReal -
            0 * v p ≤
          finiteEnergyTargetGeodesic F v t x +
            |t| * finiteEnergyTargetTestBound K v
      linarith
    linarith
  · have hupper :
        finiteEnergyTargetGeodesic F v t x ≤
          F.potential x +
            |t| * finiteEnergyTargetTestBound K v := by
      unfold finiteEnergyTargetGeodesic
      apply csSup_le
        ((finiteEnergyFiniteTargetSet_nonempty F).image _)
      rintro _ ⟨p, hp, rfl⟩
      have hfenchel := finiteEnergyFiniteTarget_fenchel F hp x
      have htest := abs_targetTest_le_finiteEnergyTargetTestBound
        K v hp.1
      have ht : -t * v p ≤
          |t| * finiteEnergyTargetTestBound K v := by
        calc
          -t * v p = -(t * v p) := by ring
          _ ≤ |t * v p| := neg_le_abs _
          _ = |t| * |v p| := abs_mul _ _
          _ ≤ |t| * finiteEnergyTargetTestBound K v :=
            mul_le_mul_of_nonneg_left htest (abs_nonneg t)
      unfold finiteEnergyTargetDualPhase
      linarith
    linarith

private theorem finiteEnergyTargetGeodesic_densityIntegrable {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp (-finiteEnergyTargetGeodesic F v t x))
      (volume : Measure (Space n)) := by
  let A : ℝ := |t| * finiteEnergyTargetTestBound K v
  have hmeas : AEStronglyMeasurable
      (fun x : Space n =>
        Real.exp (-finiteEnergyTargetGeodesic F v t x))
      (volume : Measure (Space n)) :=
    (Real.continuous_exp.comp
      (continuous_finiteEnergyTargetGeodesic F v t).neg).aestronglyMeasurable
  refine (F.densityIntegrable.const_mul
    (Real.exp A)).mono' hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  dsimp [A]
  linarith

end MomentTargetGeodesic

namespace MomentTargetGeodesicVariation

open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open MomentCoercivityCompactness MomentFunctionalCoercivity MomentNonlinearTightness MomentOptimizer
open MomentConvexRecovery MomentTargetGeodesic
open scoped BigOperators ENNReal NNReal Topology

private theorem exists_finiteEnergySource_linear_coercivity
    {n : ℕ} (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (F : SourceFiniteEnergyPotential K)
        (x : Space n),
        δ * ‖x‖ ≤ F.potential x +
          B * finiteEnergySourceBodyEnergy F := by
  obtain ⟨ρ, δ, hρ, hδ, hball⟩ :=
    exists_uniform_inner_supportBall K
  have hpow : 0 < ρ ^ n := pow_pos hρ n
  refine ⟨δ, normalizedVolume K.carrier / ρ ^ n,
    hδ, div_pos K.volume_pos hpow, ?_⟩
  intro F x
  obtain ⟨c, hsubset, hpair⟩ := hball x
  have hfinite :
      (volume : Measure (Space n))
          (Metric.ball c (ρ / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top K.compact.measure_ne_top
      (measure_mono hsubset)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        δ * ‖x‖ - F.potential x)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const hfinite
  have hdualK :=
    finiteEnergySourceExtendedLegendre_integrableOn F
  have hdualball : IntegrableOn
      (fun p : Space n =>
        (sourceExtendedBodyLegendre F.potential p).toReal)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    hdualK.mono_set hsubset
  have haeBall :
      ∀ᵐ p : Space n
        ∂((volume : Measure (Space n)).restrict
          (Metric.ball c (ρ / 2))),
        p ∈ finiteEnergyFiniteTargetSet F :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubset (ae_mem_finiteEnergyFiniteTargetSet F)
  have hdualmass :
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) =
      normalizedVolume K.carrier *
        finiteEnergySourceBodyEnergy F := by
    have h := finiteEnergySourceBodyEnergy_eq_setIntegral F
    have hvol := K.volume_pos.ne'
    field_simp at h
    linarith
  have hbound :
      ρ ^ n * (δ * ‖x‖ - F.potential x) ≤
        normalizedVolume K.carrier *
          finiteEnergySourceBodyEnergy F := by
    calc
      ρ ^ n * (δ * ‖x‖ - F.potential x) =
          (∫ _p in Metric.ball c (ρ / 2),
            δ * ‖x‖ - F.potential x
            ∂(volume : Measure (Space n))) := by
            rw [MeasureTheory.setIntegral_const,
              realVolume_uniformInnerBall c hρ]
            simp only [smul_eq_mul]
      _ ≤ (∫ p in Metric.ball c (ρ / 2),
            (sourceExtendedBodyLegendre F.potential p).toReal
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.integral_mono_ae
              hconst hdualball
            filter_upwards
              [MeasureTheory.ae_restrict_mem
                Metric.isOpen_ball.measurableSet, haeBall]
              with p hp hpfinite
            have hpfenchel :=
              finiteEnergyFiniteTarget_fenchel F hpfinite x
            linarith [hpair p hp]
      _ ≤ (∫ p in K.carrier,
            (sourceExtendedBodyLegendre F.potential p).toReal
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_set hdualK
            · filter_upwards with p
              exact ENNReal.toReal_nonneg
            · exact Filter.Eventually.of_forall hsubset
      _ = normalizedVolume K.carrier *
            finiteEnergySourceBodyEnergy F := hdualmass
  have hdiv :
      δ * ‖x‖ - F.potential x ≤
        (normalizedVolume K.carrier *
          finiteEnergySourceBodyEnergy F) / ρ ^ n := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [mul_comm] using hbound
  calc
    δ * ‖x‖ ≤
        F.potential x +
          (normalizedVolume K.carrier *
            finiteEnergySourceBodyEnergy F) / ρ ^ n := by
          linarith
    _ = F.potential x +
        (normalizedVolume K.carrier / ρ ^ n) *
          finiteEnergySourceBodyEnergy F := by
          ring

private theorem exists_finiteEnergyTargetGeodesic_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        δ * ‖x‖ ≤ finiteEnergyTargetGeodesic F v t x + C := by
  obtain ⟨δ, B, hδ, _hB, hcoerc⟩ :=
    exists_finiteEnergySource_linear_coercivity K
  refine ⟨δ,
    B * finiteEnergySourceBodyEnergy F +
      |t| * finiteEnergyTargetTestBound K v,
    hδ, ?_⟩
  intro x
  have hF := hcoerc F x
  have ht := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  linarith

private theorem exists_finiteEnergyTargetGeodesic_minimum
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ∃ m : Space n,
      ∀ x : Space n,
        finiteEnergyTargetGeodesic F v t m ≤
          finiteEnergyTargetGeodesic F v t x := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergyTargetGeodesic_linear_coercivity F v t
  let R : ℝ := max 0
    ((finiteEnergyTargetGeodesic F v t 0 + C) / δ)
  have hR : 0 ≤ R := le_max_left _ _
  have hzero :
      (0 : Space n) ∈
        Metric.closedBall (0 : Space n) R := by
    simpa only [mem_closedBall, dist_self] using hR
  obtain ⟨m, hm, hmin⟩ :=
    (isCompact_closedBall (0 : Space n) R).exists_isMinOn
      ⟨0, hzero⟩
      (continuous_finiteEnergyTargetGeodesic F v t).continuousOn
  refine ⟨m, ?_⟩
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : Space n) R
  · exact hmin hx
  · have hnorm : R < ‖x‖ := by
      have h := lt_of_not_ge
        (show ¬dist x (0 : Space n) ≤ R from
          (Metric.mem_closedBall.not.mp hx))
      simpa only [gt_iff_lt, dist_zero_right] using h
    have hthreshold :
        finiteEnergyTargetGeodesic F v t 0 + C ≤ δ * R := by
      have hmax :
          (finiteEnergyTargetGeodesic F v t 0 + C) / δ ≤ R :=
        le_max_right 0 _
      have h := (div_le_iff₀ hδ).mp hmax
      nlinarith
    have hxcoerc := hcoerc x
    have hzeroMin := hmin hzero
    change
      finiteEnergyTargetGeodesic F v t m ≤
        finiteEnergyTargetGeodesic F v t 0 at hzeroMin
    nlinarith [mul_lt_mul_of_pos_left hnorm hδ]

private def finiteEnergyTargetGeodesicMinimumPoint
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : Space n :=
  (exists_finiteEnergyTargetGeodesic_minimum F v t).choose

private theorem finiteEnergyTargetGeodesicMinimumPoint_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t) ≤
      finiteEnergyTargetGeodesic F v t x :=
  (exists_finiteEnergyTargetGeodesic_minimum F v t).choose_spec x

private theorem finiteEnergyTargetGeodesic_sub_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x y : Space n) :
    finiteEnergyTargetGeodesic F v t (x + y) -
        finiteEnergyTargetGeodesic F v t y ≤
      SupportFunction.supportFunction K.carrier x := by
  have hle :
      finiteEnergyTargetGeodesic F v t (x + y) ≤
        finiteEnergyTargetGeodesic F v t y +
          SupportFunction.supportFunction K.carrier x := by
    unfold finiteEnergyTargetGeodesic
    apply csSup_le
      ((finiteEnergyFiniteTargetSet_nonempty F).image _)
    rintro _ ⟨p, hp, rfl⟩
    have hphase := le_csSup
      (finiteEnergyTargetDualPhase_bddAbove F v t y)
      (show finiteEnergyTargetDualPhase F v t p y ∈
        (fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q y) ''
            finiteEnergyFiniteTargetSet F
        from ⟨p, hp, rfl⟩)
    have hpair := SupportFunction.pairing_le_supportFunction
      K.compact hp.1 x
    unfold finiteEnergyTargetDualPhase at hphase ⊢
    change
      SupportFunction.pairing p (x + y) -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p ≤
        sSup
          ((fun q : Space n =>
            SupportFunction.pairing q y -
              (sourceExtendedBodyLegendre F.potential q).toReal -
                t * v q) '' finiteEnergyFiniteTargetSet F) +
          SupportFunction.supportFunction K.carrier x
    rw [MonomialDivergence.pairing_add_right]
    linarith
  linarith

private def minimumNormalizedTargetGeodesicContinuousMap
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : C(Space n, ℝ) where
  toFun x :=
    finiteEnergyTargetGeodesic F v t
        (x + finiteEnergyTargetGeodesicMinimumPoint F v t) -
      finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t)
  continuous_toFun :=
    ((continuous_finiteEnergyTargetGeodesic F v t).comp
      (continuous_id.add continuous_const)).sub continuous_const

private theorem minimumNormalizedTargetGeodesicContinuousMap_zero
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    minimumNormalizedTargetGeodesicContinuousMap F v t 0 = 0 := by
  simp only [minimumNormalizedTargetGeodesicContinuousMap, ContinuousMap.coe_mk, zero_add, sub_self]

private theorem minimumNormalizedTargetGeodesicContinuousMap_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    0 ≤ minimumNormalizedTargetGeodesicContinuousMap F v t x := by
  change
    0 ≤ finiteEnergyTargetGeodesic F v t
        (x + finiteEnergyTargetGeodesicMinimumPoint F v t) -
      finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t)
  exact sub_nonneg.mpr
    (finiteEnergyTargetGeodesicMinimumPoint_le
      F v t (x + finiteEnergyTargetGeodesicMinimumPoint F v t))

private theorem minimumNormalizedTargetGeodesicContinuousMap_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    minimumNormalizedTargetGeodesicContinuousMap F v t x ≤
      SupportFunction.supportFunction K.carrier x := by
  exact finiteEnergyTargetGeodesic_sub_le_support F v t x
    (finiteEnergyTargetGeodesicMinimumPoint F v t)

private theorem minimumNormalizedTargetGeodesicContinuousMap_lipschitz
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (minimumNormalizedTargetGeodesicContinuousMap F v t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h :=
    (finiteEnergyTargetGeodesic_lipschitz F v t).dist_le_mul
      (x + finiteEnergyTargetGeodesicMinimumPoint F v t)
      (y + finiteEnergyTargetGeodesicMinimumPoint F v t)
  simpa only [minimumNormalizedTargetGeodesicContinuousMap, ContinuousMap.coe_mk,
    dist_sub_eq_dist_add_right, sub_add_cancel, Real.dist_eq, ge_iff_le, dist_add_right] using h

private theorem convexOn_minimumNormalizedTargetGeodesicContinuousMap
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ConvexOn ℝ Set.univ
      (minimumNormalizedTargetGeodesicContinuousMap F v t) := by
  let g := finiteEnergyTargetGeodesic F v t
  let z := finiteEnergyTargetGeodesicMinimumPoint F v t
  change ConvexOn ℝ Set.univ (fun x => g (x + z) - g z)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo :
      a • (x + z) + b • (y + z) =
        (a • x + b • y) + z := by
    calc
      a • (x + z) + b • (y + z) =
          (a • x + b • y) + (a • z + b • z) := by
        rw [smul_add, smul_add]
        abel
      _ = (a • x + b • y) + z := by
        rw [← add_smul, hab, one_smul]
  have h := (convexOn_finiteEnergyTargetGeodesic F v t).2
    (Set.mem_univ (x + z)) (Set.mem_univ (y + z)) ha hb hab
  rw [hcombo] at h
  change g ((a • x + b • y) + z) ≤
    a * g (x + z) + b * g (y + z) at h
  change g ((a • x + b • y) + z) - g z ≤
    a * (g (x + z) - g z) + b * (g (y + z) - g z)
  calc
    g ((a • x + b • y) + z) - g z ≤
        (a * g (x + z) + b * g (y + z)) - g z :=
      sub_le_sub_right h _
    _ = (a * g (x + z) + b * g (y + z)) -
        (a + b) * g z := by simp only [hab, one_mul]
    _ = a * (g (x + z) - g z) +
        b * (g (y + z) - g z) := by ring

private theorem minimumNormalizedTargetGeodesic_densityIntegrable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp
          (-minimumNormalizedTargetGeodesicContinuousMap F v t x))
      (volume : Measure (Space n)) := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have htranslate :=
    (finiteEnergyTargetGeodesic_densityIntegrable F v t).comp_add_right m
  have hscaled := htranslate.const_mul
    (Real.exp (finiteEnergyTargetGeodesic F v t m))
  have hfun :
      (fun x : Space n =>
        Real.exp
          (-minimumNormalizedTargetGeodesicContinuousMap F v t x)) =
      (fun x : Space n =>
        Real.exp (finiteEnergyTargetGeodesic F v t m) *
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    change
      -(finiteEnergyTargetGeodesic F v t (x + m) -
        finiteEnergyTargetGeodesic F v t m) =
      finiteEnergyTargetGeodesic F v t m +
        -finiteEnergyTargetGeodesic F v t (x + m)
    ring
  rw [hfun]
  exact hscaled

private def minimumNormalizedTargetGeodesicDualMajorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (p : Space n) : ℝ :=
  (sourceExtendedBodyLegendre F.potential p).toReal + t * v p -
    SupportFunction.pairing p
      (finiteEnergyTargetGeodesicMinimumPoint F v t) +
    finiteEnergyTargetGeodesic F v t
      (finiteEnergyTargetGeodesicMinimumPoint F v t)

private theorem minimumNormalizedTargetGeodesicDualMajorant_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    0 ≤ minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  have hphase := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp (finiteEnergyTargetGeodesicMinimumPoint F v t)
  unfold finiteEnergyTargetDualPhase at hphase
  unfold minimumNormalizedTargetGeodesicDualMajorant
  linarith

private theorem minimumNormalizedTargetGeodesic_phase_le_majorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    phase p (minimumNormalizedTargetGeodesicContinuousMap F v t) x ≤
      minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have hphase := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp (x + m)
  unfold finiteEnergyTargetDualPhase at hphase
  change
    SupportFunction.pairing p x -
      (finiteEnergyTargetGeodesic F v t (x + m) -
        finiteEnergyTargetGeodesic F v t m) ≤
      (sourceExtendedBodyLegendre F.potential p).toReal +
        t * v p - SupportFunction.pairing p m +
          finiteEnergyTargetGeodesic F v t m
  rw [MonomialDivergence.pairing_add_right] at hphase
  linarith

private theorem minimumNormalizedTargetGeodesic_extendedLegendre_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    sourceExtendedBodyLegendre
        (minimumNormalizedTargetGeodesicContinuousMap F v t) p ≤
      ENNReal.ofReal
        (minimumNormalizedTargetGeodesicDualMajorant F v t p) := by
  unfold sourceExtendedBodyLegendre
  apply iSup_le
  intro j
  exact ENNReal.ofReal_le_ofReal
    (minimumNormalizedTargetGeodesic_phase_le_majorant
      F v t hp (TopologicalSpace.denseSeq (Space n) j))

private theorem minimumNormalizedTargetGeodesicDualMajorant_integrableOn
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    IntegrableOn
      (minimumNormalizedTargetGeodesicDualMajorant F v t)
      K.carrier (volume : Measure (Space n)) := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hv : IntegrableOn
      (fun p : Space n => v p)
      K.carrier (volume : Measure (Space n)) :=
    v.continuous.continuousOn.integrableOn_compact K.compact
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (finiteEnergyTargetGeodesicMinimumPoint F v t)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  exact ((hdual.add (hv.const_mul t)).sub hpair).add hconst

private theorem minimumNormalizedTargetGeodesic_legendreFinite
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    (∫⁻ p in K.carrier,
      sourceExtendedBodyLegendre
        (minimumNormalizedTargetGeodesicContinuousMap F v t) p
      ∂(volume : Measure (Space n))) < ⊤ := by
  have hnonneg :
      ∀ᵐ p : Space n
        ∂((volume : Measure (Space n)).restrict K.carrier),
        0 ≤ minimumNormalizedTargetGeodesicDualMajorant F v t p := by
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesicDualMajorant_nonneg F v t hp
  have hmono :
      (∫⁻ p in K.carrier,
        sourceExtendedBodyLegendre
          (minimumNormalizedTargetGeodesicContinuousMap F v t) p
        ∂(volume : Measure (Space n))) ≤
      ∫⁻ p in K.carrier,
        ENNReal.ofReal
          (minimumNormalizedTargetGeodesicDualMajorant F v t p)
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesic_extendedLegendre_le
      F v t hp
  have hmajor :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (minimumNormalizedTargetGeodesicDualMajorant_integrableOn
        F v t) hnonneg
  exact lt_of_le_of_lt hmono
    (by rw [← hmajor]; exact ENNReal.ofReal_lt_top)

private def finiteEnergySourceOfTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : SourceFiniteEnergyPotential K where
  potential := minimumNormalizedTargetGeodesicContinuousMap F v t
  normalized := minimumNormalizedTargetGeodesicContinuousMap_zero
    F v t
  lipschitz := minimumNormalizedTargetGeodesicContinuousMap_lipschitz
    F v t
  convex := convexOn_minimumNormalizedTargetGeodesicContinuousMap
    F v t
  nonnegative := minimumNormalizedTargetGeodesicContinuousMap_nonneg
    F v t
  supportUpper := minimumNormalizedTargetGeodesicContinuousMap_le_support
    F v t
  legendreFinite := minimumNormalizedTargetGeodesic_legendreFinite
    F v t
  densityIntegrable := minimumNormalizedTargetGeodesic_densityIntegrable
    F v t

private def finiteEnergyTargetGeodesicPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : ℝ :=
  ∫ x : Space n,
    Real.exp (-finiteEnergyTargetGeodesic F v t x)
    ∂(volume : Measure (Space n))

private theorem finiteEnergyTargetGeodesicPartition_pos
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    0 < finiteEnergyTargetGeodesicPartition F v t := by
  exact MeasureTheory.integral_exp_pos
    (finiteEnergyTargetGeodesic_densityIntegrable F v t)

private theorem finiteEnergySourcePartition_ofTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    finiteEnergySourcePartition
        (finiteEnergySourceOfTargetGeodesic F v t) =
      Real.exp
        (finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t)) *
      finiteEnergyTargetGeodesicPartition F v t := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  unfold finiteEnergySourcePartition
  change
    (∫ x : Space n,
      Real.exp
        (-(finiteEnergyTargetGeodesic F v t (x + m) -
          finiteEnergyTargetGeodesic F v t m))
      ∂(volume : Measure (Space n))) =
      Real.exp (finiteEnergyTargetGeodesic F v t m) *
        finiteEnergyTargetGeodesicPartition F v t
  calc
    (∫ x : Space n,
      Real.exp
        (-(finiteEnergyTargetGeodesic F v t (x + m) -
          finiteEnergyTargetGeodesic F v t m))
      ∂(volume : Measure (Space n))) =
      ∫ x : Space n,
        Real.exp (finiteEnergyTargetGeodesic F v t m) *
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))
        ∂(volume : Measure (Space n)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [← Real.exp_add]
        congr 1
        ring
    _ = Real.exp (finiteEnergyTargetGeodesic F v t m) *
        (∫ x : Space n,
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))
          ∂(volume : Measure (Space n))) :=
      MeasureTheory.integral_const_mul _ _
    _ = Real.exp (finiteEnergyTargetGeodesic F v t m) *
        finiteEnergyTargetGeodesicPartition F v t := by
      rw [MeasureTheory.integral_add_right_eq_self
        (fun x : Space n =>
          Real.exp (-finiteEnergyTargetGeodesic F v t x)) m]
      rfl

private theorem minimumNormalizedTargetGeodesic_extendedLegendre_toReal_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    (sourceExtendedBodyLegendre
      (minimumNormalizedTargetGeodesicContinuousMap F v t) p).toReal ≤
      minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  calc
    (sourceExtendedBodyLegendre
      (minimumNormalizedTargetGeodesicContinuousMap F v t) p).toReal ≤
      (ENNReal.ofReal
        (minimumNormalizedTargetGeodesicDualMajorant F v t p)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (minimumNormalizedTargetGeodesic_extendedLegendre_le
          F v t hp)
    _ = minimumNormalizedTargetGeodesicDualMajorant F v t p :=
      ENNReal.toReal_ofReal
        (minimumNormalizedTargetGeodesicDualMajorant_nonneg F v t hp)

private theorem setIntegral_minimumNormalizedTargetGeodesicDualMajorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    (∫ p in K.carrier,
      minimumNormalizedTargetGeodesicDualMajorant F v t p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) +
      t * (∫ p in K.carrier, v p
        ∂(volume : Measure (Space n))) +
      normalizedVolume K.carrier *
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hv : IntegrableOn
      (fun p : Space n => v p)
      K.carrier (volume : Measure (Space n)) :=
    v.continuous.continuousOn.integrableOn_compact K.compact
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (finiteEnergyTargetGeodesicMinimumPoint F v t)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  calc
    (∫ p in K.carrier,
      minimumNormalizedTargetGeodesicDualMajorant F v t p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal +
          t * v p - SupportFunction.pairing p m
        ∂(volume : Measure (Space n))) +
      (∫ _p in K.carrier,
        finiteEnergyTargetGeodesic F v t m
        ∂(volume : Measure (Space n))) := by
      simpa only [minimumNormalizedTargetGeodesicDualMajorant, integral_const, MeasurableSet.univ,
        measureReal_restrict_apply, univ_inter, smul_eq_mul, Pi.sub_apply, Pi.add_apply, m] using
        MeasureTheory.integral_add
          ((hdual.add (hv.const_mul t)).sub hpair) hconst
    _ =
      ((∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) +
        t * (∫ p in K.carrier, v p
          ∂(volume : Measure (Space n))) -
        (∫ p in K.carrier,
          SupportFunction.pairing p m
          ∂(volume : Measure (Space n)))) +
      (∫ _p in K.carrier,
        finiteEnergyTargetGeodesic F v t m
        ∂(volume : Measure (Space n))) := by
      congr 1
      calc
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal +
            t * v p - SupportFunction.pairing p m
          ∂(volume : Measure (Space n))) =
          (∫ p in K.carrier,
            (sourceExtendedBodyLegendre F.potential p).toReal +
              t * v p
            ∂(volume : Measure (Space n))) -
          (∫ p in K.carrier,
            SupportFunction.pairing p m
            ∂(volume : Measure (Space n))) := by
          simpa only [Pi.add_apply, m] using
            MeasureTheory.integral_sub
              (hdual.add (hv.const_mul t)) hpair
        _ = _ := by
          rw [MeasureTheory.integral_add hdual (hv.const_mul t),
            MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [sourceCenteredBody_setIntegral_pairing_eq_zero,
        MeasureTheory.setIntegral_const]
      simp only [sub_zero, measureReal_def, smul_eq_mul, normalizedVolume, m]

private theorem finiteEnergySourceBodyEnergy_ofTargetGeodesic_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    finiteEnergySourceBodyEnergy
        (finiteEnergySourceOfTargetGeodesic F v t) ≤
      finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
  have hdualNormalized :=
    finiteEnergySourceExtendedLegendre_integrableOn
      (finiteEnergySourceOfTargetGeodesic F v t)
  have hmajor :=
    minimumNormalizedTargetGeodesicDualMajorant_integrableOn F v t
  have hmono :
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre
          (finiteEnergySourceOfTargetGeodesic F v t).potential p).toReal
        ∂(volume : Measure (Space n))) ≤
      ∫ p in K.carrier,
        minimumNormalizedTargetGeodesicDualMajorant F v t p
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.integral_mono_ae hdualNormalized hmajor
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesic_extendedLegendre_toReal_le
      F v t hp
  rw [finiteEnergySourceBodyEnergy_eq_setIntegral
    (finiteEnergySourceOfTargetGeodesic F v t)]
  calc
    (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre
            (finiteEnergySourceOfTargetGeodesic F v t).potential p).toReal
          ∂(volume : Measure (Space n))) ≤
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          minimumNormalizedTargetGeodesicDualMajorant F v t p
          ∂(volume : Measure (Space n))) :=
        mul_le_mul_of_nonneg_left hmono
          (inv_nonneg.mpr K.volume_pos.le)
    _ = finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
        rw [setIntegral_minimumNormalizedTargetGeodesicDualMajorant,
          finiteEnergySourceBodyEnergy_eq_setIntegral,
          integral_normalizedTargetBodyMeasure]
        have hvol := K.volume_pos.ne'
        field_simp

private theorem exists_exact_optimizer_targetGeodesic_logPartition_le
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      ∀ (v : C(Space n, ℝ)) (t : ℝ),
        Real.log (finiteEnergyTargetGeodesicPartition F v t) ≤
          Real.log (finiteEnergySourcePartition F) +
            t * (∫ p : Space n, v p
              ∂(normalizedTargetBodyMeasure K)) := by
  obtain ⟨F, heq, hmax⟩ :=
    exists_finiteEnergySourceBerman_exact_optimizer K
  refine ⟨F, heq, hmax, ?_⟩
  intro v t
  let G : SourceFiniteEnergyPotential K :=
    finiteEnergySourceOfTargetGeodesic F v t
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have hG := hmax G
  have henergy := finiteEnergySourceBodyEnergy_ofTargetGeodesic_le
    F v t
  have hpart := finiteEnergySourcePartition_ofTargetGeodesic F v t
  have hpos := finiteEnergyTargetGeodesicPartition_pos F v t
  have hlog :
      Real.log (finiteEnergySourcePartition G) =
        finiteEnergyTargetGeodesic F v t m +
          Real.log (finiteEnergyTargetGeodesicPartition F v t) := by
    change
      Real.log
        (finiteEnergySourcePartition
          (finiteEnergySourceOfTargetGeodesic F v t)) = _
    rw [hpart,
      Real.log_mul
        (Real.exp_pos
          (finiteEnergyTargetGeodesic F v t m)).ne'
        hpos.ne', Real.log_exp]
  unfold finiteEnergySourceBermanFunctional at hG
  change
    finiteEnergySourceBodyEnergy G ≤
      finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t m at henergy
  rw [hlog] at hG
  linarith

end MomentTargetGeodesicVariation

end Ehrhart

end
