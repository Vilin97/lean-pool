/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal
public import LeanPool.QuadraticCarleson.QuadraticCarleson.SparseMaximalLp

/-!
# The finite sparse maximal weak `(1,1)` lemma

This file develops the analytic core of paper Lemma `l:weak11sparse`. It is
organized around the paper's two genuine measure-theoretic operations:
excision of a maximal-function exceptional set and foliation by a measurable
maximizing index.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson


theorem L0Infinity.integrable_finiteSparseProof (f : L0Infinity) : Integrable f :=
  f.integrable

/-- A measurable bounded-set indicator as a member of the paper's test
function class. The containing compact set is kept explicit so that no
topological regularity of the set itself is needed. -/
noncomputable def setIndicatorL0Infinity (s K : Set ℝ) (hs : MeasurableSet s)
    (hK : IsCompact K) (hsK : s ⊆ K) : L0Infinity where
  toFun := s.indicator (fun _ ↦ (1 : ℂ))
  measurable_toFun := measurable_const.indicator hs
  bounded_toFun := ⟨1, fun x ↦ by
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]⟩
  hasCompactSupport_toFun := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxs
    exact hx (by simp [Set.indicator_of_notMem (fun h ↦ hxs (hsK h))])

@[simp] theorem setIndicatorL0Infinity_apply (s K : Set ℝ) (hs : MeasurableSet s)
    (hK : IsCompact K) (hsK : s ⊆ K) (x : ℝ) :
    setIndicatorL0Infinity s K hs hK hsK x = s.indicator (fun _ ↦ (1 : ℂ)) x := rfl

/-- Any explicit nonnegative weak bound bounds the infimum defining the weak
operator norm. -/
theorem weakOneOneNorm_le_of_hasWeakOneOneBound
    {T : L0Infinity → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : HasWeakOneOneBound C T) : weakOneOneNorm T ≤ C := by
  unfold weakOneOneNorm
  apply csInf_le
  · exact ⟨0, fun D hD ↦ hD.1⟩
  · exact ⟨hC, h⟩

/-- The finite maximum is almost everywhere equal to the maximum formed from
measurable representatives of the locally integrable outputs. This is the
representative bridge needed before applying the measurable selector. -/
theorem finiteMax_ae_eq_measurable_representatives
    {N : ℕ} (T : Fin N → TestOperator) (f : L0Infinity)
    (hlocal : ∀ j, LocallyIntegrable (T j f) volume) :
    finiteMax T f =ᵐ[volume] fun x ↦
      ↑(Finset.univ.sup fun j ↦
        ‖(hlocal j).aestronglyMeasurable.mk (T j f) x‖₊) := by
  classical
  have hj (j : Fin N) :
      T j f =ᵐ[volume] (hlocal j).aestronglyMeasurable.mk (T j f) :=
    (hlocal j).aestronglyMeasurable.ae_eq_mk
  filter_upwards [ae_all_iff.mpr hj] with x hx
  unfold finiteMax
  congr 1
  apply Finset.sup_congr rfl
  intro j _
  rw [hx j]

/-- Exhausting a measurable superlevel set by compact intervals is enough to
prove its distribution bound. This is the direct level-set replacement for
the restricted weak-type dual characterization quoted in the paper. -/
theorem mul_measure_level_le_of_closedBall
    (u : ℝ → ℝ) (hu : Measurable u) {a : ℝ} (C : ℝ≥0∞)
    (h : ∀ n : ℕ, ENNReal.ofReal a *
      volume ({x | a < u x} ∩ Metric.closedBall 0 n) ≤ C) :
    ENNReal.ofReal a * volume {x | a < u x} ≤ C := by
  let E : ℕ → Set ℝ := fun n ↦ {x | a < u x} ∩ Metric.closedBall 0 n
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_lt measurable_const hu).inter measurableSet_closedBall
  have hEmono : Monotone E := by
    intro n m hnm x hx
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact ⟨hx.1, Metric.closedBall_subset_closedBall hcast hx.2⟩
  have hEunion : ⋃ n, E n = {x | a < u x} := by
    rw [show (⋃ n, E n) = {x | a < u x} ∩ ⋃ n : ℕ, Metric.closedBall (0 : ℝ) n by
      rw [inter_iUnion]]
    rw [Metric.iUnion_closedBall_nat, inter_univ]
  rw [← hEunion, hEmono.measure_iUnion]
  rw [ENNReal.mul_iSup]
  exact iSup_le h

/-- Two-stage maximal-function excision. The constants are deliberately
generous: after removing a level set of `M F` and a level set of `M 1_H`, at
least half of the original finite-measure set remains. The second removal
is what ensures that every interval meeting the good set has small density
of the first exceptional set. -/
theorem centeredMaximal_excision
    (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hmassTop : (∫⁻ x, F x) ≠ ∞) (hmassZero : (∫⁻ x, F x) ≠ 0)
    (E : Set ℝ) (hE : MeasurableSet E) (hEzero : volume E ≠ 0)
    (hEtop : volume E ≠ ∞) :
    let mass := ∫⁻ x, F x
    let b := 2048 * mass / volume E
    let H := {x | b < centeredHardyLittlewoodMaximal F x}
    let Hwide := {x | (1 : ℝ≥0∞) / 32 <
      centeredHardyLittlewoodMaximal (H.indicator 1) x}
    volume E / 2 ≤ volume (E \ (H ∪ Hwide)) := by
  dsimp only
  let mass := ∫⁻ x, F x
  let b := 2048 * mass / volume E
  let H : Set ℝ := {x | b < centeredHardyLittlewoodMaximal F x}
  let Hwide : Set ℝ := {x | (1 : ℝ≥0∞) / 32 <
    centeredHardyLittlewoodMaximal (H.indicator 1) x}
  have hM : Measurable (centeredHardyLittlewoodMaximal F) :=
    measurable_centeredHardyLittlewoodMaximal hF
  have hH : MeasurableSet H := measurableSet_lt measurable_const hM
  have hHind : Measurable (H.indicator fun _ ↦ (1 : ℝ≥0∞)) :=
    measurable_const.indicator hH
  have hHwide : MeasurableSet Hwide := measurableSet_lt measurable_const
    (measurable_centeredHardyLittlewoodMaximal hHind)
  have hb0 : b ≠ 0 := by simp [b, mass, hmassZero, hEtop]
  have hbtop : b ≠ ∞ := by dsimp [b, mass]; finiteness
  have hweak := centeredHardyLittlewoodMaximal_weak_bound F b
  have hHsmall : volume H ≤ volume E / 512 := by
    have hh : volume H ≤ (4 * mass) / b :=
      (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)).2
        (by simpa [H, mass, mul_comm] using hweak)
    apply hh.trans_eq
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    have hmreal : mass.toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨by simpa [mass] using hmassZero,
        by simpa [mass] using hmassTop⟩
    simp only [b, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul]
    field_simp [hmreal]
    ring
  have hweakWide := centeredHardyLittlewoodMaximal_weak_bound
    (H.indicator fun _ ↦ (1 : ℝ≥0∞)) ((1 : ℝ≥0∞) / 32)
  have hindIntegral : (∫⁻ x, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) = volume H := by
    rw [lintegral_indicator hH]
    simp
  rw [hindIntegral] at hweakWide
  change ((1 : ℝ≥0∞) / 32) * volume Hwide ≤ 4 * volume H at hweakWide
  have hwideSmall : volume Hwide ≤ 128 * volume H := by
    have ha0 : (1 : ℝ≥0∞) / 32 ≠ 0 := by norm_num
    have hatop : (1 : ℝ≥0∞) / 32 ≠ ∞ := by norm_num
    have hh : volume Hwide ≤ (4 * volume H) / ((1 : ℝ≥0∞) / 32) :=
      (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hatop)).2
        (by simpa [Hwide, mul_comm] using hweakWide)
    calc
      volume Hwide ≤ (4 * volume H) / ((1 : ℝ≥0∞) / 32) := hh
      _ = 128 * volume H := by norm_num [div_eq_mul_inv]; ring
  have hbad : volume (H ∪ Hwide) ≤ volume E / 2 := by
    calc
      volume (H ∪ Hwide) ≤ volume H + volume Hwide := measure_union_le _ _
      _ ≤ volume E / 512 + 128 * (volume E / 512) :=
        add_le_add hHsmall (hwideSmall.trans (mul_le_mul' le_rfl hHsmall))
      _ ≤ volume E / 2 := by
        calc
          volume E / 512 + 128 * (volume E / 512) =
              129 * (volume E / 512) := by ring
          _ ≤ 256 * (volume E / 512) :=
            mul_le_mul' (by norm_num) le_rfl
          _ = volume E / 2 := by
            apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
            simp [ENNReal.toReal_div]
            ring
  have hdiff : E \ (H ∪ Hwide) = E \ (E ∩ (H ∪ Hwide)) := by
    ext x
    simp
  rw [hdiff, measure_sdiff (inter_subset_left) (hE.inter (hH.union hHwide)).nullMeasurableSet
    (ne_top_of_le_ne_top hEtop (measure_mono inter_subset_left))]
  apply ENNReal.le_sub_of_add_le_left
    (ne_top_of_le_ne_top hEtop (measure_mono inter_subset_left))
  calc
    volume (E ∩ (H ∪ Hwide)) + volume E / 2 ≤ volume E / 2 + volume E / 2 := by
      gcongr
      exact (measure_mono inter_subset_right).trans hbad
    _ = volume E := ENNReal.add_halves _

/-- A localized version of the sparse embedding. Only intervals for which
the second local average is nonzero need a large major subset; this is the
form used after restricting the testing function to one leaf of the
measurable foliation. -/
theorem sparseForm_le_lintegral_on_of_majorSubsets
    {p η : ℝ} {S : Set RealInterval} (hη : 0 < η) (hScount : S.Countable)
    (f g : ℝ → ℂ) (D : Set ℝ) (hD : MeasurableSet D)
    (E : {I : RealInterval // I ∈ S} → Set ℝ)
    (hEmeas : ∀ I, MeasurableSet (E I))
    (hEsub : ∀ I, E I ⊆ I.1.carrier)
    (hEdisj : Pairwise fun I J ↦ Disjoint (E I) (E J))
    (hElarge : ∀ I, localAverage p g I.1 ≠ 0 →
      η * I.1.length ≤ (volume (E I)).toReal)
    (hED : ∀ I, E I ⊆ D) :
    sparseForm p f g S ≤ ENNReal.ofReal η⁻¹ *
      ∫⁻ x in D, intervalMaximalAverage 1 f x * intervalMaximalAverage p g x := by
  classical
  let _ : Countable {I : RealInterval // I ∈ S} := hScount.to_subtype
  let M : ℝ → ℝ≥0∞ := fun x ↦
    intervalMaximalAverage 1 f x * intervalMaximalAverage p g x
  have hterm : ∀ I : {I : RealInterval // I ∈ S},
      ENNReal.ofReal
          (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) ≤
        ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x := by
    intro I
    by_cases havg : localAverage p g I.1 = 0
    · simp [havg]
    have hIfinite : volume I.1.carrier ≠ ∞ := by simp
    have hEfinite : volume (E I) ≠ ∞ :=
      ne_top_of_le_ne_top hIfinite (measure_mono (hEsub I))
    have hlengthReal : I.1.length ≤ η⁻¹ * (volume (E I)).toReal := by
      calc
        I.1.length = η⁻¹ * (η * I.1.length) := by
          rw [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
        _ ≤ η⁻¹ * (volume (E I)).toReal :=
          mul_le_mul_of_nonneg_left (hElarge I havg) (inv_nonneg.mpr hη.le)
    have hlength : ENNReal.ofReal I.1.length ≤
        ENNReal.ofReal η⁻¹ * volume (E I) := by
      calc
        ENNReal.ofReal I.1.length ≤
            ENNReal.ofReal (η⁻¹ * (volume (E I)).toReal) :=
          ENNReal.ofReal_le_ofReal hlengthReal
        _ = ENNReal.ofReal η⁻¹ * ENNReal.ofReal (volume (E I)).toReal := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hη.le)]
        _ = ENNReal.ofReal η⁻¹ * volume (E I) := by
          rw [ENNReal.ofReal_toReal hEfinite]
    have hintegral :
        ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) * volume (E I) ≤
          ∫⁻ x in E I, M x := by
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hEmeas I)
      intro x hx
      exact mul_le_mul'
        (ofReal_localAverage_le_intervalMaximalAverage 1 f I.1 (hEsub I hx))
        (ofReal_localAverage_le_intervalMaximalAverage p g I.1 (hEsub I hx))
    rw [ENNReal.ofReal_mul
      (mul_nonneg I.1.length_pos.le (localAverage_nonneg 1 f I.1)),
      ENNReal.ofReal_mul I.1.length_pos.le]
    calc
      ENNReal.ofReal I.1.length * ENNReal.ofReal (localAverage 1 f I.1) *
          ENNReal.ofReal (localAverage p g I.1) ≤
        (ENNReal.ofReal η⁻¹ * volume (E I)) *
          ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) :=
        mul_le_mul' (mul_le_mul' hlength le_rfl) le_rfl
      _ = ENNReal.ofReal η⁻¹ *
          (ENNReal.ofReal (localAverage 1 f I.1) *
            ENNReal.ofReal (localAverage p g I.1) * volume (E I)) := by
        ac_rfl
      _ ≤ ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x :=
        mul_le_mul' le_rfl hintegral
  rw [sparseForm]
  calc
    ∑' I : {I : RealInterval // I ∈ S},
        ENNReal.ofReal
          (I.1.length * localAverage 1 f I.1 * localAverage p g I.1) ≤
      ∑' I : {I : RealInterval // I ∈ S},
        ENNReal.ofReal η⁻¹ * ∫⁻ x in E I, M x := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal η⁻¹ * ∫⁻ x in ⋃ I, E I, M x := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun I ↦ hEmeas I) hEdisj]
    _ ≤ ENNReal.ofReal η⁻¹ * ∫⁻ x in D, M x := by
      apply mul_le_mul' le_rfl
      have hU : MeasurableSet (⋃ I, E I) := MeasurableSet.iUnion hEmeas
      rw [← lintegral_indicator hU, ← lintegral_indicator hD]
      apply lintegral_mono
      apply Set.indicator_le_indicator_of_subset
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨I, hxI⟩
        exact hED I hxI
      · exact fun _ ↦ bot_le

/-- The exponent-one local average of a characteristic function is the
relative Lebesgue measure of the set in the interval. -/
theorem localAverage_one_indicator (H : Set ℝ) (hH : MeasurableSet H)
    (I : RealInterval) :
    localAverage 1 (H.indicator fun _ ↦ (1 : ℂ)) I =
      (volume (H ∩ I.carrier)).toReal / I.length := by
  have hfun : (fun x : ℝ ↦ ‖H.indicator (fun _ ↦ (1 : ℂ)) x‖ ^ (1 : ℝ)) =
      H.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ H <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [localAverage, hfun]
  have hI := I.measurableSet_carrier
  rw [show (∫ x in I.carrier, H.indicator (fun _ ↦ (1 : ℝ)) x) =
      (volume (H ∩ I.carrier)).toReal by
    rw [← integral_indicator hI]
    have hind : I.carrier.indicator (H.indicator fun _ ↦ (1 : ℝ)) =
        (H ∩ I.carrier).indicator (fun _ ↦ (1 : ℝ)) := by
      funext x
      by_cases hxH : x ∈ H <;> by_cases hxI : x ∈ I.carrier <;>
        simp [hxH, hxI]
    rw [hind]
    simp [hH.inter hI]
    rfl]
  rw [one_div_one, Real.rpow_one]
  field_simp

/-- A nonzero local average of an indicator forces the interval to meet the
indicated set. -/
theorem exists_mem_carrier_inter_of_localAverage_indicator_ne_zero
    {p : ℝ} (hp : 0 < p) (G : Set ℝ) (I : RealInterval)
    (havg : localAverage p (G.indicator fun _ ↦ (1 : ℂ)) I ≠ 0) :
    ∃ x, x ∈ I.carrier ∧ x ∈ G := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ x ∈ I.carrier,
      ‖G.indicator (fun _ ↦ (1 : ℂ)) x‖ ^ p = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem (hnone x hx), Real.zero_rpow hp.ne']
  apply havg
  rw [localAverage]
  have hint : (∫ x in I.carrier,
      ‖G.indicator (fun _ ↦ (1 : ℂ)) x‖ ^ p) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem I.measurableSet_carrier] with x hx
    exact hzero x hx
  rw [hint, mul_zero]
  exact Real.zero_rpow (one_div_ne_zero hp.ne')

/-- Outside the second exceptional set, every interval through the point has
at most one eighth of its length in the first exceptional set. The factor
four is exactly the uncentered-to-centered interval comparison. -/
theorem interval_indicator_density_le_eighth_of_maximal_le
    (H : Set ℝ) (hH : MeasurableSet H) (I : RealInterval) {x : ℝ}
    (hx : x ∈ I.carrier)
    (hMx : centeredHardyLittlewoodMaximal (H.indicator 1) x ≤ (1 : ℝ≥0∞) / 32) :
    (volume (H ∩ I.carrier)).toReal ≤ I.length / 8 := by
  let hC : ℝ → ℂ := H.indicator fun _ ↦ (1 : ℂ)
  have hmeas : Measurable hC := measurable_const.indicator hH
  have hint : IntegrableOn (fun y ↦ ‖hC y‖ ^ (1 : ℝ)) I.carrier := by
    apply IntegrableOn.of_bound (by simp) (hmeas.norm.pow_const 1).aestronglyMeasurable.restrict 1
    filter_upwards with y
    by_cases hy : y ∈ H <;> simp [hC, hy]
  have hcomp := ofReal_localAverage_le_centeredHardyLittlewoodMaximal_rpow
    1 zero_lt_one hC I hint hx
  have henorm (y : ℝ) : ‖hC y‖ₑ = H.indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
    by_cases hy : y ∈ H <;> simp [hC, hy]
  simp_rw [henorm] at hcomp
  simp only [one_div, inv_one, ENNReal.rpow_one] at hcomp
  have havgENN : ENNReal.ofReal (localAverage 1 hC I) ≤ (1 : ℝ≥0∞) / 8 := by
    calc
      ENNReal.ofReal (localAverage 1 hC I) ≤
          4 * centeredHardyLittlewoodMaximal (H.indicator 1) x := hcomp
      _ ≤ 4 * ((1 : ℝ≥0∞) / 32) := mul_le_mul' le_rfl hMx
      _ = (1 : ℝ≥0∞) / 8 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num
  have havg : localAverage 1 hC I ≤ (1 : ℝ) / 8 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp
    simpa using havgENN
  rw [localAverage_one_indicator H hH I] at havg
  have hlen := I.length_pos
  rw [div_le_iff₀ hlen] at havg
  nlinarith

/-- Cutting the original `1/4`-sparse major subsets by the first exceptional
set leaves `1/8`-major subsets whenever every contributing interval meets the
second good set. -/
theorem sparseForm_le_eight_lintegral_off_exceptional
    {p : ℝ} {S : Set RealInterval} (hS : IsSparse (1 / 4) S)
    (f g : ℝ → ℂ) (H : Set ℝ) (hH : MeasurableSet H)
    (hactive : ∀ I : {I : RealInterval // I ∈ S},
      localAverage p g I.1 ≠ 0 → ∃ x ∈ I.1.carrier,
        centeredHardyLittlewoodMaximal (H.indicator 1) x ≤ (1 : ℝ≥0∞) / 32) :
    sparseForm p f g S ≤ 8 *
      ∫⁻ x in Hᶜ, intervalMaximalAverage 1 f x * intervalMaximalAverage p g x := by
  classical
  have hScount := hS.countable
  rcases hS with ⟨-, -, E, hEmeas, hEsub, hEdisj, hEsize⟩
  let E' : {I : RealInterval // I ∈ S} → Set ℝ := fun I ↦ E I \ H
  have hE'meas (I : {I : RealInterval // I ∈ S}) : MeasurableSet (E' I) :=
    (hEmeas I).diff hH
  have hE'sub (I : {I : RealInterval // I ∈ S}) : E' I ⊆ I.1.carrier :=
    fun _ hx ↦ hEsub I hx.1
  have hE'disj : Pairwise fun I J ↦ Disjoint (E' I) (E' J) := by
    intro I J hIJ
    exact (hEdisj hIJ).mono (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.1)
  have hE'large (I : {I : RealInterval // I ∈ S})
      (havg : localAverage p g I.1 ≠ 0) :
      (1 / 8 : ℝ) * I.1.length ≤ (volume (E' I)).toReal := by
    obtain ⟨x, hxI, hxM⟩ := hactive I havg
    have hdensity := interval_indicator_density_le_eighth_of_maximal_le
      H hH I.1 hxI hxM
    have hinter : (volume (E I ∩ H)).toReal ≤ I.1.length / 8 := by
      apply (MeasureTheory.measureReal_mono ?_
        (ne_top_of_le_ne_top (by simp : volume I.1.carrier ≠ ∞)
          (measure_mono inter_subset_right))).trans
        hdensity
      intro y hy
      exact ⟨hy.2, hEsub I hy.1⟩
    have hEfinite : volume (E I) ≠ ∞ :=
      ne_top_of_le_ne_top (by simp : volume I.1.carrier ≠ ∞)
        (measure_mono (hEsub I))
    have hdiff : (volume (E' I)).toReal =
        (volume (E I)).toReal - (volume (E I ∩ H)).toReal := by
      dsimp only [E']
      rw [show E I \ H = E I \ (E I ∩ H) by ext y; simp]
      exact MeasureTheory.measureReal_sdiff inter_subset_left ((hEmeas I).inter hH) hEfinite
    rw [hdiff]
    have hquarter := hEsize I
    norm_num at hquarter ⊢
    linarith
  have hE'off (I : {I : RealInterval // I ∈ S}) : E' I ⊆ Hᶜ :=
    fun _ hx ↦ hx.2
  have h := sparseForm_le_lintegral_on_of_majorSubsets
    (p := p) (S := S) (f := f) (g := g) (D := Hᶜ)
    (by norm_num : (0 : ℝ) < 1 / 8) hScount hH.compl E'
    hE'meas hE'sub hE'disj hE'large hE'off
  simpa using h

/-- The weak `(1,1)` maximal estimate integrated only below a finite level.
This is the layer-cake estimate used for the first Hölder factor after
excision. -/
theorem centeredMaximal_capped_rpow_lintegral_le
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) {b q : ℝ}
    (hmassTop : (∫⁻ y, F y) ≠ ∞) (hb : 0 < b) (hq : 1 < q) :
    (∫⁻ x in {x | centeredHardyLittlewoodMaximal F x ≤ ENNReal.ofReal b},
        centeredHardyLittlewoodMaximal F x ^ q) ≤
      ENNReal.ofReal (4 * q / (q - 1)) * (∫⁻ y, F y) *
        ENNReal.ofReal (b ^ (q - 1)) := by
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  let D : Set ℝ := {x | M x ≤ ENNReal.ofReal b}
  let u : ℝ → ℝ≥0∞ := D.indicator M
  let g : ℝ → ℝ := fun x ↦ (u x).toReal
  have hM : Measurable M := measurable_centeredHardyLittlewoodMaximal hF
  have hD : MeasurableSet D := measurableSet_le hM measurable_const
  have hu : Measurable u := hM.indicator hD
  have hufinite (x : ℝ) : u x ≠ ∞ := by
    by_cases hx : x ∈ D
    · have hxD : M x ≤ ENNReal.ofReal b := hx
      have hxle : u x ≤ ENNReal.ofReal b := by
        simpa [u, Set.indicator_of_mem hx] using hxD
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxle
    · simp [u, Set.indicator_of_notMem hx]
  have hg : Measurable g := hu.ennreal_toReal
  have hgnonneg : ∀ x, 0 ≤ g x := fun _ ↦ ENNReal.toReal_nonneg
  have hpow (x : ℝ) : ENNReal.ofReal (g x ^ q) = u x ^ q := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (zero_lt_one.trans hq).le, ENNReal.ofReal_toReal (hufinite x)]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Eventually.of_forall hgnonneg) hg.aemeasurable (zero_lt_one.trans hq)
  have htail (t : ℝ) (ht : 0 < t) :
      volume {x | t < g x} * ENNReal.ofReal (t ^ (q - 1)) ≤
        (Iio b).indicator
          (fun t ↦ 4 * (∫⁻ y, F y) * ENNReal.ofReal (t ^ (q - 2))) t := by
    by_cases htb : t < b
    · rw [Set.indicator_of_mem (show t ∈ Iio b from htb)]
      have hsub : {x | t < g x} ⊆ {x | ENNReal.ofReal t < M x} := by
        intro x hx
        have hltu : ENNReal.ofReal t < u x :=
          (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hufinite x)).mpr hx
        by_cases hxD : x ∈ D
        · simpa [u, Set.indicator_of_mem hxD] using hltu
        · simp [u, Set.indicator_of_notMem hxD] at hltu
      have hw := centeredHardyLittlewoodMaximal_weak_bound F (ENNReal.ofReal t)
      have hpower : ENNReal.ofReal (t ^ (q - 1)) =
          ENNReal.ofReal t * ENNReal.ofReal (t ^ (q - 2)) := by
        rw [← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [show q - 1 = 1 + (q - 2) by ring, Real.rpow_add ht,
          Real.rpow_one]
      rw [hpower]
      calc
        volume {x | t < g x} *
            (ENNReal.ofReal t * ENNReal.ofReal (t ^ (q - 2))) =
            (ENNReal.ofReal t * volume {x | t < g x}) *
              ENNReal.ofReal (t ^ (q - 2)) := by ac_rfl
        _ ≤ (ENNReal.ofReal t * volume {x | ENNReal.ofReal t < M x}) *
              ENNReal.ofReal (t ^ (q - 2)) := by gcongr
        _ ≤ (4 * ∫⁻ y, F y) * ENNReal.ofReal (t ^ (q - 2)) :=
          mul_le_mul' hw le_rfl
    · rw [Set.indicator_of_notMem (show t ∉ Iio b from htb)]
      simp only [nonpos_iff_eq_zero]
      have hempty : {x | t < g x} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hule : u x ≤ ENNReal.ofReal b := by
          by_cases hxD : x ∈ D
          · have hxD' : M x ≤ ENNReal.ofReal b := hxD
            simpa [u, Set.indicator_of_mem hxD] using hxD'
          · simp [u, Set.indicator_of_notMem hxD]
        have hgle : g x ≤ b := by
          simpa [g, ENNReal.toReal_ofReal hb.le] using
            ((ENNReal.toReal_le_toReal (hufinite x) ENNReal.ofReal_ne_top).mpr hule)
        exact (not_lt_of_ge (hgle.trans (le_of_not_gt htb))) hx
      simp [hempty]
  simp_rw [hpow] at hlayer
  rw [← lintegral_indicator hD]
  have huPow : D.indicator (fun x ↦ M x ^ q) = fun x ↦ u x ^ q := by
    funext x
    by_cases hx : x ∈ D
    · simp [u, hx]
    · simp [u, hx, ENNReal.zero_rpow_of_pos (zero_lt_one.trans hq)]
  rw [huPow]
  rw [hlayer]
  calc
    ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ),
          volume {x | t < g x} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ),
          (Iio b).indicator
            (fun t ↦ 4 * (∫⁻ y, F y) * ENNReal.ofReal (t ^ (q - 2))) t := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono'
      · exact measurableSet_Ioi
      · intro t ht
        exact htail t ht
    _ = ENNReal.ofReal q *
        (4 * (∫⁻ y, F y) *
          ∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal (t ^ (q - 2))) := by
      rw [setLIntegral_indicator measurableSet_Iio]
      rw [show (Iio b ∩ Ioi (0 : ℝ)) = Ioo 0 b by ext t; simp [and_comm]]
      rw [lintegral_const_mul' _ _ (by finiteness)]
    _ = ENNReal.ofReal (4 * q / (q - 1)) * (∫⁻ y, F y) *
        ENNReal.ofReal (b ^ (q - 1)) := by
      rw [lintegral_rpow_Ioo_zero hq hb]
      rw [ENNReal.ofReal_div_of_pos (by linarith : 0 < q - 1),
        ENNReal.ofReal_div_of_pos (by linarith : 0 < q - 1),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        div_eq_mul_inv]
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- The analytic estimate for one leaf of the maximizing-index foliation.
The first maximal factor is integrated only off the exceptional set, while
the second uses the global strong maximal theorem. -/
theorem sparseForm_foliation_leaf_le
    {p r b : ℝ} (hp : 0 < p) (hr : 1 < r) (hpr : p < r) (hb : 0 < b)
    {S : Set RealInterval} (hS : IsSparse (1 / 4) S)
    (f g : L0Infinity)
    (hactive : ∀ I : {I : RealInterval // I ∈ S},
      localAverage p g I.1 ≠ 0 → ∃ x ∈ I.1.carrier,
        centeredHardyLittlewoodMaximal
          ({y | ENNReal.ofReal b < centeredHardyLittlewoodMaximal
            (fun z ↦ ‖f z‖ₑ) y}.indicator 1) x ≤ (1 : ℝ≥0∞) / 32) :
    sparseForm p f g S ≤
      8 * (
        ((4 : ℝ≥0∞) ^ holderConjugate r *
          (ENNReal.ofReal (4 * holderConjugate r /
              (holderConjugate r - 1)) * (∫⁻ y, ‖f y‖ₑ) *
            ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
              (1 / holderConjugate r) *
        ((4 : ℝ≥0∞) ^ (r / p) *
          ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
            ∫⁻ x, ‖g x‖ₑ ^ r) ^ (1 / r)) := by
  let F : ℝ → ℝ≥0∞ := fun y ↦ ‖f y‖ₑ
  have hF : Measurable F := f.measurable_toFun.enorm
  let H : Set ℝ := {y | ENNReal.ofReal b < centeredHardyLittlewoodMaximal F y}
  have hH : MeasurableSet H := measurableSet_lt measurable_const
    (measurable_centeredHardyLittlewoodMaximal hF)
  have hmassTop : (∫⁻ y, F y) ≠ ∞ := by
    have hfhi := hasFiniteIntegral_iff_enorm.mp
      f.integrable_finiteSparseProof.hasFiniteIntegral
    change (∫⁻ y, ‖f y‖ₑ) < ∞ at hfhi
    exact ne_of_lt (by simpa [F] using hfhi)
  have hbase := sparseForm_le_eight_lintegral_off_exceptional
    hS f g H hH (by simpa [H, F] using hactive)
  apply hbase.trans
  have hpMajor (x : ℝ) : intervalMaximalAverage p g x ≤
      intervalAverageMajorant p g x :=
    intervalMaximalAverage_le_intervalAverageMajorant hp g x
  have h1Major (x : ℝ) : intervalMaximalAverage 1 f x ≤
      4 * centeredHardyLittlewoodMaximal F x := by
    simpa [F] using intervalMaximalAverage_one_le_centeredHardyLittlewoodMaximal f x
  have hprod : (∫⁻ x in Hᶜ,
      intervalMaximalAverage 1 f x * intervalMaximalAverage p g x) ≤
      ∫⁻ x in Hᶜ,
        (4 * centeredHardyLittlewoodMaximal F x) * intervalAverageMajorant p g x := by
    apply setLIntegral_mono'
    · exact hH.compl
    · intro x _
      exact mul_le_mul' (h1Major x) (hpMajor x)
  apply mul_le_mul' le_rfl
  apply hprod.trans
  have hq : 1 < holderConjugate r := one_lt_holderConjugate_of_one_lt hr
  let U : ℝ → ℝ≥0∞ := fun x ↦ 4 * centeredHardyLittlewoodMaximal F x
  have hU : Measurable U := measurable_const.mul
    (measurable_centeredHardyLittlewoodMaximal hF)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict Hᶜ) (holderConjugate_spec hr).symm
    hU.aemeasurable
    (measurable_intervalAverageMajorant p g).aemeasurable
  have hholder' : (∫⁻ x in Hᶜ,
      (4 * centeredHardyLittlewoodMaximal F x) * intervalAverageMajorant p g x) ≤
      ((∫⁻ x in Hᶜ, (4 * centeredHardyLittlewoodMaximal F x) ^
          holderConjugate r) ^ (1 / holderConjugate r) *
        (∫⁻ x in Hᶜ, intervalAverageMajorant p g x ^ r) ^ (1 / r)) := by
    simpa only [Pi.mul_apply, U] using hholder
  apply hholder'.trans
  apply mul_le_mul'
  · apply ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr (zero_lt_one.trans hq).le)
    calc
      (∫⁻ x in Hᶜ, (4 * centeredHardyLittlewoodMaximal F x) ^
          holderConjugate r) =
          (4 : ℝ≥0∞) ^ holderConjugate r *
            ∫⁻ x in Hᶜ,
              centeredHardyLittlewoodMaximal F x ^ holderConjugate r := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (zero_lt_one.trans hq).le]
        rw [lintegral_const_mul' _ _ (by finiteness)]
      _ ≤ (4 : ℝ≥0∞) ^ holderConjugate r *
          (ENNReal.ofReal (4 * holderConjugate r /
              (holderConjugate r - 1)) * (∫⁻ y, ‖f y‖ₑ) *
            ENNReal.ofReal (b ^ (holderConjugate r - 1))) := by
        apply mul_le_mul' le_rfl
        have hset : Hᶜ = {x | centeredHardyLittlewoodMaximal F x ≤ ENNReal.ofReal b} := by
          ext x
          simp [H]
        rw [hset]
        simpa [F] using centeredMaximal_capped_rpow_lintegral_le F hF hmassTop hb hq
  · apply ENNReal.rpow_le_rpow
      ((setLIntegral_le_lintegral _ _).trans
        (intervalAverageMajorant_rpow_lintegral_le p r hp hpr g))
      (one_div_nonneg.mpr (zero_lt_one.trans hr).le)

/-- Pairing the positive operator `|T|` with a measurable characteristic
function is exactly the integral of `|Tf|` on that set. -/
theorem norm_operatorPairing_absolute_indicator
    (T : TestOperator) (f : L0Infinity) (G K : Set ℝ)
    (hG : MeasurableSet G) (hK : IsCompact K) (hGK : G ⊆ K) :
    ‖operatorPairing (absoluteValueOperator T) f
        (setIndicatorL0Infinity G K hG hK hGK)‖ = ∫ x in G, ‖T f x‖ := by
  have hnonneg : 0 ≤ ∫ x in G, ‖T f x‖ :=
    integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
  have heq : operatorPairing (absoluteValueOperator T) f
      (setIndicatorL0Infinity G K hG hK hGK) =
      ((∫ x in G, ‖T f x‖ : ℝ) : ℂ) := by
    rw [operatorPairing]
    have hpoint : (fun x ↦ absoluteValueOperator T f x *
        star (setIndicatorL0Infinity G K hG hK hGK x)) =
        G.indicator (fun x ↦ ((‖T f x‖ : ℝ) : ℂ)) := by
      funext x
      by_cases hx : x ∈ G <;> simp [absoluteValueOperator_apply, hx]
    rw [hpoint, integral_indicator hG]
    exact integral_complex_ofReal
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

theorem lintegral_enorm_setIndicator_rpow
    (G K : Set ℝ) (hG : MeasurableSet G) (hK : IsCompact K) (hGK : G ⊆ K)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ‖setIndicatorL0Infinity G K hG hK hGK x‖ₑ ^ r) = volume G := by
  have hpoint (x : ℝ) :
      ‖setIndicatorL0Infinity G K hG hK hGK x‖ₑ ^ r =
        G.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ G
    · simp [setIndicatorL0Infinity_apply, hx]
    · simp [setIndicatorL0Infinity_apply, hx, ENNReal.zero_rpow_of_pos hr]
  simp_rw [hpoint]
  rw [lintegral_indicator hG]
  simp

/-- The measurable leaves produced by the canonical maximizing index. -/
noncomputable def maximizingFoliationSet (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ)
    (G : Set ℝ) (j : Fin (n + 1)) : Set ℝ :=
  G ∩ measurableMaximizingIndex n R ⁻¹' {j}

theorem measurableSet_maximizingFoliationSet
    (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ) (hR : ∀ j, Measurable (R j))
    (G : Set ℝ) (hG : MeasurableSet G) (j : Fin (n + 1)) :
    MeasurableSet (maximizingFoliationSet n R G j) :=
  hG.inter ((measurable_measurableMaximizingIndex n R hR) (measurableSet_singleton j))

theorem pairwise_disjoint_maximizingFoliationSet
    (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ) (G : Set ℝ) :
    Pairwise fun i j ↦ Disjoint (maximizingFoliationSet n R G i)
      (maximizingFoliationSet n R G j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : measurableMaximizingIndex n R x = i := hxi.2
  have hj : measurableMaximizingIndex n R x = j := hxj.2
  exact hij (hi.symm.trans hj)

theorem iUnion_maximizingFoliationSet
    (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ) (G : Set ℝ) :
    ⋃ j, maximizingFoliationSet n R G j = G := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
    exact hxj.1
  · intro hx
    exact Set.mem_iUnion.mpr
      ⟨measurableMaximizingIndex n R x, ⟨hx, rfl⟩⟩

/-- Measure summation for the measurable maximizing foliation. -/
theorem sum_volume_maximizingFoliationSet
    (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ) (hR : ∀ j, Measurable (R j))
    (G : Set ℝ) (hG : MeasurableSet G) :
    ∑ j, volume (maximizingFoliationSet n R G j) = volume G := by
  calc
    ∑ j, volume (maximizingFoliationSet n R G j) =
        ∑' j, volume (maximizingFoliationSet n R G j) := by simp
    _ = volume (⋃ j, maximizingFoliationSet n R G j) :=
      (measure_iUnion (pairwise_disjoint_maximizingFoliationSet n R G)
        (fun j ↦ measurableSet_maximizingFoliationSet n R hR G hG j)).symm
    _ = volume G := by rw [iUnion_maximizingFoliationSet]

/-- ENNReal form of the finite-dimensional Hölder estimate for a measurable
foliation. -/
theorem sum_volume_rpow_maximizingFoliationSet_le
    (n : ℕ) (R : Fin (n + 1) → ℝ → ℂ) (hR : ∀ j, Measurable (R j))
    (G : Set ℝ) (hG : MeasurableSet G) (hGtop : volume G ≠ ∞)
    {r : ℝ} (hr : 1 < r) :
    ∑ j, volume (maximizingFoliationSet n R G j) ^ (1 / r) ≤
      ENNReal.ofReal ((volume G).toReal ^ (1 / r) *
        ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
  let E : Fin (n + 1) → Set ℝ := fun j ↦ maximizingFoliationSet n R G j
  have hEmeas : ∀ j, MeasurableSet (E j) := fun j ↦
    measurableSet_maximizingFoliationSet n R hR G hG j
  have hEdisj : Pairwise fun i j ↦ Disjoint (E i) (E j) :=
    pairwise_disjoint_maximizingFoliationSet n R G
  have hsub : (⋃ j, E j) ⊆ G := by
    rw [show (⋃ j, E j) = G by exact iUnion_maximizingFoliationSet n R G]
  have hreal := sum_measureReal_rpow_one_div_le E G hEmeas hEdisj hsub hGtop hr
  have hterm (j : Fin (n + 1)) :
      volume (E j) ^ (1 / r) =
        ENNReal.ofReal ((volume (E j)).toReal ^ (1 / r)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (one_div_nonneg.mpr (zero_lt_one.trans hr).le)]
    rw [ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top hGtop
      (measure_mono ((Set.subset_iUnion E j).trans hsub))
  change ∑ j, volume (E j) ^ (1 / r) ≤ _
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal hreal
  · intro j _
    exact Real.rpow_nonneg MeasureTheory.measureReal_nonneg _

/-- One foliated characteristic-function leaf, with all dependence on its
measure factored into the final `|G|^(1/r)` term. -/
theorem sparseForm_indicator_leaf_le_factored
    {p r b : ℝ} (hp : 0 < p) (hr : 1 < r) (hpr : p < r) (hb : 0 < b)
    {S : Set RealInterval} (hS : IsSparse (1 / 4) S)
    (f : L0Infinity) (G K : Set ℝ) (hG : MeasurableSet G)
    (hK : IsCompact K) (hGK : G ⊆ K)
    (hactive : ∀ I : {I : RealInterval // I ∈ S},
      localAverage p (setIndicatorL0Infinity G K hG hK hGK) I.1 ≠ 0 →
        ∃ x ∈ I.1.carrier,
          centeredHardyLittlewoodMaximal
            ({y | ENNReal.ofReal b < centeredHardyLittlewoodMaximal
              (fun z ↦ ‖f z‖ₑ) y}.indicator 1) x ≤ (1 : ℝ≥0∞) / 32) :
    sparseForm p f (setIndicatorL0Infinity G K hG hK hGK) S ≤
      (8 *
        ((4 : ℝ≥0∞) ^ holderConjugate r *
          (ENNReal.ofReal (4 * holderConjugate r /
              (holderConjugate r - 1)) * (∫⁻ y, ‖f y‖ₑ) *
            ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
              (1 / holderConjugate r) *
        ((4 : ℝ≥0∞) ^ (r / p) *
          ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p))) ^
            (1 / r)) * volume G ^ (1 / r) := by
  have hleaf := sparseForm_foliation_leaf_le hp hr hpr hb hS f
    (setIndicatorL0Infinity G K hG hK hGK) hactive
  rw [lintegral_enorm_setIndicator_rpow G K hG hK hGK
    (zero_lt_one.trans hr)] at hleaf
  apply hleaf.trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (zero_lt_one.trans hr).le)]
  ring

/-- Measurable representative of the finite maximum. -/
noncomputable def measurableFiniteMaxRep {N : ℕ} (T : Fin N → TestOperator)
    (f : L0Infinity) (hlocal : ∀ j, LocallyIntegrable (T j f) volume) (x : ℝ) : ℝ :=
  ↑(Finset.univ.sup fun j ↦ ‖(hlocal j).aestronglyMeasurable.mk (T j f) x‖₊)

theorem measurable_measurableFiniteMaxRep {N : ℕ} (T : Fin N → TestOperator)
    (f : L0Infinity) (hlocal : ∀ j, LocallyIntegrable (T j f) volume) :
    Measurable (measurableFiniteMaxRep T f hlocal) := by
  classical
  unfold measurableFiniteMaxRep
  fun_prop

theorem finiteMax_ae_eq_measurableFiniteMaxRep {N : ℕ} (T : Fin N → TestOperator)
    (f : L0Infinity) (hlocal : ∀ j, LocallyIntegrable (T j f) volume) :
    finiteMax T f =ᵐ[volume] measurableFiniteMaxRep T f hlocal :=
  finiteMax_ae_eq_measurable_representatives T f hlocal

/-- The full compact-level aggregation before numerical simplification. -/
theorem finiteMaxRep_compact_level_bound
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A)
    {p r ε a : ℝ} (hp : 1 < p) (hp2 : p < 2) (hr : 1 < r)
    (hpr : p < r) (hε : 0 < ε)
    (f : L0Infinity) (K E : Set ℝ) (hK : IsCompact K)
    (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hElevel : E ⊆ {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x})
    (hmassZero : (∫⁻ y, ‖f y‖ₑ) ≠ 0) (hEzero : volume E ≠ 0) :
    let mass := ∫⁻ y, ‖f y‖ₑ
    let b := (2048 * mass / volume E).toReal
    let C := A * holderConjugate p + ε
    let common : ℝ≥0∞ :=
      8 *
        ((4 : ℝ≥0∞) ^ holderConjugate r *
          (ENNReal.ofReal (4 * holderConjugate r /
              (holderConjugate r - 1)) * mass *
            ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
              (1 / holderConjugate r) *
        ((4 : ℝ≥0∞) ^ (r / p) *
          ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p))) ^
            (1 / r)
    ENNReal.ofReal a * (volume E / 2) ≤
      ENNReal.ofReal C * common *
        ENNReal.ofReal ((volume E).toReal ^ (1 / r) *
          ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
  classical
  dsimp only
  let mass : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ
  let bE : ℝ≥0∞ := 2048 * mass / volume E
  let b : ℝ := bE.toReal
  let C : ℝ := A * holderConjugate p + ε
  let common : ℝ≥0∞ :=
    8 *
      ((4 : ℝ≥0∞) ^ holderConjugate r *
        (ENNReal.ofReal (4 * holderConjugate r /
            (holderConjugate r - 1)) * mass *
          ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
            (1 / holderConjugate r) *
      ((4 : ℝ≥0∞) ^ (r / p) *
        ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p))) ^
          (1 / r)
  have hmassTop : mass ≠ ∞ := by
    have hfhi := hasFiniteIntegral_iff_enorm.mp
      f.integrable_finiteSparseProof.hasFiniteIntegral
    exact ne_of_lt (by simpa [mass] using hfhi)
  have hEtop : volume E ≠ ∞ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hEK)
  have hbE0 : bE ≠ 0 := by simp [bE, mass, hmassZero, hEtop]
  have hbEtop : bE ≠ ∞ := by dsimp [bE]; finiteness
  have hbpos : 0 < b := ENNReal.toReal_pos hbE0 hbEtop
  have hofReal_b : ENNReal.ofReal b = bE := ENNReal.ofReal_toReal hbEtop
  let F : ℝ → ℝ≥0∞ := fun y ↦ ‖f y‖ₑ
  let H : Set ℝ := {x | bE < centeredHardyLittlewoodMaximal F x}
  let Hwide : Set ℝ := {x | (1 : ℝ≥0∞) / 32 <
    centeredHardyLittlewoodMaximal (H.indicator 1) x}
  let G : Set ℝ := E \ (H ∪ Hwide)
  have hF : Measurable F := f.measurable_toFun.enorm
  have hH : MeasurableSet H := measurableSet_lt measurable_const
    (measurable_centeredHardyLittlewoodMaximal hF)
  have hHwide : MeasurableSet Hwide := measurableSet_lt measurable_const
    (measurable_centeredHardyLittlewoodMaximal (measurable_const.indicator hH))
  have hG : MeasurableSet G := hE.diff (hH.union hHwide)
  have hGE : G ⊆ E := sdiff_subset
  have hGhalf : volume E / 2 ≤ volume G := by
    simpa [mass, bE, F, H, Hwide, G] using
      centeredMaximal_excision F hF hmassTop hmassZero E hE hEzero hEtop
  let hlocal : ∀ j, LocallyIntegrable (T j f) volume := fun j ↦ hT.2.1 j f
  let R : Fin (n + 1) → ℝ → ℂ := fun j ↦
    (hlocal j).aestronglyMeasurable.mk (T j f)
  have hR (j : Fin (n + 1)) : Measurable (R j) :=
    (hlocal j).aestronglyMeasurable.measurable_mk
  let Gj : Fin (n + 1) → Set ℝ := fun j ↦ maximizingFoliationSet n R G j
  have hGj (j : Fin (n + 1)) : MeasurableSet (Gj j) :=
    measurableSet_maximizingFoliationSet n R hR G hG j
  have hGjK (j : Fin (n + 1)) : Gj j ⊆ K := fun x hx ↦ hEK (hGE hx.1)
  have hTGint (j : Fin (n + 1)) : IntegrableOn (fun x ↦ ‖T j f x‖) (Gj j) :=
    Integrable.mono_measure (((hlocal j).integrableOn_isCompact hK).norm)
      ((Measure.restrict_mono (hGjK j)) le_rfl)
  have hTR (j : Fin (n + 1)) : T j f =ᵐ[volume] R j :=
    (hlocal j).aestronglyMeasurable.ae_eq_mk
  have hlowerLeaf (j : Fin (n + 1)) :
      ENNReal.ofReal a * volume (Gj j) ≤
        ENNReal.ofReal (∫ x in Gj j, ‖T j f x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hTGint j)
      (Eventually.of_forall fun _ ↦ norm_nonneg _)]
    simp_rw [ofReal_norm]
    rw [← setLIntegral_const]
    apply setLIntegral_mono_ae' (hGj j)
    filter_upwards [hTR j] with x hxT
    intro hxGj
    have hxlev : a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x :=
      hElevel (hGE hxGj.1)
    have hxmax : ‖R j x‖ = measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x := by
      have hj : measurableMaximizingIndex n R x = j := hxGj.2
      calc
        ‖R j x‖ = ‖R (measurableMaximizingIndex n R x) x‖ := by rw [hj]
        _ = ↑(Finset.univ.sup fun k ↦ ‖R k x‖₊) := by
          simpa using congrArg ((↑·) : ℝ≥0 → ℝ)
            (norm_measurableMaximizingIndex_eq_sup n R x)
        _ = measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x := rfl
    rw [hxT, ← ofReal_norm, hxmax]
    exact ENNReal.ofReal_le_ofReal hxlev.le
  have hsparse (j : Fin (n + 1)) :
      HasSparseOnePBound C p (absoluteValueOperator (T j)) := by
    simpa [C] using hT.hasSparseOnePBound_add hp hp2 j hε
  have hupperLeaf (j : Fin (n + 1)) :
      ENNReal.ofReal (∫ x in Gj j, ‖T j f x‖) ≤
        ENNReal.ofReal C * common * volume (Gj j) ^ (1 / r) := by
    let gj := setIndicatorL0Infinity (Gj j) K (hGj j) hK (hGjK j)
    rcases hsparse j f gj with ⟨S, hS, hpair⟩
    have hpair' : ENNReal.ofReal (∫ x in Gj j, ‖T j f x‖) ≤
        ENNReal.ofReal C * sparseForm p f gj S := by
      rw [← norm_operatorPairing_absolute_indicator (T j) f (Gj j) K
        (hGj j) hK (hGjK j)]
      exact hpair
    apply hpair'.trans
    have hactive : ∀ I : {I : RealInterval // I ∈ S},
        localAverage p gj I.1 ≠ 0 → ∃ x ∈ I.1.carrier,
          centeredHardyLittlewoodMaximal (H.indicator 1) x ≤ (1 : ℝ≥0∞) / 32 := by
      intro I havg
      obtain ⟨x, hxI, hxGj⟩ :=
        exists_mem_carrier_inter_of_localAverage_indicator_ne_zero
          (zero_lt_one.trans hp) (Gj j) I.1 (by
            change localAverage p ((Gj j).indicator fun _ ↦ (1 : ℂ)) I.1 ≠ 0 at havg
            exact havg)
      refine ⟨x, hxI, le_of_not_gt ?_⟩
      exact (not_or.mp hxGj.1.2).2
    have hfact := sparseForm_indicator_leaf_le_factored
      (zero_lt_one.trans hp) hr hpr hbpos hS f (Gj j) K (hGj j) hK (hGjK j) ?_
    · have hfact' : sparseForm p f gj S ≤
          common * volume (Gj j) ^ (1 / r) := by
          simpa only [common, mass, b, one_div] using hfact
      calc
        ENNReal.ofReal C * sparseForm p f gj S ≤
            ENNReal.ofReal C * (common * volume (Gj j) ^ (1 / r)) :=
          mul_le_mul' le_rfl hfact'
        _ = ENNReal.ofReal C * common * volume (Gj j) ^ (1 / r) := by ring
    · simpa [F, H, hofReal_b, gj] using hactive
  calc
    ENNReal.ofReal a * (volume E / 2) ≤ ENNReal.ofReal a * volume G :=
      mul_le_mul' le_rfl hGhalf
    _ = ∑ j, ENNReal.ofReal a * volume (Gj j) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [Gj] using (sum_volume_maximizingFoliationSet n R hR G hG).symm
    _ ≤ ∑ j, ENNReal.ofReal (∫ x in Gj j, ‖T j f x‖) :=
      Finset.sum_le_sum fun j _ ↦ hlowerLeaf j
    _ ≤ ∑ j, ENNReal.ofReal C * common * volume (Gj j) ^ (1 / r) :=
      Finset.sum_le_sum fun j _ ↦ hupperLeaf j
    _ = ENNReal.ofReal C * common *
        ∑ j, volume (Gj j) ^ (1 / r) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal C * common *
        ENNReal.ofReal ((volume G).toReal ^ (1 / r) *
          ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
      apply mul_le_mul' le_rfl
      simpa [Gj] using sum_volume_rpow_maximizingFoliationSet_le
        n R hR G hG (ne_top_of_le_ne_top hEtop (measure_mono hGE)) hr
    _ ≤ ENNReal.ofReal C * common *
        ENNReal.ofReal ((volume E).toReal ^ (1 / r) *
          ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right
      · apply Real.rpow_le_rpow MeasureTheory.measureReal_nonneg
          (MeasureTheory.measureReal_mono hGE hEtop)
          (one_div_nonneg.mpr (zero_lt_one.trans hr).le)
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem holderConjugate_sub_one_div {r : ℝ} (hr : 1 < r) :
    (holderConjugate r - 1) / holderConjugate r = 1 / r := by
  rw [holderConjugate]
  field_simp [ne_of_gt (zero_lt_one.trans hr), ne_of_gt (sub_pos.mpr hr)]
  ring

theorem holderConjugate_ratio {r : ℝ} (hr : 1 < r) :
    holderConjugate r / (holderConjugate r - 1) = r := by
  rw [holderConjugate]
  field_simp [ne_of_gt (zero_lt_one.trans hr), ne_of_gt (sub_pos.mpr hr)]
  ring

theorem inv_holderConjugate_add_inv {r : ℝ} (hr : 1 < r) :
    1 / holderConjugate r + 1 / r = 1 := by
  simpa [one_div, add_comm] using (holderConjugate_spec hr).inv_add_inv_eq_one

/-- The explicit factor obtained by combining the finite sparse, Hölder, and Hardy–Littlewood
estimates before simplification. -/
noncomputable def finiteSparseRawFactor (p r : ℝ) : ℝ :=
  8 *
    ((4 : ℝ) ^ holderConjugate r *
      (4 * holderConjugate r / (holderConjugate r - 1))) ^
        (1 / holderConjugate r) *
    ((4 : ℝ) ^ (r / p) *
      centeredHardyLittlewoodRpowConstant (r / p)) ^ (1 / r) *
    (2048 : ℝ) ^ (1 / r)

/-- Exact cancellation of the compact level-set measure against the chosen
threshold `b = 2048 mass / |E|`. -/
theorem finiteSparse_common_normalization
    {p r : ℝ} (hp : 1 < p) (hr : 1 < r) (hpr : p < r) (m e : ℝ≥0∞)
    (hm0 : m ≠ 0) (hmt : m ≠ ∞) (he0 : e ≠ 0) (het : e ≠ ∞)
    (X : ℝ) (hX : 0 ≤ X) :
    let b := (2048 * m / e).toReal
    let common : ℝ≥0∞ :=
      8 *
        ((4 : ℝ≥0∞) ^ holderConjugate r *
          (ENNReal.ofReal (4 * holderConjugate r /
              (holderConjugate r - 1)) * m *
            ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
              (1 / holderConjugate r) *
        ((4 : ℝ≥0∞) ^ (r / p) *
          ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p))) ^
            (1 / r)
    common * ENNReal.ofReal (e.toReal ^ (1 / r) * X) =
      ENNReal.ofReal (finiteSparseRawFactor p r * m.toReal * X) := by
  dsimp only
  have hq : 0 < holderConjugate r := (holderConjugate_spec hr).symm.pos
  have hq1 : 1 < holderConjugate r := one_lt_holderConjugate_of_one_lt hr
  have hcoef : 0 ≤ 4 * holderConjugate r / (holderConjugate r - 1) := by positivity
  have hs : 1 < r / p := (lt_div_iff₀ (zero_lt_one.trans hp)).2 (by simpa using hpr)
  have hHL : 0 ≤ centeredHardyLittlewoodRpowConstant (r / p) :=
    (centeredHardyLittlewoodRpowConstant_pos hs).le
  have hbtop : 2048 * m / e ≠ ∞ := by finiteness
  have hb0 : 2048 * m / e ≠ 0 := by simp [hm0, het]
  have hbpos : 0 < (2048 * m / e).toReal := ENNReal.toReal_pos hb0 hbtop
  have hbpow : ENNReal.ofReal
      ((2048 * m / e).toReal ^ (holderConjugate r - 1)) =
      (2048 * m / e) ^ (holderConjugate r - 1) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hbpos.le (sub_nonneg.mpr hq1.le),
      ENNReal.ofReal_toReal hbtop]
  have heX : ENNReal.ofReal (e.toReal ^ (1 / r) * X) =
      e ^ (1 / r) * ENNReal.ofReal X := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (one_div_nonneg.mpr (zero_lt_one.trans hr).le),
      ENNReal.ofReal_toReal het]
  rw [hbpow, heX]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _
    (one_div_nonneg.mpr hq.le)]
  rw [← ENNReal.rpow_mul (4 : ℝ≥0∞) (holderConjugate r)
    (1 / holderConjugate r)]
  rw [show holderConjugate r * (1 / holderConjugate r) = 1 by
      field_simp [hq.ne'], ENNReal.rpow_one]
  rw [← ENNReal.rpow_mul (2048 * m / e)]
  have hexp : (holderConjugate r - 1) * (1 / holderConjugate r) = 1 / r := by
    simpa [div_eq_mul_inv] using holderConjugate_sub_one_div hr
  rw [hexp]
  rw [ENNReal.div_rpow_of_nonneg _ _ (one_div_nonneg.mpr (zero_lt_one.trans hr).le),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (zero_lt_one.trans hr).le)]
  have hepow0 : e ^ (1 / r) ≠ 0 := by
    intro hz
    rcases ENNReal.rpow_eq_zero_iff.mp hz with h | h
    · exact he0 h.1
    · exact (not_lt_of_ge (one_div_nonneg.mpr (zero_lt_one.trans hr).le)) h.2
  have hepowtop : e ^ (1 / r) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (one_div_nonneg.mpr (zero_lt_one.trans hr).le) het
  have hepow0' : e ^ r⁻¹ ≠ 0 := by simpa [one_div] using hepow0
  have hepowtop' : e ^ r⁻¹ ≠ ∞ := by simpa [one_div] using hepowtop
  simp only [div_eq_mul_inv]
  ring_nf
  rw [mul_assoc _ (e ^ r⁻¹) (e ^ r⁻¹)⁻¹]
  rw [ENNReal.mul_inv_cancel hepow0' hepowtop']
  simp only [mul_one]
  rw [mul_assoc _ (2048 ^ r⁻¹) (m ^ r⁻¹),
    mul_comm (2048 ^ r⁻¹) (m ^ r⁻¹),
    ← mul_assoc _ (m ^ r⁻¹) (2048 ^ r⁻¹)]
  rw [mul_assoc _ (m ^ (holderConjugate r)⁻¹) (m ^ r⁻¹)]
  rw [← ENNReal.rpow_add _ _ hm0 hmt]
  have hinv : (holderConjugate r)⁻¹ + r⁻¹ = 1 := by
    simpa [one_div] using inv_holderConjugate_add_inv hr
  rw [hinv, ENNReal.rpow_one]
  have hcoef_norm : holderConjugate r * (-1 + holderConjugate r)⁻¹ * 4 =
      4 * holderConjugate r / (holderConjugate r - 1) := by
    field_simp; ring
  rw [hcoef_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (p := (holderConjugate r)⁻¹)
      hcoef (inv_nonneg.mpr hq.le)]
  rw [show (2048 : ℝ≥0∞) = ENNReal.ofReal (2048 : ℝ) by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg (p := r⁻¹)
      (by norm_num : (0 : ℝ) ≤ 2048) (inv_nonneg.mpr (zero_lt_one.trans hr).le)]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg (p := r * p⁻¹)
      (by norm_num : (0 : ℝ) ≤ 4)
      (mul_nonneg (zero_lt_one.trans hr).le (inv_nonneg.mpr (zero_lt_one.trans hp).le))]
  rw [← ENNReal.ofReal_mul
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)]
  have hHL' : 0 ≤ centeredHardyLittlewoodRpowConstant (r * p⁻¹) := by
    simpa [div_eq_mul_inv] using hHL
  rw [ENNReal.ofReal_rpow_of_nonneg
      (x := 4 ^ (r * p⁻¹) * centeredHardyLittlewoodRpowConstant (r * p⁻¹))
      (p := r⁻¹) (mul_nonneg
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _) hHL')
      (inv_nonneg.mpr (zero_lt_one.trans hr).le)]
  rw [← ENNReal.ofReal_toReal hmt]
  rw [show (32 : ℝ≥0∞) = ENNReal.ofReal 32 by norm_num]
  simp only [finiteSparseRawFactor]
  repeat' rw [← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    hcoef]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hqmul : holderConjugate r * (1 / holderConjugate r) = 1 := by
    field_simp [hq.ne']
  rw [hqmul, Real.rpow_one]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  simp only [div_eq_mul_inv]
  ring

/-- The constants generated by the two maximal-function excisions are
controlled by the four-factor expression already optimized in
`FiniteSparseMaximal`. The numerical constant is deliberately coarse and
universal. -/
theorem finiteSparseRawFactor_le
    {p r : ℝ} (hp : 1 < p) (hr : 1 < r) (hpr : p < r) (hr4 : r ≤ 4) :
    finiteSparseRawFactor p r ≤
      (2 : ℝ) ^ 36 * r ^ (1 / holderConjugate r) *
        (r / (r - p)) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hq : 1 < holderConjugate r := one_lt_holderConjugate_of_one_lt hr
  have hq0 : 0 < holderConjugate r := zero_lt_one.trans hq
  have hqinv0 : 0 ≤ 1 / holderConjugate r := one_div_nonneg.mpr hq0.le
  have hqinv1 : 1 / holderConjugate r ≤ 1 := (div_le_one hq0).2 hq.le
  have hs : 1 < r / p := (lt_div_iff₀ hp0).2 (by simpa using hpr)
  have hs0 : 0 ≤ r / p := (zero_lt_one.trans hs).le
  have hs4 : r / p ≤ 4 := by
    rw [div_le_iff₀ hp0]
    nlinarith
  have hs_sub : 0 ≤ r / p - 1 := sub_nonneg.mpr hs.le
  have hs_sub3 : r / p - 1 ≤ 3 := by linarith
  have htwo : (2 : ℝ) ^ (r / p - 1) ≤ 8 := by
    calc
      (2 : ℝ) ^ (r / p - 1) ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_sub3
      _ = 8 := by norm_num
  have hgap0 : 0 ≤ r / (r - p) :=
    div_nonneg hr0.le (sub_nonneg.mpr hpr.le)
  have hgap1 : 1 ≤ r / (r - p) := by
    rw [le_div_iff₀ (sub_pos.mpr hpr)]
    linarith
  have hsminus : (r / p - 1)⁻¹ = p / (r - p) := by
    field_simp [hp0.ne', (sub_pos.mpr hpr).ne']
  have hp_gap_le : p / (r - p) ≤ r / (r - p) :=
    div_le_div_of_nonneg_right hpr.le (sub_pos.mpr hpr).le
  have hHL : centeredHardyLittlewoodRpowConstant (r / p) ≤
      256 * (r / (r - p)) := by
    rw [centeredHardyLittlewoodRpowConstant]
    have hden : 0 < r / p - 1 := sub_pos.mpr hs
    calc
      8 * (r / p) * ((2 : ℝ) ^ (r / p - 1) / (r / p - 1)) ≤
          8 * 4 * (8 / (r / p - 1)) := by gcongr
      _ = 256 * (r / p - 1)⁻¹ := by field_simp; ring
      _ ≤ 256 * (r / (r - p)) := by
        rw [hsminus]
        gcongr
  have hfirst :
      ((4 : ℝ) ^ holderConjugate r *
        (4 * holderConjugate r / (holderConjugate r - 1))) ^
          (1 / holderConjugate r) ≤
        64 * r ^ (1 / holderConjugate r) := by
    rw [mul_div_assoc, holderConjugate_ratio hr]
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hmul : holderConjugate r * (1 / holderConjugate r) = 1 := by
      field_simp [hq0.ne']
    rw [hmul, Real.rpow_one]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le]
    have hfourpow : (4 : ℝ) ^ (1 / holderConjugate r) ≤ 4 :=
      Real.rpow_le_self_of_one_le (by norm_num) hqinv1
    have hrrpow : 0 ≤ r ^ (1 / holderConjugate r) := Real.rpow_nonneg hr0.le _
    have hprod := mul_le_mul_of_nonneg_right hfourpow hrrpow
    nlinarith
  have hrinv0 : 0 ≤ 1 / r := one_div_nonneg.mpr hr0.le
  have hrinv1 : 1 / r ≤ 1 := (div_le_one hr0).2 hr.le
  have hinvpr : 1 / r ≤ 1 / p := one_div_le_one_div_of_le hp0 hpr.le
  have hfourS : (4 : ℝ) ^ (r / p) ≤ 256 := by
    calc
      (4 : ℝ) ^ (r / p) ≤ (4 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs4
      _ = 256 := by norm_num
  have hsecond :
      ((4 : ℝ) ^ (r / p) * centeredHardyLittlewoodRpowConstant (r / p)) ^
          (1 / r) ≤
        65536 * (r / (r - p)) ^ (1 / p) := by
    have hHLpos : 0 ≤ centeredHardyLittlewoodRpowConstant (r / p) :=
      (centeredHardyLittlewoodRpowConstant_pos hs).le
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) hHLpos]
    calc
      ((4 : ℝ) ^ (r / p)) ^ (1 / r) *
          centeredHardyLittlewoodRpowConstant (r / p) ^ (1 / r) ≤
          256 ^ (1 / r) * (256 * (r / (r - p))) ^ (1 / r) := by
            exact mul_le_mul
              (Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hfourS hrinv0)
              (Real.rpow_le_rpow hHLpos hHL hrinv0)
              (Real.rpow_nonneg hHLpos _) (Real.rpow_nonneg (by norm_num) _)
      _ = 256 ^ (1 / r) *
          (256 ^ (1 / r) * (r / (r - p)) ^ (1 / r)) := by
            rw [Real.mul_rpow (by norm_num) hgap0]
      _ ≤ 256 * (256 * (r / (r - p)) ^ (1 / p)) := by
            gcongr
            · exact Real.rpow_le_self_of_one_le (by norm_num) hrinv1
            · exact Real.rpow_le_self_of_one_le (by norm_num) hrinv1
      _ = 65536 * (r / (r - p)) ^ (1 / p) := by ring
  have h2048 : (2048 : ℝ) ^ (1 / r) ≤ 2048 :=
    Real.rpow_le_self_of_one_le (by norm_num) hrinv1
  unfold finiteSparseRawFactor
  have hfirst0 : 0 ≤
      ((4 : ℝ) ^ holderConjugate r *
        (4 * holderConjugate r / (holderConjugate r - 1))) ^
          (1 / holderConjugate r) := Real.rpow_nonneg (mul_nonneg
            (Real.rpow_nonneg (by norm_num) _)
            (div_nonneg (mul_nonneg (by norm_num) hq0.le) (sub_nonneg.mpr hq.le))) _
  have hsecond0 : 0 ≤
      ((4 : ℝ) ^ (r / p) * centeredHardyLittlewoodRpowConstant (r / p)) ^
          (1 / r) := Real.rpow_nonneg (mul_nonneg
            (Real.rpow_nonneg (by norm_num) _)
            (centeredHardyLittlewoodRpowConstant_pos hs).le) _
  calc
    8 * ((4 : ℝ) ^ holderConjugate r *
          (4 * holderConjugate r / (holderConjugate r - 1))) ^
            (1 / holderConjugate r) *
        ((4 : ℝ) ^ (r / p) * centeredHardyLittlewoodRpowConstant (r / p)) ^
            (1 / r) *
          2048 ^ (1 / r) ≤
        8 * (64 * r ^ (1 / holderConjugate r)) *
          (65536 * (r / (r - p)) ^ (1 / p)) * 2048 := by
            gcongr
    _ = (2 : ℝ) ^ 36 * r ^ (1 / holderConjugate r) *
          (r / (r - p)) ^ (1 / p) := by norm_num; ring

/-- The compact-level estimate after the exact normalization has been
performed. -/
theorem finiteMaxRep_compact_level_bound_normalized
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A)
    {p r ε a : ℝ} (hp : 1 < p) (hp2 : p < 2) (hr : 1 < r)
    (hpr : p < r) (hε : 0 < ε)
    (f : L0Infinity) (K E : Set ℝ) (hK : IsCompact K)
    (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hElevel : E ⊆ {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x})
    (hmassZero : (∫⁻ y, ‖f y‖ₑ) ≠ 0) (hEzero : volume E ≠ 0) :
    ENNReal.ofReal a * (volume E / 2) ≤
      ENNReal.ofReal
        ((A * holderConjugate p + ε) * finiteSparseRawFactor p r *
          (∫⁻ y, ‖f y‖ₑ).toReal *
          ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
  let mass : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ
  let b : ℝ := (2048 * mass / volume E).toReal
  let common : ℝ≥0∞ :=
    8 *
      ((4 : ℝ≥0∞) ^ holderConjugate r *
        (ENNReal.ofReal (4 * holderConjugate r /
            (holderConjugate r - 1)) * mass *
          ENNReal.ofReal (b ^ (holderConjugate r - 1)))) ^
            (1 / holderConjugate r) *
      ((4 : ℝ≥0∞) ^ (r / p) *
        ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p))) ^
          (1 / r)
  have hmassTop : mass ≠ ∞ := by
    have hfhi := hasFiniteIntegral_iff_enorm.mp
      f.integrable_finiteSparseProof.hasFiniteIntegral
    exact ne_of_lt (by simpa [mass] using hfhi)
  have hEtop : volume E ≠ ∞ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hEK)
  have hbase := finiteMaxRep_compact_level_bound n T A hT hp hp2 hr hpr hε
    f K E hK hE hEK hElevel hmassZero hEzero
  have hnorm := finiteSparse_common_normalization hp hr hpr mass (volume E)
    hmassZero hmassTop hEzero hEtop
    (((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC : 0 ≤ A * holderConjugate p + ε := by
    have hA := hT.1
    have hpconj : 0 ≤ holderConjugate p :=
      (holderConjugate_spec hp).symm.pos.le
    positivity
  change ENNReal.ofReal a * (volume E / 2) ≤ _
  have hbase' : ENNReal.ofReal a * (volume E / 2) ≤
      ENNReal.ofReal (A * holderConjugate p + ε) * common *
        ENNReal.ofReal ((volume E).toReal ^ (1 / r) *
          ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
    simpa only [mass, b, common] using hbase
  calc
    ENNReal.ofReal a * (volume E / 2) ≤
        ENNReal.ofReal (A * holderConjugate p + ε) * common *
          ENNReal.ofReal ((volume E).toReal ^ (1 / r) *
            ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := hbase'
    _ = ENNReal.ofReal (A * holderConjugate p + ε) *
          ENNReal.ofReal (finiteSparseRawFactor p r * mass.toReal *
            ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) := by
      rw [mul_assoc, hnorm]
    _ = _ := by
      rw [← ENNReal.ofReal_mul hC]
      congr 1
      dsimp only [mass]
      ring

theorem finiteSparse_normalized_factor_le
    {N : ℕ} {A p r ε : ℝ} (hA : 0 ≤ A) (hp : 1 < p) (hr : 1 < r)
    (hpr : p < r) (hr4 : r ≤ 4) (hε : 0 < ε) :
    2 * (A * holderConjugate p + ε) * finiteSparseRawFactor p r *
        (N : ℝ) ^ (1 / holderConjugate r) ≤
      (2 : ℝ) ^ 37 * (A + ε) * finiteSparseFactor N p r := by
  have hpconj : 1 < holderConjugate p := one_lt_holderConjugate_of_one_lt hp
  have hcoef : A * holderConjugate p + ε ≤
      (A + ε) * holderConjugate p := by
    nlinarith
  have hraw := finiteSparseRawFactor_le hp hr hpr hr4
  have hNpow : 0 ≤ (N : ℝ) ^ (1 / holderConjugate r) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hraw0 : 0 ≤ finiteSparseRawFactor p r := by
    unfold finiteSparseRawFactor
    have hs : 1 < r / p := (lt_div_iff₀ (zero_lt_one.trans hp)).2 (by simpa using hpr)
    have hq : 1 < holderConjugate r := one_lt_holderConjugate_of_one_lt hr
    have hb1 : 0 ≤ (4 : ℝ) ^ holderConjugate r *
        (4 * holderConjugate r / (holderConjugate r - 1)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hq.le))
          (sub_nonneg.mpr hq.le))
    have hb2 : 0 ≤ (4 : ℝ) ^ (r / p) *
        centeredHardyLittlewoodRpowConstant (r / p) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (centeredHardyLittlewoodRpowConstant_pos hs).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hb1 _)) (Real.rpow_nonneg hb2 _))
      (Real.rpow_nonneg (by norm_num) _)
  have hright0 : 0 ≤ r ^ (1 / holderConjugate r) *
      (r / (r - p)) ^ (1 / p) := by positivity
  have hnewcoef0 : 0 ≤ 2 * ((A + ε) * holderConjugate p) := by positivity
  rw [finiteSparseFactor]
  calc
    2 * (A * holderConjugate p + ε) * finiteSparseRawFactor p r *
        (N : ℝ) ^ (1 / holderConjugate r) ≤
      2 * ((A + ε) * holderConjugate p) *
        ((2 : ℝ) ^ 36 * r ^ (1 / holderConjugate r) *
          (r / (r - p)) ^ (1 / p)) *
        (N : ℝ) ^ (1 / holderConjugate r) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hraw
              hraw0 hnewcoef0) hNpow
    _ = (2 : ℝ) ^ 37 * (A + ε) *
        (holderConjugate p * r ^ (1 / holderConjugate r) *
          (r / (r - p)) ^ (1 / p) *
          (N : ℝ) ^ (1 / holderConjugate r)) := by norm_num; ring

/-- Compact superlevels satisfy the optimized bound, with a positive slack
only in the sparse-norm coefficient. -/
theorem finiteMaxRep_compact_level_bound_optimized
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A)
    {p r ε a : ℝ} (hp : 1 < p) (hp2 : p < 2) (hr : 1 < r)
    (hpr : p < r) (hr4 : r ≤ 4) (hε : 0 < ε)
    (f : L0Infinity) (K E : Set ℝ) (hK : IsCompact K)
    (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hElevel : E ⊆ {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x})
    (hmassZero : (∫⁻ y, ‖f y‖ₑ) ≠ 0) (hEzero : volume E ≠ 0) :
    ENNReal.ofReal a * volume E ≤
      ENNReal.ofReal
        ((2 : ℝ) ^ 37 * (A + ε) * finiteSparseFactor (n + 1) p r) *
          ∫⁻ y, ‖f y‖ₑ := by
  have hhalf := finiteMaxRep_compact_level_bound_normalized n T A hT hp hp2 hr
    hpr hε f K E hK hE hEK hElevel hmassZero hEzero
  have hfactor := finiteSparse_normalized_factor_le (N := n + 1) hT.1 hp hr hpr hr4 hε
  have hmassTop : (∫⁻ y, ‖f y‖ₑ) ≠ ∞ := by
    exact ne_of_lt (hasFiniteIntegral_iff_enorm.mp
      f.integrable_finiteSparseProof.hasFiniteIntegral)
  have hmassReal0 : 0 ≤ (∫⁻ y, ‖f y‖ₑ).toReal := ENNReal.toReal_nonneg
  have hraw0 : 0 ≤ finiteSparseRawFactor p r := by
    unfold finiteSparseRawFactor
    have hs : 1 < r / p := (lt_div_iff₀ (zero_lt_one.trans hp)).2 (by simpa using hpr)
    have hq : 1 < holderConjugate r := one_lt_holderConjugate_of_one_lt hr
    have hb1 : 0 ≤ (4 : ℝ) ^ holderConjugate r *
        (4 * holderConjugate r / (holderConjugate r - 1)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hq.le))
          (sub_nonneg.mpr hq.le))
    have hb2 : 0 ≤ (4 : ℝ) ^ (r / p) *
        centeredHardyLittlewoodRpowConstant (r / p) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (centeredHardyLittlewoodRpowConstant_pos hs).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hb1 _)) (Real.rpow_nonneg hb2 _))
      (Real.rpow_nonneg (by norm_num) _)
  have hcoef0 : 0 ≤ A * holderConjugate p + ε := by
    have hpconj : 0 ≤ holderConjugate p := (holderConjugate_spec hp).symm.pos.le
    exact add_nonneg (mul_nonneg hT.1 hpconj) hε.le
  have hfiniteFactor0 : 0 ≤ finiteSparseFactor (n + 1) p r := by
    unfold finiteSparseFactor
    have hpconj : 0 ≤ holderConjugate p := (holderConjugate_spec hp).symm.pos.le
    have hgap : 0 ≤ r / (r - p) :=
      div_nonneg (zero_lt_one.trans hr).le (sub_nonneg.mpr hpr.le)
    exact mul_nonneg (mul_nonneg (mul_nonneg hpconj (Real.rpow_nonneg
      (zero_lt_one.trans hr).le _)) (Real.rpow_nonneg hgap _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    ENNReal.ofReal a * volume E =
        (ENNReal.ofReal a * (volume E / 2)) * 2 := by
      rw [mul_assoc, ENNReal.div_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    _ ≤ ENNReal.ofReal
          ((A * holderConjugate p + ε) * finiteSparseRawFactor p r *
            (∫⁻ y, ‖f y‖ₑ).toReal *
            ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r)) * 2 :=
      mul_le_mul' hhalf le_rfl
    _ = ENNReal.ofReal
          (2 * (A * holderConjugate p + ε) * finiteSparseRawFactor p r *
            ((n + 1 : ℕ) : ℝ) ^ (1 / holderConjugate r) *
            (∫⁻ y, ‖f y‖ₑ).toReal) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (mul_nonneg
          (mul_nonneg (mul_nonneg hcoef0 hraw0) hmassReal0)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
      congr 1
      ring
    _ ≤ ENNReal.ofReal
          (((2 : ℝ) ^ 37 * (A + ε) * finiteSparseFactor (n + 1) p r) *
            (∫⁻ y, ‖f y‖ₑ).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hfactor hmassReal0
    _ = ENNReal.ofReal
          ((2 : ℝ) ^ 37 * (A + ε) * finiteSparseFactor (n + 1) p r) *
          ∫⁻ y, ‖f y‖ₑ := by
      rw [ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (by positivity) (add_nonneg hT.1 hε.le)) hfiniteFactor0),
        ENNReal.ofReal_toReal hmassTop]

theorem localAverage_one_eq_zero_of_ae_eq_zero
    {f : ℝ → ℂ} (hf : f =ᵐ[volume] 0) (I : RealInterval) :
    localAverage 1 f I = 0 := by
  have hnorm : (fun x ↦ ‖f x‖) =ᵐ[volume] 0 := by
    filter_upwards [hf] with x hx
    simp [hx]
  have hnormI : (fun x ↦ ‖f x‖) =ᵐ[volume.restrict I.carrier] 0 :=
    ae_restrict_le hnorm
  unfold localAverage
  have hint : ∫ x in I.carrier, ‖f x‖ ^ (1 : ℝ) = 0 := by
    calc
      ∫ x in I.carrier, ‖f x‖ ^ (1 : ℝ) =
          ∫ _x in I.carrier, (0 : ℝ) := integral_congr_ae (by
            filter_upwards [hnormI] with x hx
            simp [hx])
      _ = 0 := by simp
  rw [hint]
  simp

theorem sparseForm_eq_zero_of_ae_eq_zero
    {p : ℝ} {f : ℝ → ℂ} (hf : f =ᵐ[volume] 0) (g : ℝ → ℂ)
    (S : Set RealInterval) : sparseForm p f g S = 0 := by
  classical
  unfold sparseForm
  rw [ENNReal.tsum_eq_zero]
  intro I
  simp [localAverage_one_eq_zero_of_ae_eq_zero hf I.1]

/-- Zero input mass forces every member of a finite sparse-bounded family to
vanish almost everywhere. This treats the normalization-degenerate case
without dividing by the mass. -/
theorem finiteMaxRep_ae_eq_zero_of_mass_zero
    {N : ℕ} (T : Fin N → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A) (f : L0Infinity)
    (hmass : ∫⁻ y, ‖f y‖ₑ = 0) :
    measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) =ᵐ[volume] 0 := by
  classical
  have hfzero : (f : ℝ → ℂ) =ᵐ[volume] 0 := by
    have henorm := (lintegral_eq_zero_iff f.measurable_toFun.enorm).mp hmass
    filter_upwards [henorm] with x hx
    exact enorm_eq_zero.mp hx
  have hTzero (j : Fin N) : T j f =ᵐ[volume] 0 := by
    have hlocal := hT.2.1 j f
    have hp : (1 : ℝ) < 3 / 2 := by norm_num
    have hp2 : (3 / 2 : ℝ) < 2 := by norm_num
    have hsparse := hT.hasSparseOnePBound_add hp hp2 j (by norm_num : (0 : ℝ) < 1)
    have hball (n : ℕ) : T j f =ᵐ[volume.restrict (Metric.closedBall 0 n)] 0 := by
      let K : Set ℝ := Metric.closedBall 0 n
      have hK : IsCompact K := isCompact_closedBall (0 : ℝ) n
      have hKm : MeasurableSet K := measurableSet_closedBall
      let g := setIndicatorL0Infinity K K hKm hK (Subset.rfl)
      rcases hsparse f g with ⟨S, hS, hpair⟩
      have hform : sparseForm (3 / 2) f g S = 0 :=
        sparseForm_eq_zero_of_ae_eq_zero hfzero g S
      have hpair0 : operatorPairing (absoluteValueOperator (T j)) f g = 0 := by
        have : ENNReal.ofReal
            ‖operatorPairing (absoluteValueOperator (T j)) f g‖ ≤ 0 := by
          simpa [hform] using hpair
        exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp (bot_unique this))
          (norm_nonneg _))
      have hint : ∫ x in K, ‖T j f x‖ = 0 := by
        have hnormpair := norm_operatorPairing_absolute_indicator (T j) f K K
          hKm hK (Subset.rfl)
        simpa [g, hpair0] using hnormpair.symm
      have hintable : IntegrableOn (fun x ↦ ‖T j f x‖) K :=
        ((hlocal.integrableOn_isCompact hK).norm)
      exact (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun _ ↦ norm_nonneg _) hintable).mp hint
        |>.mono fun x hx ↦ norm_eq_zero.mp hx
    have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
        x ∈ Metric.closedBall (0 : ℝ) n → T j f x = 0 := by
      rw [ae_all_iff]
      intro n
      exact (ae_restrict_iff' measurableSet_closedBall).mp (hball n)
    filter_upwards [hall] with x hx
    have hxuniv : x ∈ ⋃ n : ℕ, Metric.closedBall (0 : ℝ) n := by
      rw [Metric.iUnion_closedBall_nat]
      trivial
    rcases Set.mem_iUnion.mp hxuniv with ⟨n, hn⟩
    exact hx n hn
  have hrepzero (j : Fin N) :
      (hT.2.1 j f).aestronglyMeasurable.mk (T j f) =ᵐ[volume] 0 :=
    (hT.2.1 j f).aestronglyMeasurable.ae_eq_mk.symm.trans (hTzero j)
  filter_upwards [ae_all_iff.mpr hrepzero] with x hx
  unfold measurableFiniteMaxRep
  simp [hx]

theorem finiteMaxRep_level_bound_optimized
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A)
    {p r ε a : ℝ} (hp : 1 < p) (hp2 : p < 2) (hr : 1 < r)
    (hpr : p < r) (hr4 : r ≤ 4) (hε : 0 < ε) (ha : 0 < a)
    (f : L0Infinity) :
    ENNReal.ofReal a * volume
        {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x} ≤
      ENNReal.ofReal
        ((2 : ℝ) ^ 37 * (A + ε) * finiteSparseFactor (n + 1) p r) *
          ∫⁻ y, ‖f y‖ₑ := by
  let u := measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f)
  have hu : Measurable u := measurable_measurableFiniteMaxRep T f _
  apply mul_measure_level_le_of_closedBall u hu _
  intro k
  let K : Set ℝ := Metric.closedBall 0 k
  let E : Set ℝ := {x | a < u x} ∩ K
  have hK : IsCompact K := isCompact_closedBall (0 : ℝ) k
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const hu).inter measurableSet_closedBall
  have hEK : E ⊆ K := inter_subset_right
  have hElevel : E ⊆ {x | a < u x} := inter_subset_left
  by_cases hmass : ∫⁻ y, ‖f y‖ₑ = 0
  · have hzero := finiteMaxRep_ae_eq_zero_of_mass_zero T A hT f hmass
    have hlevelzero : volume {x | a < u x} = 0 := by
      have hae : {x | a < u x} =ᵐ[volume] (∅ : Set ℝ) := by
        filter_upwards [hzero] with x hx
        have hx' : u x = 0 := by simpa [u] using hx
        apply propext
        change (a < u x ↔ False)
        rw [hx']
        simp [not_lt_of_ge ha.le]
      simpa using hae.measure_eq
    have hEz : volume E = 0 := measure_mono_null hElevel hlevelzero
    change ENNReal.ofReal a * volume E ≤ _
    rw [hEz, mul_zero]
    exact bot_le
  · by_cases hEzero : volume E = 0
    · change ENNReal.ofReal a * volume E ≤ _
      rw [hEzero, mul_zero]
      exact bot_le
    · exact finiteMaxRep_compact_level_bound_optimized n T A hT hp hp2 hr hpr
        hr4 hε f K E hK hE hEK hElevel hmass hEzero

/-- Explicit universal constant delivered by the proof. -/
noncomputable def finiteSparseMaximalUniversalConstant : ℝ :=
  (2 : ℝ) ^ 37 * 50 * Real.exp 3

theorem finiteSparseMaximalUniversalConstant_pos :
    0 < finiteSparseMaximalUniversalConstant := by
  unfold finiteSparseMaximalUniversalConstant
  positivity

theorem finiteMaxRep_level_bound_logarithmic_add
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A) {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (f : L0Infinity) :
    ENNReal.ofReal a * volume
        {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x} ≤
      ENNReal.ofReal (finiteSparseMaximalUniversalConstant * (A + ε) *
        paperLog 1 (n + 1) ^ 2) * ∫⁻ y, ‖f y‖ₑ := by
  let L := safeLogScale (n + 1)
  let p := logarithmicP L
  let r := logarithmicR L
  have hL : 4 < L := four_lt_safeLogScale (n + 1)
  have hp : 1 < p := one_lt_logarithmicP hL
  have hp2 : p < 2 := logarithmicP_lt_two hL
  have hr : 1 < r := one_lt_logarithmicR hL
  have hpr : p < r := logarithmicP_lt_logarithmicR hL
  have hr4 : r ≤ 4 := logarithmicR_le_four hL
  have hbase := finiteMaxRep_level_bound_optimized n T A hT hp hp2 hr hpr hr4 hε ha f
  have hfactor := finiteSparseFactor_paperLog_le_all (n + 1)
  have hAeps : 0 ≤ A + ε := add_nonneg hT.1 hε.le
  calc
    ENNReal.ofReal a * volume
        {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x} ≤
      ENNReal.ofReal ((2 : ℝ) ^ 37 * (A + ε) *
        finiteSparseFactor (n + 1) p r) * ∫⁻ y, ‖f y‖ₑ := hbase
    _ ≤ ENNReal.ofReal (finiteSparseMaximalUniversalConstant * (A + ε) *
        paperLog 1 (n + 1) ^ 2) * ∫⁻ y, ‖f y‖ₑ := by
      apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      dsimp only [p, r, L]
      unfold finiteSparseMaximalUniversalConstant
      calc
        (2 : ℝ) ^ 37 * (A + ε) *
            finiteSparseFactor (n + 1)
              (logarithmicP (safeLogScale (n + 1)))
              (logarithmicR (safeLogScale (n + 1))) ≤
          (2 : ℝ) ^ 37 * (A + ε) *
            (50 * Real.exp 3 * paperLog 1 (n + 1) ^ 2) := by
              gcongr
              simpa [Nat.cast_add, Nat.cast_one] using hfactor
        _ = (2 : ℝ) ^ 37 * 50 * Real.exp 3 * (A + ε) *
            paperLog 1 (n + 1) ^ 2 := by ring

theorem finiteMaxRep_level_bound_logarithmic
    (n : ℕ) (T : Fin (n + 1) → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A) {a : ℝ} (ha : 0 < a)
    (f : L0Infinity) :
    ENNReal.ofReal a * volume
        {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x} ≤
      ENNReal.ofReal (finiteSparseMaximalUniversalConstant * A *
        paperLog 1 (n + 1) ^ 2) * ∫⁻ y, ‖f y‖ₑ := by
  let lhs : ℝ≥0∞ := ENNReal.ofReal a * volume
    {x | a < measurableFiniteMaxRep T f (fun j ↦ hT.2.1 j f) x}
  let mass : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ
  let c : ℝ := finiteSparseMaximalUniversalConstant
  let l : ℝ := paperLog 1 (n + 1) ^ 2
  have hc : Continuous (fun ε : ℝ ↦ c * (A + ε) * l) := by fun_prop
  have heps : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hct : Tendsto (fun k : ℕ ↦ c * (A + (1 : ℝ) / (k + 1)) * l)
      atTop (nhds (c * A * l)) := by
    simpa [Function.comp_def] using (hc.tendsto 0).comp heps
  have henn : Tendsto
      (fun k : ℕ ↦ ENNReal.ofReal (c * (A + (1 : ℝ) / (k + 1)) * l))
      atTop (nhds (ENNReal.ofReal (c * A * l))) :=
    ENNReal.tendsto_ofReal hct
  have hmassTop : mass ≠ ∞ := by
    exact ne_of_lt (hasFiniteIntegral_iff_enorm.mp
      f.integrable_finiteSparseProof.hasFiniteIntegral)
  have hlim := ENNReal.Tendsto.mul henn (Or.inr hmassTop) tendsto_const_nhds
    (Or.inr ENNReal.ofReal_ne_top)
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun k ↦
    finiteMaxRep_level_bound_logarithmic_add n T A hT (by positivity) ha f

/-- Operational form of paper Lemma `l:weak11sparse`: the finite maximum
itself, rather than merely the infimum defining its weak norm, satisfies the
distribution inequality with one universal constant. -/
theorem finiteSparseMaximal_hasWeakOneOneBound
    {N : ℕ} (T : Fin N → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A) :
    HasWeakOneOneBound
      (finiteSparseMaximalUniversalConstant * A * paperLog 1 N ^ 2)
      (finiteMax T) := by
  intro f a ha
  cases N with
  | zero =>
      simp [finiteMax, not_lt_of_ge ha.le]
  | succ n =>
      let hlocal : ∀ j, LocallyIntegrable (T j f) volume := fun j ↦ hT.2.1 j f
      have hae := finiteMax_ae_eq_measurableFiniteMaxRep T f hlocal
      have hsets : {x | a < finiteMax T f x} =ᵐ[volume]
          {x | a < measurableFiniteMaxRep T f hlocal x} := by
        filter_upwards [hae] with x hx
        rw [hx]
      rw [hsets.measure_eq]
      simpa only [hlocal, Nat.cast_add, Nat.cast_one] using
        finiteMaxRep_level_bound_logarithmic n T A hT ha f

/-- Universal operational witness, in a definitionally equivalent form to
`KrauseLaceyLacunaryBlock.HasFiniteSparseMaximalWeakBound`. -/
theorem exists_finiteSparseMaximal_hasWeakOneOneBound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} (T : Fin N → TestOperator) (A : ℝ),
      FiniteSparseMaximalHypothesis T A →
        HasWeakOneOneBound (K * A * paperLog 1 N ^ 2) (finiteMax T) := by
  refine ⟨finiteSparseMaximalUniversalConstant,
    finiteSparseMaximalUniversalConstant_pos.le, ?_⟩
  intro N T A hT
  exact finiteSparseMaximal_hasWeakOneOneBound T A hT

theorem finiteSparseMaximal_weakOneOneNorm_le
    {N : ℕ} (T : Fin N → TestOperator) (A : ℝ)
    (hT : FiniteSparseMaximalHypothesis T A) :
    weakOneOneNorm (finiteMax T) ≤
      finiteSparseMaximalUniversalConstant * A * paperLog 1 N ^ 2 := by
  apply weakOneOneNorm_le_of_hasWeakOneOneBound
  · exact mul_nonneg (mul_nonneg finiteSparseMaximalUniversalConstant_pos.le hT.1)
      (paperLog_one_sq_nonneg N)
  · exact finiteSparseMaximal_hasWeakOneOneBound T A hT

/-- Paper Lemma `l:weak11sparse`, including the absolute placement of the
constant outside all family quantifiers. -/
theorem weak11sparseStatement_proof : weak11sparseStatement := by
  refine ⟨finiteSparseMaximalUniversalConstant,
    finiteSparseMaximalUniversalConstant_pos, ?_⟩
  intro N T A hT
  exact finiteSparseMaximal_weakOneOneNorm_le T A hT

end QuadraticCarleson
