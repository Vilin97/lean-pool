/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodBoundaryControl
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftAction
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseReflection

/-!
# Finite three-grid reduction for Hardy--Littlewood sparse domination

Finite rational-radius maxima on the support of the testing input reduce
to three actual finite laminar interval maxima. The radius enlargement
costs eight, independently of the number of radii. Monotone convergence
then permits a finite approximation to the full positive pairing.
-/

open Function MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticCarleson.HardyLittlewoodSparseReduction

open KrauseLaceyThreeShiftGrid KrauseLaceySharpSmoothAdapter
open HardyLittlewoodBoundaryControl KrauseLaceySparseReflection


noncomputable
section

/-- The supremum of the norm averages over members of `S` containing the evaluation point. -/
def finiteIntervalMaximal (S : Finset RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ I ∈ S, ⨆ (_ : x ∈ I.carrier), ENNReal.ofReal (localAverage 1 f I)

/-- The centered maximal average of the norm of `f`, restricted to the finite set of positive
rational radii `s`. -/
def finiteCenteredMaximal (s : Finset PositiveRational) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q ∈ s, centeredAverage (q : ℝ) (fun y ↦ ‖f y‖ₑ) x

theorem closedBall_subset_carrier_of_mem_centralThird
    (I : RealInterval) {x r : ℝ} (hx : x ∈ I.centralThird)
    (hr : 3 * r < I.length) : closedBall x r ⊆ I.carrier := by
  intro y hy
  rw [mem_closedBall, Real.dist_eq, abs_le] at hy
  change (2 * I.left + I.right) / 3 < x ∧
    x ≤ (I.left + 2 * I.right) / 3 at hx
  change I.left < y ∧ y ≤ I.right
  dsimp [RealInterval.length] at hr
  constructor <;> linarith

/-- A ball contained in an interval of at most eight times its length is
controlled by eight times that interval's normalized average. -/
theorem centeredAverage_le_eight_intervalAverage
    (f : L0Infinity) (I : RealInterval) {x r : ℝ} (hr : 0 < r)
    (hsub : closedBall x r ⊆ I.carrier) (hlen : I.length ≤ 16 * r) :
    centeredAverage r (fun y ↦ ‖f y‖ₑ) x ≤
      8 * ENNReal.ofReal (localAverage 1 f I) := by
  have hd : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hI : ENNReal.ofReal I.length ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr I.length_pos
  have hav := ofReal_localAverage_one_eq f I f.integrable.integrableOn
  have hmass : (∫⁻ y in I.carrier, ‖f y‖ₑ) =
      ENNReal.ofReal (localAverage 1 f I) * ENNReal.ofReal I.length := by
    rw [hav, ENNReal.div_mul_cancel hI ENNReal.ofReal_ne_top]
  have hlen' : ENNReal.ofReal I.length ≤ 8 * ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  unfold centeredAverage
  apply (ENNReal.div_le_iff hd ENNReal.ofReal_ne_top).mpr
  calc
    _ ≤ ∫⁻ y in I.carrier, ‖f y‖ₑ := lintegral_mono_set hsub
    _ = _ := hmass
    _ ≤ ENNReal.ofReal (localAverage 1 f I) * (8 * ENNReal.ofReal (2 * r)) :=
      mul_le_mul' le_rfl hlen'
    _ = _ := by ring

/-- The dyadic grid scale chosen to cover a ball of positive rational radius `q`. -/
def radiusGridScale (q : PositiveRational) : ℤ :=
  dyadicFloorScale (q : ℝ) (by exact_mod_cast q.property) + 2

theorem radiusGridScale_bounds (q : PositiveRational) :
    8 * (q : ℝ) < (2 : ℝ) ^ (radiusGridScale q + 2) ∧
      (2 : ℝ) ^ (radiusGridScale q + 2) ≤ 16 * (q : ℝ) := by
  have hp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have heq : (2 : ℝ) ^ (radiusGridScale q + 2) = 8 * dyadicCeilRadius (q : ℝ) hp := by
    unfold radiusGridScale dyadicCeilRadius
    rw [show dyadicFloorScale (q : ℝ) hp + 2 + 2 =
      (dyadicFloorScale (q : ℝ) hp + 1) + 3 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [heq]
  constructor
  · nlinarith [lt_dyadicCeilRadius (q : ℝ) hp]
  · nlinarith [dyadicCeilRadius_le_two_mul (q : ℝ) hp]

/-- The largest grid scale associated with the radii in `s`, with value zero when `s` is empty. -/
def radiusTopScale (s : Finset PositiveRational) : ℤ :=
  if hs : s.Nonempty then s.sup' hs radiusGridScale else 0

theorem radiusGridScale_le_top {s : Finset PositiveRational} {q : PositiveRational}
    (hq : q ∈ s) : radiusGridScale q ≤ radiusTopScale s := by
  rw [radiusTopScale, dite_eq_left ⟨q, hq⟩]
  exact Finset.le_sup' radiusGridScale hq

/-- The natural-number depth of the radius scale below the common top scale. -/
def radiusDepth (s : Finset PositiveRational) (q : PositiveRational) : ℕ :=
  (radiusTopScale s - radiusGridScale q).toNat

theorem top_sub_radiusDepth {s : Finset PositiveRational} {q : PositiveRational}
    (hq : q ∈ s) : radiusTopScale s - (radiusDepth s q : ℤ) = radiusGridScale q := by
  rw [radiusDepth, Int.toNat_of_nonneg (sub_nonneg.mpr (radiusGridScale_le_top hq))]
  ring

theorem exists_mem_centralThird_of_fixedScaleInput_eq
    (S : Finset RealInterval) (g : ℝ → ℂ)
    (hinput : krauseLaceyFixedScaleInput S g = g)
    {x : ℝ} (hx : g x ≠ 0) : ∃ I ∈ S, x ∈ I.centralThird := by
  classical
  by_contra h
  apply hx
  rw [← congrFun hinput x, krauseLaceyFixedScaleInput]
  apply Finset.sum_eq_zero
  intro I hI
  exact Set.indicator_of_notMem (fun hxi ↦ h ⟨I, hI, hxi⟩) g

/-- Every finite radius maximum, when tested against a compactly supported
function, is controlled by three finite laminar interval maxima. No
sparseness or stopping estimate is assumed in this geometric reduction. -/
theorem exists_three_laminar_maxima_domination
    (s : Finset PositiveRational) (g : L0Infinity) :
    ∃ G : Fin 3 → Finset RealInterval,
      (∀ shift, Set.Pairwise (↑(G shift) : Set RealInterval) fun I J ↦
        I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) ∧
      ∀ (f : L0Infinity) (x : ℝ), g x ≠ 0 →
        finiteCenteredMaximal s f x ≤ 8 * ∑ shift : Fin 3, finiteIntervalMaximal (G shift) f x := by
  classical
  let top := radiusTopScale s
  let depths := s.image (radiusDepth s)
  obtain ⟨E, hE⟩ := exists_finiteThreeShiftFamily_localization_all_depths g top
  let G : Fin 3 → Finset RealInterval := fun shift ↦
    completeFiniteShiftGridForest top shift (depths.sup id)
      (finiteOneShiftMultiscaleAddresses depths E shift)
  refine ⟨G, fun shift ↦ completeFiniteShiftGridForest_laminar _ _ _ _, ?_⟩
  intro f x hx
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hdepth : radiusDepth s q ∈ depths := Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨I, hI, hxI⟩ := exists_mem_centralThird_of_fixedScaleInput_eq
    _ _ (hE (radiusDepth s q)).2.2 hx
  rw [finiteThreeShiftFamily_eq_biUnion] at hI
  obtain ⟨shift, _, hIshift⟩ := Finset.mem_biUnion.mp hI
  have hIG : I ∈ G shift := by
    apply finiteOneShiftMultiscaleFamily_subset_completeForest top depths E shift
      (depths.sup id) (fun d hd ↦ Finset.le_sup (f := id) hd)
    exact Finset.mem_biUnion.mpr ⟨radiusDepth s q, hdepth, hIshift⟩
  have hlen : I.length = (2 : ℝ) ^ (radiusGridScale q + 2) := by
    obtain ⟨n, _, _, rfl⟩ := mem_finiteOneShiftFamily hIshift
    rw [finiteShiftGridInterval_length_eq_scale, finiteShiftGridScale,
      finiteShiftGridDepth_interval]
    change (2 : ℝ) ^ (radiusTopScale s - (radiusDepth s q : ℤ) + 2) = _
    rw [top_sub_radiusDepth hq]
  have hrad : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have hbound := radiusGridScale_bounds q
  have hball : closedBall x (q : ℝ) ⊆ I.carrier :=
    closedBall_subset_carrier_of_mem_centralThird I hxI (by rw [hlen]; linarith [hbound.1])
  calc
    _ ≤ 8 * ENNReal.ofReal (localAverage 1 f I) :=
      centeredAverage_le_eight_intervalAverage f I hrad hball (by simpa [hlen] using hbound.2)
    _ ≤ 8 * finiteIntervalMaximal (G shift) f x := by
      apply mul_le_mul' le_rfl
      exact le_iSup_of_le I (le_iSup_of_le hIG
        (le_iSup_of_le (I.centralThird_subset_carrier hxI) le_rfl))
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      exact Finset.single_le_sum
        (f := fun shift ↦ finiteIntervalMaximal (G shift) f x)
        (fun _ _ ↦ zero_le) (Finset.mem_univ shift)

theorem measurable_finiteCenteredMaximal
    (s : Finset PositiveRational) (f : L0Infinity) :
    Measurable (finiteCenteredMaximal s f) := by
  exact Measurable.biSup (↑s : Set PositiveRational) s.countable_toSet fun q hq ↦
    measurable_centeredAverage (q : ℝ) f.measurable_toFun.enorm

theorem finiteCenteredMaximal_mono {s t : Finset PositiveRational} (hst : s ⊆ t)
    (f : ℝ → ℂ) (x : ℝ) : finiteCenteredMaximal s f x ≤ finiteCenteredMaximal t f x := by
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  exact le_iSup_of_le q (le_iSup_of_le (hst hq) le_rfl)

theorem centeredMaximal_eq_iSup_finite (f : ℝ → ℂ) (x : ℝ) :
    centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x =
      ⨆ s : Finset PositiveRational, finiteCenteredMaximal s f x := by
  exact iSup_eq_iSup_finset _

theorem lintegral_centeredMaximal_pairing_eq_iSup_finite (f g : L0Infinity) :
    (∫⁻ x, centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x * ‖g x‖ₑ) =
      ⨆ s : Finset PositiveRational, ∫⁻ x, finiteCenteredMaximal s f x * ‖g x‖ₑ := by
  simp_rw [centeredMaximal_eq_iSup_finite, ENNReal.iSup_mul]
  apply lintegral_iSup_directed_of_measurable
  · intro s
    exact (measurable_finiteCenteredMaximal s f).mul g.measurable_toFun.enorm
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      exact mul_le_mul' (finiteCenteredMaximal_mono Finset.subset_union_left f x) le_rfl
    · intro x
      exact mul_le_mul' (finiteCenteredMaximal_mono Finset.subset_union_right f x) le_rfl

theorem measurable_finiteIntervalMaximal (S : Finset RealInterval) (f : ℝ → ℂ) :
    Measurable (finiteIntervalMaximal S f) := by
  apply Measurable.biSup (↑S : Set RealInterval) S.countable_toSet
  intro I hI
  have hi : Measurable (I.carrier.indicator
      (fun _ : ℝ ↦ ENNReal.ofReal (localAverage 1 f I))) :=
    measurable_const.indicator I.measurableSet_carrier
  convert hi using 1
  funext x
  by_cases hx : x ∈ I.carrier <;> simp [hx]

/-- Normalized averages increase with the exponent. The proof uses the
probability measure obtained by dividing the interval measure by its length. -/
theorem localAverage_one_le (g : L0Infinity) (I : RealInterval) {p : ℝ} (hp : 1 ≤ p) :
    localAverage 1 g I ≤ localAverage p g I := by
  let μ : Measure ℝ := (ENNReal.ofReal I.length)⁻¹ • volume.restrict I.carrier
  have hlen : ENNReal.ofReal I.length ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr I.length_pos
  let : IsProbabilityMeasure μ := ⟨by
    simp [μ, Measure.smul_apply, ENNReal.inv_mul_cancel hlen ENNReal.ofReal_ne_top]⟩
  have hav (r : ℝ) (hr : 0 < r) : ENNReal.ofReal (localAverage r g I) = eLpNorm' g r μ := by
    rw [ofReal_localAverage_eq_rpow_lintegral r hr g I (g.integrableOn_norm_rpow I hr.le)]
    simp only [eLpNorm', μ, lintegral_smul_measure, smul_eq_mul, ENNReal.div_eq_inv_mul]
  apply (ENNReal.ofReal_le_ofReal_iff (localAverage_nonneg p g I)).mp
  rw [hav 1 (by norm_num), hav p (lt_of_lt_of_le (by norm_num) hp)]
  exact eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) hp μ
    g.measurable_toFun.aestronglyMeasurable

theorem sparseForm_one_le (f : ℝ → ℂ) (g : L0Infinity) (S : Set RealInterval)
    {p : ℝ} (hp : 1 ≤ p) : sparseForm 1 f g S ≤ sparseForm p f g S := by
  apply ENNReal.tsum_le_tsum
  intro I
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (localAverage_one_le g I.1 hp)
    (mul_nonneg I.1.length_pos.le (localAverage_nonneg 1 f I.1))

/-- Exponent transfer costs no constant. -/
theorem hasSparseOnePBound_of_one {C p : ℝ} {T : TestOperator}
    (hp : 1 ≤ p) (hT : HasSparseOnePBound C 1 T) : HasSparseOnePBound C p T := by
  intro f g
  obtain ⟨S, hS, hb⟩ := hT f g
  exact ⟨S, hS, hb.trans (mul_le_mul' le_rfl (sparseForm_one_le f g S hp))⟩

theorem isSparse_empty : IsSparse (1 / 4) (∅ : Set RealInterval) := by
  refine ⟨by norm_num, by norm_num, fun _ ↦ ∅, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro I
    exact I.2.elim
  · intro I
    exact I.2.elim

/-- A finite laminar stopping theorem transfers to the full centered
operator. Three grids cost `3`, the radius enclosure costs `8`, and
selecting a finite approximation to half the pairing costs `2`. -/
theorem hasSparseOneOneBound_centered_of_finite_laminar
    {K : ℝ}
    (hfinite : ∀ (S : Finset RealInterval) (f g : L0Infinity),
      Set.Pairwise (↑S : Set RealInterval) (fun I J ↦
        I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) →
      ∃ R : Set RealInterval, IsSparse (1 / 4) R ∧
        (∫⁻ x, finiteIntervalMaximal S f x * ‖g x‖ₑ) ≤
          ENNReal.ofReal K * sparseForm 1 f g R) :
    HasSparseOnePBound (48 * K) 1 centeredHardyLittlewoodBoundaryOperator := by
  classical
  intro f g
  let B := ENNReal.ofReal ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f g‖
  by_cases hB : B = 0
  · refine ⟨∅, isSparse_empty, ?_⟩
    change B ≤ _
    rw [hB]
    exact zero_le
  have hBi : B ≤ ∫⁻ x,
      centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x * ‖g x‖ₑ := by
    have hstar (z : ℂ) : ‖star z‖ₑ = ‖z‖ₑ := by simp [← ofReal_norm]
    have hh := enorm_integral_le_lintegral_enorm (μ := volume)
      (fun x ↦ centeredHardyLittlewoodBoundaryOperator f x * star (g x))
    simpa only [B, operatorPairing, ofReal_norm, enorm_mul,
      enorm_centeredHardyLittlewoodBoundaryOperator, hstar] using hh
  rw [lintegral_centeredMaximal_pairing_eq_iSup_finite] at hBi
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp
    ((ENNReal.half_lt_self hB (show B ≠ ∞ from ENNReal.ofReal_ne_top)).trans_le hBi)
  obtain ⟨G, hGlam, hG⟩ := exists_three_laminar_maxima_domination s g
  choose R hR hbound using fun shift ↦ hfinite (G shift) f g (hGlam shift)
  obtain ⟨shift₀, _, hmax⟩ := Finset.univ.exists_max_image
    (fun shift : Fin 3 ↦ sparseForm 1 f g (R shift)) Finset.univ_nonempty
  refine ⟨R shift₀, hR shift₀, ?_⟩
  have hdom : (∫⁻ x, finiteCenteredMaximal s f x * ‖g x‖ₑ) ≤
      8 * ∑ shift : Fin 3, ∫⁻ x, finiteIntervalMaximal (G shift) f x * ‖g x‖ₑ := by
    calc
      _ ≤ ∫⁻ x, 8 * ∑ shift : Fin 3, finiteIntervalMaximal (G shift) f x * ‖g x‖ₑ := by
        apply lintegral_mono
        intro x
        by_cases hx : g x = 0
        · simp [hx]
        · simpa only [Finset.sum_mul, mul_assoc] using mul_le_mul' (hG f x hx) le_rfl
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
        congr 1
        exact lintegral_finsetSum _ fun shift _ ↦
          (measurable_finiteIntervalMaximal (G shift) f).mul g.measurable_toFun.enorm
  have hsum : (∑ shift : Fin 3, ∫⁻ x, finiteIntervalMaximal (G shift) f x * ‖g x‖ₑ) ≤
      3 * (ENNReal.ofReal K * sparseForm 1 f g (R shift₀)) := by
    calc
      _ ≤ ∑ shift : Fin 3, ENNReal.ofReal K * sparseForm 1 f g (R shift₀) := by
        apply Finset.sum_le_sum
        intro shift _
        exact (hbound shift).trans (mul_le_mul' le_rfl (hmax shift (Finset.mem_univ shift)))
      _ = _ := by simp [nsmul_eq_mul]
  have hhalf : B ≤ 2 * ∫⁻ x, finiteCenteredMaximal s f x * ‖g x‖ₑ := by
    have hh := (ENNReal.div_le_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hs.le
    simpa only [mul_comm] using hh
  change B ≤ _
  calc
    _ ≤ 2 * (8 * (3 * (ENNReal.ofReal K * sparseForm 1 f g (R shift₀)))) :=
      hhalf.trans (mul_le_mul' le_rfl (hdom.trans (mul_le_mul' le_rfl hsum)))
    _ = ENNReal.ofReal (48 * K) * sparseForm 1 f g (R shift₀) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 48)]
      norm_num
      ring


end
end QuadraticCarleson.HardyLittlewoodSparseReduction
