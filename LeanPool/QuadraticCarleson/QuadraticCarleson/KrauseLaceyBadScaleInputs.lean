/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingExtraction
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySeparatedGeneration

/-!
# Actual bad-scale inputs in the local Krause--Lacey argument

The bad intervals are the actual maximal threshold-ten children for `f`
(the second stopping input is zero). The grouping uses the source's exact
condition `max (2^k₀) |J| = 2^ℓ`, including every smaller child at the base
scale. No cancellation is subtracted from these bad inputs.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction


open Classical in
/-- The actual source family `B(ℓ)`. -/
noncomputable def badScaleCells (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) : Finset RealInterval :=
  (stoppingChildren S f 0 I₀).filter fun J ↦ max ((2 : ℝ) ^ k₀) J.length = (2 : ℝ) ^ ℓ

open Classical in
/-- The uncancelled bad input `B_ℓ = ∑_{J∈B(ℓ)} f 1_J`. -/
noncomputable def badScaleInput (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) (x : ℝ) : ℂ :=
  ∑ J ∈ badScaleCells S f I₀ k₀ ℓ, J.carrier.indicator f x

open Classical in
theorem badScaleCells_subset (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) :
    badScaleCells S f I₀ k₀ ℓ ⊆ stoppingChildren S f 0 I₀ :=
  Finset.filter_subset _ _

open Classical in
theorem length_le_of_mem_badScaleCells
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ J : RealInterval} {k₀ ℓ : ℤ}
    (hJ : J ∈ badScaleCells S f I₀ k₀ ℓ) : J.length ≤ (2 : ℝ) ^ ℓ :=
  (le_max_right _ _).trans_eq (Finset.mem_filter.mp hJ).2

open Classical in
theorem badScaleCells_pairwiseDisjoint
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ ℓ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(badScaleCells S f I₀ k₀ ℓ) : Set RealInterval)
      (Disjoint on RealInterval.carrier) := by
  intro J hJ K hK hne
  exact stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
    (badScaleCells_subset S f I₀ k₀ ℓ hJ) (badScaleCells_subset S f I₀ k₀ ℓ hK) hne

open Classical in
theorem norm_sum_carrier_indicator_le (T : Finset RealInterval) (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑T) (Disjoint on RealInterval.carrier)) (x : ℝ) :
    ‖∑ J ∈ T, J.carrier.indicator f x‖ ≤ ‖f x‖ := by
  by_cases hex : ∃ J ∈ T, x ∈ J.carrier
  · obtain ⟨J, hJ, hxJ⟩ := hex
    rw [Finset.sum_eq_single J]
    · rw [indicator_of_mem hxJ]
    · intro K hK hKJ
      apply indicator_of_notMem
      intro hxK
      exact Set.disjoint_left.mp (hdisj hJ hK hKJ.symm) hxJ hxK
    · intro hn
      exact (hn hJ).elim
  · have hz : ∀ J ∈ T, J.carrier.indicator f x = 0 := by
      intro J hJ
      exact indicator_of_notMem (fun hx ↦ hex ⟨J, hJ, hx⟩) f
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact norm_nonneg _

open Classical in
theorem measurable_badScaleInput (S : Finset RealInterval) {f : ℝ → ℂ}
    (hf : Measurable f) (I₀ : RealInterval) (k₀ ℓ : ℤ) :
    Measurable (badScaleInput S f I₀ k₀ ℓ) := by
  exact Finset.measurable_sum _ (fun J _ ↦ hf.indicator J.measurableSet_carrier)

open Classical in
theorem integrable_badScaleInput (S : Finset RealInterval) {f : ℝ → ℂ}
    (hf : Integrable f) (I₀ : RealInterval) (k₀ ℓ : ℤ) :
    Integrable (badScaleInput S f I₀ k₀ ℓ) := by
  exact integrable_finsetSum _ (fun J _ ↦ hf.indicator J.measurableSet_carrier)

open Classical in
theorem norm_badScaleInput_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ ℓ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (x : ℝ) : ‖badScaleInput S f I₀ k₀ ℓ x‖ ≤ ‖f x‖ :=
  norm_sum_carrier_indicator_le _ f (badScaleCells_pairwiseDisjoint f I₀ k₀ ℓ hlam) x

open Classical in
/-- Parent closure of the finite source dyadic tree. This is purely
geometric: every non-root interval has a strictly larger candidate parent
of at most twice its length. -/
def HasDyadicParents (S : Finset RealInterval) (I₀ : RealInterval) : Prop :=
  ∀ J ∈ S, J ≠ I₀ → ∃ K ∈ S,
    J.carrier ⊆ K.carrier ∧ J.length < K.length ∧ K.length ≤ 2 * J.length

open Classical in
/-- Maximality and the actual dyadic parent give the upper mass bound
on each selected bad interval. It is not an additional stopping hypothesis. -/
theorem stoppingChild_mass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ J : RealInterval}
    (hf : Integrable f) (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (hJ : J ∈ stoppingChildren S f 0 I₀) :
    (∫ x in J.carrier, ‖f x‖) ≤ 20 * intervalL1Average f I₀ * J.length := by
  obtain ⟨K, hK, hJK, hlen, hlen'⟩ := hparent J
    (stoppingChildren_subset S f 0 I₀ hJ)
    (fun heq ↦ self_not_mem_stoppingChildren S f 0 I₀ (heq ▸ hJ))
  have hnot : ¬ IsBadDescendant f 0 I₀ K := by
    intro hbad
    have heq := (mem_stoppingChildren_iff.mp hJ).2 K
      (mem_badDescendants_iff.mpr ⟨hK, hbad⟩) hJK
    rw [heq] at hlen
    exact (lt_irrefl _ hlen)
  have havg : intervalL1Average f K ≤ 10 * intervalL1Average f I₀ := by
    by_contra hn
    exact hnot ⟨hsub K hK, Or.inl (lt_of_not_ge hn)⟩
  calc
    (∫ x in J.carrier, ‖f x‖) ≤ ∫ x in K.carrier, ‖f x‖ :=
      setIntegral_mono_set hf.norm.integrableOn
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x)) hJK.eventuallyLE
    _ = intervalL1Average f K * K.length := (intervalL1Average_mul_length f K).symm
    _ ≤ (10 * intervalL1Average f I₀) * (2 * J.length) :=
      mul_le_mul havg hlen' K.length_pos.le (by positivity [intervalL1Average_nonneg f I₀])
    _ = _ := by ring

open Classical in
/-- The actual bad-scale input inherits the controlled averages on every
interval of the constructed good collection. -/
theorem badScaleInput_localMass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ ℓ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hI : I ∈ goodCollection S f 0 I₀) :
    (∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ ℓ x‖) ≤
      10 * intervalL1Average f I₀ * I.length := by
  calc
    _ ≤ ∫ x in I.centralThird, ‖f x‖ := by
      apply integral_mono (integrable_badScaleInput S hf I₀ k₀ ℓ).norm.integrableOn
        hf.norm.integrableOn
      intro x
      exact norm_badScaleInput_le f I₀ k₀ ℓ hlam x
    _ ≤ ∫ x in I.carrier, ‖f x‖ :=
      setIntegral_mono_set hf.norm.integrableOn
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
        I.centralThird_subset_carrier.eventuallyLE
    _ = intervalL1Average f I * I.length := (intervalL1Average_mul_length f I).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (goodCollection_averages_le hsub hI).1 I.length_pos.le

open Classical in
/-- A local window sees only children inside the window expanded by their
maximum length. Disjointness then turns upper child masses into a local
mass bound, without any pointwise bound on `f`. -/
theorem integral_window_sum_indicators_le
    (T : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (hdisj : Set.Pairwise (↑T) (Disjoint on RealInterval.carrier))
    {L M a b : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hab : a ≤ b)
    (hlen : ∀ J ∈ T, J.length ≤ L)
    (hmass : ∀ J ∈ T, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length) :
    (∫ x in Icc a b, ‖∑ J ∈ T, J.carrier.indicator f x‖) ≤ M * (b - a + 2 * L) := by
  let U := T.filter fun J ↦ (J.carrier ∩ Icc a b).Nonempty
  let E : RealInterval := ⟨a - L, b + L, by linarith⟩
  have hUsub : U ⊆ T := Finset.filter_subset _ _
  have hE (J : RealInterval) (hJ : J ∈ U) : J.carrier ⊆ E.carrier := by
    obtain ⟨z, hzJ, hzwin⟩ := (Finset.mem_filter.mp hJ).2
    have hJlen := hlen J (hUsub hJ)
    intro x hx
    change a - L < x ∧ x ≤ b + L
    change J.left < z ∧ z ≤ J.right at hzJ
    change J.left < x ∧ x ≤ J.right at hx
    dsimp [RealInterval.length] at hJlen
    constructor <;> linarith [hzwin.1, hzwin.2]
  have heq (x : ℝ) (hx : x ∈ Icc a b) :
      (∑ J ∈ T, J.carrier.indicator f x) = ∑ J ∈ U, J.carrier.indicator f x := by
    symm
    apply Finset.sum_subset hUsub
    intro J hJ hJU
    apply indicator_of_notMem
    intro hxJ
    exact hJU (Finset.mem_filter.mpr ⟨hJ, ⟨x, hxJ, hx⟩⟩)
  have hpoint : Integrable (fun x ↦ ∑ J ∈ U, J.carrier.indicator f x) :=
    integrable_finsetSum U (fun J _ ↦ hf.indicator J.measurableSet_carrier)
  have hnorms : Integrable (fun x ↦ ∑ J ∈ U, ‖J.carrier.indicator f x‖) :=
    integrable_finsetSum U (fun J _ ↦ (hf.indicator J.measurableSet_carrier).norm)
  calc
    _ = ∫ x in Icc a b, ‖∑ J ∈ U, J.carrier.indicator f x‖ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only
      rw [heq x hx]
    _ ≤ ∫ x in Icc a b, ∑ J ∈ U, ‖J.carrier.indicator f x‖ :=
      integral_mono hpoint.norm.integrableOn hnorms.integrableOn (fun x ↦ norm_sum_le _ _)
    _ = ∑ J ∈ U, ∫ x in Icc a b, ‖J.carrier.indicator f x‖ :=
      integral_finsetSum _ (fun J _ ↦ (hf.indicator J.measurableSet_carrier).norm.integrableOn)
    _ ≤ ∑ J ∈ U, ∫ x in J.carrier, ‖f x‖ := by
      apply Finset.sum_le_sum
      intro J hJ
      calc
        _ ≤ ∫ x, ‖J.carrier.indicator f x‖ :=
          setIntegral_le_integral (hf.indicator J.measurableSet_carrier).norm
            (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        _ = _ := by rw [show (fun x ↦ ‖J.carrier.indicator f x‖) =
            J.carrier.indicator (fun x ↦ ‖f x‖) by
              funext x; exact norm_indicator_eq_indicator_norm f x]
                    rw [integral_indicator J.measurableSet_carrier]
    _ ≤ ∑ J ∈ U, M * J.length := Finset.sum_le_sum (fun J hJ ↦ hmass J (hUsub hJ))
    _ = M * ∑ J ∈ U, J.length := (Finset.mul_sum _ _ _).symm
    _ ≤ M * E.length := mul_le_mul_of_nonneg_left
      (sum_intervalLength_le_of_disjoint U E
        (fun J hJ K hK hne ↦ hdisj (hUsub hJ) (hUsub hK) hne) hE) hM
    _ = _ := by dsimp [E, RealInterval.length]; ring

open Classical in
/-- The source local-mass estimate (4.4), here on the precise unit window
needed by the diagonal kernel. It follows from the actual stopping parents. -/
theorem badScaleInput_unitWindowMass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) (hℓ : 0 ≤ ℓ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) (x : ℝ) :
    (∫ t in Icc (x - 1 / 2) (x + 1 / 2), ‖badScaleInput S f I₀ k₀ ℓ t‖) ≤
      60 * intervalL1Average f I₀ * (2 : ℝ) ^ ℓ := by
  have hpow : 1 ≤ (2 : ℝ) ^ ℓ := by
    simpa only [zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hℓ
  have h := integral_window_sum_indicators_le (badScaleCells S f I₀ k₀ ℓ) hf
    (badScaleCells_pairwiseDisjoint f I₀ k₀ ℓ hlam)
    (by positivity : 0 < (2 : ℝ) ^ ℓ)
    (by positivity [intervalL1Average_nonneg f I₀] : 0 ≤ 20 * intervalL1Average f I₀)
    (by linarith : x - 1 / 2 ≤ x + 1 / 2)
    (fun J hJ ↦ length_le_of_mem_badScaleCells hJ)
    (fun J hJ ↦ stoppingChild_mass_le hf hparent hsub (badScaleCells_subset S f I₀ k₀ ℓ hJ))
  apply h.trans
  have hnonneg := intervalL1Average_nonneg f I₀
  nlinarith

open Classical in
theorem exists_mem_badScaleCells_of_ne_zero
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ ℓ : ℤ} {x : ℝ}
    (hx : badScaleInput S f I₀ k₀ ℓ x ≠ 0) :
    ∃ J ∈ badScaleCells S f I₀ k₀ ℓ, x ∈ J.carrier := by
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro J hJ
  exact indicator_of_notMem (fun hxJ ↦ hn ⟨J, hJ, hxJ⟩) f

open Classical in
/-- Different actual bad scales have disjoint spatial supports. -/
theorem badScale_indices_eq_of_ne_zero
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {ℓ m : ℤ} {x : ℝ}
    (hℓ : badScaleInput S f I₀ k₀ ℓ x ≠ 0) (hm : badScaleInput S f I₀ k₀ m x ≠ 0) :
    ℓ = m := by
  obtain ⟨J, hJ, hxJ⟩ := exists_mem_badScaleCells_of_ne_zero hℓ
  obtain ⟨K, hK, hxK⟩ := exists_mem_badScaleCells_of_ne_zero hm
  have heq : J = K := by
    by_contra hn
    exact Set.disjoint_left.mp (stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
      (badScaleCells_subset S f I₀ k₀ ℓ hJ) (badScaleCells_subset S f I₀ k₀ m hK) hn) hxJ hxK
  have hp : (2 : ℝ) ^ ℓ = (2 : ℝ) ^ m := by
    rw [← (Finset.mem_filter.mp hJ).2, ← (Finset.mem_filter.mp hK).2, heq]
  exact (zpow_right_inj₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp hp

open Classical in
/-- The precise restricted input to an interval's bad-scale piece. -/
noncomputable def intervalBadInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) : ℝ → ℂ :=
  I.centralThird.indicator (badScaleInput S f I₀ k₀ (scale I + 2 - s))

open Classical in
/-- There is no overlap multiplicity in the actual interval bad inputs,
even across different dyadic scales. -/
theorem intervalBadInput_unique_of_ne_zero
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hlenI : I.length = (2 : ℝ) ^ (scale I + 2))
    (hlenJ : J.length = (2 : ℝ) ^ (scale J + 2)) {x : ℝ}
    (hxI : intervalBadInput S f I₀ k₀ s scale I x ≠ 0)
    (hxJ : intervalBadInput S f I₀ k₀ s scale J x ≠ 0) : I = J := by
  have hi := Set.indicator_apply_ne_zero.mp hxI
  have hj := Set.indicator_apply_ne_zero.mp hxJ
  have hidx := badScale_indices_eq_of_ne_zero f I₀ k₀ hlam hi.2 hj.2
  have hlen : I.length = J.length := by rw [hlenI, hlenJ, show scale I = scale J by omega]
  by_contra hne
  rcases hlam hI hJ hne with hsub | hsub | hdisj
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm
  · exact Set.disjoint_left.mp hdisj (I.centralThird_subset_carrier hi.1)
      (J.centralThird_subset_carrier hj.1)

open Classical in
/-- Pointwise no-loss packing for all actual restricted bad inputs. -/
theorem sum_norm_intervalBadInput_le
    {S : Finset RealInterval} (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hlen : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    (∑ I ∈ N, ‖intervalBadInput S f I₀ k₀ s scale I x‖) ≤ ‖f x‖ := by
  by_cases hex : ∃ I ∈ N, intervalBadInput S f I₀ k₀ s scale I x ≠ 0
  · obtain ⟨I, hI, hxI⟩ := hex
    rw [Finset.sum_eq_single I]
    · exact (norm_indicator_le_norm_self _ _).trans
        (norm_badScaleInput_le f I₀ k₀ (scale I + 2 - s) hlam x)
    · intro J hJ hJI
      have hz : intervalBadInput S f I₀ k₀ s scale J x = 0 := by
        by_contra hxJ
        exact hJI (intervalBadInput_unique_of_ne_zero f I₀ k₀ s scale hlam
          (hN hJ) (hN hI) (hlen J hJ) (hlen I hI) hxJ hxI)
      rw [hz, norm_zero]
    · intro hn
      exact (hn hI).elim
  · have hz (I : RealInterval) (hI : I ∈ N) : intervalBadInput S f I₀ k₀ s scale I x = 0 :=
      not_ne_iff.mp fun hx ↦ hex ⟨I, hI, hx⟩
    rw [Finset.sum_eq_zero (fun I hI ↦ by rw [hz I hI, norm_zero])]
    exact norm_nonneg _

open Classical in
/-- Exact no-loss mass packing for all actual interval bad inputs. -/
theorem sum_intervalBadInput_mass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hlen : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) :
    (∑ I ∈ N, ∫ x in I.centralThird,
      ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) ≤ ∫ x, ‖f x‖ := by
  have hint (I : RealInterval) : Integrable (intervalBadInput S f I₀ k₀ s scale I) :=
    (integrable_badScaleInput S hf I₀ k₀ _).indicator I.measurableSet_centralThird
  have hmass (I : RealInterval) :
      (∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) =
        ∫ x, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
    simp only [intervalBadInput, norm_indicator_eq_indicator_norm,
      integral_indicator I.measurableSet_centralThird]
  simp_rw [hmass]
  rw [← integral_finsetSum _ (fun I _ ↦ (hint I).norm)]
  exact integral_mono (integrable_finsetSum _ (fun I _ ↦ (hint I).norm)) hf.norm
    (sum_norm_intervalBadInput_le f I₀ k₀ s scale hlam N hN hlen)

open Classical in
/-- The same no-loss packing holds locally for an arbitrary collection of
descendants, even when their parent intervals overlap across scales. -/
theorem sum_intervalBadInput_mass_le_local
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hlen : ∀ J ∈ N, J.length = (2 : ℝ) ^ (scale J + 2))
    (I : RealInterval) (hsub : ∀ J ∈ N, J.carrier ⊆ I.carrier) :
    (∑ J ∈ N, ∫ x in J.centralThird,
      ‖badScaleInput S f I₀ k₀ (scale J + 2 - s) x‖) ≤ ∫ x in I.carrier, ‖f x‖ := by
  have hint (J : RealInterval) : Integrable (intervalBadInput S f I₀ k₀ s scale J) :=
    (integrable_badScaleInput S hf I₀ k₀ _).indicator J.measurableSet_centralThird
  have heq (J : RealInterval) (hJ : J ∈ N) :
      (∫ x in J.centralThird, ‖badScaleInput S f I₀ k₀ (scale J + 2 - s) x‖) =
        ∫ x in I.carrier, ‖intervalBadInput S f I₀ k₀ s scale J x‖ := by
    simp only [intervalBadInput, norm_indicator_eq_indicator_norm,
      setIntegral_indicator J.measurableSet_centralThird]
    rw [Set.inter_eq_right.mpr (J.centralThird_subset_carrier.trans (hsub J hJ))]
  rw [Finset.sum_congr rfl heq, ← integral_finsetSum _ (fun J _ ↦ (hint J).norm.integrableOn)]
  exact integral_mono (integrable_finsetSum _ (fun J _ ↦ (hint J).norm.integrableOn))
    hf.norm.integrableOn (sum_norm_intervalBadInput_le f I₀ k₀ s scale hlam N hN hlen)


end KrauseLaceyBadScale
end QuadraticCarleson
