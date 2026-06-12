/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.BlockLocalization
import LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis

/-! # ProductAnnulusLocalization -/


open MeasureTheory
open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# ProductAnnulusLocalization

Finite block-localization scaffold for product annuli and coefficient windows.
-/

private theorem toFun_ofPkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  let _ := hd
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]

private theorem norm_nonneg_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d} (F : Pkappa d kappa) :
    0 ≤ ‖F‖ := by
  let _ := hd
  exact Real.sqrt_nonneg _

private theorem norm_ne_zero_of_ne_zero_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF : F ≠ 0) :
    ‖F‖ ≠ 0 := by
  let _ := hd
  intro hnorm
  apply hF
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hcoeff_ne : F alpha ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) := by
      simpa using
        (Finset.single_le_sum (f := fun a : Idx d => ‖F a‖ ^ 2) (s := F.support) (a := alpha)
          (fun a _ => by positivity) hmem)
    have hterm_pos : 0 < ‖F alpha‖ ^ 2 := by
      have hnorm_pos : 0 < ‖F alpha‖ := norm_pos_iff.mpr hcoeff_ne
      nlinarith
    have hsum_pos : 0 < Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) :=
      lt_of_lt_of_le hterm_pos hle
    change Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) = 0 at hnorm
    have hsqrt_pos :
        0 < Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) :=
      Real.sqrt_pos.mpr hsum_pos
    linarith
  · exact Finsupp.notMem_support_iff.mp hmem

private lemma continuous_Phi_wip
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

private lemma continuous_evalPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi_wip kappa alpha)

private lemma measurableSet_productAnnulus_wip
    {d : Nat} (j : Idx d) :
    MeasurableSet (productAnnulus j) := by
  have h :
      MeasurableSet
        (⋂ q : Fin d, {z : Cd d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (ι := Fin d) ?_
    intro q
    have hge :
        MeasurableSet {z : Cd d | (j q : ℝ) ≤ ‖z q‖} := by
      exact measurableSet_le measurable_const
        (measurable_norm.comp (continuous_apply q).measurable)
    have hlt :
        MeasurableSet {z : Cd d | ‖z q‖ < (j q : ℝ) + 1} := by
      exact measurableSet_lt
        (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.setOf_and] using hge.inter hlt
  simpa [productAnnulus, Set.setOf_forall] using h

private lemma productAnnulus_eq_of_mem_wip
    {d : Nat} {j ℓ : Idx d} {z : Cd d}
    (hj : z ∈ productAnnulus j) (hℓ : z ∈ productAnnulus ℓ) :
    j = ℓ := by
  funext q
  rcases hj q with ⟨hj_lower, hj_upper⟩
  rcases hℓ q with ⟨hℓ_lower, hℓ_upper⟩
  refine le_antisymm ?_ ?_
  · by_contra hlt
    have hlt' : ℓ q + 1 ≤ j q := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
    have hlt_real : ((ℓ q : Nat) : ℝ) + 1 ≤ j q := by
      exact_mod_cast hlt'
    linarith
  · by_contra hlt
    have hlt' : j q + 1 ≤ ℓ q := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
    have hlt_real : ((j q : Nat) : ℝ) + 1 ≤ ℓ q := by
      exact_mod_cast hlt'
    linarith

private lemma sum_indicator_productAnnulus_le_wip
    {d : Nat} (s : Finset (Idx d)) (z : Cd d) (a : ℝ)
    (ha : 0 ≤ a) :
    ∑ j ∈ s, Set.indicator (productAnnulus j) (fun _ : Cd d => a) z ≤ a := by
  classical
  by_cases hs : ∃ j ∈ s, z ∈ productAnnulus j
  · rcases hs with ⟨j0, hj0s, hj0z⟩
    have hsum :
        ∑ j ∈ s, Set.indicator (productAnnulus j) (fun _ : Cd d => a) z =
          Set.indicator (productAnnulus j0) (fun _ : Cd d => a) z := by
      exact Finset.sum_eq_single_of_mem j0 hj0s (fun j hjs hjne => by
        have hjz : z ∉ productAnnulus j := by
          intro hjz
          have heq := productAnnulus_eq_of_mem_wip hjz hj0z
          exact hjne heq
        simp [Set.indicator, hjz])
    rw [hsum]
    simp [Set.indicator, hj0z]
  · have hzero : ∀ j ∈ s, z ∉ productAnnulus j := by
      intro j hjs
      by_contra hjz
      exact hs ⟨j, hjs, hjz⟩
    rw [Finset.sum_eq_zero]
    · linarith
    · intro j hj
      simp [Set.indicator, hzero j hj]

private theorem integrable_evalPkappa_sq_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Integrable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  by_cases hF : F = 0
  · subst hF
    simp [evalPkappa]
  · have hmeas :
        AEStronglyMeasurable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) :=
      ((continuous_evalPkappa_wip kappa F).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    by_contra hInt
    have hundef :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 :=
      MeasureTheory.integral_undef hInt
    have hmass :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 :=
      evalPkappa_total_mass hd kappa F
    have hnorm_ne : ‖F‖ ≠ 0 := norm_ne_zero_of_ne_zero_pkappa_wip hd hF
    have hpos : 0 < ‖F‖ ^ 2 := by
      have hnorm_pos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg_pkappa_wip hd F) hnorm_ne.symm
      nlinarith
    linarith

private theorem finite_sum_annulusMass_le_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (s : Finset (Idx d)) :
    ∑ j ∈ s, annulusMass j (ofPkappa kappa F) ≤ ‖F‖ ^ 2 := by
  classical
  have htoFun := toFun_ofPkappa_wip hd kappa F
  have hInt :
      Integrable (fun z : Cd d => ‖toFun kappa (ofPkappa kappa F) z‖ ^ 2) (gammaD d) := by
    simpa [htoFun] using integrable_evalPkappa_sq_wip hd kappa F
  calc
    ∑ j ∈ s, annulusMass j (ofPkappa kappa F)
      = ∫ z : Cd d,
          ∑ j ∈ s, if z ∈ productAnnulus j then ‖toFun kappa (ofPkappa kappa F) z‖ ^ 2 else 0
          ∂ gammaD d := by
            rw [MeasureTheory.integral_finsetSum]
            · simp [annulusMass, Set.indicator]
            · intro j hj
              refine (hInt.indicator (measurableSet_productAnnulus_wip j)).congr ?_
              filter_upwards with z
              simp only [Set.indicator]
    _ ≤ ∫ z : Cd d, ‖toFun kappa (ofPkappa kappa F) z‖ ^ 2 ∂ gammaD d := by
          refine MeasureTheory.integral_mono_ae ?_ hInt ?_
          · refine MeasureTheory.integrable_finsetSum _ ?_
            intro j hj
            refine (hInt.indicator (measurableSet_productAnnulus_wip j)).congr ?_
            filter_upwards with z
            simp only [Set.indicator]
          · filter_upwards with z
            exact sum_indicator_productAnnulus_le_wip s z
              (‖toFun kappa (ofPkappa kappa F) z‖ ^ 2) (by positivity)
    _ = ‖F‖ ^ 2 := by
          simpa [htoFun] using evalPkappa_total_mass hd kappa F

private theorem phi1D_eq_oneDimPhi_wip
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor :
        (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
          (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) *
                (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by
            exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by
            field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ =>
          ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private theorem Phi_eq_PhiKappaAlpha_wip
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    Phi kappa alpha z = Hermite1DimdLEAN.PhiKappaAlpha kappa alpha z := by
  unfold Phi Hermite1DimdLEAN.PhiKappaAlpha
  refine Finset.prod_congr rfl ?_
  intro q hq
  exact phi1D_eq_oneDimPhi_wip (kappa q) (alpha q) (z q)

private theorem evalPkappa_eq_evalHermiteSum_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappa kappa F = Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ := by
  ext z
  unfold evalPkappa Hermite1DimdLEAN.evalHermiteSum Hermite1DimdLEAN.FiniteHermiteSum.support
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Phi_eq_PhiKappaAlpha_wip]

private theorem annulusMass_ofPkappa_eq_annulusMass_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (F : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa F) =
      Hermite1DimdLEAN.annulusMass j (Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩) := by
  classical
  have hgauss : gammaD d = Hermite1DimdLEAN.gaussianMeasure d := by
    unfold gammaD Hermite1DimdLEAN.gaussianMeasure
    congr 1
  have hleft :
      annulusMass j (ofPkappa kappa F) =
        ∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d := by
    simp [annulusMass, hgauss,
      toFun_ofPkappa_wip hd kappa F, evalPkappa_eq_evalHermiteSum_wip kappa F,
      Set.indicator]
  have hright :
      Hermite1DimdLEAN.annulusMass j (Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩) =
        ∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d := by
    unfold Hermite1DimdLEAN.annulusMass
    change
      (∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d) =
        (∫ z : Cd d,
          if z ∈ productAnnulus j then ‖Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ z‖ ^ 2 else 0
          ∂ Hermite1DimdLEAN.gaussianMeasure d)
    simp [productAnnulus]
  rw [hleft, hright]

private theorem ofPkappa_total_mass_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) :
    (∫ z, ‖toFun kappa (ofPkappa kappa F) z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 := by
  let _ := hd
  simpa [toFun_ofPkappa_wip hd kappa F] using evalPkappa_total_mass hd kappa F

private theorem mem_squareBlock_finset_iff_blockIndex_eq_wip
    (ℓ n : Nat) :
    n ∈ HermiteLEAN.squareBlock ℓ ↔ HermiteLEAN.blockIndex n = ℓ := by
  rw [HermiteLEAN.squareBlock, Finset.mem_Ico]
  constructor
  · intro h
    exact ((Nat.eq_sqrt).2 (by simpa [Nat.pow_two] using h)).symm
  · intro h
    simpa [Nat.pow_two] using (Nat.eq_sqrt).1 h.symm

private def coeffBlockFinset_wip {d : Nat} (ℓ : Idx d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => HermiteLEAN.squareBlock (ℓ q)

private def nearBlocks_wip {d : Nat} (j : Idx d) (M : Nat) : Finset (Idx d) :=
  (Fintype.piFinset fun q : Fin d => Finset.range (j q + M + 1)).filter fun ℓ =>
    Hermite1DimdLEAN.blockDistance j ℓ ≤ M

private def nearLowBlocks_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (lowAnnuli d J).biUnion fun j => nearBlocks_wip j M

private def nearLowCoeffSet_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (nearLowBlocks_wip (d := d) J M).biUnion fun ℓ => coeffBlockFinset_wip ℓ

private theorem mem_coeffBlockFinset_wip
    {d : Nat} (ℓ alpha : Idx d) :
    alpha ∈ coeffBlockFinset_wip ℓ ↔ Hermite1DimdLEAN.blockIndexMulti alpha = ℓ := by
  constructor
  · intro h
    funext q
    exact
      (mem_squareBlock_finset_iff_blockIndex_eq_wip (ℓ q) (alpha q)).mp
        ((Fintype.mem_piFinset.mp h) q)
  · intro h
    refine Fintype.mem_piFinset.mpr ?_
    intro q
    exact
      (mem_squareBlock_finset_iff_blockIndex_eq_wip (ℓ q) (alpha q)).mpr
        (by simpa [Hermite1DimdLEAN.blockIndexMulti] using congrArg (fun f => f q) h)

private theorem mem_nearLowBlocks_wip
    {d : Nat} (J M : Nat) (ℓ : Idx d) :
    ℓ ∈ nearLowBlocks_wip (d := d) J M ↔
      ∃ j ∈ lowAnnuli d J, Hermite1DimdLEAN.blockDistance j ℓ ≤ M := by
  constructor
  · intro h
    rw [nearLowBlocks_wip, Finset.mem_biUnion] at h
    rcases h with ⟨j, hj, hℓ⟩
    exact ⟨j, hj, (Finset.mem_filter.mp hℓ).2⟩
  · rintro ⟨j, hj, hdist⟩
    rw [nearLowBlocks_wip, Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hdist⟩
    rw [Fintype.mem_piFinset]
    intro q
    have hqdist : Nat.dist (j q) (ℓ q) ≤ M := by
      have hle : Nat.dist (j q) (ℓ q) ≤ Hermite1DimdLEAN.blockDistance j ℓ := by
        dsimp [Hermite1DimdLEAN.blockDistance]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun r : Fin d => Nat.dist (j r) (ℓ r)) (by simp)
      exact le_trans hle hdist
    have hidx_upper : ℓ q ≤ j q + M := by
      have htri : ℓ q ≤ j q + Nat.dist (ℓ q) (j q) :=
        Nat.dist_tri_right' (ℓ q) (j q)
      have hdist' : Nat.dist (ℓ q) (j q) ≤ M := by
        simpa [Nat.dist_comm] using hqdist
      exact le_trans htri (Nat.add_le_add_left hdist' _)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hidx_upper)

private theorem mem_nearLowCoeffSet_wip
    {d : Nat} (J M : Nat) (alpha : Idx d) :
    alpha ∈ nearLowCoeffSet_wip (d := d) J M ↔
      ∃ j ∈ lowAnnuli d J,
        Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha) ≤ M := by
  constructor
  · intro h
    rw [nearLowCoeffSet_wip, Finset.mem_biUnion] at h
    rcases h with ⟨ℓ, hℓ, hα⟩
    rcases (mem_nearLowBlocks_wip (J := J) (M := M) ℓ).mp hℓ with ⟨j, hj, hjdist⟩
    have hblock : Hermite1DimdLEAN.blockIndexMulti alpha = ℓ :=
      (mem_coeffBlockFinset_wip ℓ alpha).mp hα
    exact ⟨j, hj, by simpa [hblock] using hjdist⟩
  · rintro ⟨j, hj, hjdist⟩
    rw [nearLowCoeffSet_wip, Finset.mem_biUnion]
    refine ⟨Hermite1DimdLEAN.blockIndexMulti alpha, ?_, ?_⟩
    · exact
        (mem_nearLowBlocks_wip (J := J) (M := M) (Hermite1DimdLEAN.blockIndexMulti alpha)).mpr
          ⟨j, hj, hjdist⟩
    · exact
        (mem_coeffBlockFinset_wip (Hermite1DimdLEAN.blockIndexMulti alpha) alpha).mpr rfl

private theorem truncate_ofPkappa_apply_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (H : Pkappa d kappa) (alpha : Idx d) :
    truncateFinset E (ofPkappa kappa H) alpha = if alpha ∈ E then H alpha else 0 := by
  have hsum :
      truncateFinset E (ofPkappa kappa H) alpha =
        (∑ beta ∈ E, Finsupp.single beta (coeffSkappa (ofPkappa kappa H) beta)) alpha := by
    rfl
  rw [hsum]
  by_cases h : alpha ∈ E
  · simp [h, coeffSkappa, ofPkappa, Finsupp.single_apply]
  · simp [h, coeffSkappa, ofPkappa, Finsupp.single_apply]

private theorem farPart_apply_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (H : Pkappa d kappa) (alpha : Idx d) :
    (H - truncateFinset E (ofPkappa kappa H)) alpha = if alpha ∈ E then 0 else H alpha := by
  by_cases h : alpha ∈ E
  · simp [truncate_ofPkappa_apply_wip kappa E H alpha, h]
  · simp [truncate_ofPkappa_apply_wip kappa E H alpha, h]

private theorem norm_sq_eq_sum_wip
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) :
    ‖F‖ ^ 2 = Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
  change (Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))) ^ 2 =
    Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2)
  rw [Real.sq_sqrt]
  positivity

private theorem hermiteNormSq_eq_norm_sq_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Hermite1DimdLEAN.hermiteNormSq kappa ⟨F⟩ = ‖F‖ ^ 2 := by
  rw [norm_sq_eq_sum_wip]
  simpa [Hermite1DimdLEAN.FiniteHermiteSum.support] using
    (Hermite1DimdLEAN.finiteParseval kappa ⟨F⟩)

private theorem evalPkappa_add_apply_wip
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index'] <;> simp [add_mul]

private theorem annulusMass_add_le_two_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (j : Idx d) (F G : Pkappa d kappa) :
    annulusMass j (ofPkappa kappa (F + G)) ≤
      2 * annulusMass j (ofPkappa kappa F) + 2 * annulusMass j (ofPkappa kappa G) := by
  classical
  have hIntF :
      Integrable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
    simpa using integrable_evalPkappa_sq_wip hd kappa F
  have hIntG :
      Integrable (fun z : Cd d => ‖evalPkappa kappa G z‖ ^ 2) (gammaD d) := by
    simpa using integrable_evalPkappa_sq_wip hd kappa G
  have hIntFG :
      Integrable (fun z : Cd d => ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) := by
    simpa using integrable_evalPkappa_sq_wip hd kappa (F + G)
  calc
    annulusMass j (ofPkappa kappa (F + G))
      = ∫ z : Cd d,
          Set.indicator (productAnnulus j)
            (fun w => ‖evalPkappa kappa (F + G) w‖ ^ 2) z ∂ gammaD d := by
            simp [annulusMass, toFun_ofPkappa_wip hd kappa (F + G)]
    _ ≤ ∫ z : Cd d,
          (2 : ℝ) * Set.indicator (productAnnulus j) (fun w => ‖evalPkappa kappa F w‖ ^ 2) z +
            (2 : ℝ) * Set.indicator (productAnnulus j) (fun w => ‖evalPkappa kappa G w‖ ^ 2) z
          ∂ gammaD d := by
            have hIntRHS :
                Integrable
                  (fun z : Cd d =>
                    (2 : ℝ) * Set.indicator (productAnnulus j)
                      (fun w => ‖evalPkappa kappa F w‖ ^ 2) z +
                    (2 : ℝ) * Set.indicator (productAnnulus j)
                      (fun w => ‖evalPkappa kappa G w‖ ^ 2) z)
                  (gammaD d) := by
              exact
                (hIntF.indicator (measurableSet_productAnnulus_wip j)).const_mul 2 |>.add
                  ((hIntG.indicator (measurableSet_productAnnulus_wip j)).const_mul 2)
            have hmono :
                (fun z : Cd d =>
                  Set.indicator (productAnnulus j)
                    (fun w => ‖evalPkappa kappa (F + G) w‖ ^ 2) z) ≤ᵐ[gammaD d]
                (fun z : Cd d =>
                  (2 : ℝ) * Set.indicator (productAnnulus j)
                    (fun w => ‖evalPkappa kappa F w‖ ^ 2) z +
                  (2 : ℝ) * Set.indicator (productAnnulus j)
                    (fun w => ‖evalPkappa kappa G w‖ ^ 2) z) := by
              filter_upwards with z
              by_cases hz : z ∈ productAnnulus j
              · have hnorm :
                    ‖evalPkappa kappa (F + G) z‖ ≤
                      ‖evalPkappa kappa F z‖ + ‖evalPkappa kappa G z‖ := by
                  simpa [evalPkappa_add_apply_wip kappa F G z] using
                    norm_add_le (evalPkappa kappa F z) (evalPkappa kappa G z)
                have hsq_nonneg :
                    0 ≤ (‖evalPkappa kappa F z‖ - ‖evalPkappa kappa G z‖) ^ 2 := by
                  positivity
                have hsq :
                    ‖evalPkappa kappa (F + G) z‖ ^ 2 ≤
                      2 * ‖evalPkappa kappa F z‖ ^ 2 + 2 * ‖evalPkappa kappa G z‖ ^ 2 := by
                  have hsq_sum :
                      (‖evalPkappa kappa F z‖ + ‖evalPkappa kappa G z‖) ^ 2 ≤
                        2 * ‖evalPkappa kappa F z‖ ^ 2 + 2 * ‖evalPkappa kappa G z‖ ^ 2 := by
                    nlinarith
                  have hsq_norm :
                      ‖evalPkappa kappa (F + G) z‖ ^ 2 ≤
                        (‖evalPkappa kappa F z‖ + ‖evalPkappa kappa G z‖) ^ 2 := by
                    apply (sq_le_sq).2
                    simpa
                      [abs_of_nonneg (norm_nonneg _),
                        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using
                      hnorm
                  exact le_trans hsq_norm hsq_sum
                simpa [Set.indicator, hz] using hsq
              · simp [Set.indicator, hz]
            exact MeasureTheory.integral_mono_ae
              (hIntFG.indicator (measurableSet_productAnnulus_wip j)) hIntRHS hmono
    _ = 2 * annulusMass j (ofPkappa kappa F) + 2 * annulusMass j (ofPkappa kappa G) := by
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
            simp [annulusMass, toFun_ofPkappa_wip hd kappa F, toFun_ofPkappa_wip hd kappa G]
          · exact (hIntF.indicator (measurableSet_productAnnulus_wip j)).const_mul 2
          · exact (hIntG.indicator (measurableSet_productAnnulus_wip j)).const_mul 2

private theorem lowAnnulusMass_add_le_two_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (F G : Pkappa d kappa) :
    lowAnnulusMass J (ofPkappa kappa (F + G)) ≤
      2 * lowAnnulusMass J (ofPkappa kappa F) + 2 * lowAnnulusMass J (ofPkappa kappa G) := by
  unfold lowAnnulusMass
  calc
    Finset.sum (lowAnnuli d J) (fun j => annulusMass j (ofPkappa kappa (F + G)))
      ≤ Finset.sum (lowAnnuli d J)
          (fun j =>
            2 * annulusMass j (ofPkappa kappa F) +
              2 * annulusMass j (ofPkappa kappa G)) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact annulusMass_add_le_two_wip hd kappa j F G
    _ = 2 * lowAnnulusMass J (ofPkappa kappa F) + 2 * lowAnnulusMass J (ofPkappa kappa G) := by
          simp [lowAnnulusMass, Finset.sum_add_distrib, two_mul, add_assoc]

private theorem farPart_support_subset_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (H : Pkappa d kappa) :
    (H - truncateFinset E (ofPkappa kappa H)).support ⊆ H.support := by
  intro alpha halpha
  have hcoeff_ne :
      (H - truncateFinset E (ofPkappa kappa H)) alpha ≠ 0 := Finsupp.mem_support_iff.mp halpha
  by_cases hE : alpha ∈ E
  · have hzero :
        (H - truncateFinset E (ofPkappa kappa H)) alpha = 0 := by
      simp [farPart_apply_wip kappa E H alpha, hE]
    exact (hcoeff_ne hzero).elim
  · have hH_ne : H alpha ≠ 0 := by
      simpa [farPart_apply_wip kappa E H alpha, hE] using hcoeff_ne
    exact Finsupp.mem_support_iff.mpr hH_ne

private theorem norm_sq_farPart_le_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (H : Pkappa d kappa) :
    ‖H - truncateFinset E (ofPkappa kappa H)‖ ^ 2 ≤ ‖H‖ ^ 2 := by
  let Hfar : Pkappa d kappa := H - truncateFinset E (ofPkappa kappa H)
  have hsubset : Hfar.support ⊆ H.support := farPart_support_subset_wip kappa E H
  calc
    ‖Hfar‖ ^ 2 = Finset.sum Hfar.support (fun alpha => ‖Hfar alpha‖ ^ 2) := norm_sq_eq_sum_wip Hfar
    _ = Finset.sum Hfar.support (fun alpha => ‖H alpha‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          have hnotE : alpha ∉ E := by
            intro hE
            have hzero : Hfar alpha = 0 := by
              simp [Hfar, farPart_apply_wip kappa E H alpha, hE]
            exact (Finsupp.mem_support_iff.mp halpha) hzero
          simp [Hfar, farPart_apply_wip kappa E H alpha, hnotE]
    _ ≤ Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro alpha hα _
            positivity)
    _ = ‖H‖ ^ 2 := by rw [← norm_sq_eq_sum_wip H]

private theorem remainderPart_eq_self_of_support_far_wip
    {d : Nat} (kappa : MultiIndex d) (j : Idx d) (M : Nat)
    (F : Pkappa d kappa)
    (hfar : ∀ alpha ∈ F.support,
      M < Hermite1DimdLEAN.blockDistance j (Hermite1DimdLEAN.blockIndexMulti alpha)) :
    Hermite1DimdLEAN.remainderPart j M ⟨F⟩ = ⟨F⟩ := by
  unfold Hermite1DimdLEAN.remainderPart
  congr
  ext alpha
  by_cases hα : alpha ∈ F.support
  · have hdist := hfar alpha hα
    simp [Hermite1DimdLEAN.farCoeffSet, Hermite1DimdLEAN.FiniteHermiteSum.support, hdist]
  · simp [Hermite1DimdLEAN.farCoeffSet, Hermite1DimdLEAN.FiniteHermiteSum.support,
      Finsupp.notMem_support_iff.mp hα]

theorem annulusMassPartition
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) (H : Pkappa d kappa) :
    lowAnnulusMass J (ofPkappa kappa H) + highAnnulusMass J (ofPkappa kappa H) = ‖H‖ ^ 2 := by
  let _ := hd
  /-
  This is the assembly-facing finite partition identity. The eventual proof
  should keep the coercion `Pkappa -> Skappa` hidden behind this lemma.
  -/
  unfold highAnnulusMass
  ring_nf
  simpa using ofPkappa_total_mass_wip hd kappa H

theorem lowAnnulusProjection
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (J : Nat) :
    ∃ E : Finset (Idx d), ∃ rho : ℝ, 0 < rho ∧
      ∀ {H : Pkappa d kappa},
        ‖H‖ = 1 ->
        Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= rho ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let _ := hd
  /-
  Frozen bridge from finite coefficient control to low-annulus mass control.
  -/
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, htail, hpartial⟩ :=
    Hermite1DimdLEAN.finitePartialLeakage (κ := kappa)
  have hsmall_event :
      ∀ᶠ M : ℕ in Filter.atTop,
        Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M < 1 / 16 := by
    exact htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  rw [Filter.eventually_atTop] at hsmall_event
  obtain ⟨M, hM⟩ := hsmall_event
  let E : Finset (Idx d) := nearLowCoeffSet_wip (d := d) J M
  let rho : ℝ := 1 / 16
  refine ⟨E, rho, by norm_num [rho], ?_⟩
  intro H hH_norm hcoeff_small
  let Hnear : Pkappa d kappa := truncateFinset E (ofPkappa kappa H)
  let Hfar : Pkappa d kappa := H - Hnear
  have hdecomp : Hnear + Hfar = H := by
    ext alpha
    simp [Hfar, Hnear, sub_eq_add_neg, add_left_comm]
  have hnear_norm_sq :
      ‖Hnear‖ ^ 2 = Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    calc
      ‖Hnear‖ ^ 2
          = Finset.sum E (fun alpha => ‖coeffSkappa (ofPkappa kappa H) alpha‖ ^ 2) := by
              simpa [Hnear] using exact_truncate_coeff_energy hd E (ofPkappa kappa H)
      _ = Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro alpha hα
            simp [coeff_ofPkappa, hd]
  have hnear_low :
      lowAnnulusMass J (ofPkappa kappa Hnear) ≤ rho := by
    calc
      lowAnnulusMass J (ofPkappa kappa Hnear) ≤ ‖Hnear‖ ^ 2 := by
        simpa [lowAnnulusMass] using
          finite_sum_annulusMass_le_wip hd kappa Hnear (lowAnnuli d J)
      _ = Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := hnear_norm_sq
      _ ≤ rho := hcoeff_small
  have hH_sq : ‖H‖ ^ 2 = 1 := by
    nlinarith [hH_norm]
  have hfar_norm_sq_le_one : ‖Hfar‖ ^ 2 ≤ 1 := by
    calc
      ‖Hfar‖ ^ 2 ≤ ‖H‖ ^ 2 := by
        simpa [Hfar, Hnear] using norm_sq_farPart_le_wip kappa E H
      _ = 1 := hH_sq
  have hfar_norm_sq_nonneg : 0 ≤ ‖Hfar‖ ^ 2 := by
    positivity
  have hfar_self :
      ∀ j ∈ lowAnnuli d J,
        Hermite1DimdLEAN.remainderPart j M ⟨Hfar⟩ = ⟨Hfar⟩ := by
    intro j hj
    apply remainderPart_eq_self_of_support_far_wip kappa j M Hfar
    intro alpha hα
    have hα_ne : Hfar alpha ≠ 0 := Finsupp.mem_support_iff.mp hα
    have hnotE : alpha ∉ E := by
      intro hE
      have hzero : Hfar alpha = 0 := by
        simpa [Hfar, Hnear, hE] using farPart_apply_wip kappa E H alpha
      exact hα_ne hzero
    by_contra hdist
    have hmemE : alpha ∈ E := by
      exact
        (mem_nearLowCoeffSet_wip (J := J) (M := M) alpha).mpr
          ⟨j, hj, Nat.not_lt.mp hdist⟩
    exact hnotE hmemE
  have hloc_nonneg :
      0 ≤ Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M := by
    unfold Hermite1DimdLEAN.localizationLeakageCoefficient
    positivity
  have hloc_small :
      Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M ≤ rho := by
    exact le_of_lt (by simpa [rho] using hM M le_rfl)
  have hfar_low :
      lowAnnulusMass J (ofPkappa kappa Hfar) ≤ rho := by
    calc
      lowAnnulusMass J (ofPkappa kappa Hfar)
          = Finset.sum (lowAnnuli d J) (fun j =>
              Hermite1DimdLEAN.annulusMass j
                (Hermite1DimdLEAN.evalHermiteSum kappa
                  (Hermite1DimdLEAN.remainderPart j M ⟨Hfar⟩))) := by
              unfold lowAnnulusMass
              refine Finset.sum_congr rfl ?_
              intro j hj
              calc
                annulusMass j (ofPkappa kappa Hfar)
                    = Hermite1DimdLEAN.annulusMass j
                        (Hermite1DimdLEAN.evalHermiteSum kappa ⟨Hfar⟩) := by
                            exact annulusMass_ofPkappa_eq_annulusMass_wip hd kappa j Hfar
                _ = Hermite1DimdLEAN.annulusMass j
                      (Hermite1DimdLEAN.evalHermiteSum kappa
                        (Hermite1DimdLEAN.remainderPart j M ⟨Hfar⟩)) := by
                          rw [hfar_self j hj]
      _ ≤ Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M *
            Hermite1DimdLEAN.hermiteNormSq kappa ⟨Hfar⟩ := by
              simpa using hpartial (lowAnnuli d J) M ⟨Hfar⟩
      _ = Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M * ‖Hfar‖ ^ 2 := by
            rw [hermiteNormSq_eq_norm_sq_wip kappa Hfar]
      _ ≤ Hermite1DimdLEAN.localizationLeakageCoefficient C c B d M := by
            nlinarith [hloc_nonneg, hfar_norm_sq_nonneg, hfar_norm_sq_le_one]
      _ ≤ rho := hloc_small
  calc
    lowAnnulusMass J (ofPkappa kappa H)
      ≤ 2 * lowAnnulusMass J (ofPkappa kappa Hnear) +
          2 * lowAnnulusMass J (ofPkappa kappa Hfar) := by
            simpa [hdecomp] using lowAnnulusMass_add_le_two_wip hd kappa J Hnear Hfar
    _ ≤ 2 * rho + 2 * rho := by
          nlinarith [hnear_low, hfar_low]
    _ = 1 / 4 := by
          norm_num [rho]

end DimdPolyLEAN
