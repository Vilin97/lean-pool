/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FinitePVMSelection
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.LeadingCutoff
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteValueSeparation
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteValueFibers
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramBandPolar
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFan
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.StandardInstances

/-!
# Approximate leading singular families

The first `k` approximation numbers above `ε` are grouped by equal value.  A
single finite separation radius gives disjoint narrow Gram bands for the
distinct values.  Cumulative approximation-number cutoff ranks are subtracted
to obtain the multiplicity of each band, and finite orthonormal families are
selected from the corresponding PVM ranges.

The polar partial isometry converts the resulting Gram residuals into both
approximate singular equations.  No compactness, singular-value attainment,
or tactic search is used.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace BigOperators
open Set
open ApproximationNumber

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A finite simultaneous approximate singular system for the non-negligible
part of the first `k` approximation numbers. -/
structure ApproximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → E0
  left : Fin count → E1
  right_orthonormal : Orthonormal ℂ right
  left_orthonormal : Orthonormal ℂ left
  selected_large : ∀ i : Fin count, ε < X.approximationNumber i
  apply_residual : ∀ i : Fin count,
    ‖X (right i) - (X.approximationNumber i : ℂ) • left i‖ ≤ ε
  adjoint_residual : ∀ i : Fin count,
    ‖X.adjoint (left i) - (X.approximationNumber i : ℂ) • right i‖ ≤ ε
  tail_small : ∀ n, count ≤ n → n < k → X.approximationNumber n ≤ ε

namespace ApproximateLeadingSingularFamily

variable {X : E0 →L[ℂ] E1} {k : ℕ} {ε : ℝ}

/-- The right vectors of an approximate leading singular family are unit vectors. -/
@[simp] theorem norm_right (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.right i‖ = 1 :=
  F.right_orthonormal.norm_eq_one i

/-- The left vectors of an approximate leading singular family are unit vectors. -/
@[simp] theorem norm_left (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.left i‖ = 1 :=
  F.left_orthonormal.norm_eq_one i

/-- Negating the right family preserves orthonormality. -/
theorem orthonormal_neg_right
    (F : ApproximateLeadingSingularFamily X k ε) :
    Orthonormal ℂ (fun i => -F.right i) := by
  have hright := F.right_orthonormal
  rw [orthonormal_iff_ite] at hright ⊢
  intro i j
  simpa using hright i j

end ApproximateLeadingSingularFamily

/-- The finite Gram-band data used before applying the polar partial isometry. -/
structure GramSpectralBandModel
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → E0
  right_orthonormal : Orthonormal ℂ right
  right_mem_polarInitial : ∀ i, right i ∈ X.polarInitial
  gram_residual : ∀ i,
    ‖gramOperator X (right i) -
      ((X.approximationNumber (i : ℕ)) ^ 2 : ℂ) • right i‖ ≤
        ε * X.approximationNumber (i : ℕ) / 4
  selected_large : ∀ i : Fin count,
    ε < X.approximationNumber (i : ℕ)
  tail_small : ∀ n, count ≤ n → n < k → X.approximationNumber n ≤ ε

/-- Distinct value labels determine disjoint Gram bands. -/
theorem gramBands_disjoint
    {n : ℕ} (a : Fin n → ℝ) {η : ℝ}
    (hη0 : 0 ≤ η)
    (hηa : ∀ i, η < a i)
    (hsep : ∀ i j, a i ≠ a j → 2 * η < |a i - a j|)
    {leftLabel rightLabel : FiniteValueLabel a}
    (hlabels : leftLabel ≠ rightLabel) :
    Disjoint
      (Set.Icc ((leftLabel.1 - η) ^ 2) ((leftLabel.1 + η) ^ 2))
      (Set.Icc ((rightLabel.1 - η) ^ 2) ((rightLabel.1 + η) ^ 2)) := by
  have hvals : leftLabel.1 ≠ rightLabel.1 := by
    intro h
    exact hlabels (Subtype.ext h)
  rcases Finset.mem_image.mp leftLabel.2 with ⟨i, _, hi⟩
  rcases Finset.mem_image.mp rightLabel.2 with ⟨j, _, hj⟩
  have hηLeft : η < leftLabel.1 := by simpa only [hi] using hηa i
  have hηRight : η < rightLabel.1 := by simpa only [hj] using hηa j
  have hgap : 2 * η < |leftLabel.1 - rightLabel.1| := by
    have hij : a i ≠ a j := by simpa only [hi, hj] using hvals
    simpa only [hi, hj] using hsep i j hij
  rw [Set.disjoint_left]
  intro t htLeft htRight
  rcases lt_or_gt_of_ne hvals with hlt | hgt
  · have hcenter : leftLabel.1 + η < rightLabel.1 - η := by
      rw [abs_of_neg (sub_neg.mpr hlt)] at hgap
      nlinarith
    have hleftUpper : 0 < leftLabel.1 + η := by nlinarith [hηLeft, hη0]
    have hrightLower : 0 < rightLabel.1 - η := by linarith
    have hsquare : (leftLabel.1 + η) ^ 2 < (rightLabel.1 - η) ^ 2 := by
      nlinarith
    exact (not_lt_of_ge htRight.1) (htLeft.2.trans_lt hsquare)
  · have hcenter : rightLabel.1 + η < leftLabel.1 - η := by
      rw [abs_of_pos (sub_pos.mpr hgt)] at hgap
      nlinarith
    have hrightUpper : 0 < rightLabel.1 + η := by nlinarith [hηRight, hη0]
    have hleftLower : 0 < leftLabel.1 - η := by linarith
    have hsquare : (rightLabel.1 + η) ^ 2 < (leftLabel.1 - η) ^ 2 := by
      nlinarith
    exact (not_lt_of_ge htLeft.1) (htRight.2.trans_lt hsquare)

/-- A repeated approximation value supplies enough dimensions in its Gram spectral band. -/
private theorem finiteValueFiber_card_le_gramBand_rank
    (X : E0 →L[ℂ] E1) (count : ℕ) {η : ℝ} (hη0 : 0 < η)
    (hηa : ∀ i : Fin count, η < X.approximationNumber (i : ℕ))
    (label : FiniteValueLabel (fun i : Fin count => X.approximationNumber (i : ℕ))) :
    ((finiteValueFiber (fun i : Fin count => X.approximationNumber (i : ℕ)) label).card :
      Cardinal) ≤ ((gramSpectralPVM X).proj
        (Set.Icc ((label.1 - η) ^ 2) ((label.1 + η) ^ 2)) measurableSet_Icc).rank := by
  classical
  let a : Fin count → ℝ := fun i => X.approximationNumber (i : ℕ)
  let P := gramSpectralPVM X
  let p : ℕ := (finiteValueFirst a label).val
  let q : ℕ := (finiteValueLast a label).val
  have hηLabel : η < label.1 := by
    rcases Finset.mem_image.mp label.2 with ⟨i, _, hi⟩
    simpa only [hi] using hηa i
  have hlow0 : 0 ≤ label.1 - η := by linarith
  have hlowlt :
      label.1 - η < X.approximationNumber q := by
    have hqval : X.approximationNumber q = label.1 := by
      simpa only [a, q] using finiteValueLast_value a label
    rw [hqval]
    linarith
  have huplt :
      X.approximationNumber p < label.1 + η := by
    have hpval : X.approximationNumber p = label.1 := by
      simpa only [a, p] using finiteValueFirst_value a label
    rw [hpval]
    linarith
  have hlowRank : ((q + 1 : ℕ) : Cardinal) ≤
      (P.proj (Set.Ici ((label.1 - η) ^ 2)) measurableSet_Ici).rank := by
    simpa only [P] using
      natCast_succ_le_rank_gramProjection_Ici_of_lt_approximationNumber
        X q hlow0 hlowlt
  have hupRank :
      (P.proj (Set.Ioi ((label.1 + η) ^ 2)) measurableSet_Ioi).rank ≤
        (p : Cardinal) := by
    simpa only [P] using
      rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt
        X p (by linarith) huplt
  have hspanRank : (((q + 1) - p : ℕ) : Cardinal) ≤
      (P.proj (Set.Icc ((label.1 - η) ^ 2) ((label.1 + η) ^ 2))
        measurableSet_Icc).rank :=
    natCast_sub_le_rank_pvm_Icc_of_cutoff_bounds P
      (by nlinarith : (label.1 - η) ^ 2 ≤ (label.1 + η) ^ 2)
      p (q + 1) hlowRank hupRank
  have hcard : (finiteValueFiber a label).card ≤ q + 1 - p := by
    simpa only [p, q] using finiteValueFiber_card_le_span a label
  have hcardCast : ((finiteValueFiber a label).card : Cardinal) ≤
      (((q + 1) - p : ℕ) : Cardinal) := by exact_mod_cast hcard
  exact hcardCast.trans hspanRank

/-- Labeling indices by their value fibers preserves the complete finite index set. -/
private noncomputable def finiteValueIndexEquiv {count : ℕ} (a : Fin count → ℝ) :
    (Σ label : FiniteValueLabel a, {i : Fin count // i ∈ finiteValueFiber a label}) ≃
      Fin count := by
  classical
  let Index := Σ label : FiniteValueLabel a,
    {i : Fin count // i ∈ finiteValueFiber a label}
  let toIndex : Index → Fin count := fun z => z.2.1
  have htoIndex_inj : Function.Injective toIndex := by
    rintro ⟨leftLabel, i⟩ ⟨rightLabel, j⟩ hij
    change i.1 = j.1 at hij
    have hiVal : a i.1 = leftLabel.1 :=
      (mem_finiteValueFiber a leftLabel i.1).mp i.2
    have hjVal : a j.1 = rightLabel.1 :=
      (mem_finiteValueFiber a rightLabel j.1).mp j.2
    have hlabelValue : leftLabel.1 = rightLabel.1 := by
      calc
        leftLabel.1 = a i.1 := hiVal.symm
        _ = a j.1 := by rw [hij]
        _ = rightLabel.1 := hjVal
    have hlabel : leftLabel = rightLabel := Subtype.ext hlabelValue
    subst rightLabel
    have hindex : i = j := Subtype.ext hij
    subst j
    rfl
  have htoIndex_surj : Function.Surjective toIndex := by
    intro i
    refine ⟨⟨finiteValueLabel a i,
      -- Unfolding `finiteValueFiber` beats `mem_finiteValueFiber` to the goal and leaves a
      -- raw `setOf` membership that no longer discharges itself.
      ⟨i, by simp [finiteValueLabel]⟩⟩, rfl⟩
  exact Equiv.ofBijective toIndex ⟨htoIndex_inj, htoIndex_surj⟩

/-- If no approximation value exceeds the threshold, the empty family is a band model. -/
private theorem gramSpectralBandModel_of_leadingCount_eq_zero
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) (hcount0 : leadingCount X k ε = 0) :
    Nonempty (GramSpectralBandModel X k ε) := by
  exact ⟨{
      count := 0
      count_le := Nat.zero_le k
      right := fun i => Fin.elim0 i
      right_orthonormal := Orthonormal.of_isEmpty _
      right_mem_polarInitial := fun i => Fin.elim0 i
      gram_residual := fun i => Fin.elim0 i
      selected_large := fun i => Fin.elim0 i
      tail_small := by
        intro n _ hn
        exact approximationNumber_le_of_leadingCount_le X k ε
          (by simpa only [hcount0] using Nat.zero_le n) hn
    }⟩

/-- Explicit finite PVM band assembly for the strict leading prefix. -/
theorem exists_gramSpectralBandModel
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (GramSpectralBandModel X k ε) := by
  classical
  let count := leadingCount X k ε
  have hcount_le : count ≤ k := by
    simpa only [count] using leadingCount_le X k ε
  have hselected : ∀ i : Fin count,
      ε < X.approximationNumber (i : ℕ) := by
    intro i
    exact approximationNumber_gt_of_lt_leadingCount X k ε i.isLt
  have htail : ∀ n, count ≤ n → n < k →
      X.approximationNumber n ≤ ε := by
    intro n hcountn hnk
    exact approximationNumber_le_of_leadingCount_le X k ε hcountn hnk
  by_cases hcount0 : count = 0
  · exact gramSpectralBandModel_of_leadingCount_eq_zero X k ε hcount0
  · let a : Fin count → ℝ := fun i => X.approximationNumber (i : ℕ)
    have ha : ∀ i, 0 < a i := by
      intro i
      exact hε.trans (hselected i)
    obtain ⟨η, hη0, hηε, hηa, hηsep⟩ :=
      exists_uniform_positive_separation a ha hε
    let P := gramSpectralPVM X
    let band : FiniteValueLabel a → Set ℝ := fun label =>
      Set.Icc ((label.1 - η) ^ 2) ((label.1 + η) ^ 2)
    have hbandRank : ∀ label : FiniteValueLabel a,
        ((finiteValueFiber a label).card : Cardinal) ≤
          (P.proj (band label) measurableSet_Icc).rank := by
      intro label
      exact finiteValueFiber_card_le_gramBand_rank X count hη0 hηa label
    have hselect : ∀ label : FiniteValueLabel a,
        ∃ v : Fin (finiteValueFiber a label).card → E0,
          Orthonormal ℂ v ∧
          ∀ i, v i ∈ (P.proj (band label) measurableSet_Icc).range := by
      intro label
      exact exists_orthonormal_mem_pvmRange_of_natCast_le_rank
        P (band label) measurableSet_Icc _ (hbandRank label)
    choose blockVec hblockOrtho hblockMem using hselect
    let Index := Σ label : FiniteValueLabel a,
      {i : Fin count // i ∈ finiteValueFiber a label}
    let toIndex : Index → Fin count := fun z => z.2.1
    let indexEquiv : Index ≃ Fin count := finiteValueIndexEquiv a
    let allVec : Index → E0 := fun z =>
      blockVec z.1 ((finiteValueFiber a z.1).equivFin z.2)
    have hallOrtho : Orthonormal ℂ allVec := by
      rw [orthonormal_iff_ite]
      rintro ⟨leftLabel, i⟩ ⟨rightLabel, j⟩
      by_cases hlabels : leftLabel = rightLabel
      · subst rightLabel
        by_cases hij : i = j
        · subst j
          simp only [allVec]
          have hnorm := (hblockOrtho leftLabel).norm_eq_one
            ((finiteValueFiber a leftLabel).equivFin i)
          rw [inner_self_eq_norm_sq_to_K, hnorm]
          norm_num
        · have hidx :
              (finiteValueFiber a leftLabel).equivFin i ≠
                (finiteValueFiber a leftLabel).equivFin j :=
            (finiteValueFiber a leftLabel).equivFin.injective.ne hij
          have hinner := (orthonormal_iff_ite.mp (hblockOrtho leftLabel))
            ((finiteValueFiber a leftLabel).equivFin i)
            ((finiteValueFiber a leftLabel).equivFin j)
          rw [ite_eq_right hidx] at hinner
          have hsigma : (Sigma.mk leftLabel i : Index) ≠ Sigma.mk leftLabel j := by
            intro h
            cases h
            exact hij rfl
          simpa only [allVec, ite_eq_right hsigma] using hinner
      · have hdisj := gramBands_disjoint a hη0.le hηa hηsep hlabels
        have hinner := inner_eq_zero_of_mem_disjoint_pvmRanges P
          measurableSet_Icc measurableSet_Icc hdisj
          (hblockMem leftLabel ((finiteValueFiber a leftLabel).equivFin i))
          (hblockMem rightLabel ((finiteValueFiber a rightLabel).equivFin j))
        have hsigma : (Sigma.mk leftLabel i : Index) ≠ Sigma.mk rightLabel j := by
          intro h
          exact hlabels (Sigma.mk.inj_iff.mp h).1
        simpa only [allVec, band, ite_eq_right hsigma] using hinner
    let right : Fin count → E0 := allVec ∘ indexEquiv.symm
    have hrightOrtho : Orthonormal ℂ right :=
      hallOrtho.comp indexEquiv.symm indexEquiv.symm.injective
    have hrightBand : ∀ i : Fin count,
        right i ∈ (P.proj (band (indexEquiv.symm i).1) measurableSet_Icc).range := by
      intro i
      exact hblockMem (indexEquiv.symm i).1
        ((finiteValueFiber a (indexEquiv.symm i).1).equivFin
          (indexEquiv.symm i).2)
    have hrightValue : ∀ i : Fin count,
        a i = (indexEquiv.symm i).1.1 := by
      intro i
      have heq : toIndex (indexEquiv.symm i) = i := indexEquiv.apply_symm_apply i
      have hmem := (indexEquiv.symm i).2.2
      have hval := (mem_finiteValueFiber a (indexEquiv.symm i).1
        (indexEquiv.symm i).2.1).mp hmem
      change (indexEquiv.symm i).2.1 = i at heq
      simpa only [heq] using hval
    have hrightInitial : ∀ i : Fin count, right i ∈ X.polarInitial := by
      intro i
      have hLabelEta : η < (indexEquiv.symm i).1.1 := by
        have h := hηa i
        rwa [hrightValue i] at h
      have hLower : 0 < ((indexEquiv.symm i).1.1 - η) ^ 2 :=
        sq_pos_of_pos (sub_pos.mpr hLabelEta)
      exact mem_polarInitial_of_mem_gramBand X hLower
        (by simpa only [P, band] using hrightBand i)
    have hgramResidual : ∀ i : Fin count,
        ‖gramOperator X (right i) -
          ((X.approximationNumber (i : ℕ)) ^ 2 : ℂ) • right i‖ ≤
            ε * X.approximationNumber (i : ℕ) / 4 := by
      intro i
      have hLabelEta : η < (indexEquiv.symm i).1.1 := by
        have h := hηa i
        rwa [hrightValue i] at h
      have hnorm : ‖right i‖ = 1 := hrightOrtho.norm_eq_one i
      have hres := gram_residual_le_of_mem_band X hη0 hLabelEta hηε hnorm
        (by simpa only [P, band] using hrightBand i)
      simpa only [a, hrightValue i, Complex.ofReal_pow] using hres
    exact ⟨{
      count := count
      count_le := hcount_le
      right := right
      right_orthonormal := hrightOrtho
      right_mem_polarInitial := hrightInitial
      gram_residual := hgramResidual
      selected_large := hselected
      tail_small := htail
    }⟩

/-- A Gram spectral-band model produces the required simultaneous approximate
singular family via the polar partial isometry. -/
def GramSpectralBandModel.toApproximateLeadingSingularFamily
    {X : E0 →L[ℂ] E1} {k : ℕ} {ε : ℝ}
    (M : GramSpectralBandModel X k ε) (hε : 0 ≤ ε) :
    ApproximateLeadingSingularFamily X k ε := by
  let left : Fin M.count → E1 := fun i => X.polarPartial (M.right i)
  have hleftOrtho : Orthonormal ℂ left := by
    rw [orthonormal_iff_ite]
    intro i j
    unfold left
    rw [X.inner_polarPartial_apply_of_mem
      (M.right_mem_polarInitial i) (M.right_mem_polarInitial j)]
    exact orthonormal_iff_ite.mp M.right_orthonormal i j
  refine {
    count := M.count
    count_le := M.count_le
    right := M.right
    left := left
    right_orthonormal := M.right_orthonormal
    left_orthonormal := hleftOrtho
    selected_large := M.selected_large
    apply_residual := ?_
    adjoint_residual := ?_
    tail_small := M.tail_small
  }
  · intro i
    let value := X.approximationNumber (i : ℕ)
    have hvalue : 0 < value := hε.trans_lt (M.selected_large i)
    have hgram :
        ‖gramOperator X (M.right i) - (value : ℂ) ^ 2 • M.right i‖ ≤
          (ε / 4) * value := by
      convert M.gram_residual i using 1 ; dsimp only [value] ; ring
    have hgramReal :
        ‖gramOperator X (M.right i) - ((value ^ 2 : ℝ) : ℂ) • M.right i‖ ≤
          (ε / 4) * value := by
      simpa only [Complex.ofReal_pow] using hgram
    have hmod := modulus_residual_le_of_gram_residual
      (X := X) (x := M.right i) (lam := value) (δ := ε / 4)
      hvalue (div_nonneg hε (by norm_num)) hgramReal
    calc
      ‖X (M.right i) - (value : ℂ) • left i‖ =
          ‖X.polarPartial
            (X.modulus (M.right i) - (value : ℂ) • M.right i)‖ := by
        unfold left
        rw [map_sub, map_smul, X.polarPartial_apply_modulus]
      _ ≤ ‖X.modulus (M.right i) - (value : ℂ) • M.right i‖ :=
        norm_polarPartial_apply_le X _
      _ ≤ ε / 4 := hmod
      _ ≤ ε := by linarith
  · intro i
    let value := X.approximationNumber (i : ℕ)
    have hvalue : 0 < value := hε.trans_lt (M.selected_large i)
    have hgram :
        ‖gramOperator X (M.right i) - (value : ℂ) ^ 2 • M.right i‖ ≤
          (ε / 4) * value := by
      convert M.gram_residual i using 1 ; dsimp only [value] ; ring
    have hgramReal :
        ‖gramOperator X (M.right i) - ((value ^ 2 : ℝ) : ℂ) • M.right i‖ ≤
          (ε / 4) * value := by
      simpa only [Complex.ofReal_pow] using hgram
    have hmod := modulus_residual_le_of_gram_residual
      (X := X) (x := M.right i) (lam := value) (δ := ε / 4)
      hvalue (div_nonneg hε (by norm_num)) hgramReal
    have hadj : X.adjoint (left i) = X.modulus (M.right i) := by
      unfold left
      rw [X.adjoint_eq_modulus_comp_adjoint_polarPartial,
        ContinuousLinearMap.comp_apply,
        X.adjoint_polarPartial_polarPartial_apply_of_mem
          (M.right_mem_polarInitial i)]
    rw [hadj]
    exact hmod.trans (by linarith)

/-- Simultaneous approximate leading singular families exist for every bounded
operator. -/
theorem exists_approximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (ApproximateLeadingSingularFamily X k ε) := by
  obtain ⟨M⟩ := exists_gramSpectralBandModel X k hε
  exact ⟨M.toApproximateLeadingSingularFamily hε.le⟩

/-- The transformed leading prefix is the selected part plus a uniformly small
omitted tail. -/
theorem sum_doubleAngleTangent_le_selected_add_tail
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hXr : ‖X‖ ≤ r)
    (F : ApproximateLeadingSingularFamily X k ε) :
    (∑ n ∈ Finset.range k,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n)) ≤
      (∑ i : Fin F.count,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i)) +
        (k - F.count) * ((2 / (1 - r ^ 2)) * ε) := by
  classical
  have hcount := F.count_le
  rw [← Finset.sum_range_add_sum_Ico
    (f := fun n => DavisKahan.TanTwoTheta.doubleAngleTangent
      (X.approximationNumber n)) hcount]
  have hhead :
      (∑ n ∈ Finset.range F.count,
          DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n)) =
        ∑ i : Fin F.count,
          DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber i) :=
    (Fin.sum_univ_eq_sum_range
      (fun n => DavisKahan.TanTwoTheta.doubleAngleTangent
        (X.approximationNumber n)) F.count).symm
  rw [hhead]
  apply add_le_add_right
  calc
    (∑ n ∈ Finset.Ico F.count k,
        DavisKahan.TanTwoTheta.doubleAngleTangent (X.approximationNumber n))
        ≤ ∑ _n ∈ Finset.Ico F.count k,
            ((2 / (1 - r ^ 2)) * ε) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnmem := Finset.mem_Ico.mp hn
          have han0 : 0 ≤ X.approximationNumber n :=
            X.approximationNumber_nonneg n
          have hane : X.approximationNumber n ≤ ε :=
            F.tail_small n hnmem.1 hnmem.2
          have hanr : X.approximationNumber n ≤ r :=
            (X.approximationNumber_le_norm n).trans hXr
          unfold DavisKahan.TanTwoTheta.doubleAngleTangent
          have hdenr : 0 < 1 - r ^ 2 := by nlinarith
          have hdena : 0 < 1 - (X.approximationNumber n) ^ 2 := by
            nlinarith
          apply (div_le_iff₀ hdena).2
          have hden_order :
              1 - r ^ 2 ≤ 1 - (X.approximationNumber n) ^ 2 := by
            nlinarith
          have hcoef0 : 0 ≤ (2 / (1 - r ^ 2)) * ε :=
            mul_nonneg (div_nonneg (by norm_num) hdenr.le) hε
          calc
            2 * X.approximationNumber n ≤ 2 * ε := by nlinarith
            _ = ((2 / (1 - r ^ 2)) * ε) * (1 - r ^ 2) := by
              field_simp [ne_of_gt hdenr]
            _ ≤ ((2 / (1 - r ^ 2)) * ε) *
                (1 - (X.approximationNumber n) ^ 2) :=
              mul_le_mul_of_nonneg_left hden_order hcoef0
    _ = (k - F.count) * ((2 / (1 - r ^ 2)) * ε) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
            Nat.cast_sub hcount]

end

end DavisKahan
end TauCeti
