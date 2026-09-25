/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingExtraction
public import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximalProof

/-!
# Sparse domination of a finite laminar maximal function

Principal intervals are constructed by descending-length finite induction.
After selecting a longest interval, retain only intervals outside it or with
average more than ten times its average. This gives both a covering estimate
and strict average separation of every nested pair of selected intervals.
The actual maximal stopping children therefore supply the sparse major sets.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson.FiniteLaminarMaximalSparse

open KrauseLaceyStoppingExtraction


noncomputable
section

/-- Properly nested intervals in the family have norm averages separated by a factor greater
than ten. -/
def AverageSeparated (f : ℝ → ℂ) (R : Finset RealInterval) : Prop :=
  ∀ I ∈ R, ∀ J ∈ R, I ≠ J → J.carrier ⊆ I.carrier →
    10 * intervalL1Average f I < intervalL1Average f J

/-- An actual principal family, together with its covering and average
separation invariants. No sparse or stopping-tree existence is assumed. -/
theorem exists_principal_family (S : Finset RealInterval) (f : ℝ → ℂ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    ∃ R : Finset RealInterval, R ⊆ S ∧ AverageSeparated f R ∧
      ∀ J ∈ S, ∃ I ∈ R, J.carrier ⊆ I.carrier ∧
        intervalL1Average f J ≤ 10 * intervalL1Average f I := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨I, hI, hmax⟩ := S.exists_max_image RealInterval.length hS
      let T := S.filter fun J ↦ ¬ J.carrier ⊆ I.carrier ∨
        10 * intervalL1Average f I < intervalL1Average f J
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hIT : I ∉ T := by
        simp only [T, Finset.mem_filter]
        intro hi
        rcases hi.2 with hn | hb
        · exact hn Subset.rfl
        · linarith [intervalL1Average_nonneg f I]
      have hstrict : T ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hTS, fun h ↦ hIT (h.symm ▸ hI)⟩
      obtain ⟨R, hRT, hsep, hcover⟩ := ih T hstrict (hlam.mono hTS)
      refine ⟨insert I R, Finset.insert_subset hI (hRT.trans hTS), ?_, ?_⟩
      · intro J hJ K hK hJK hsub
        rcases Finset.mem_insert.mp hJ with hJI | hJR
        · subst J
          have hKR : K ∈ R := (Finset.mem_insert.mp hK).resolve_left hJK.symm
          exact ((Finset.mem_filter.mp (hRT hKR)).2).resolve_left
            (not_not.mpr hsub)
        · rcases Finset.mem_insert.mp hK with hKI | hKR
          · subst K
            exact (hJK (interval_eq_of_carrier_subset_of_length_le hsub
              (hmax J (hTS (hRT hJR)))).symm).elim
          · exact hsep J hJR K hKR hJK hsub
      · intro J hJ
        by_cases hJT : J ∈ T
        · obtain ⟨K, hK, hJK, hb⟩ := hcover J hJT
          exact ⟨K, Finset.mem_insert_of_mem hK, hJK, hb⟩
        · have hnot : ¬ (¬ J.carrier ⊆ I.carrier ∨
              10 * intervalL1Average f I < intervalL1Average f J) := by
            intro hh
            exact hJT (Finset.mem_filter.mpr ⟨hJ, hh⟩)
          exact ⟨I, Finset.mem_insert_self _ _, not_not.mp (not_or.mp hnot).1,
            le_of_not_gt (not_or.mp hnot).2⟩
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [AverageSeparated]
      · intro J hJ
        exact (hS ⟨J, hJ⟩).elim

/-- The constructed average separation implies the complete stopping-tree
separation invariant, and hence actual sparse major subsets. -/
theorem isSparse_of_averageSeparated (R : Finset RealInterval) (f : ℝ → ℂ)
    (hf : Integrable f) (hsep : AverageSeparated f R)
    (hlam : Set.Pairwise (↑R : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    IsSparse (1 / 4) (↑R : Set RealInterval) := by
  apply krauseLacey_finiteStoppingTree_isSparse R (stoppingChildren R f 0) f 0 hf
    (integrable_zero ℝ ℂ volume)
  · intro I hI
    exact stoppingChildren_pairwiseDisjoint f 0 I hlam
  · intro I hI J hJ
    exact (stoppingChildren_bad hJ).1
  · intro I hI J hJ
    exact (stoppingChildren_bad hJ).2
  · intro I hI J hJ hIJ
    rcases hlam hI hJ hIJ with hsub | hsub | hdis
    · exact Or.inr (Or.inr (badDescendant_subset_stoppingChild
        (mem_badDescendants_iff.mpr ⟨hI, hsub, Or.inl (hsep J hJ I hI hIJ.symm hsub)⟩)))
    · exact Or.inr (Or.inl (badDescendant_subset_stoppingChild
        (mem_badDescendants_iff.mpr ⟨hJ, hsub, Or.inl (hsep I hI J hJ hIJ hsub)⟩)))
    · exact Or.inl hdis

theorem localAverage_one_eq_intervalL1Average (f : ℝ → ℂ) (I : RealInterval) :
    localAverage 1 f I = intervalL1Average f I := by
  simp [localAverage, intervalL1Average]

/-- The actual finite maximal average, with interval membership retained
inside the supremum. -/
def finiteLaminarMaximal (S : Finset RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ I ∈ S, ⨆ (_ : x ∈ I.carrier), ENNReal.ofReal (localAverage 1 f I)

/-- The positive sparse averaging function associated to a finite family. -/
def sparseAveragingFunction (R : Finset RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑ I ∈ R, I.carrier.indicator (fun _ ↦ ENNReal.ofReal (localAverage 1 f I)) x

theorem finiteLaminarMaximal_le_of_cover
    (S R : Finset RealInterval) (f : ℝ → ℂ)
    (hcover : ∀ J ∈ S, ∃ I ∈ R, J.carrier ⊆ I.carrier ∧
      intervalL1Average f J ≤ 10 * intervalL1Average f I) (x : ℝ) :
    finiteLaminarMaximal S f x ≤ 10 * sparseAveragingFunction R f x := by
  classical
  apply iSup_le
  intro J
  apply iSup_le
  intro hJ
  apply iSup_le
  intro hx
  obtain ⟨I, hI, hJI, havg⟩ := hcover J hJ
  have hpoint : ENNReal.ofReal (localAverage 1 f I) ≤ sparseAveragingFunction R f x := by
    unfold sparseAveragingFunction
    have hh := Finset.single_le_sum (f := fun K : RealInterval ↦
      K.carrier.indicator (fun _ ↦ ENNReal.ofReal (localAverage 1 f K)) x)
      (fun K (_hK : K ∈ R) ↦ zero_le) hI
    simpa only [Set.indicator_of_mem (hJI hx)] using hh
  calc
    ENNReal.ofReal (localAverage 1 f J) ≤ 10 * ENNReal.ofReal (localAverage 1 f I) := by
      simpa only [localAverage_one_eq_intervalL1Average,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal havg
    _ ≤ _ := mul_le_mul' le_rfl hpoint

/-- Pointwise sparse domination with universal constant ten. -/
theorem exists_sparse_pointwise_domination (S : Finset RealInterval) (f : ℝ → ℂ)
    (hf : Integrable f)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    ∃ R : Finset RealInterval, R ⊆ S ∧ IsSparse (1 / 4) (↑R : Set RealInterval) ∧
      ∀ x, finiteLaminarMaximal S f x ≤ 10 * sparseAveragingFunction R f x := by
  obtain ⟨R, hRS, hsep, hcover⟩ := exists_principal_family S f hlam
  exact ⟨R, hRS, isSparse_of_averageSeparated R f hf hsep (hlam.mono hRS),
    finiteLaminarMaximal_le_of_cover S R f hcover⟩

/-- Integrating the positive sparse averaging function gives exactly the
project's `(1,1)` sparse form. -/
theorem lintegral_sparseAveragingFunction_mul_enorm
    (R : Finset RealInterval) (f g : ℝ → ℂ) (hg : Integrable g) :
    (∫⁻ x, sparseAveragingFunction R f x * ‖g x‖ₑ) =
      sparseForm 1 f g (↑R : Set RealInterval) := by
  classical
  have hind (I : RealInterval) (x : ℝ) :
      I.carrier.indicator (fun _ ↦ ENNReal.ofReal (localAverage 1 f I)) x * ‖g x‖ₑ =
        ENNReal.ofReal (localAverage 1 f I) *
          I.carrier.indicator (fun y ↦ ‖g y‖ₑ) x := by
    by_cases hx : x ∈ I.carrier <;> simp [hx]
  calc
    _ = ∫⁻ x, ∑ I ∈ R, ENNReal.ofReal (localAverage 1 f I) *
        I.carrier.indicator (fun y ↦ ‖g y‖ₑ) x := by
      simp only [sparseAveragingFunction, Finset.sum_mul, hind]
    _ = ∑ I ∈ R, ENNReal.ofReal (localAverage 1 f I) *
        ∫⁻ x in I.carrier, ‖g x‖ₑ := by
      have hm (I : RealInterval) : AEMeasurable (fun x ↦
          ENNReal.ofReal (localAverage 1 f I) *
            I.carrier.indicator (fun y ↦ ‖g y‖ₑ) x) volume :=
        aemeasurable_const.mul (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier)
      rw [lintegral_finsetSum' _ (fun I _ ↦ hm I)]
      apply Finset.sum_congr rfl
      intro I hI
      rw [lintegral_const_mul'' _
        (hg.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier),
        lintegral_indicator I.measurableSet_carrier]
    _ = ∑ I ∈ R, ENNReal.ofReal
        (I.length * localAverage 1 f I * localAverage 1 g I) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [← ofReal_integral_norm_eq_lintegral_enorm hg.integrableOn,
        ← ENNReal.ofReal_mul (localAverage_nonneg 1 f I),
        ← intervalL1Average_mul_length g I, localAverage_one_eq_intervalL1Average g I]
      congr 1
      ring
    _ = _ := by
      rw [sparseForm]
      exact (Finset.tsum_subtype R fun I ↦ ENNReal.ofReal
        (I.length * localAverage 1 f I * localAverage 1 g I)).symm

/-- Sparse domination of the finite laminar maximal pairing, with a universal
constant ten and the actual constructed subfamily. -/
theorem exists_sparse_domination_finiteLaminarMaximal
    (S : Finset RealInterval) (f g : L0Infinity)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    ∃ R : Finset RealInterval, R ⊆ S ∧ IsSparse (1 / 4) (↑R : Set RealInterval) ∧
      (∫⁻ x, (⨆ I ∈ S, ⨆ (_ : x ∈ I.carrier),
        ENNReal.ofReal (localAverage 1 f I)) * ‖g x‖ₑ) ≤
          10 * sparseForm 1 f g (↑R : Set RealInterval) := by
  obtain ⟨R, hRS, hR, hpoint⟩ :=
    exists_sparse_pointwise_domination S f f.integrable_finiteSparseProof hlam
  refine ⟨R, hRS, hR, ?_⟩
  calc
    _ ≤ ∫⁻ x, 10 * (sparseAveragingFunction R f x * ‖g x‖ₑ) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← mul_assoc]
      exact mul_le_mul' (hpoint x) le_rfl
    _ = 10 * ∫⁻ x, sparseAveragingFunction R f x * ‖g x‖ₑ := by
      exact lintegral_const_mul' _ _ (by norm_num)
    _ = _ := by
      rw [lintegral_sparseAveragingFunction_mul_enorm R f g g.integrable_finiteSparseProof]


end
end QuadraticCarleson.FiniteLaminarMaximalSparse
