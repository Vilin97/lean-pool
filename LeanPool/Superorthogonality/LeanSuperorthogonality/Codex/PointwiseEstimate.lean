/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
/-
The code in namespace `Codex` was machine generated.
-/
module

-- public import Mathlib

public import LeanPool.Superorthogonality.LeanSuperorthogonality.Defs

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasureSpace ι where
  volume := Measure.count

section PointwiseEstimate

variable {k : ℕ}

namespace Codex

private abbrev pointwiseConstant (k : ℕ) : ENNReal :=
  ((k)! - 1 : ENNReal)

private abbrev pointwiseBound (hk : 2 ≤ k) (a : Fin k → ι → ℂ) : ENNReal :=
  pointwiseConstant k * (B hk a) ^ 2 * (max (A hk a) (B hk a)) ^ (k - 2)

private abbrev normalizedPointwiseBound (hk : 2 ≤ k) (a : Fin k → ι → ℂ) :
    ENNReal :=
  pointwiseConstant k * (max 1 (A hk a)) ^ (k - 2)

private abbrev initFamily {k : ℕ} (a : Fin (k + 1) → ι → ℂ) :
    Fin k → ι → ℂ :=
  fun i ↦ a (Fin.castSucc i)

private abbrev collisionFamily {k : ℕ} (a : Fin (k + 1) → ι → ℂ) (i : Fin k) :
    Fin k → ι → ℂ :=
  Function.update (initFamily a) i
    (fun j ↦ a (Fin.castSucc i) j * a (Fin.last k) j)

private abbrev rescaleFamily (hk : 2 ≤ k) (a : Fin k → ι → ℂ) :
    Fin k → ι → ℂ :=
  fun i ↦ ((B hk a).toReal : ℂ)⁻¹ • a i

/-
The base algebra in the paper: for k = 2, the difference between the off-diagonal
sum Q_2 and the product of sums is exactly the negative diagonal sum.
-/
omit [Countable ι] in
private lemma Q_two_sub_prod_eq_neg_diagonal (a : Fin 2 → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Q a - ∏ i, s (a i) = -(∑' j, a 0 j * a 1 j) := by
  let offDiag : Set (ι × ι) := {p | p.1 ≠ p.2}
  have h_prod_sum : (∏ i, s (a i)) = ∑' p : ι × ι, a 0 p.1 * a 1 p.2 := by
    convert tsum_mul_tsum_of_summable_norm (ha 0) (ha 1) using 1
    exact Fin.prod_univ_two _
  have hQ_pair :
      Q a = ∑' p : ι × ι, offDiag.indicator (fun p ↦ a 0 p.1 * a 1 p.2) p := by
    rw [← Equiv.tsum_eq (finTwoArrowEquiv ι)]
    apply tsum_congr
    intro j
    by_cases hj : j 0 = j 1
    · have hnot : ¬ all_distinct 2 j := by
        intro h
        exact h 0 1 (by decide) hj
      have hnotmem : j ∉ set_all_distinct 2 := hnot
      have hnotmem' : (finTwoArrowEquiv ι j) ∉ offDiag := by
        simpa [offDiag] using hj
      rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hnotmem']
    · have hdist : all_distinct 2 j := by
        intro i i' hii'
        fin_cases i <;> fin_cases i'
        · contradiction
        · exact hj
        · exact fun h ↦ hj h.symm
        · contradiction
      have hmem : j ∈ set_all_distinct 2 := hdist
      have hmem' : (finTwoArrowEquiv ι j) ∈ offDiag := by
        simpa [offDiag] using hj
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      simp [Fin.prod_univ_two]
  have hpair_summable : Summable (fun p : ι × ι ↦ a 0 p.1 * a 1 p.2) :=
    summable_mul_of_summable_norm (ha 0) (ha 1)
  have h_split :
      (∑' p : ι × ι, a 0 p.1 * a 1 p.2) =
        (∑' p : offDiag, a 0 p.1.1 * a 1 p.1.2) +
        (∑' p : (offDiagᶜ : Set (ι × ι)), a 0 p.1.1 * a 1 p.1.2) := by
    rw [← hpair_summable.tsum_subtype_add_tsum_subtype_compl offDiag]
  have hQ_subtype :
      (∑' p : ι × ι, offDiag.indicator (fun p ↦ a 0 p.1 * a 1 p.2) p) =
        ∑' p : offDiag, a 0 p.1.1 * a 1 p.1.2 := by
    exact (tsum_subtype offDiag (fun p : ι × ι ↦ a 0 p.1 * a 1 p.2)).symm
  have hdiag :
      (∑' p : (offDiagᶜ : Set (ι × ι)), a 0 p.1.1 * a 1 p.1.2) =
        ∑' j : ι, a 0 j * a 1 j := by
    have hdiag_eq : ∀ p : (offDiagᶜ : Set (ι × ι)), p.1.1 = p.1.2 := by
      intro p
      have hpnot : ¬ p.1 ∈ offDiag := by
        simpa only [Set.mem_compl_iff] using p.2
      exact Classical.not_not.mp (by simpa [offDiag] using hpnot)
    let diagEquiv : (offDiagᶜ : Set (ι × ι)) ≃ ι :=
      { toFun := fun p : (offDiagᶜ : Set (ι × ι)) ↦ p.1.1
        invFun := fun j ↦ ⟨(j, j), by simp [offDiag]⟩
        left_inv := by
          intro p
          apply Subtype.ext
          have hp := hdiag_eq p
          ext <;> simp [hp]
        right_inv := by
          intro j
          rfl }
    rw [← Equiv.tsum_eq diagEquiv]
    apply tsum_congr
    intro p
    simp [diagEquiv, hdiag_eq p]
  rw [hQ_pair, h_prod_sum, hQ_subtype, h_split, hdiag]
  abel

/-
The analytic estimate in the base case: the diagonal sum is controlled by
Cauchy-Schwarz and the largest l^2 norm.
-/
private lemma diagonal_enorm_tsum_le_B_sq (a : Fin 2 → ι → ℂ)
    (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ‖(∑' j, a 0 j * a 1 j)‖ₑ ≤
      (B (by norm_num : 2 ≤ (2 : ℕ)) a) ^ 2 := by
  have hvolume : (volume : Measure ι) = Measure.count := rfl
  have hholder :
      (∫⁻ j : ι, ‖a 0 j‖ₑ * ‖a 1 j‖ₑ ∂(Measure.count : Measure ι)) ≤
        eLpNorm (a 0) 2 (Measure.count : Measure ι) *
          eLpNorm (a 1) 2 (Measure.count : Measure ι) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have h0 : AEMeasurable (fun j : ι ↦ ‖a 0 j‖ₑ) (Measure.count : Measure ι) :=
      (measurable_of_countable _).aemeasurable
    have h1 : AEMeasurable (fun j : ι ↦ ‖a 1 j‖ₑ) (Measure.count : Measure ι) :=
      (measurable_of_countable _).aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (μ := (Measure.count : Measure ι)) hpq h0 h1
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤),
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simpa [one_div] using h
  have hB0 :
      eLpNorm (a 0) 2 (Measure.count : Measure ι) ≤
        B (by norm_num : 2 ≤ (2 : ℕ)) a := by
    rw [← hvolume]
    unfold B
    exact Finset.le_max' _ _ (by simp)
  have hB1 :
      eLpNorm (a 1) 2 (Measure.count : Measure ι) ≤
        B (by norm_num : 2 ≤ (2 : ℕ)) a := by
    rw [← hvolume]
    unfold B
    exact Finset.le_max' _ _ (by simp)
  calc
    ‖(∑' j, a 0 j * a 1 j)‖ₑ ≤ ∑' j, ‖a 0 j * a 1 j‖ₑ :=
      enorm_tsum_le_tsum_enorm
    _ = ∑' j, ‖a 0 j‖ₑ * ‖a 1 j‖ₑ := by
      simp [enorm_mul]
    _ = ∫⁻ j : ι, ‖a 0 j‖ₑ * ‖a 1 j‖ₑ ∂(Measure.count : Measure ι) := by
      exact (lintegral_count (fun j : ι ↦ ‖a 0 j‖ₑ * ‖a 1 j‖ₑ)).symm
    _ ≤ eLpNorm (a 0) 2 (Measure.count : Measure ι) *
        eLpNorm (a 1) 2 (Measure.count : Measure ι) := hholder
    _ ≤ (B (by norm_num : 2 ≤ (2 : ℕ)) a) ^ 2 := by
      simpa [pow_two] using mul_le_mul' hB0 hB1

private lemma pointwise_estimate_normalized_base (a : Fin 2 → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by norm_num : 2 ≤ (2 : ℕ)) a ≤ 1) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      normalizedPointwiseBound (by norm_num : 2 ≤ (2 : ℕ)) a := by
  have hnorm :
      normalizedPointwiseBound (by norm_num : 2 ≤ (2 : ℕ)) a = 1 := by
    change ((2 : ENNReal) - 1) *
        (max 1 (A (by norm_num : 2 ≤ (2 : ℕ)) a)) ^ 0 = 1
    rw [show (2 : ENNReal) - 1 = 1 by
      exact ENNReal.sub_eq_of_eq_add ENNReal.one_ne_top (by norm_num)]
    simp
  calc
    ‖Q a - ∏ i, s (a i)‖ₑ = ‖∑' j, a 0 j * a 1 j‖ₑ := by
      rw [Q_two_sub_prod_eq_neg_diagonal a ha]
      simp
    _ ≤ (B (by norm_num : 2 ≤ (2 : ℕ)) a) ^ 2 :=
      diagonal_enorm_tsum_le_B_sq a ha
    _ ≤ 1 := by
      calc
        (B (by norm_num : 2 ≤ (2 : ℕ)) a) ^ 2 ≤ (1 : ENNReal) ^ 2 :=
          ENNReal.pow_le_pow_left hB
        _ = 1 := by norm_num
    _ = normalizedPointwiseBound (by norm_num : 2 ≤ (2 : ℕ)) a := hnorm.symm

/-
The recursive identity from the proof of Proposition 2. The last coordinate is
first summed freely, and then the k collision terms where it equals one of the
previous coordinates are subtracted.
-/
omit [Countable ι] in
private lemma all_distinct_snoc_iff {k : ℕ} (g : Fin k → ι) (m : ι) :
    all_distinct (k + 1) (Fin.snoc g m) ↔
      all_distinct k g ∧ ∀ i : Fin k, g i ≠ m := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i i' hii'
      simpa [Fin.snoc] using
        h (Fin.castSucc i) (Fin.castSucc i') (by simpa [Fin.ext_iff] using hii')
    · intro i
      simpa [Fin.snoc] using
        h (Fin.castSucc i) (Fin.last k) (ne_of_lt (Fin.castSucc_lt_last i))
  · rintro ⟨hg, hm⟩ i i' hii'
    cases i using Fin.lastCases with
    | last =>
        cases i' using Fin.lastCases with
        | last => contradiction
        | cast j =>
            simpa [Fin.snoc] using (hm j).symm
    | cast i =>
        cases i' using Fin.lastCases with
        | last =>
            simpa [Fin.snoc] using hm i
        | cast j =>
            simpa [Fin.snoc] using hg i j (by
              intro hij
              apply hii'
              simpa [Fin.ext_iff] using hij)

omit [Countable ι] in
private lemma summable_prod_norm {k : ℕ} (a : Fin k → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Summable (fun j : Fin k → ι => ∏ i, ‖a i (j i)‖) := by
  induction k with
  | zero =>
      exact ⟨_, hasSum_fintype _⟩
  | succ k ih =>
    have h_tail :
        Summable (fun j : Fin k → ι => ∏ i, ‖a (Fin.succ i) (j i)‖) :=
      ih (fun i ↦ a (Fin.succ i)) (fun i ↦ ha (Fin.succ i))
    have h_first : Summable (fun j : ι ↦ ‖a (0 : Fin (k + 1)) j‖) := ha 0
    have h_pair :
        Summable
          (fun p : ι × (Fin k → ι) =>
            ‖a 0 p.1‖ * ∏ i, ‖a (Fin.succ i) (p.2 i)‖) := by
      exact Summable.mul_of_nonneg
        (f := fun j : ι ↦ ‖a (0 : Fin (k + 1)) j‖)
        (g := fun j : Fin k → ι ↦ ∏ i, ‖a (Fin.succ i) (j i)‖)
        h_first h_tail
        (fun j ↦ norm_nonneg _)
        (fun j ↦ Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    have hinj : Function.Injective
        (fun j : Fin (k + 1) → ι ↦ (j 0, fun i : Fin k ↦ j (Fin.succ i))) := by
      intro x y hxy
      ext i
      cases i using Fin.cases with
      | zero =>
          exact congrArg Prod.fst hxy
      | succ i =>
          exact congr_fun (congrArg Prod.snd hxy) i
    rw [show
      (fun j : Fin (k + 1) → ι => ∏ i, ‖a i (j i)‖) =
        ((fun p : ι × (Fin k → ι) =>
          ‖a 0 p.1‖ * ∏ i, ‖a (Fin.succ i) (p.2 i)‖) ∘
            fun j : Fin (k + 1) → ι ↦ (j 0, fun i : Fin k ↦ j (Fin.succ i))) by
        funext j
        rw [Fin.prod_univ_succ]
        rfl]
    exact h_pair.comp_injective hinj

omit [Countable ι] in
private lemma summable_Q_term {k : ℕ} (a : Fin k → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Summable (fun j : Fin k → ι =>
      indicator (set_all_distinct k) (fun j ↦ ∏ i, a i (j i)) j) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) ?_ (summable_prod_norm a ha)
  intro j
  by_cases hj : j ∈ set_all_distinct k
  · simp [Set.indicator_of_mem hj, norm_prod]
  · exact (by simp [Set.indicator_of_notMem hj,
      Finset.prod_nonneg fun _ _ ↦ norm_nonneg _])

omit [Countable ι] in
private lemma tsum_fin_succ_eq_tsum_snoc {k : ℕ}
    (f : (Fin (k + 1) → ι) → ℂ) (hf : Summable f) :
    ∑' j, f j = ∑' (g : Fin k → ι), ∑' (m : ι), f (Fin.snoc g m) := by
  let e : (Fin k → ι) × ι ≃ (Fin (k + 1) → ι) :=
    Equiv.ofBijective (fun p : (Fin k → ι) × ι ↦ Fin.snoc p.1 p.2)
      ⟨by
        intro p q hpq
        exact Prod.ext
          (funext fun i ↦ by simpa using congr_fun hpq (Fin.castSucc i))
          (by simpa using congr_fun hpq (Fin.last k)),
       by
        intro j
        exact ⟨(Fin.init j, j (Fin.last k)), Fin.snoc_init_self j⟩⟩
  have hF : Summable (fun p : (Fin k → ι) × ι ↦ f (Fin.snoc p.1 p.2)) := by
    exact hf.comp_injective (by
      intro p q hpq
      exact Prod.ext
        (funext fun i ↦ by simpa using congr_fun hpq (Fin.castSucc i))
        (by simpa using congr_fun hpq (Fin.last k)))
  have hfiber : ∀ g : Fin k → ι, Summable (fun m : ι ↦ f (Fin.snoc g m)) := by
    intro g
    exact hf.comp_injective (by
      intro m n hmn
      simpa using congr_fun hmn (Fin.last k))
  rw [← e.tsum_eq f]
  exact hF.tsum_prod' hfiber

omit [Countable ι] in
private lemma tsum_compl_range_injective {k : ℕ} (g : Fin k → ι) (hg : all_distinct k g)
    (f : ι → ℂ) (hf : Summable (fun j ↦ ‖f j‖)) :
    ∑' m : { m // ∀ i : Fin k, g i ≠ m }, f m =
      s f - ∑ i : Fin k, f (g i) := by
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    exact hg i j hne hij
  have hcompl :
      (∑' m : { m // ∀ i : Fin k, g i ≠ m }, f m) =
        ∑' m : ((Set.range g)ᶜ : Set ι), f m := by
    let e : { m // ∀ i : Fin k, g i ≠ m } ≃ ((Set.range g)ᶜ : Set ι) :=
      { toFun := fun m ↦ ⟨m.1, by
          simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
          intro i
          exact m.2 i⟩
        invFun := fun m ↦ ⟨m.1, by
          intro i hgi
          exact m.2 ⟨i, hgi⟩⟩
        left_inv := by
          intro m
          rfl
        right_inv := by
          intro m
          rfl }
    exact e.tsum_eq (fun m : ((Set.range g)ᶜ : Set ι) ↦ f m)
  have hrange :
      (∑' m : Set.range g, f m) = ∑ i : Fin k, f (g i) := by
    rw [tsum_range f hginj, tsum_fintype]
  have hsplit :
      (∑' m : Set.range g, f m) +
          (∑' m : ((Set.range g)ᶜ : Set ι), f m) =
        s f := by
    simpa [s] using (hf.of_norm.tsum_subtype_add_tsum_subtype_compl (Set.range g))
  rw [hcompl, ← hrange]
  exact eq_sub_of_add_eq' hsplit

omit [Countable ι] in
private lemma collisionFamily_prod {k : ℕ} (a : Fin (k + 1) → ι → ℂ)
    (i : Fin k) (g : Fin k → ι) :
    ∏ t, collisionFamily a i t (g t) =
      (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i) := by
  classical
  let base : Fin k → ℂ := fun t ↦ initFamily a t (g t)
  let bumped : Fin k → ℂ := Function.update base i (base i * a (Fin.last k) (g i))
  have hbumped : (fun t : Fin k ↦ collisionFamily a i t (g t)) = bumped := by
    funext t
    by_cases hti : t = i
    · subst t
      simp [bumped, base, collisionFamily]
    · simp [bumped, base, collisionFamily, Function.update_of_ne hti]
  rw [hbumped]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i) (f := base)
    (b := base i * a (Fin.last k) (g i))]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i) (f := base)]
  ring

omit [Countable ι] in
private lemma Q_succ_fiber {k : ℕ} (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) (g : Fin k → ι) :
    (∑' m : ι,
      indicator (set_all_distinct (k + 1)) (fun j ↦ ∏ i, a i (j i)) (Fin.snoc g m)) =
      indicator (set_all_distinct k)
        (fun g ↦ (∏ i, initFamily a i (g i)) *
          (s (a (Fin.last k)) - ∑ i : Fin k, a (Fin.last k) (g i))) g := by
  let avoid : Set ι := fun m ↦ ∀ i : Fin k, g i ≠ m
  by_cases hg : all_distinct k g
  · have hterm : ∀ m : ι,
        indicator (set_all_distinct (k + 1)) (fun j ↦ ∏ i, a i (j i)) (Fin.snoc g m) =
          avoid.indicator
            (fun m ↦ (∏ i, initFamily a i (g i)) * a (Fin.last k) m) m := by
      intro m
      by_cases hm : ∀ i : Fin k, g i ≠ m
      · have hsnoc : Fin.snoc g m ∈ set_all_distinct (k + 1) :=
          (all_distinct_snoc_iff g m).2 ⟨hg, hm⟩
        have havoid : m ∈ avoid := hm
        rw [Set.indicator_of_mem hsnoc, Set.indicator_of_mem havoid]
        rw [Fin.prod_univ_castSucc]
        simp [initFamily, Fin.snoc]
      · have hsnoc : Fin.snoc g m ∉ set_all_distinct (k + 1) := by
          intro h
          exact hm ((all_distinct_snoc_iff g m).1 h).2
        have havoid : m ∉ avoid := hm
        rw [Set.indicator_of_notMem hsnoc, Set.indicator_of_notMem havoid]
    rw [tsum_congr hterm]
    rw [← (tsum_subtype avoid
      (fun m : ι ↦ (∏ i, initFamily a i (g i)) * a (Fin.last k) m))]
    rw [tsum_mul_left]
    change (∏ i, initFamily a i (g i)) *
        (∑' m : { m // ∀ i : Fin k, g i ≠ m }, a (Fin.last k) m) =
      indicator (set_all_distinct k)
        (fun g ↦ (∏ i, initFamily a i (g i)) *
          (s (a (Fin.last k)) - ∑ i : Fin k, a (Fin.last k) (g i))) g
    rw [tsum_compl_range_injective g hg (a (Fin.last k)) (ha (Fin.last k))]
    rw [Set.indicator_of_mem (show g ∈ set_all_distinct k from hg)]
  · have hzero : (fun m : ι ↦
        indicator (set_all_distinct (k + 1)) (fun j ↦ ∏ i, a i (j i)) (Fin.snoc g m)) =
        fun _ ↦ 0 := by
      funext m
      have hsnoc : Fin.snoc g m ∉ set_all_distinct (k + 1) := by
        intro h
        exact hg ((all_distinct_snoc_iff g m).1 h).1
      exact Set.indicator_of_notMem hsnoc _
    rw [hzero, tsum_zero]
    rw [Set.indicator_of_notMem (show g ∉ set_all_distinct k from hg)]

omit [Countable ι] in
private lemma initFamily_summable_core {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ∀ i, Summable (fun j ↦ ‖initFamily a i j‖) := by
  intro i
  exact ha (Fin.castSucc i)

omit [Countable ι] in
private lemma collisionFamily_summable_core {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) (i : Fin k) :
    ∀ t, Summable (fun j ↦ ‖collisionFamily a i t j‖) := by
  intro t
  by_cases hti : t = i
  · subst t
    have hlast_le : ∀ j : ι, ‖a (Fin.last k) j‖ ≤ ∑' j : ι, ‖a (Fin.last k) j‖ :=
      fun j ↦ Summable.le_tsum (ha (Fin.last k)) j (fun _ _ ↦ norm_nonneg _)
    have hprod :
        Summable
          (fun j : ι ↦ ‖a (Fin.castSucc i) j‖ * ‖a (Fin.last k) j‖) := by
      refine Summable.of_nonneg_of_le
        (fun j ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
        ((ha (Fin.castSucc i)).mul_right (∑' j : ι, ‖a (Fin.last k) j‖))
      intro j
      exact mul_le_mul_of_nonneg_left (hlast_le j) (norm_nonneg _)
    simpa [collisionFamily, norm_mul] using hprod
  · simpa [collisionFamily, Function.update_of_ne hti] using ha (Fin.castSucc t)

omit [Countable ι] in
private lemma Q_init_mul_last_eq_tsum {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Q (initFamily a) * s (a (Fin.last k)) =
      ∑' g : Fin k → ι,
        indicator (set_all_distinct k)
          (fun g ↦ (∏ i, initFamily a i (g i)) * s (a (Fin.last k))) g := by
  have hinit := initFamily_summable_core a ha
  have hQ : Summable (fun g : Fin k → ι =>
      indicator (set_all_distinct k) (fun g ↦ ∏ i, initFamily a i (g i)) g) :=
    summable_Q_term (initFamily a) hinit
  rw [Q]
  rw [← hQ.tsum_mul_right (s (a (Fin.last k)))]
  apply tsum_congr
  intro g
  by_cases hg : g ∈ set_all_distinct k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
    simp

omit [Countable ι] in
private lemma Q_collision_eq_tsum {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ) (i : Fin k) :
    Q (collisionFamily a i) =
      ∑' g : Fin k → ι,
        indicator (set_all_distinct k)
          (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g := by
  rw [Q]
  apply tsum_congr
  intro g
  by_cases hg : g ∈ set_all_distinct k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    exact collisionFamily_prod a i g
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]

omit [Countable ι] in
private lemma sum_Q_collision_eq_tsum {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    (∑ i : Fin k, Q (collisionFamily a i)) =
      ∑' g : Fin k → ι,
        indicator (set_all_distinct k)
          (fun g ↦ (∏ t, initFamily a t (g t)) *
            ∑ i : Fin k, a (Fin.last k) (g i)) g := by
  have hterm : ∀ i : Fin k, Summable (fun g : Fin k → ι =>
      indicator (set_all_distinct k)
        (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g) := by
    intro i
    exact (summable_Q_term (collisionFamily a i)
      (collisionFamily_summable_core a ha i)).congr (by
        intro g
        by_cases hg : g ∈ set_all_distinct k
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
          exact collisionFamily_prod a i g
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg])
  calc
    (∑ i : Fin k, Q (collisionFamily a i)) =
        ∑ i : Fin k, ∑' g : Fin k → ι,
          indicator (set_all_distinct k)
            (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Q_collision_eq_tsum a i]
    _ = ∑' g : Fin k → ι, ∑ i : Fin k,
          indicator (set_all_distinct k)
            (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g := by
      rw [(Summable.tsum_finsetSum (s := Finset.univ)
        (f := fun i g ↦ indicator (set_all_distinct k)
          (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g)
        (by intro i _; exact hterm i)).symm]
    _ = ∑' g : Fin k → ι,
        indicator (set_all_distinct k)
          (fun g ↦ (∏ t, initFamily a t (g t)) *
            ∑ i : Fin k, a (Fin.last k) (g i)) g := by
      apply tsum_congr
      intro g
      by_cases hg : g ∈ set_all_distinct k
      · simp_rw [Set.indicator_of_mem hg]
        rw [Finset.mul_sum]
      · simp_rw [Set.indicator_of_notMem hg]
        simp

omit [Countable ι] in
private lemma Q_succ_recursive {k : ℕ} (_hk : 1 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Q a = Q (initFamily a) * s (a (Fin.last k)) -
      ∑ i : Fin k, Q (collisionFamily a i) := by
  have h_reindex :
      Q a =
        ∑' g : Fin k → ι,
          indicator (set_all_distinct k)
            (fun g ↦ (∏ i, initFamily a i (g i)) *
              (s (a (Fin.last k)) - ∑ i : Fin k, a (Fin.last k) (g i))) g := by
    rw [Q]
    rw [tsum_fin_succ_eq_tsum_snoc _ (summable_Q_term a ha)]
    apply tsum_congr
    intro g
    exact Q_succ_fiber a ha g
  have hF : Summable (fun g : Fin k → ι =>
      indicator (set_all_distinct k)
        (fun g ↦ (∏ i, initFamily a i (g i)) * s (a (Fin.last k))) g) := by
    have hbase : Summable (fun g : Fin k → ι =>
        indicator (set_all_distinct k) (fun g ↦ ∏ i, initFamily a i (g i)) g) :=
      summable_Q_term (initFamily a) (initFamily_summable_core a ha)
    exact (hbase.mul_right (s (a (Fin.last k)))).congr (by
      intro g
      by_cases hg : g ∈ set_all_distinct k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
        simp)
  have hterm : ∀ i : Fin k, Summable (fun g : Fin k → ι =>
      indicator (set_all_distinct k)
        (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g) := by
    intro i
    exact (summable_Q_term (collisionFamily a i)
      (collisionFamily_summable_core a ha i)).congr (by
        intro g
        by_cases hg : g ∈ set_all_distinct k
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
          exact collisionFamily_prod a i g
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg])
  let H : Fin k → (Fin k → ι) → ℂ := fun i g ↦
    indicator (set_all_distinct k)
      (fun g ↦ (∏ t, initFamily a t (g t)) * a (Fin.last k) (g i)) g
  have hGsum : Summable (fun g : Fin k → ι => ∑ i : Fin k, H i g) := by
    have hG_finset : ∀ s : Finset (Fin k), Summable (fun g : Fin k → ι => ∑ i ∈ s, H i g) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simp [H]
      | insert i s his ih =>
          simpa [Finset.sum_insert his, H] using (hterm i).add ih
    simpa [H] using hG_finset Finset.univ
  have hG : Summable (fun g : Fin k → ι =>
      indicator (set_all_distinct k)
        (fun g ↦ (∏ t, initFamily a t (g t)) *
          ∑ i : Fin k, a (Fin.last k) (g i)) g) := by
    exact hGsum.congr (by
      intro g
      by_cases hg : g ∈ set_all_distinct k
      · simp [H, Set.indicator_of_mem hg, Finset.mul_sum]
      · simp [H, Set.indicator_of_notMem hg])
  rw [h_reindex, Q_init_mul_last_eq_tsum a ha, sum_Q_collision_eq_tsum a ha]
  rw [← hF.tsum_sub hG]
  apply tsum_congr
  intro g
  by_cases hg : g ∈ set_all_distinct k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    ring
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
    simp

omit [Countable ι] in
private lemma collisionFamily_summable {k : ℕ} (_hk : 1 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) (i : Fin k) :
    ∀ t, Summable (fun j ↦ ‖collisionFamily a i t j‖) := by
  exact collisionFamily_summable_core a ha i

omit [Countable ι] in
private lemma initFamily_summable {k : ℕ}
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ∀ i, Summable (fun j ↦ ‖initFamily a i j‖) := by
  exact initFamily_summable_core a ha

/-
Under the normalization B <= 1, every scalar sum of a collided pair has modulus at
most 1. This is the Cauchy-Schwarz line in the induction step.
-/
private lemma collision_sum_enorm_le_one {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    ‖s (fun j ↦ a (Fin.castSucc i) j * a (Fin.last k) j)‖ₑ ≤ 1 := by
  have hvolume : (volume : Measure ι) = Measure.count := rfl
  have hholder :
      (∫⁻ j : ι, ‖a (Fin.castSucc i) j‖ₑ * ‖a (Fin.last k) j‖ₑ
          ∂(Measure.count : Measure ι)) ≤
        eLpNorm (a (Fin.castSucc i)) 2 (Measure.count : Measure ι) *
          eLpNorm (a (Fin.last k)) 2 (Measure.count : Measure ι) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have h0 : AEMeasurable (fun j : ι ↦ ‖a (Fin.castSucc i) j‖ₑ)
        (Measure.count : Measure ι) :=
      (measurable_of_countable _).aemeasurable
    have h1 : AEMeasurable (fun j : ι ↦ ‖a (Fin.last k) j‖ₑ)
        (Measure.count : Measure ι) :=
      (measurable_of_countable _).aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (μ := (Measure.count : Measure ι)) hpq h0 h1
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤),
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simpa [one_div] using h
  have hBi :
      eLpNorm (a (Fin.castSucc i)) 2 (Measure.count : Measure ι) ≤
        B (by omega : 2 ≤ k + 1) a := by
    rw [← hvolume]
    unfold B
    exact Finset.le_max' _ _ (by simp)
  have hBlast :
      eLpNorm (a (Fin.last k)) 2 (Measure.count : Measure ι) ≤
        B (by omega : 2 ≤ k + 1) a := by
    rw [← hvolume]
    unfold B
    exact Finset.le_max' _ _ (by simp)
  calc
    ‖s (fun j ↦ a (Fin.castSucc i) j * a (Fin.last k) j)‖ₑ ≤
        ∑' j, ‖a (Fin.castSucc i) j * a (Fin.last k) j‖ₑ := by
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' j, ‖a (Fin.castSucc i) j‖ₑ * ‖a (Fin.last k) j‖ₑ := by
      simp [enorm_mul]
    _ = ∫⁻ j : ι, ‖a (Fin.castSucc i) j‖ₑ * ‖a (Fin.last k) j‖ₑ
        ∂(Measure.count : Measure ι) := by
      exact (lintegral_count
        (fun j : ι ↦ ‖a (Fin.castSucc i) j‖ₑ * ‖a (Fin.last k) j‖ₑ)).symm
    _ ≤ eLpNorm (a (Fin.castSucc i)) 2 (Measure.count : Measure ι) *
        eLpNorm (a (Fin.last k)) 2 (Measure.count : Measure ι) := hholder
    _ ≤ (B (by omega : 2 ≤ k + 1) a) ^ 2 := by
      simpa [pow_two] using mul_le_mul' hBi hBlast
    _ ≤ 1 := by
      calc
        (B (by omega : 2 ≤ k + 1) a) ^ 2 ≤ (1 : ENNReal) ^ 2 :=
          ENNReal.pow_le_pow_left hB
        _ = 1 := by norm_num

omit [Countable ι] in
private lemma eLpNorm_coord_le_B {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (i : Fin k) :
    eLpNorm (a i) 2 ≤ B hk a := by
  unfold B
  exact Finset.le_max' _ _ (by simp)

omit [Countable ι] in
private lemma eLpNorm_two_lt_top_of_summable_norm (a : ι → ℂ)
    (ha : Summable (fun j ↦ ‖a j‖)) :
    eLpNorm a 2 < ⊤ := by
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  change (∫⁻ j : ι, ‖a j‖ₑ ^ (2 : ENNReal).toReal
    ∂(Measure.count : Measure ι)) < ⊤
  rw [lintegral_count]
  have hmem1 : Memℓp a (1 : ENNReal) := by
    apply memℓp_gen
    simpa using ha
  have hmem2 : Memℓp a (2 : ENNReal) := hmem1.of_exponent_ge (by norm_num)
  have hsquare : Summable (fun j : ι ↦ ‖a j‖ ^ (2 : ENNReal).toReal) :=
    hmem2.summable (by norm_num)
  refine lt_of_eq_of_lt ?_ hsquare.tsum_ofReal_lt_top
  apply tsum_congr
  intro j
  rw [← ofReal_norm]
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (a j))
    (by norm_num : 0 ≤ (2 : ENNReal).toReal)]

omit [Countable ι] in
private lemma B_ne_top_of_summable_norm {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    B hk a ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  unfold B
  rw [Finset.max'_lt_iff]
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
  exact eLpNorm_two_lt_top_of_summable_norm (a i) (ha i)

omit [Countable ι] in
private lemma enorm_le_one_of_eLpNorm_le_one (a : ι → ℂ)
    (ha : eLpNorm a 2 ≤ 1) (j : ι) :
    ‖a j‖ₑ ≤ 1 := by
  exact (enorm_le_eLpNorm_count a j (by norm_num : (2 : ENNReal) ≠ 0)).trans ha

omit [Countable ι] in
private lemma eLpNorm_mul_le_of_right_enorm_le_one (a b : ι → ℂ)
    (hb : ∀ j, ‖b j‖ₑ ≤ 1) :
    eLpNorm (fun j ↦ a j * b j) 2 ≤ eLpNorm a 2 := by
  apply eLpNorm_mono_enorm
  intro j
  rw [enorm_mul]
  exact mul_le_of_le_one_right (show (0 : ENNReal) ≤ ‖a j‖ₑ from bot_le) (hb j)

omit [Countable ι] in
private lemma B_initFamily_le_one {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) :
    B hk (initFamily a) ≤ 1 := by
  unfold B
  rw [Finset.max'_le_iff]
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
  exact (Finset.le_max' _ _ (by simp [initFamily])).trans hB

omit [Countable ι] in
private lemma B_collisionFamily_le_one {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    B hk (collisionFamily a i) ≤ 1 := by
  let hk1 : 2 ≤ k + 1 := by omega
  have hBhk1 : B hk1 a ≤ 1 := by
    simpa [hk1] using hB
  have hcoord (t : Fin k) :
      eLpNorm (a (Fin.castSucc t)) 2 ≤ 1 :=
    (eLpNorm_coord_le_B hk1 a (Fin.castSucc t)).trans hBhk1
  have hlast_point : ∀ j : ι, ‖a (Fin.last k) j‖ₑ ≤ 1 := by
    intro j
    exact enorm_le_one_of_eLpNorm_le_one (a (Fin.last k))
      ((eLpNorm_coord_le_B hk1 a (Fin.last k)).trans hBhk1) j
  have hprod :
      eLpNorm (fun j ↦ a (Fin.castSucc i) j * a (Fin.last k) j) 2 ≤ 1 :=
    (eLpNorm_mul_le_of_right_enorm_le_one (a (Fin.castSucc i)) (a (Fin.last k))
      hlast_point).trans (hcoord i)
  unfold B
  rw [Finset.max'_le_iff]
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
  by_cases hti : t = i
  · subst t
    simpa [collisionFamily] using hprod
  · simpa [collisionFamily, initFamily, Function.update_of_ne hti] using hcoord t

omit [Countable ι] in
private lemma A_initFamily_le_step_max {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ) :
    A hk (initFamily a) ≤ max 1 (A (by omega : 2 ≤ k + 1) a) := by
  unfold A
  refine (ENNReal.ofReal_le_ofReal ?_).trans (le_max_right _ _)
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
  exact Finset.le_max' _ _ (by simp [initFamily])

private lemma A_collisionFamily_le_step_max {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    A hk (collisionFamily a i) ≤ max 1 (A (by omega : 2 ≤ k + 1) a) := by
  have hcollision_real :
      ‖s (fun j ↦ a (Fin.castSucc i) j * a (Fin.last k) j)‖ ≤ (1 : ℝ) := by
    rw [← show ‖(1 : ℂ)‖ = (1 : ℝ) by norm_num]
    rw [← enorm_le_iff_norm_le]
    simpa using collision_sum_enorm_le_one hk a ha hB i
  unfold A
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_max]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
  by_cases hti : t = i
  · subst t
    exact (by
      simpa [collisionFamily] using hcollision_real.trans (le_max_left _ _))
  · have hcoord :
        ‖s (a (Fin.castSucc t))‖ ≤
          (Finset.univ.image fun i ↦ ‖s (a i)‖).max'
            ⟨‖s (a ⟨0, zero_lt_of_lt (by omega : 2 ≤ k + 1)⟩)‖, by simp⟩ :=
      Finset.le_max' _ _ (by simp)
    exact (by
      simpa [collisionFamily, initFamily, Function.update_of_ne hti] using
        hcoord.trans (le_max_right _ _))

private lemma collision_product_sums_bound {k : ℕ} (hk : 2 ≤ k)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    ‖∏ t, s (collisionFamily a i t)‖ₑ ≤
      (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
  let M : ENNReal := max 1 (A (by omega : 2 ≤ k + 1) a)
  have hcoord (t : Fin k) (hti : t ≠ i) :
      ‖s (collisionFamily a i t)‖ₑ ≤ M := by
    have hraw :
        ‖s (a (Fin.castSucc t))‖ₑ ≤ A (by omega : 2 ≤ k + 1) a := by
      rw [← ofReal_norm]
      unfold A
      exact ENNReal.ofReal_le_ofReal (Finset.le_max' _ _ (by simp))
    simpa [M, collisionFamily, initFamily, Function.update_of_ne hti] using
      hraw.trans (le_max_right _ _)
  have hcollision :
      ‖s (collisionFamily a i i)‖ₑ ≤ 1 := by
    simpa [collisionFamily] using collision_sum_enorm_le_one hk a ha hB i
  have hprod_erase :
      (∏ t ∈ Finset.univ.erase i, ‖s (collisionFamily a i t)‖ₑ) ≤
        M ^ (k - 1) := by
    calc
      (∏ t ∈ Finset.univ.erase i, ‖s (collisionFamily a i t)‖ₑ) ≤
          ∏ _t ∈ Finset.univ.erase i, M := by
        exact Finset.prod_le_prod
          (fun _t _ht ↦ bot_le)
          (fun t ht ↦ hcoord t (Finset.mem_erase.mp ht).1)
      _ = M ^ (k - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
  calc
    ‖∏ t, s (collisionFamily a i t)‖ₑ =
        ∏ t, ‖s (collisionFamily a i t)‖ₑ := by
      rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg]
      · simp [ofReal_norm]
      · intro _t _ht
        positivity
    _ = ‖s (collisionFamily a i i)‖ₑ *
        ∏ t ∈ Finset.univ.erase i, ‖s (collisionFamily a i t)‖ₑ := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun t ↦ ‖s (collisionFamily a i t)‖ₑ) (Finset.mem_univ i)]
    _ ≤ 1 * M ^ (k - 1) := mul_le_mul' hcollision hprod_erase
    _ = (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
      simp [M]

private lemma collision_error_bound_normalized {k : ℕ} (hk : 2 ≤ k)
    (ih : ∀ (b : Fin k → ι → ℂ),
      (∀ i, Summable (fun j ↦ ‖b i j‖)) →
      B hk b ≤ 1 →
      ‖Q b - ∏ i, s (b i)‖ₑ ≤ normalizedPointwiseBound hk b)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    ‖Q (collisionFamily a i) - ∏ t, s (collisionFamily a i t)‖ₑ ≤
      pointwiseConstant k *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 2) := by
  have hih := ih (collisionFamily a i)
    (collisionFamily_summable (by omega : 1 ≤ k) a ha i)
    (B_collisionFamily_le_one hk a ha hB i)
  have hA :
      max 1 (A hk (collisionFamily a i)) ≤
        max 1 (A (by omega : 2 ≤ k + 1) a) := by
    exact max_le (le_max_left _ _) (A_collisionFamily_le_step_max hk a ha hB i)
  calc
    ‖Q (collisionFamily a i) - ∏ t, s (collisionFamily a i t)‖ₑ
        ≤ pointwiseConstant k * (max 1 (A hk (collisionFamily a i))) ^ (k - 2) := by
      simpa [normalizedPointwiseBound] using hih
    _ ≤ pointwiseConstant k *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 2) := by
      exact mul_le_mul' le_rfl (ENNReal.pow_le_pow_left hA)

private lemma collision_Q_bound_normalized {k : ℕ} (hk : 2 ≤ k)
    (ih : ∀ (b : Fin k → ι → ℂ),
      (∀ i, Summable (fun j ↦ ‖b i j‖)) →
      B hk b ≤ 1 →
      ‖Q b - ∏ i, s (b i)‖ₑ ≤ normalizedPointwiseBound hk b)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) (i : Fin k) :
    ‖Q (collisionFamily a i)‖ₑ ≤
      (pointwiseConstant k + 1) *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
  let M : ENNReal := max 1 (A (by omega : 2 ≤ k + 1) a)
  let P : ℂ := ∏ t, s (collisionFamily a i t)
  have herr :
      ‖Q (collisionFamily a i) - P‖ₑ ≤ pointwiseConstant k * M ^ (k - 2) := by
    simpa [M, P] using collision_error_bound_normalized hk ih a ha hB i
  have hprod : ‖P‖ₑ ≤ M ^ (k - 1) := by
    simpa [M, P] using collision_product_sums_bound hk a ha hB i
  have hM : 1 ≤ M := le_max_left _ _
  have hpow : M ^ (k - 2) ≤ M ^ (k - 1) :=
    pow_le_pow_right₀ hM (by omega)
  have htri :
      ‖Q (collisionFamily a i)‖ₑ ≤
        ‖Q (collisionFamily a i) - P‖ₑ + ‖P‖ₑ := by
    have h : (Q (collisionFamily a i) - P) + P = Q (collisionFamily a i) := by
      abel
    calc
      ‖Q (collisionFamily a i)‖ₑ =
          ‖(Q (collisionFamily a i) - P) + P‖ₑ := by
        rw [h]
      _ ≤ ‖Q (collisionFamily a i) - P‖ₑ + ‖P‖ₑ :=
        enorm_add_le (Q (collisionFamily a i) - P) P
  calc
    ‖Q (collisionFamily a i)‖ₑ
        ≤ ‖Q (collisionFamily a i) - P‖ₑ + ‖P‖ₑ := htri
    _ ≤ pointwiseConstant k * M ^ (k - 2) + M ^ (k - 1) :=
      add_le_add herr hprod
    _ ≤ pointwiseConstant k * M ^ (k - 1) + 1 * M ^ (k - 1) := by
      exact add_le_add (mul_le_mul' le_rfl hpow) (by simp)
    _ = (pointwiseConstant k + 1) *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
      simp [M, add_mul]

/-
This is the triangle-inequality estimate at the end of the induction step:
one initial error term times the last scalar sum, plus k bounded collision terms.
-/
private lemma normalized_step_error_bound {k : ℕ} (hk : 2 ≤ k)
    (ih : ∀ (b : Fin k → ι → ℂ),
      (∀ i, Summable (fun j ↦ ‖b i j‖)) →
      B hk b ≤ 1 →
      ‖Q b - ∏ i, s (b i)‖ₑ ≤ normalizedPointwiseBound hk b)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      (((k + 1 : ℕ) : ENNReal) * pointwiseConstant k + (k : ENNReal)) *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
  let M : ENNReal := max 1 (A (by omega : 2 ≤ k + 1) a)
  let E : ℂ := Q (initFamily a) - ∏ t, s (initFamily a t)
  let L : ℂ := s (a (Fin.last k))
  let Csum : ℂ := ∑ i : Fin k, Q (collisionFamily a i)
  have hprod_split :
      (∏ i : Fin (k + 1), s (a i)) = (∏ t : Fin k, s (initFamily a t)) * L := by
    rw [Fin.prod_univ_castSucc]
  have hmain : Q a - ∏ i, s (a i) = E * L - Csum := by
    dsimp [E, L, Csum]
    rw [Q_succ_recursive (by omega : 1 ≤ k) a ha, hprod_split]
    ring
  have hinit_error :
      ‖E‖ₑ ≤ pointwiseConstant k * M ^ (k - 2) := by
    have hih := ih (initFamily a) (initFamily_summable a ha)
      (B_initFamily_le_one hk a hB)
    have hA :
        max 1 (A hk (initFamily a)) ≤ M := by
      exact max_le (le_max_left _ _) (by
        simpa [M] using A_initFamily_le_step_max hk a)
    dsimp [E]
    calc
      ‖Q (initFamily a) - ∏ t, s (initFamily a t)‖ₑ
          ≤ pointwiseConstant k * (max 1 (A hk (initFamily a))) ^ (k - 2) := by
        simpa [normalizedPointwiseBound] using hih
      _ ≤ pointwiseConstant k * M ^ (k - 2) := by
        exact mul_le_mul' le_rfl (ENNReal.pow_le_pow_left hA)
  have hlast : ‖L‖ₑ ≤ M := by
    have hraw :
        ‖s (a (Fin.last k))‖ₑ ≤ A (by omega : 2 ≤ k + 1) a := by
      rw [← ofReal_norm]
      unfold A
      exact ENNReal.ofReal_le_ofReal (Finset.le_max' _ _ (by simp))
    dsimp [L]
    exact hraw.trans (le_max_right _ _)
  have hinit_term : ‖E * L‖ₑ ≤ pointwiseConstant k * M ^ (k - 1) := by
    calc
      ‖E * L‖ₑ = ‖E‖ₑ * ‖L‖ₑ := by rw [enorm_mul]
      _ ≤ (pointwiseConstant k * M ^ (k - 2)) * M :=
        mul_le_mul' hinit_error hlast
      _ = pointwiseConstant k * M ^ (k - 1) := by
        rw [mul_assoc, ← pow_succ, show k - 2 + 1 = k - 1 by omega]
  have hcollision_sum :
      ‖Csum‖ₑ ≤ (k : ENNReal) * ((pointwiseConstant k + 1) * M ^ (k - 1)) := by
    dsimp [Csum]
    calc
      ‖∑ i : Fin k, Q (collisionFamily a i)‖ₑ
          ≤ ∑ i : Fin k, ‖Q (collisionFamily a i)‖ₑ :=
        enorm_sum_le Finset.univ (fun i : Fin k ↦ Q (collisionFamily a i))
      _ ≤ ∑ _i : Fin k, (pointwiseConstant k + 1) * M ^ (k - 1) := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa [M] using collision_Q_bound_normalized hk ih a ha hB i
      _ = (k : ENNReal) * ((pointwiseConstant k + 1) * M ^ (k - 1)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htri :
      ‖Q a - ∏ i, s (a i)‖ₑ ≤ ‖E * L‖ₑ + ‖Csum‖ₑ := by
    rw [hmain]
    simpa [sub_eq_add_neg] using enorm_add_le (E * L) (-Csum)
  calc
    ‖Q a - ∏ i, s (a i)‖ₑ ≤ ‖E * L‖ₑ + ‖Csum‖ₑ := htri
    _ ≤ pointwiseConstant k * M ^ (k - 1) +
        (k : ENNReal) * ((pointwiseConstant k + 1) * M ^ (k - 1)) :=
      add_le_add hinit_term hcollision_sum
    _ = (((k + 1 : ℕ) : ENNReal) * pointwiseConstant k + (k : ENNReal)) *
        (max 1 (A (by omega : 2 ≤ k + 1) a)) ^ (k - 1) := by
      simp [M]
      ring_nf

private lemma pointwiseConstant_succ {k : ℕ} :
    pointwiseConstant (k + 1) =
      (((k + 1 : ℕ) : ENNReal) * pointwiseConstant k + (k : ENNReal)) := by
  unfold pointwiseConstant
  rw [Nat.factorial_succ]
  apply ENNReal.sub_eq_of_eq_add (by simp)
  have hf1 : (1 : ENNReal) ≤ ((k)! : ENNReal) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k)
  have hfac : ((k)! : ENNReal) - 1 + 1 = ((k)! : ENNReal) :=
    tsub_add_cancel_of_le hf1
  rw [Nat.cast_mul]
  calc
    ((k + 1 : ℕ) : ENNReal) * ((k)! : ENNReal)
        = ((k + 1 : ℕ) : ENNReal) * (((k)! : ENNReal) - 1 + 1) := by
      rw [hfac]
    _ = ((k + 1 : ℕ) : ENNReal) * (((k)! : ENNReal) - 1) +
        ((k + 1 : ℕ) : ENNReal) := by
      rw [mul_add, mul_one]
    _ = ((k + 1 : ℕ) : ENNReal) * (((k)! : ENNReal) - 1) + (k : ENNReal) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc]

private lemma pointwise_estimate_normalized_step {k : ℕ} (hk : 2 ≤ k)
    (ih : ∀ (b : Fin k → ι → ℂ),
      (∀ i, Summable (fun j ↦ ‖b i j‖)) →
      B hk b ≤ 1 →
      ‖Q b - ∏ i, s (b i)‖ₑ ≤ normalizedPointwiseBound hk b)
    (a : Fin (k + 1) → ι → ℂ)
    (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B (by omega : 2 ≤ k + 1) a ≤ 1) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      normalizedPointwiseBound (by omega : 2 ≤ k + 1) a := by
  have hexp : k + 1 - 2 = k - 1 := by omega
  simpa [normalizedPointwiseBound, pointwiseConstant_succ, hexp] using
    normalized_step_error_bound hk ih a ha hB

private lemma pointwise_estimate_normalized (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB : B hk a ≤ 1) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤ normalizedPointwiseBound hk a := by
  revert a ha hB
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  induction n with
  | zero =>
      intro a ha hB
      simpa using pointwise_estimate_normalized_base a ha hB
  | succ m ih =>
      intro a ha hB
      simpa [Nat.add_assoc] using
        pointwise_estimate_normalized_step (k := m + 2) (by omega)
          (fun b hb hBb ↦ ih (by omega) b hb hBb) a ha hB

omit [Countable ι] in
private lemma rescaleFamily_summable (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ∀ i, Summable (fun j ↦ ‖rescaleFamily hk a i j‖) := by
  intro i
  refine ((ha i).mul_left ‖(((B hk a).toReal : ℂ)⁻¹)‖).congr ?_
  intro j
  simp [rescaleFamily]

omit [Countable ι] in
private lemma eLpNorm_rescaleFamily_le (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (i : Fin k) :
    eLpNorm (rescaleFamily hk a i) 2 ≤
      ‖(((B hk a).toReal : ℂ)⁻¹)‖ₑ * eLpNorm (a i) 2 := by
  exact eLpNorm_const_smul_le (c := (((B hk a).toReal : ℂ)⁻¹)) (f := a i)
    (p := (2 : ENNReal)) (μ := (volume : Measure ι))

omit [Countable ι] in
private lemma B_rescaleFamily_le_one (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a ≠ 0) :
    B hk (rescaleFamily hk a) ≤ 1 := by
  by_cases htop : B hk a = ⊤
  · have hcoord (i : Fin k) : eLpNorm (rescaleFamily hk a i) 2 ≤ 1 := by
      have hzero : rescaleFamily hk a i = 0 := by
        funext j
        simp [rescaleFamily, htop]
      simp [hzero]
    unfold B
    rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact hcoord i
  · have hpos : 0 < (B hk a).toReal := ENNReal.toReal_pos hB0 htop
    have hc_ne : ((B hk a).toReal : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    have hc_enorm : ‖(((B hk a).toReal : ℂ)⁻¹)‖ₑ = (B hk a)⁻¹ := by
      rw [enorm_inv hc_ne]
      have hbase : ‖((B hk a).toReal : ℂ)‖ₑ = B hk a := by
        calc
          ‖((B hk a).toReal : ℂ)‖ₑ =
              ENNReal.ofReal ‖((B hk a).toReal : ℂ)‖ := by
            rw [ofReal_norm]
          _ = ENNReal.ofReal (B hk a).toReal := by
            rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
          _ = B hk a := ENNReal.ofReal_toReal htop
      rw [hbase]
    have hscale : ‖(((B hk a).toReal : ℂ)⁻¹)‖ₑ * B hk a = 1 := by
      rw [hc_enorm]
      exact ENNReal.inv_mul_cancel hB0 htop
    have hcoord (i : Fin k) : eLpNorm (rescaleFamily hk a i) 2 ≤ 1 := by
      have hmul :
          ‖(((B hk a).toReal : ℂ)⁻¹)‖ₑ * eLpNorm (a i) 2 ≤
            ‖(((B hk a).toReal : ℂ)⁻¹)‖ₑ * B hk a :=
        mul_le_mul' le_rfl (eLpNorm_coord_le_B hk a i)
      exact (eLpNorm_rescaleFamily_le hk a i).trans (hmul.trans_eq hscale)
    unfold B
    rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact hcoord i

omit [Countable ι] in
private lemma s_rescaleFamily (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) (i : Fin k) :
    s (rescaleFamily hk a i) = ((B hk a).toReal : ℂ)⁻¹ * s (a i) := by
  simp [s, rescaleFamily, smul_eq_mul, tsum_mul_left]

omit [Countable ι] in
private lemma prod_s_rescaleFamily (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    (∏ i, s (rescaleFamily hk a i)) =
      ((B hk a).toReal : ℂ)⁻¹ ^ k * ∏ i, s (a i) := by
  calc
    (∏ i, s (rescaleFamily hk a i))
        = ∏ i : Fin k, ((B hk a).toReal : ℂ)⁻¹ * s (a i) := by
      simp [s_rescaleFamily hk a ha]
    _ = (∏ _i : Fin k, ((B hk a).toReal : ℂ)⁻¹) * ∏ i, s (a i) := by
      rw [Finset.prod_mul_distrib]
    _ = ((B hk a).toReal : ℂ)⁻¹ ^ k * ∏ i, s (a i) := by
      simp [Finset.prod_const, Fintype.card_fin]

omit [Countable ι] in
private lemma Q_rescaleFamily (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    Q (rescaleFamily hk a) =
      ((B hk a).toReal : ℂ)⁻¹ ^ k * Q a := by
  let c : ℂ := ((B hk a).toReal : ℂ)⁻¹
  have hterm (j : Fin k → ι) :
      indicator (set_all_distinct k) (fun j ↦ ∏ i, rescaleFamily hk a i (j i)) j =
        c ^ k * indicator (set_all_distinct k) (fun j ↦ ∏ i, a i (j i)) j := by
    by_cases hj : j ∈ set_all_distinct k
    · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj]
      simp [c, rescaleFamily, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
        Fintype.card_fin]
    · simp [Set.indicator_of_notMem hj]
  unfold Q
  rw [tsum_congr hterm, tsum_mul_left]

omit [Countable ι] in
private lemma B_mul_A_rescaleFamily_le_A (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a ≠ 0) :
    B hk a * A hk (rescaleFamily hk a) ≤ A hk a := by
  let M : ℝ :=
    (Finset.univ.image fun i ↦ ‖s (a i)‖).max'
      ⟨‖s (a ⟨0, zero_lt_of_lt hk⟩)‖, by simp⟩
  let M' : ℝ :=
    (Finset.univ.image fun i ↦ ‖s (rescaleFamily hk a i)‖).max'
      ⟨‖s (rescaleFamily hk a ⟨0, zero_lt_of_lt hk⟩)‖, by simp⟩
  have hBtop : B hk a ≠ ⊤ := B_ne_top_of_summable_norm hk a ha
  have hpos : 0 < (B hk a).toReal := ENNReal.toReal_pos hB0 hBtop
  have hc_norm :
      ‖(((B hk a).toReal : ℂ)⁻¹)‖ = ((B hk a).toReal)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hM' : M' ≤ ((B hk a).toReal)⁻¹ * M := by
    dsimp [M']
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    calc
      ‖s (rescaleFamily hk a i)‖ =
          ‖(((B hk a).toReal : ℂ)⁻¹ * s (a i))‖ := by
        rw [s_rescaleFamily hk a ha i]
      _ = ‖(((B hk a).toReal : ℂ)⁻¹)‖ * ‖s (a i)‖ := by
        rw [norm_mul]
      _ = ((B hk a).toReal)⁻¹ * ‖s (a i)‖ := by
        rw [hc_norm]
      _ ≤ ((B hk a).toReal)⁻¹ * M := by
        exact mul_le_mul_of_nonneg_left
          (Finset.le_max' _ _ (by simp)) (inv_nonneg.mpr hpos.le)
  have hBM' : (B hk a).toReal * M' ≤ M := by
    calc
      (B hk a).toReal * M' ≤
          (B hk a).toReal * (((B hk a).toReal)⁻¹ * M) :=
        mul_le_mul_of_nonneg_left hM' hpos.le
      _ = M := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  unfold A
  change B hk a * ENNReal.ofReal M' ≤ ENNReal.ofReal M
  rw [← ENNReal.ofReal_toReal hBtop, ← ENNReal.ofReal_mul hpos.le]
  exact ENNReal.ofReal_le_ofReal hBM'

omit [Countable ι] in
private lemma rescale_Q_sub_prod_enorm (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a ≠ 0) :
    ‖Q a - ∏ i, s (a i)‖ₑ =
      (B hk a) ^ k *
        ‖Q (rescaleFamily hk a) - ∏ i, s (rescaleFamily hk a i)‖ₑ := by
  let c : ℂ := ((B hk a).toReal : ℂ)⁻¹
  have hBtop : B hk a ≠ ⊤ := B_ne_top_of_summable_norm hk a ha
  have hpos : 0 < (B hk a).toReal := ENNReal.toReal_pos hB0 hBtop
  have hc_ne : ((B hk a).toReal : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hc_enorm : ‖c‖ₑ = (B hk a)⁻¹ := by
    dsimp [c]
    rw [enorm_inv hc_ne]
    have hbase : ‖((B hk a).toReal : ℂ)‖ₑ = B hk a := by
      calc
        ‖((B hk a).toReal : ℂ)‖ₑ =
            ENNReal.ofReal ‖((B hk a).toReal : ℂ)‖ := by
          rw [ofReal_norm]
        _ = ENNReal.ofReal (B hk a).toReal := by
          rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
        _ = B hk a := ENNReal.ofReal_toReal hBtop
    rw [hbase]
  have hscaled :
      Q (rescaleFamily hk a) - ∏ i, s (rescaleFamily hk a i) =
        c ^ k * (Q a - ∏ i, s (a i)) := by
    dsimp [c]
    rw [Q_rescaleFamily hk a ha, prod_s_rescaleFamily hk a ha]
    ring
  rw [hscaled, enorm_mul, enorm_pow, hc_enorm]
  rw [← mul_assoc]
  have hpow : (B hk a) ^ k * (B hk a)⁻¹ ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hB0 hBtop, one_pow]
  rw [hpow, one_mul]

omit [Countable ι] in
private lemma rescale_normalized_bound_le_original (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a ≠ 0) :
    (B hk a) ^ k * normalizedPointwiseBound hk (rescaleFamily hk a) ≤
      pointwiseBound hk a := by
  let X : ENNReal := max 1 (A hk (rescaleFamily hk a))
  let M : ENNReal := max (A hk a) (B hk a)
  have hBA : B hk a * A hk (rescaleFamily hk a) ≤ A hk a :=
    B_mul_A_rescaleFamily_le_A hk a ha hB0
  have hBmax : B hk a * X ≤ M := by
    dsimp [X, M]
    rw [mul_max, mul_one]
    exact max_le (le_max_right _ _) (hBA.trans (le_max_left _ _))
  have hpow :
      (B hk a) ^ (k - 2) * X ^ (k - 2) ≤ M ^ (k - 2) := by
    calc
      (B hk a) ^ (k - 2) * X ^ (k - 2)
          = (B hk a * X) ^ (k - 2) := by
        rw [mul_pow]
      _ ≤ M ^ (k - 2) := ENNReal.pow_le_pow_left hBmax
  have hcore :
      (B hk a) ^ k * X ^ (k - 2) ≤ (B hk a) ^ 2 * M ^ (k - 2) := by
    have hkpow : (B hk a) ^ k = (B hk a) ^ 2 * (B hk a) ^ (k - 2) := by
      have hkdecomp : k = 2 + (k - 2) := by omega
      exact (congrArg (fun n ↦ (B hk a) ^ n) hkdecomp).trans (pow_add _ _ _)
    calc
      (B hk a) ^ k * X ^ (k - 2)
          = (B hk a) ^ 2 * ((B hk a) ^ (k - 2) * X ^ (k - 2)) := by
        rw [hkpow]
        ring_nf
      _ ≤ (B hk a) ^ 2 * M ^ (k - 2) := mul_le_mul' le_rfl hpow
  unfold normalizedPointwiseBound pointwiseBound
  change (B hk a) ^ k * (pointwiseConstant k * X ^ (k - 2)) ≤
    pointwiseConstant k * (B hk a) ^ 2 * M ^ (k - 2)
  calc
    (B hk a) ^ k * (pointwiseConstant k * X ^ (k - 2))
        = pointwiseConstant k * ((B hk a) ^ k * X ^ (k - 2)) := by
      ring_nf
    _ ≤ pointwiseConstant k * ((B hk a) ^ 2 * M ^ (k - 2)) :=
      mul_le_mul' le_rfl hcore
    _ = pointwiseConstant k * (B hk a) ^ 2 * M ^ (k - 2) := by
      ring_nf

private lemma pointwise_estimate_of_B_eq_zero (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (_ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a = 0) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤ pointwiseBound hk a := by
  have hk0 : k ≠ 0 := by omega
  have hcoord0 (i : Fin k) : eLpNorm (a i) 2 = 0 := by
    exact le_antisymm ((eLpNorm_coord_le_B hk a i).trans_eq hB0) bot_le
  have hpoint (i : Fin k) (j : ι) : a i j = 0 := by
    have hnorm : ‖a i j‖ₑ = 0 := by
      exact le_antisymm
        ((enorm_le_eLpNorm_count (a i) j (by norm_num : (2 : ENNReal) ≠ 0)).trans_eq
          (hcoord0 i)) bot_le
    exact enorm_eq_zero.mp hnorm
  have hQ : Q a = 0 := by
    simp [Q, hpoint, hk0]
  have hs (i : Fin k) : s (a i) = 0 := by
    simp [s, hpoint i]
  simp [pointwiseBound, hB0, hQ, hs, hk0]

omit [Countable ι] in
private lemma pointwise_estimate_scale_back (hk : 2 ≤ k)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖))
    (hB0 : B hk a ≠ 0)
    (hScaled :
      ‖Q (rescaleFamily hk a) - ∏ i, s (rescaleFamily hk a i)‖ₑ ≤
        normalizedPointwiseBound hk (rescaleFamily hk a)) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤ pointwiseBound hk a := by
  rw [rescale_Q_sub_prod_enorm hk a ha hB0]
  exact (mul_le_mul' le_rfl hScaled).trans
    (rescale_normalized_bound_le_original hk a ha hB0)

/-
Scaling reduction from the paper. Once the normalized estimate is known for
a / B, homogeneity gives the original bound with the factor B^2 max(A,B)^(k-2).
-/
private lemma pointwise_estimate_of_normalized (hk : 2 ≤ k)
    (hNorm : ∀ (b : Fin k → ι → ℂ),
      (∀ i, Summable (fun j ↦ ‖b i j‖)) →
      B hk b ≤ 1 →
      ‖Q b - ∏ i, s (b i)‖ₑ ≤ normalizedPointwiseBound hk b)
    (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤ pointwiseBound hk a := by
  by_cases hB0 : B hk a = 0
  · exact pointwise_estimate_of_B_eq_zero hk a ha hB0
  · exact pointwise_estimate_scale_back hk a ha hB0 <|
      hNorm (rescaleFamily hk a) (rescaleFamily_summable hk a ha)
        (B_rescaleFamily_le_one hk a ha hB0)

theorem pointwise_estimate (hk : 2 ≤ k) (a : Fin k → ι → ℂ)
  (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) : ‖Q a - ∏ i, s (a i)‖ₑ ≤
      (((k)! - 1 : ENNReal) * (B hk a) ^ 2 * (max (A hk a) (B hk a)) ^ (k - 2)) := by
  exact pointwise_estimate_of_normalized hk
    (fun b hb hBb ↦ pointwise_estimate_normalized hk b hb hBb) a ha

end Codex

end PointwiseEstimate

end Superorthogonal

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
