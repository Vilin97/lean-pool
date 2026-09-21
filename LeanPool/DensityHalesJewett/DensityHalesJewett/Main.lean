/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination

/-!
# Density Hales--Jewett

The binary base case and induction on the alphabet size.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Identify a binary word with the coordinates on which it equals `1`. -/
def binarySupport {ι : Type*} [Fintype ι] (w : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i ↦ w i = 1

/-- Two binary words are the ordered points of a combinatorial line exactly when their supports
are strictly comparable. -/
lemma binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      binarySupport x ⊂ binarySupport y := by
  have hmem : ∀ (w : ι → Fin 2) (j : ι), j ∈ binarySupport w ↔ w j = 1 := by simp [binarySupport]
  constructor
  · rintro ⟨l, rfl, rfl⟩
    obtain ⟨i, hi⟩ := l.proper
    refine (ssubset_iff_of_subset ?_).2 ⟨i, by simp [hmem, hi], by simp [hmem, hi]⟩
    intro j hj
    cases hj' : l.idxFun j <;> simp_all
  · intro h
    obtain ⟨i, hiy, hix⟩ := exists_of_ssubset h
    have hsub : ∀ j, x j = 1 → y j = 1 := by
      intro j hj
      exact (hmem y j).1 (h.1 ((hmem x j).2 hj))
    refine ⟨⟨fun j ↦ if x j = y j then some (x j) else none, i, by grind⟩, ?_, ?_⟩ <;>
      funext j <;> grind [Combinatorics.Line.coe_apply]

/-- Binary support faithfully records a binary word. -/
lemma binarySupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (binarySupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  apply Fin.ext
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [binarySupport, mem_filter, mem_univ, true_and] using Finset.ext_iff.mp hxy i
  grind

/-- A squared elementary upper bound for the normalized central binomial coefficient. -/
lemma centralBinom_ratio_sq_mul_le (m : ℕ) :
    ((Nat.centralBinom m : ℝ) / 4 ^ m) ^ 2 * (3 * m + 1) ≤ 1 := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec : ((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hratio : (Nat.centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / 4 ^ m) *
            ((2 * m + 1 : ℝ) / (2 * (m + 1))) := by
        rw [pow_succ]
        field_simp
        push_cast at hrec ⊢
        linear_combination 2 * hrec
      rw [hratio, mul_pow, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) ih
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr
      push_cast
      ring_nf
      nlinarith

/-- The middle binomial coefficient is at most the reciprocal square-root proportion of the
Boolean cube. -/
lemma centralBinom_ratio_le_inv_sqrt (m : ℕ) :
    (Nat.centralBinom m : ℝ) / 4 ^ m ≤ (√(3 * m + 1))⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by positivity)),
    ← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [one_pow] using centralBinom_ratio_sq_mul_le m

/-- The two normalizations of the binomial denominator, one per half-dimension and one per
dimension, agree. -/
private lemma two_pow_two_mul (m : ℕ) : (2 : ℝ) ^ (2 * m) = 4 ^ m := by
  rw [pow_mul]
  norm_num

/-- Reduce the normalized middle binomial coefficient in any dimension to the central coefficient
in half that dimension. -/
lemma middleBinomial_ratio_le_central (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤
      (Nat.centralBinom (n / 2) : ℝ) / 4 ^ (n / 2) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : 2 * m / 2 = m := by grind
    rw [hdiv, Nat.centralBinom, two_pow_two_mul]
  · subst n
    have hdiv : (2 * m + 1) / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    cases m with
    | zero => norm_num
    | succ m =>
      have hchoose : (2 * (m + 1) + 1).choose (m + 1) ≤
          2 * Nat.centralBinom (m + 1) := by
        rw [Nat.choose_succ_left (2 * (m + 1)) (m + 1) (by grind)]
        simpa only [Nat.add_sub_cancel, two_mul] using
          add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
      rw [pow_succ, two_pow_two_mul, mul_comm (4 ^ (m + 1) : ℝ) 2]
      apply le_trans (b := (2 * Nat.centralBinom (m + 1) : ℝ) /
        (2 * 4 ^ (m + 1)))
      · exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * 4 ^ (m + 1))).mpr <| by
            exact_mod_cast hchoose
      · field_simp
        rfl

/-- Eventually the middle layer occupies less than any prescribed positive proportion of the
Boolean cube. -/
lemma exists_middleBinomial_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → (n.choose (n / 2) : ℝ) < δ * 2 ^ n := by
  have ht : Filter.Tendsto (fun m : ℕ ↦ (√(3 * (m : ℝ) + 1))⁻¹)
      Filter.atTop (nhds 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply Real.tendsto_sqrt_atTop.comp
    simpa only [add_comm] using
      tendsto_const_nhds.add_atTop
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ))
          Filter.atTop Filter.atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hδ)
  refine ⟨2 * M, ?_⟩
  intro n hn
  have hMn : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by grind)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
  apply (middleBinomial_ratio_le_central n).trans_lt
  apply (centralBinom_ratio_le_inv_sqrt (n / 2)).trans_lt
  exact hM (n / 2) hMn

/-- Density Hales--Jewett for the binary alphabet. -/
lemma dhj_two : HasDensityHJ 2 := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_middleBinomial_lt δ hδ
  refine ⟨N, ?_⟩
  intro n hn A hA
  by_contra hline
  let B := A.image binarySupport
  have hB : IsAntichain (· ⊆ ·) (B : Set (Finset (Fin n))) := by
    intro s hs t ht hst hsub
    change s ∈ B at hs
    change t ∈ B at ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    apply hline
    obtain ⟨l, hlx, hly⟩ := (binary_line_iff_ssubset x y).2 <|
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩
    refine ⟨l, ?_⟩
    intro a
    obtain rfl | ⟨i, rfl⟩ := a.eq_zero_or_eq_succ
    · rw [hlx]
      exact hx
    · simp only [Fin.eq_zero i]
      change l 1 ∈ A
      rwa [hly]
  have hcard : #A ≤ n.choose (n / 2) := by
    rw [← Finset.card_image_of_injective A binarySupport_injective]
    simpa only [B, Fintype.card_fin] using hB.sperner
  exact (not_lt_of_ge (hA.trans <| by exact_mod_cast hcard)) (hN n hn)

/-- A positive uniform increment eventually raises the density floor above one. -/
lemma exists_density_increment_steps {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 1 < δ + (R : ℝ) * (Parameters.γ k δ / 2) := by
  refine ⟨⌈2 / (Parameters.γ k δ)⌉₊ + 1, ?_⟩
  refine lt_trans (?_) (lt_add_of_pos_left _ hδ)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ zero_lt_two).2
  simp only [one_mul]
  apply (div_lt_iff₀ (Parameters.γ_pos hk hδ)).1
  apply lt_of_le_of_lt (Nat.ceil_le.mp le_rfl) (by grind)

/-- Choose the dimensions for a finite density-increment iteration backwards.

The last parameter cube has dimension one.  At stage `j`, the preceding dimension is large enough
to apply `density_increment` with density floor `δ + j * (γ k δ / 2)` and target dimension
`d (j + 1)`. -/
lemma exists_density_increment_schedule (k R : ℕ) (δ : ℝ) :
    ∃ d : ℕ → ℕ,
      d R = 1 ∧
      (∀ j, j ≤ R → 1 ≤ d j) ∧
      ∀ j, j < R →
        incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j := by
  let γ := Parameters.γ k δ
  let d_aux : ℕ → ℕ :=
    Nat.rec 1 (fun t d_t => max 1 (incrementBound k d_t (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))))
  let d : ℕ → ℕ := fun j => d_aux (R - j)
  have h_aux_succ (t : ℕ) : d_aux (t + 1) =
      max 1 (incrementBound k (d_aux t) (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))) := rfl
  have h_aux_one (t : ℕ) : 1 ≤ d_aux t := by
    induction t with
    | zero => simp [d_aux]
    | succ t ih => rw [h_aux_succ t]; exact le_max_left _ _
  have h_d_R : d R = 1 := by
    dsimp [d, d_aux]
    simp
  have h_d_one (j : ℕ) (hj : j ≤ R) : 1 ≤ d j := by
    dsimp [d]
    exact h_aux_one (R - j)
  have h_d_step (j : ℕ) (hj : j < R) :
      incrementBound k (d (j + 1)) (δ + (j : ℝ) * (γ / 2)) ≤ d j := by
    have h_sub : R - j = (R - (j + 1)) + 1 := by omega
    have h_index : (R - ((R - (j + 1) : ℕ) + 1) : ℕ) = j := by omega
    dsimp [d]
    rw [h_sub, h_aux_succ (R - (j + 1)), h_index]
    exact le_max_right _ _
  exact ⟨d, h_d_R, h_d_one, h_d_step⟩

/-- Split the first `m` coordinates from the remaining coordinates of `Fin n`. -/
def prefixCoordinateEquiv {m n : ℕ} (hmn : m ≤ n) : Fin m ⊕ Fin (n - m) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hmn))

/-- Assemble a word from its first `m` coordinates and a fixed remaining suffix. -/
def prefixCoordinateWord {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (x : Fin m → α) (y : Fin (n - m) → α) : Fin n → α :=
  Sum.elim x y ∘ (prefixCoordinateEquiv hmn).symm

/-- The coordinate subspace obtained by fixing every coordinate after the first `m`. -/
def prefixCoordinateSubspace {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) : Combinatorics.Subspace (Fin m) α (Fin n) where
  idxFun i := ((prefixCoordinateEquiv hmn).symm i).elim Sum.inr (Sum.inl ∘ y)
  proper e := by
    refine ⟨prefixCoordinateEquiv hmn (Sum.inl e), ?_⟩
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp]
lemma prefixCoordinateSubspace_apply {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) (x : Fin m → α) :
    prefixCoordinateSubspace hmn y x = prefixCoordinateWord hmn x y := by
  funext i
  change (((prefixCoordinateEquiv hmn).symm i).elim Sum.inr (Sum.inl ∘ y)).elim id x =
    Sum.elim x y ((prefixCoordinateEquiv hmn).symm i)
  cases (prefixCoordinateEquiv hmn).symm i <;> rfl

/-- Some fixed suffix leaves a first-coordinate fiber at least as dense as the ambient family. -/
lemma exists_dense_prefixCoordinateWord {k m n : ℕ} (hmn : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ y : Fin (n - m) → Fin (k + 1),
      (A.dens : ℝ) ≤
        ((Finset.univ.filter fun x : Fin m → Fin (k + 1) ↦
          prefixCoordinateWord hmn x y ∈ A).dens : ℝ) := by
  let eCoord := (Equiv.sumComm (Fin (n - m)) (Fin m)).trans (prefixCoordinateEquiv hmn)
  let eWord := eCoord.arrowCongr (Equiv.refl (Fin (k + 1)))
  let A' := A.map eWord.symm.toEmbedding
  have hA' : (A'.dens : ℝ) = (A.dens : ℝ) := by
    simp only [A', Finset.dens_map_equiv]
  have havg :
      (A.dens : ℝ) ≤ Finset.expect Finset.univ (fun y : Fin (n - m) → Fin (k + 1) ↦
        ((fiber A' y).dens : ℝ)) := by
    rw [average_density_fiber, hA']
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  refine ⟨y, ?_⟩
  have hword (x : Fin m → Fin (k + 1)) :
      eWord (Sum.elim y x) = prefixCoordinateWord hmn x y := by
    funext i
    cases h : (prefixCoordinateEquiv hmn).symm i <;>
      simp [eWord, eCoord, prefixCoordinateWord, Equiv.arrowCongr, Sum.elim, h,
        Function.comp_apply]
  have hfiber : fiber A' y = Finset.univ.filter fun x : Fin m → Fin (k + 1) ↦
      prefixCoordinateWord hmn x y ∈ A := by
    ext x
    simp only [mem_fiber, Finset.mem_filter, Finset.mem_univ, true_and, A',
      Finset.mem_map_equiv, Equiv.symm_symm]
    rw [hword]
  rwa [← hfiber]

/-- A coordinate fiber of any prescribed smaller dimension has relative density at least the
ambient density. -/
lemma exists_density_preserving_subspace_of_le {k m n : ℕ} (hmn : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (A.dens : ℝ) ≤ (Subspace.relativeDensity V A : ℝ) := by
  obtain ⟨y, hy⟩ := exists_dense_prefixCoordinateWord hmn A
  refine ⟨prefixCoordinateSubspace hmn y, ?_⟩
  simpa only [Subspace.relativeDensity, prefixCoordinateSubspace_apply] using hy

/-- One scheduled density-increment stage either produces an ambient line or advances the nested
subspace while preserving the quantitative density invariant. -/
lemma density_increment_chain_step {k R n j : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ t, t ≤ R → 1 ≤ d t)
    (hstep : ∀ t, t < R →
      incrementBound k (d (t + 1))
        (δ + (t : ℝ) * (Parameters.γ k δ / 2)) ≤ d t)
    (hj : j < R) (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n))
    (hV : δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
      (Subspace.relativeDensity V A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ W : Combinatorics.Subspace (Fin (d (j + 1))) (Fin (k + 1)) (Fin n),
        δ + ((j + 1 : ℕ) : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.relativeDensity W A : ℝ) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ρ := δ + (j : ℝ) * (Parameters.γ k δ / 2)
  have hγ := Parameters.γ_mono_lowerBound hk hδ
  have hρ₀ : 0 < ρ := by
    dsimp only [ρ]
    nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hρ₁ : ρ ≤ 1 := hV.trans (by exact_mod_cast Finset.dens_le_one (s := pullback V A))
  have hinc := density_increment hk hDHJ (d (j + 1))
    (hd (j + 1) (Nat.succ_le_of_lt hj)) ρ hρ₀ hρ₁ (d j) (hstep j hj)
      (pullback V A) (by
        simpa only [ρ, Subspace.relativeDensity, pullback] using hV)
  obtain ⟨l, hl⟩ | ⟨U, hU⟩ := hinc
  · left
    use Subspace.mapLine V l
    intro a
    simpa only [Subspace.mapLine_apply, pullback, Finset.mem_filter, Finset.mem_univ,
      true_and] using hl a
  · right
    use Subspace.compose V U
    rw [Subspace.relativeDensity_compose]
    dsimp only [ρ] at hU
    have hδρ : δ ≤ δ + (j : ℝ) * (Parameters.γ k δ / 2) := by
      nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith [hγ.2 _ hδρ]

/-- Iterating the one-step lemma along the schedule either finds a line or reaches the last
scheduled subspace with the accumulated density lower bound. -/
lemma line_or_density_increment_chain {k R n : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R →
      incrementBound k (d (j + 1))
        (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (A : Finset (Fin n → Fin (k + 1)))
    (V₀ : Combinatorics.Subspace (Fin (d 0)) (Fin (k + 1)) (Fin n))
    (hV₀ : δ ≤ (Subspace.relativeDensity V₀ A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin (d R)) (Fin (k + 1)) (Fin n),
        δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.relativeDensity V A : ℝ) := by
  suffices ∀ j, j ≤ R →
      (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n),
          δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
            (Subspace.relativeDensity V A : ℝ) by
    exact this R le_rfl
  intro j hj
  induction j with
  | zero =>
      right
      exact ⟨V₀, by simpa only [Nat.cast_zero, zero_mul, add_zero] using hV₀⟩
  | succ j ih =>
      obtain hline | ⟨V, hV⟩ := ih (Nat.le_of_succ_le hj)
      · left
        exact hline
      · exact density_increment_chain_step hk hDHJ hδ d hd hstep
          (Nat.lt_of_succ_le hj) A V hV

/-- Iterate the density-increment dichotomy along a backward dimension schedule.

Pull back the family after each increment and compose the resulting nested subspaces.  A line in
any parameter cube gives a line in the original family.  Otherwise monotonicity of `Parameters.γ`
raises the density by at least `Parameters.γ k δ / 2` at every stage, and the final relative
density is at most one. -/
lemma line_or_iterated_density_le_one {k R n : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ → ℕ)
    (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R →
      incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (hn : d 0 ≤ n) (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤ 1 := by
  obtain ⟨V₀, hV₀⟩ :=
    exists_density_preserving_subspace_of_le hn A
  obtain hline | ⟨V, hV⟩ :=
    line_or_density_increment_chain hk hDHJ hδ d hd hstep A V₀ (hA.trans hV₀)
  · left
    exact hline
  · right
    exact hV.trans (mod_cast Finset.dens_le_one (s := pullback V A))

/-- Density Hales--Jewett for every finite alphabet of cardinality at least two. -/
lemma density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : HasDensityHJ k := by
  induction k, hk using Nat.le_induction with
  | base => exact dhj_two
  | succ k hk hDHJ =>
      intro δ hδ
      obtain ⟨R, hR⟩ := exists_density_increment_steps hk hδ
      obtain ⟨d, _, hd, hstep⟩ := exists_density_increment_schedule k R δ
      refine ⟨d 0, ?_⟩
      intro n hn A hA
      refine (line_or_iterated_density_le_one hk hDHJ hδ d hd hstep hn A ?_).resolve_right ?_
      · exact Subspace.density_le_of_card_le (Nat.zero_lt_succ k) δ A hA
      · exact not_le_of_gt hR

end DensityHalesJewett

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
noncomputable def densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ :=
  if 2 ≤ k then DensityHalesJewett.Subspace.densityOneBound k δ else 1

/-- The density theorem for alphabets with at most one letter. -/
lemma exists_of_density_card_le_one (α : Type*) [Fintype α]
    (hα : Fintype.card α ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin n → α))
    (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Line.diagonal α (Fin n), ?_⟩
  intro x
  have hcard : Fintype.card α = 1 :=
    Fintype.card_eq_one_of_forall_eq fun y ↦ Subsingleton.elim y x
  rw [hcard] at hAδ
  norm_num at hAδ
  obtain ⟨w, hw⟩ : A.Nonempty := Finset.card_pos.mp <| by
    exact_mod_cast hδ.trans_le hAδ
  simpa only [Subsingleton.elim (Line.diagonal α (Fin n) x) w] using hw

/-- Transport the finite-alphabet density theorem across the canonical alphabet equivalence. -/
lemma exists_of_density_card_ge_two (α : Type*) [Fintype α]
    (hα : 2 ≤ Fintype.card α) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : DensityHalesJewett.Subspace.densityOneBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let e := Fintype.equivFin α
  let wordEquiv : (Fin n → α) ≃ (Fin n → Fin (Fintype.card α)) :=
    (Equiv.refl (Fin n)).arrowCongr e
  let B := A.map wordEquiv.toEmbedding
  have hB : δ * (Fintype.card α : ℝ) ^ n ≤ #B := by
    simpa only [B, Finset.card_map] using hAδ
  obtain ⟨l, hl⟩ := DensityHalesJewett.Subspace.densityOneBound_spec
    (DensityHalesJewett.density_hales_jewett_fin (Fintype.card α) hα)
    δ hδ n hn B hB
  refine ⟨l.map e.symm, ?_⟩
  intro x
  specialize hl (e x)
  rw [Finset.mem_map_equiv] at hl
  change (e.symm ∘ l (e x)) ∈ A at hl
  rwa [← e.symm_apply_apply x, Combinatorics.Line.map_apply]

lemma densityTheoremBound_spec (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  by_cases hα : 2 ≤ Fintype.card α
  · refine exists_of_density_card_ge_two α hα δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, ite_eq_left hα] using hn
  · refine exists_of_density_card_le_one α (by grind) δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, ite_eq_right hα] using hn

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A :=
  densityTheoremBound_spec α δ hδ n hn A hAδ

end Combinatorics.Line
