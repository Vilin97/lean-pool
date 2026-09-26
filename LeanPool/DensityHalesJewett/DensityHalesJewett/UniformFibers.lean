/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.GrahamRothschild
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith

/-!
# Preliminary density lemmas

Multidimensional density Hales--Jewett, uniform fibers, and the restricted-alphabet subspace
lemma.  All subspaces below are mathlib's `Combinatorics.Subspace`.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- The density Hales--Jewett assertion for the alphabet `Fin k`. -/
def HasDensityHJ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ #A → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A

namespace Subspace

/-- A one-dimensional density Hales--Jewett threshold selected from `HasDensityHJ`. -/
noncomputable def densityOneBound (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.find (h.2 δ h.1)
  else 0

lemma densityOneBound_spec {k : ℕ} (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityOneBound k δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A := by
  classical
  rw [densityOneBound, dite_eq_left ⟨hδ, hDHJ⟩] at hn
  exact Nat.find_spec (hDHJ δ hδ) n hn A hA

/-- The one-dimensional case of multidimensional density Hales--Jewett. -/
lemma exists_one_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : densityOneBound k δ ≤ n)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin 1) (Fin k) (Fin n), IsContained V A := by
  obtain ⟨l, hl⟩ := densityOneBound_spec hDHJ δ hδ n hn A hA
  refine ⟨lineToSubspaceFinOne l, ?_⟩
  intro x
  rw [lineToSubspaceFinOne_apply]
  exact hl _

/-- A line is equivalently an `Option`-valued index word with at least one variable
coordinate. -/
private noncomputable def lineIndexEquiv (α ι : Type*) :
    Combinatorics.Line α ι ≃
      {f : ι → Option α // ¬ ∀ i, f i ≠ none} where
  toFun l := by
    refine ⟨l.idxFun, ?_⟩
    intro h
    apply l.proper.elim
    intro i hi
    exact h i hi
  invFun f := ⟨f, by simpa using f.property⟩
  left_inv l := by cases l; rfl
  right_inv _ := Subtype.ext rfl

/-- An index word with no variable coordinate is equivalently an ordinary alphabet word. -/
private noncomputable def fixedIndexWordEquiv (α ι : Type*) [Nonempty α] :
    {f : ι → Option α // ∀ i, f i ≠ none} ≃ (ι → α) where
  toFun f i := (f.1 i).getD (Classical.arbitrary α)
  invFun x := by
    refine ⟨some ∘ x, ?_⟩
    intro i
    exact Option.some_ne_none (x i)
  left_inv f := by
    refine Subtype.ext (funext ?_)
    intro i
    cases hi : f.1 i with
    | none => exact (f.2 i hi).elim
    | some b => simp [hi]
  right_inv x := by simp

/-- The exact number of combinatorial line structures in a nonempty finite-alphabet word cube. -/
lemma card_line (k m : ℕ) (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [Fintype.card_congr (lineIndexEquiv (Fin k) (Fin m)),
    Fintype.card_subtype_compl (fun f : Fin m → Option (Fin k) ↦ ∀ i, f i ≠ none),
    Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin,
    Fintype.card_congr (fixedIndexWordEquiv (Fin k) (Fin m)),
    Fintype.card_pi_const, Fintype.card_fin]

/-- The finite enumeration of line structures induced by their index words. -/
@[instance_reducible]
noncomputable def lineFintype (k m : ℕ) : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
  Fintype.ofInjective (fun l ↦ l.idxFun) fun l₁ l₂ h ↦ by
    cases l₁
    cases l₂
    cases h
    rfl

/-- A subspace over the empty alphabet, obtained by repeating parameter coordinates. -/
def emptyAlphabetSubspace {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Combinatorics.Subspace (Fin m) (Fin 0) (Fin n) where
  idxFun i := Sum.inr ⟨i.val % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩
  proper e := ⟨Fin.castLE hmn e, by simp [Nat.mod_eq_of_lt e.isLt]⟩

/-- Every empty-alphabet subspace is contained in every word family. -/
lemma emptyAlphabetSubspace_isContained {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 0)) : IsContained (emptyAlphabetSubspace hm hmn) A := by
  intro x
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- Convert the cardinal density hypothesis to the normalized finite-set density inequality. -/
lemma density_le_of_card_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    δ ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  refine (le_div_iff₀ ?_).mpr ?_
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  · simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using hA

/-- Convert a normalized density lower bound back to the cardinal form used by the
density Hales--Jewett assertion. -/
lemma card_le_of_density_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ * (k : ℝ) ^ n ≤ #A := by
  rw [Finset.nnratCast_dens] at hA
  have hpos : 0 < (Fintype.card (Fin n → Fin k) : ℝ) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using
    (le_div_iff₀ hpos).mp hA

/-- One fiber of a map to a finite nonempty type has at least the average relative density. -/
lemma exists_fiber_density {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (s : Finset X) (f : X → Y) :
    ∃ y, (s.filter fun x ↦ f x = y).dens ≥ (s.dens : ℝ) / Fintype.card Y := by
  classical
  let b : ℝ := #s / Fintype.card Y
  have hb : (#(Finset.univ : Finset Y) : ℕ) • b ≤ ∑ _x ∈ s, (1 : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul, b]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (s := s) (t := Finset.univ)
      (f := f) (w := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ Finset.mem_univ _)
      Finset.univ_nonempty hb
  refine ⟨y, ?_⟩
  rw [Finset.nnratCast_dens, Finset.nnratCast_dens]
  change (#s : ℝ) / Fintype.card Y ≤ ∑ x ∈ s with f x = y, (1 : ℝ) at hy
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hy
  rw [ge_iff_le]
  simpa only [div_div, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_one] using
    div_le_div_of_nonneg_right hy (by positivity : 0 ≤ (Fintype.card X : ℝ))

/-- At least half the ambient density lies on prefixes with fiber density at least half as large. -/
lemma half_density_prefixes {k p q : ℕ} (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ / 2 ≤
      ((Finset.univ.filter fun x : Fin p → Fin k ↦ δ / 2 ≤ ((fiber A x).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let : Nonempty (Fin p → Fin k) := Pi.instNonempty
  have hδ₁ : δ ≤ 1 := hA.trans (by exact_mod_cast Finset.dens_le_one (s := A))
  have hthreshold := density_ge_threshold (fun x : Fin p → Fin k ↦ ((fiber A x).dens : ℝ))
    δ (δ / 2)
    (fun x ↦ by exact_mod_cast Finset.dens_le_one (s := fiber A x))
    (by linarith) (by simpa only [average_density_fiber] using hA)
  refine le_trans ?_ hthreshold
  refine (le_div_iff₀ ?_).mpr ?_
  · linarith
  · nlinarith

/-- A dense suffix fiber contains a line whose points remain in the ambient family. -/
lemma exists_line_of_fiber_density {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k δ ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (x : Fin p → Fin k)
    (hx : δ ≤ ((fiber A x).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, Sum.elim x (l a) ∈ A := by
  obtain ⟨l, hl⟩ :=
    densityOneBound_spec hDHJ δ hδ q hq (fiber A x)
      (card_le_of_density_le hk δ (fiber A x) hx)
  refine ⟨l, ?_⟩
  intro a
  exact mem_fiber.mp (hl a)

/-- One suffix line is complete above a positive-density family of prefixes. -/
lemma exists_common_dense_line {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k (δ / 2) ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    letI := lineFintype k q
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q))) ≤
        ((Finset.univ.filter fun x : Fin p → Fin k ↦
          ∀ a, Sum.elim x (l a) ∈ A).dens : ℝ) := by
  classical
  let := lineFintype k q
  let B := Finset.univ.filter fun x : Fin p → Fin k ↦
    δ / 2 ≤ ((fiber A x).dens : ℝ)
  have hB : δ / 2 ≤ (B.dens : ℝ) := half_density_prefixes hk δ hδ A hA
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.dens_empty] at hB
    simp only [NNRat.cast_zero] at hB
    linarith
  have existsLine (x : {x // x ∈ B}) : ∃ l : Combinatorics.Line (Fin k) (Fin q),
      ∀ a, Sum.elim x (l a) ∈ A :=
    exists_line_of_fiber_density hk hDHJ (δ / 2) (by linarith) hq A x
      (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using x.2)
  choose lineAt hlineAt using existsLine
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (Fin p → Fin k) → Combinatorics.Line (Fin k) (Fin q) := fun x ↦
    if hx : x ∈ B then lineAt ⟨x, hx⟩ else l₀
  obtain ⟨l, hl⟩ := exists_fiber_density B f
  refine ⟨l, le_trans ?_ (le_trans hl ?_)⟩
  · simpa only [div_div] using
      div_le_div_of_nonneg_right hB
        (by positivity : 0 ≤ (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ))
  · exact_mod_cast Finset.dens_le_dens <| by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hfl : lineAt ⟨x, hx.1⟩ = l := by
        simpa only [f, dite_eq_left hx.1] using hx.2
      intro a
      rw [← hfl]
      exact hlineAt ⟨x, hx.1⟩ a

/-- Every positive target density eventually forces a subspace of any fixed positive
dimension. -/
lemma exists_eventually_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact ⟨emptyAlphabetSubspace hm hmn, emptyAlphabetSubspace_isContained hm hmn A⟩
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  induction m, hm using Nat.le_induction generalizing δ with
  | base =>
      exact ⟨densityOneBound k δ, fun n hn A hA ↦
        exists_one_of_density hDHJ δ hδ n hn A hA⟩
  | succ m hm ih =>
      let q := max 1 (densityOneBound k (δ / 2))
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hq : densityOneBound k (δ / 2) ≤ q := le_max_right _ _
      let : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
      let := lineFintype k q
      let ε := δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q)))
      have hε : 0 < ε := by
        have hlinecard : 0 < Fintype.card (Combinatorics.Line (Fin k) (Fin q)) :=
          Fintype.card_pos
        dsimp only [ε]
        exact div_pos hδ (by exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) hlinecard)
      obtain ⟨P, hP⟩ := ih ε hε
      refine ⟨P + q, ?_⟩
      intro n hn A hA
      let p := n - q
      have hqn : q ≤ n := by omega
      have hpq : p + q = n := Nat.sub_add_cancel hqn
      have hPp : P ≤ p := by omega
      let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
      let wordEquiv : (Fin p ⊕ Fin q → Fin k) ≃ (Fin n → Fin k) :=
        e.arrowCongr (Equiv.refl _)
      let A' := A.map wordEquiv.symm.toEmbedding
      have hA' : δ ≤ (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using density_le_of_card_le hk δ A hA
      obtain ⟨l, hl⟩ := exists_common_dense_line hk hDHJ δ hδ hq A' hA'
      let C := Finset.univ.filter fun x : Fin p → Fin k ↦
        ∀ a, Sum.elim x (l a) ∈ A'
      have hC : ε ≤ (C.dens : ℝ) := by
        simpa only [ε, C] using hl
      obtain ⟨V, hV⟩ := hP p hPp C (card_le_of_density_le hk ε C hC)
      let W₀ : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin p ⊕ Fin q) :=
        (Subspace.concat V (lineToSubspaceFinOne l)).reindex finSumFinEquiv
          (Equiv.refl _) (Equiv.refl _)
      let W : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n) :=
        W₀.reindex (Equiv.refl _) (Equiv.refl _) e
      refine ⟨W, ?_⟩
      intro z
      let x : Fin m → Fin k := fun i ↦ z (finSumFinEquiv (Sum.inl i))
      let a : Fin k := z (finSumFinEquiv (Sum.inr 0))
      have hx : Sum.elim (V x) (l a) ∈ A' := by
        have hxC : ∀ b, Sum.elim (V x) (l b) ∈ A' := by
          simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hV x
        exact hxC a
      rw [Finset.mem_map_equiv] at hx
      simp only [Equiv.symm_symm] at hx
      convert hx using 1
      funext i
      simp only [W, W₀, Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
        Equiv.refl_symm]
      change (Subspace.concat V (lineToSubspaceFinOne l)) (z ∘ finSumFinEquiv) (e.symm i) =
        wordEquiv (Sum.elim (V x) (l a)) i
      have hz : z ∘ finSumFinEquiv =
          Sum.elim x (fun _ : Fin 1 ↦ a) := by
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact congrArg z (congrArg finSumFinEquiv (congrArg Sum.inr (Fin.eq_zero j)))
      rw [hz, Subspace.concat_apply, lineToSubspaceFinOne_apply]
      rfl

/-- A bound for multidimensional density Hales--Jewett. -/
noncomputable def densityBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_of_density h.2.2 m h.1 δ h.2.1)
  else 0

lemma densityBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  rw [densityBound, dite_eq_left ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_of_density hDHJ m hm δ hδ) n hn A hA

/-- Multidimensional density Hales--Jewett follows from the one-dimensional assertion. -/
lemma exists_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A :=
  densityBound_spec hDHJ m hm δ hδ n hn A hA

/-- Split the coordinates of a word family into a prefix and a suffix along a cut equivalence. -/
def splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : Finset (Fin p ⊕ Fin q → Fin alphabet) :=
  A.map (e.arrowCongr (Equiv.refl (Fin alphabet))).symm.toEmbedding

@[simp]
lemma mem_splitWords {alphabet p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin alphabet)} {w : Fin p ⊕ Fin q → Fin alphabet} :
    w ∈ splitWords e A ↔ w ∘ e.symm ∈ A := by
  rw [splitWords, Finset.mem_map_equiv, Equiv.symm_symm]
  rfl

@[simp]
lemma dens_splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : (splitWords e A).dens = A.dens := by
  rw [splitWords, Finset.dens_map_equiv]

/-- The canonical cut equivalence associated with a decomposition of the ambient dimension. -/
def cutEquiv {p q n : ℕ} (h : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

/-- The subspace of a coordinate block whose parameter directions are all of its coordinates. -/
def blockSubspace (α : Type*) (m : ℕ) : Combinatorics.Subspace (Fin m) α (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩

@[simp]
lemma blockSubspace_apply {α : Type*} {m : ℕ} (x : Fin m → α) : blockSubspace α m x = x := by
  funext i
  exact (blockSubspace α m).apply_inr rfl

/-- Prepend a fixed block of letters to the coordinates of a subspace. -/
def prependFixed {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) : Combinatorics.Subspace η α (Fin (m + p)) :=
  transportSubspace finSumFinEquiv.symm u V

@[simp]
lemma prependFixed_apply {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    prependFixed u V x = Sum.elim u (V x) ∘ finSumFinEquiv.symm :=
  transportSubspace_apply finSumFinEquiv.symm u V x

/-- Regroup a cut of the coordinates following a fixed block. -/
def prependCoords {m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin m ⊕ Fin r :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin q))).trans
      (Equiv.sumAssoc (Fin m) (Fin p) (Fin q))).trans ((Equiv.refl (Fin m)).sumCongr e)

/-- Prepend a fixed coordinate block to a cut of the remaining coordinates. -/
def prependCut {m p q r n : ℕ} (h : m + r = n) (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin n :=
  (prependCoords e).trans (cutEquiv h)

/-- Regrouping the coordinates identifies a prepended word with the concatenation of the fixed
block and the cut word. -/
lemma concat_prependFixed {alphabet η m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r)
    (u : Fin m → Fin alphabet) (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCoords e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) := by
  funext s
  cases s with
  | inl a => simp [prependCoords]
  | inr b =>
      cases hb : e.symm b <;> simp [prependCoords, hb]

/-- The same identification stated for the cut of the ambient coordinates. -/
lemma concat_prependFixed_cut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCut h e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) ∘
        (cutEquiv h).symm := by
  rw [← concat_prependFixed e u V x y]
  rfl

/-- The suffix fibers of a prepended cut are the suffix fibers of the family already restricted
to the fixed prefix block. -/
lemma fiber_splitWords_prependCut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (A : Finset (Fin n → Fin alphabet)) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p)) (x : Fin η → Fin alphabet) :
    fiber (splitWords (prependCut h e) A) (prependFixed u V x) =
      fiber (splitWords e (fiber (splitWords (cutEquiv h) A) u)) (V x) := by
  ext y
  simp only [mem_fiber, mem_splitWords]
  rw [concat_prependFixed_cut]

/-- A prefix fiber sparser than the ambient density by `ε` forces another prefix fiber denser
than the ambient density by a fixed amount. -/
lemma exists_denser_fiber {alphabet m q : ℕ} (halphabet : 0 < alphabet) {ε : ℝ} (hε : 0 < ε)
    (A : Finset (Fin m ⊕ Fin q → Fin alphabet)) (u₀ : Fin m → Fin alphabet)
    (hu₀ : ((fiber A u₀).dens : ℝ) < (A.dens : ℝ) - ε) :
    ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ m ≤ ((fiber A u).dens : ℝ) := by
  classical
  by_contra! hcon
  have halphabetR : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast halphabet
  have hpow : (0 : ℝ) < (alphabet : ℝ) ^ m := pow_pos halphabetR m
  have hcard : (Fintype.card (Fin m → Fin alphabet) : ℝ) = (alphabet : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hsum : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) =
      (alphabet : ℝ) ^ m * (A.dens : ℝ) := by
    rw [← average_density_fiber A, ← hcard, ← Finset.card_univ, Finset.card_mul_expect]
  have hle : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) ≤
      ∑ u : Fin m → Fin alphabet, (((A.dens : ℝ) + ε / (alphabet : ℝ) ^ m) +
        if u = u₀ then -(ε + ε / (alphabet : ℝ) ^ m) else 0) := by
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : u = u₀
    · rw [hu, ite_eq_left rfl]
      linarith
    · rw [ite_eq_right hu, add_zero]
      linarith [hcon u]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ u₀,
    ite_eq_left (Finset.mem_univ u₀), Finset.card_univ, nsmul_eq_mul, hcard, hsum, mul_add,
    mul_div_cancel₀ ε hpow.ne'] at hle
  linarith [div_pos hε hpow]

/-- Every ambient dimension admits a cut into a prefix carrying a subspace and a nonempty suffix
above which all fibers are almost as dense as the whole family. -/
def VariableCutFibersSufficient (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet),
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ)

/-- The block density-increment argument: one coordinate block either uniformizes all suffix
fibers or increases the working density by a fixed amount, and the density upper bound bounds the
number of increments. -/
private lemma exists_variableCut_of_fuel (alphabet dimension : ℕ) (halphabet : 0 < alphabet)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t n : ℕ, dimension * (t + 1) < n → ∀ A : Finset (Fin n → Fin alphabet),
      1 ≤ (A.dens : ℝ) + t * (ε / (alphabet : ℝ) ^ dimension) →
      ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
        ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
          ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro n hn A hfuel
      have hblock : dimension ≤ dimension * (t + 1) :=
        Nat.le_mul_of_pos_right dimension (Nat.succ_pos t)
      have hd : dimension + (n - dimension) = n := by omega
      have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
        div_pos hε (pow_pos (by exact_mod_cast halphabet) dimension)
      by_cases hsucc :
          ∀ u, (A.dens : ℝ) - ε ≤ ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ)
      · exact ⟨dimension, n - dimension, cutEquiv hd, by omega,
          blockSubspace (Fin alphabet) dimension, by simpa only [blockSubspace_apply] using hsucc⟩
      push Not at hsucc
      obtain ⟨u₀, hu₀⟩ := hsucc
      obtain ⟨u, hu⟩ := exists_denser_fiber halphabet hε (splitWords (cutEquiv hd) A) u₀
        (by rwa [dens_splitWords])
      rw [dens_splitWords] at hu
      have hu₁ : ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ) ≤ 1 := by
        exact_mod_cast Finset.dens_le_one (s := fiber (splitWords (cutEquiv hd) A) u)
      have htR : (1 : ℝ) ≤ (t : ℝ) := by
        nlinarith [mul_pos hεpos hεpos]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
        have : 1 ≤ t := by exact_mod_cast htR
        omega⟩
      have hstep : dimension * (s + 1 + 1) = dimension * (s + 1) + dimension := by ring
      obtain ⟨p, q, e, hq, V, hV⟩ := ih s (by omega) (n - dimension) (by omega)
        (fiber (splitWords (cutEquiv hd) A) u)
        (by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfuel; linarith)
      refine ⟨dimension + p, q, prependCut hd e, hq, prependFixed u V, ?_⟩
      intro x
      rw [fiber_splitWords_prependCut]
      linarith [hV x]

/-- Every sufficiently large ambient dimension is sufficient for variable-cut uniform fibers. -/
lemma exists_eventually_variableCutFibersSufficient (alphabet dimension : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  by_cases halphabet : alphabet = 0
  · subst alphabet
    refine ⟨dimension + 1, ?_⟩
    intro n hn A
    refine ⟨dimension, n - dimension, cutEquiv (by omega), by omega,
      emptyAlphabetSubspace hdimension le_rfl, ?_⟩
    intro x
    exact Fin.elim0 (x ⟨0, hdimension⟩)
  have halphabet₀ : 0 < alphabet := Nat.pos_of_ne_zero halphabet
  have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
    div_pos hε (pow_pos (by exact_mod_cast halphabet₀) dimension)
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / (ε / (alphabet : ℝ) ^ dimension))
  refine ⟨dimension * (t + 1) + 1, ?_⟩
  intro n hn A
  apply exists_variableCut_of_fuel alphabet dimension halphabet₀ hε t n (by omega) A
  rw [div_lt_iff₀ hεpos] at ht
  linarith [NNRat.cast_nonneg (α := ℝ) A.dens]

/-- A sufficient ambient dimension for the variable-cut uniform-fibers lemma. -/
noncomputable def variableCutFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ dimension ∧ 0 < ε then
    Nat.find (exists_eventually_variableCutFibersSufficient alphabet dimension h.1 h.2)
  else 0

/-- The selected variable-cut bound is sufficient in every larger ambient dimension. -/
lemma variableCutFibersBound_spec (alphabet dimension n : ℕ) (hdimension : 1 ≤ dimension)
    {ε : ℝ} (hε : 0 < ε) (hn : variableCutFibersBound alphabet dimension ε ≤ n) :
    VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  rw [variableCutFibersBound, dite_eq_left ⟨hdimension, hε⟩] at hn
  exact Nat.find_spec
    (exists_eventually_variableCutFibersSufficient alphabet dimension hdimension hε) n hn

/-- Averaging restricted-parameter slice densities over suffixes equals averaging their ambient
fiber densities over restricted parameter words. -/
lemma average_restrictedParameterSlice {k M : ℕ}
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) :
    Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
      ((Finset.univ.filter fun x : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) =
      Finset.expect Finset.univ (fun x : Fin M → Fin k ↦
        ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) := by
  simp_rw [← Finset.expect_indicator_one]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  by_cases h : Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A <;> simp [h]

/-- Averaging a pointwise-dense family of suffix fibers produces one suffix above which the
restricted parameter family is dense. -/
lemma exists_dense_suffix_of_restricted_fibers {k M : ℕ} (hk : 0 < k) (δ : ℝ)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hW : ∀ x : Fin M → Fin k,
      δ / 2 ≤ ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :
    ∃ y : κ → Fin (k + 1),
      δ / 2 ≤
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have havg : δ / 2 ≤
      Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) := by
    rw [average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦ hW x
  by_contra! h
  apply (not_lt_of_ge havg)
  apply Finset.expect_lt
  · intro y _
    exact (h y).le
  · exact ⟨fun _ ↦ 0, Finset.mem_univ _, h (fun _ ↦ 0)⟩

/-- Extend a restricted parameter subspace to the full alphabet, attach a fixed suffix, and
transport the resulting subspace along an equivalence of ambient coordinates. -/
lemma extend_restricted_subspace {k m M : ℕ} {ι κ ζ : Type*}
    [DecidableEq (ζ → Fin (k + 1))] (e : ι ⊕ κ ≃ ζ)
    (A : Finset (ζ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) (y : κ → Fin (k + 1))
    (S : Combinatorics.Subspace (Fin m) (Fin k) (Fin M))
    (hS : ∀ x, (Sum.elim (W (Fin.castSucc ∘ S x)) y) ∘ e.symm ∈ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ,
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let lift_S : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M) :=
    { idxFun := fun i ↦ (S.idxFun i).map (Fin.castSuccEmb : Fin k → Fin (k + 1)) id
      proper := fun e ↦ by
        obtain ⟨i, hi⟩ := S.proper e
        refine ⟨i, ?_⟩
        simp [hi] }
  have h_lift_eval (x : Fin m → Fin k) : lift_S (Fin.castSuccEmb ∘ x) = Fin.castSucc ∘ S x := by
    ext i
    cases hi : S.idxFun i <;> simp [lift_S, Combinatorics.Subspace.coe_apply, hi]
  let concat_suffix : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ζ :=
    { idxFun := fun c ↦
        match e.symm c with
        | Sum.inl i => W.idxFun i
        | Sum.inr j => Sum.inl (y j)
      proper := fun e' ↦ by
        obtain ⟨i, hi⟩ := W.proper e'
        refine ⟨e (Sum.inl i), ?_⟩
        simp [hi] }
  have h_concat_suffix_eval (z : Fin M → Fin (k + 1)) :
      concat_suffix z = (Sum.elim (W z) y) ∘ e.symm := by
    ext c
    simp only [Subspace.coe_apply, Function.comp_apply, concat_suffix]
    cases e.symm c <;> simp [Combinatorics.Subspace.coe_apply]
  let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ :=
    compose concat_suffix lift_S
  refine ⟨V, ?_⟩
  intro w hw
  rw [restrictAlphabet, Finset.mem_image] at hw
  rcases hw with ⟨x, _, rfl⟩
  rw [compose_apply, h_lift_eval x, h_concat_suffix_eval (Fin.castSucc ∘ S x)]
  exact hS x

/-- For the empty restricted alphabet, the restricted range is empty as soon as the parameter
dimension is positive. -/
lemma exists_empty_restrictAlphabet_subset {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 1)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n) :=
    { idxFun := fun i ↦ if hi : i.val < m then Sum.inr ⟨i.val, hi⟩ else Sum.inl 0
      proper := fun e ↦ by
        refine ⟨Fin.castLE hmn e, ?_⟩
        simp only [Fin.castLE, e.isLt, ↓reduceDIte] }
  refine ⟨V, ?_⟩
  intro w hw
  simp only [restrictAlphabet, Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨x, _⟩ := hw
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- The restricted-alphabet conclusion holds in every sufficiently large dimension. -/
lemma exists_eventually_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
      δ * (k + 1 : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact exists_empty_restrictAlphabet_subset hm hmn A
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  let M := max 1 (densityBound k m (δ / 2))
  refine ⟨variableCutFibersBound (k + 1) M (δ / 2), ?_⟩
  intro n hn A hA
  have hM : 1 ≤ M := le_max_left _ _
  have hA' : δ ≤ (A.dens : ℝ) := by
    apply density_le_of_card_le (Nat.zero_lt_succ k) δ A
    convert hA using 1
    norm_num
  obtain ⟨p, q, e, _hq, W, hW⟩ :=
    variableCutFibersBound_spec (k + 1) M n hM (by linarith) hn A
  obtain ⟨y, hy⟩ :=
    exists_dense_suffix_of_restricted_fibers hk δ (splitWords e A) W fun x ↦ by
      linarith [hW (Fin.castSucc ∘ x)]
  let B := Finset.univ.filter fun x : Fin M → Fin k ↦
    Sum.elim (W (Fin.castSucc ∘ x)) y ∈ splitWords e A
  obtain ⟨S, hS⟩ :=
    exists_of_density hDHJ m hm (δ / 2) (by linarith) M (le_max_right _ _) B
      (card_le_of_density_le hk (δ / 2) B (by simpa only [B] using hy))
  apply extend_restricted_subspace e A W y S
  intro x
  rw [← mem_splitWords]
  simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hS x

/-- A bound for the restricted-alphabet subspace lemma. -/
noncomputable def restrictAlphabetBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_restrictAlphabet_subset h.2.2 m h.1 δ h.2.1)
  else 0

lemma restrictAlphabetBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  rw [restrictAlphabetBound, dite_eq_left ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_restrictAlphabet_subset hDHJ m hm δ hδ) n hn A hA

/-- A dense family over `Fin (k+1)` contains the `Fin k` restriction of a subspace. -/
lemma exists_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A :=
  restrictAlphabetBound_spec hDHJ m hm δ hδ n hn A hA

end Subspace
end DensityHalesJewett
