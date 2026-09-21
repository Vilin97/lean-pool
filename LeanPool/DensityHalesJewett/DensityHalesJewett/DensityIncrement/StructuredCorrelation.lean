/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.CorrelatedFibers
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNRat.BigOperators

/-!
# Structured correlation with insensitive intersections

Endpoint families turn many complete restricted-alphabet lines into a large intersection of
insensitive families, and the first-failure partition upgrades that intersection into a family
correlated with the ambient word family.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- A power of the restricted-alphabet proportion eventually falls below the error tolerance. -/
lemma exists_restrictedParameterWords_decay {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    ∃ m : ℕ, ((k : ℝ) / (k + 1)) ^ m < Parameters.η k δ := by
  apply exists_pow_lt_of_lt_one (Parameters.η_pos hk hδ₀)
  apply (div_lt_one (by positivity : 0 < (k + 1 : ℝ))).mpr
  norm_num

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
noncomputable def insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 2 ≤ k ∧ 0 < δ then
    Nat.find (exists_restrictedParameterWords_decay h.1 h.2)
  else 0

/-- Above the selected dimension, the restricted-alphabet proportion is at most the error
tolerance. -/
lemma insensitiveIntersectionDimension_spec {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hm : insensitiveIntersectionDimension k δ ≤ m) :
    ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k δ := by
  classical
  rw [insensitiveIntersectionDimension, dite_eq_left ⟨hk, hδ₀⟩] at hm
  refine (pow_le_pow_of_le_one (by positivity) ?_ hm).trans ?_
  · exact (div_le_one (by positivity : 0 < (k + 1 : ℝ))).mpr (by norm_num)
  · exact (Nat.find_spec (exists_restrictedParameterWords_decay hk hδ₀)).le

/-- Replace every occurrence of the final alphabet letter by a fixed restricted-alphabet
letter. -/
def replaceLastLetter {k m : ℕ} (i : Fin k) (x : Fin m → Fin (k + 1)) :
    Fin m → Fin (k + 1) :=
  fun c ↦ if x c = Fin.last k then i.castSucc else x c

/-- The endpoint family associated with one restricted-alphabet letter. -/
def endpointFamily {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (i : Fin k) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ V (replaceLastLetter i x) ∈ A

/-- Parameter words which avoid the final alphabet letter. -/
def restrictedParameterWords (k m : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ ∀ c, x c ≠ Fin.last k

/-- The restricted parameter words are exactly the pointwise images of `Fin k`-valued words. -/
lemma restrictedParameterWords_eq_map (k m : ℕ) :
    restrictedParameterWords k m =
      Finset.univ.map (Function.Embedding.piCongrRight fun _ : Fin m ↦
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) := by
  classical
  ext x
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · intro hx
    let y : Fin m → Fin k := fun c ↦ (x c).castPred (hx c)
    refine ⟨y, ?_⟩
    funext c
    exact Fin.castSucc_castPred (x c) (hx c)
  · rintro ⟨y, rfl⟩ c
    exact Fin.castSucc_ne_last (y c)

/-- The density of restricted parameter words is the expected power of the alphabet ratio. -/
lemma restrictedParameterWords_density (k m : ℕ) :
    ((restrictedParameterWords k m).dens : ℝ) = ((k : ℝ) / (k + 1)) ^ m := by
  rw [restrictedParameterWords_eq_map, Finset.nnratCast_dens, Finset.card_map,
    Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
    Fintype.card_pi_const, Fintype.card_fin]
  rw [div_pow]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- Each endpoint family is insensitive to interchanging its selected letter with the final
letter. -/
lemma endpointFamily_isInsensitive {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k) :
    IsInsensitive i.castSucc (Fin.last k) (endpointFamily A V i) := by
  intro x y hxy
  have hreplace : replaceLastLetter i x = replaceLastLetter i y := by
    funext c
    by_cases hxi : x c = i.castSucc <;> by_cases hyi : y c = i.castSucc <;>
      grind [replaceLastLetter, hxy (x c), hxy (y c)]
  simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hreplace]

/-- Encode a restricted-alphabet line by the word using the final letter on its wildcard
coordinates. -/
private def lineEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Fin m → Fin (k + 1) :=
  fun c ↦
    match l.idxFun c with
    | none => Fin.last k
    | some a => a.castSucc

/-- The endpoint word remembers every fixed letter and every wildcard coordinate of a line. -/
private lemma lineEndpoint_injective {k m : ℕ} :
    Function.Injective (lineEndpoint : Combinatorics.Line (Fin k) (Fin m) →
      (Fin m → Fin (k + 1))) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ hll
  congr
  funext c
  have hc := congrFun hll c
  cases hfc : f c <;> cases hgc : g c <;>
    simp_all [lineEndpoint, Fin.castSucc_ne_last, eq_comm (a := Fin.last k)]

/-- Complete restricted-alphabet parameter lines inject into the intersection of the endpoint
families, giving the required density lower bound. -/
lemma endpointFamily_intersection_dense {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hrestricted : ((restrictedParameterWords k m).dens : ℝ) ≤ 1 / 2)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    Parameters.θ k δ / 4 ≤
      ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
  classical
  let good := Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
    ∀ a, V (Fin.castSucc ∘ l a) ∈ A
  let endpointEmbedding :
      Combinatorics.Line (Fin k) (Fin m) ↪ (Fin m → Fin (k + 1)) :=
    ⟨lineEndpoint, lineEndpoint_injective⟩
  have hsubset :
      good.map endpointEmbedding ⊆ IsInsensitive.intersection (endpointFamily A V) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hx
    apply IsInsensitive.mem_intersection.mpr
    intro i
    simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
    have hgood :
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    have heval :
        replaceLastLetter i (lineEndpoint l) = Fin.castSucc ∘ l i := by
      funext c
      cases hc : l.idxFun c with
      | none =>
          simp [lineEndpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc]
      | some a =>
          simp [lineEndpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc,
            Fin.castSucc_ne_last]
    change V (replaceLastLetter i (lineEndpoint l)) ∈ A
    rw [heval]
    exact hgood i
  have hmono :
      ((good.map endpointEmbedding).dens : ℝ) ≤
        ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens hsubset
  refine (le_trans ?_ hmono)
  have hgood :
      Parameters.θ k δ / 2 ≤ (good.dens : ℝ) := by
    simpa only [good] using hlines
  have hlinepos :
      0 < (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) := by
    have hgoodpos : 0 < (good.dens : ℝ) :=
      (div_pos (Parameters.θ_pos hk hδ₀) (by norm_num)).trans_le hgood
    have hgne : good.Nonempty := Finset.dens_pos.mp (by exact_mod_cast hgoodpos)
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) := ⟨hgne.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [Finset.nnratCast_dens, Finset.card_map]
  rw [Finset.nnratCast_dens] at hgood hrestricted
  have hlinecard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    rw [Subspace.card_line k m (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) m
  have hwordcard :
      (Fintype.card (Fin m → Fin (k + 1)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hrestrictedcard :
      (restrictedParameterWords k m).card = k ^ m := by
    rw [restrictedParameterWords_eq_map, Finset.card_map, Finset.card_univ,
      Fintype.card_pi_const, Fintype.card_fin]
  rw [hlinecard] at hgood hlinepos
  rw [hwordcard] at ⊢
  rw [hrestrictedcard, Nat.cast_pow, hwordcard] at hrestricted
  have hwordpos : 0 < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hhalf :
      ((k + 1 : ℕ) : ℝ) ^ m / 2 ≤
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    apply (div_le_iff₀ hwordpos).mp at hrestricted
    nlinarith
  rw [le_div_iff₀ hlinepos] at hgood
  rw [le_div_iff₀ hwordpos]
  nlinarith [hhalf, hgood, Parameters.θ_pos hk hδ₀]

/-- In a line-free ambient family, a word lying both in its pullback and in every endpoint family
cannot use the final alphabet letter. -/
lemma pullback_inter_endpointFamily_subset_restricted {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A) :
    pullback V A ∩ IsInsensitive.intersection (endpointFamily A V) ⊆
      restrictedParameterWords k m := by
  intro x hx
  obtain ⟨hxpull, hxinter⟩ := Finset.mem_inter.mp hx
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  let p : Combinatorics.Line (Fin (k + 1)) (Fin m) := {
    idxFun := fun i ↦ if x i = Fin.last k then none else some (x i)
    proper := ⟨c, ite_eq_left hc⟩
  }
  have hp_last : p (Fin.last k) = x := by
    funext i
    by_cases hi : x i = Fin.last k <;>
      simp only [p, Combinatorics.Line.coe_apply, hi, ↓reduceIte, Option.getD_none,
        Option.getD_some]
  have hp_cast (i : Fin k) : p i.castSucc = replaceLastLetter i x := by
    funext j
    by_cases hj : x j = Fin.last k <;>
      simp only [p, replaceLastLetter, Combinatorics.Line.coe_apply, hj, ↓reduceIte,
        Option.getD_none, Option.getD_some]
  obtain ⟨a, ha⟩ := hfree (Subspace.composeLine V p)
  apply ha
  rw [Subspace.composeLine_apply]
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
  · rw [hp_cast]
    have hi := IsInsensitive.mem_intersection.mp hxinter i
    simpa only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · rw [hp_last]
    simpa only [pullback, Finset.mem_filter, Finset.mem_univ, true_and] using hxpull

/-- In a sufficiently large parameter cube, words avoiding the final letter have density at most
`η`. -/
lemma restrictedParameterWords_density_le_eta {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m) :
    ((restrictedParameterWords k m).dens : ℝ) ≤ Parameters.η k δ := by
  rw [restrictedParameterWords_density]
  exact insensitiveIntersectionDimension_spec hk hδ₀ hm_large

/-- Many complete restricted-alphabet lines yield a large insensitive intersection whose part
inside a line-free family is small.  This packages the endpoint construction, its injective
line count, the identification of the intersection, and the geometric-decay estimate. -/
lemma exists_endpoint_insensitive_intersection {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ IsInsensitive.intersection C).dens : ℝ) ≤
        Parameters.η k δ := by
  refine ⟨endpointFamily A V, endpointFamily_isInsensitive A V, ?_, ?_⟩
  · refine endpointFamily_intersection_dense hk hδ₀ A V ?_ hlines
    apply (restrictedParameterWords_density_le_eta hk hδ₀ hm_large).trans
    exact (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  · refine le_trans ?_ <|
      restrictedParameterWords_density_le_eta hk hδ₀ hm_large
    exact_mod_cast Finset.dens_mono <|
      pullback_inter_endpointFamily_subset_restricted A V hfree

/-- Removing an intersection of density at least `θ / 4`, while losing at most `η` of a family
of density `δ - 2η`, gives the two complement estimates used below. -/
lemma density_complement_bounds {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] (A C : Finset X) (δ η θ : ℝ)
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa only [sdiff_eq_inter_compl] using Finset.dens_inter_add_dens_sdiff A C
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa only [← compl_eq_univ_sdiff, Finset.dens_univ] using
      Finset.dens_sdiff_add_dens_eq_dens C.subset_univ
  have houtside : δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
    linarith [hsplitA, hA, hAC]
  constructor
  · refine (mul_le_mul_of_nonneg_left ?_ ?_).trans (hgain.trans houtside)
    · linarith [hsplitC, hC]
    · linarith [hδ₀, hη₀]
  · exact houtside

/-- An intersection of insensitive families with a density gain on its complement. -/
lemma exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A)
    (hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
        (δ + 6 * Parameters.η k δ) *
            ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * Parameters.η k δ ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  classical
  let : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (fun l ↦ l.idxFun) fun _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, hlines⟩ :=
    exists_subspace_many_lines hk hDHJ m hm δ hδ₀ hδ₁ n hn A hA
  · exact ((not_lt_of_ge hV) (hsmall V)).elim
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    exists_endpoint_insensitive_intersection hk δ hδ₀ hδ₁ hm_large A V hfree hlines
  refine ⟨V, C, hC, ?_⟩
  apply density_complement_bounds
  · exact hδ₀.le
  · exact (Parameters.η_pos hk hδ₀).le
  · simpa only [Subspace.relativeDensity, pullback] using hV
  · exact hCdense
  · exact hAC
  · exact Parameters.large_intersection_complement_gain hk hδ₀

/-- The part of the complement of an indexed intersection at which membership first fails. -/
def firstFailurePiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  (C i)ᶜ ∩ Finset.univ.filter fun x ↦ ∀ j, j < i → x ∈ C j

/-- Replace the first failed set by its complement, retain the preceding sets, and make all
subsequent constraints vacuous. -/
def firstFailureFamily {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  fun j ↦ if j < i then C j else if j = i then (C j)ᶜ else Finset.univ

/-- Every member of the first-failure family has the required sensitivity pair. -/
lemma firstFailureFamily_isInsensitive {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    ∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j) := by
  intro j
  dsimp [firstFailureFamily]
  by_cases hij : j < i
  · simp [hij, hC j]
  · by_cases hej : j = i
    · rw [hej]
      simpa using (hC i).compl
    · simp [hij, hej, IsInsensitive]

/-- Intersecting the first-failure family recovers its selected piece. -/
lemma firstFailureFamily_intersection {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) :
    IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i := by
  ext x
  simp only [IsInsensitive.mem_intersection, firstFailureFamily, firstFailurePiece,
    Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    constructor
    · have hxi := hx i
      simp only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] at hxi
      exact hxi
    · intro j hij
      simpa only [ite_eq_left hij] using hx j
  · rintro ⟨hnot, hbefore⟩ j
    by_cases hij : j < i
    · simpa only [ite_eq_left hij] using hbefore j hij
    · by_cases hji : j = i
      · subst j
        simpa only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] using hnot
      · simp only [ite_eq_right hij, ite_eq_right hji, Finset.mem_univ]

/-- The first-failure pieces cover the complement of the original intersection. -/
lemma firstFailurePiece_biUnion {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl] at hi
    rw [Finset.mem_compl]
    intro hinter
    exact hi.1 (IsInsensitive.mem_intersection.mp hinter i)
  · rw [Finset.mem_compl]
    intro hx
    have hfailed : ∃ i, x ∉ C i := by
      by_contra! h
      exact hx <| IsInsensitive.mem_intersection.mpr h
    let I := Finset.univ.filter fun i : Fin k ↦ x ∉ C i
    have hI : I.Nonempty := by
      obtain ⟨i, hi⟩ := hfailed
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i := I.min' hI
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl]
    constructor
    · exact (Finset.mem_filter.mp (I.min'_mem hI)).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hij
      by_contra hj
      have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      exact (not_lt_of_ge (I.min'_le j hjI)) hij

/-- A first-failure piece is disjoint from every piece at a later index. -/
lemma firstFailurePiece_disjoint_of_lt {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) {i j : Fin k} (hij : i < j) :
    Disjoint (firstFailurePiece C i : Set X) (firstFailurePiece C j : Set X) := by
  dsimp only [Disjoint]
  intro x hxi hxj
  simp only [firstFailurePiece, coe_inter, coe_compl, coe_filter, mem_univ, true_and,
    Set.subset_inter_iff] at *
  simp only [Set.bot_eq_empty, Set.subset_empty_iff]
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  exact (hxi.1 hy) (hxj.2 hy i hij)

/-- Distinct first-failure pieces are pairwise disjoint. -/
lemma firstFailurePiece_pairwiseDisjoint {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦ (firstFailurePiece C i : Set X) := by
  intro i _ j _ hij
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact firstFailurePiece_disjoint_of_lt C hij
  · exact (firstFailurePiece_disjoint_of_lt C hji).symm

/-- The first-failure partition converts the densities of its pieces, and of their intersections
with `A`, into sums. -/
lemma firstFailurePiece_density_sums {k : ℕ}
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X) :
    (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
        (((IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
      (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
        ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  constructor
  · have h := Finset.dens_biUnion (s := Finset.univ) (t := firstFailurePiece C) <|
      Finset.pairwiseDisjoint_coe.mp <| by
        simpa only [Finset.coe_univ] using firstFailurePiece_pairwiseDisjoint C
    rw [firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm
  · have hpairwise :
        (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦
          (A ∩ firstFailurePiece C i : Set X) :=
      (firstFailurePiece_pairwiseDisjoint C).mono_on fun _ _ ↦
        Set.inter_subset_right
    have h := Finset.dens_biUnion (s := Finset.univ)
      (t := fun i ↦ A ∩ firstFailurePiece C i) <|
        Finset.pairwiseDisjoint_coe.mp <| by
          simpa only [Finset.coe_univ, Finset.coe_inter] using hpairwise
    rw [← Finset.inter_biUnion, firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm

/-- The quantitative hypotheses and the first-failure density sums force one piece to be both
large and relatively dense in `A`. -/
lemma exists_dense_firstFailurePiece_of_density_sums {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumPieces : (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
      (((IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumIntersections : (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  by_contra! h
  let g := Parameters.γ k δ
  let e := Parameters.η k δ
  let c := (((IsInsensitive.intersection C)ᶜ).dens : ℝ)
  let a := ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)
  let : Nonempty (Fin k) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hk⟩⟩
  have hg₀ : 0 < g := Parameters.γ_pos hk hδ₀
  have he₀ : 0 < e := Parameters.η_pos hk hδ₀
  have hsum_lt :
      ∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ) <
        ∑ i, ((δ + g) * ((firstFailurePiece C i).dens : ℝ) + g) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    by_cases hi : g ≤ ((firstFailurePiece C i).dens : ℝ)
    · linarith [h i (by simpa only [g] using hi)]
    · have hinter :
          ((A ∩ firstFailurePiece C i).dens : ℝ) ≤ ((firstFailurePiece C i).dens : ℝ) := by
        exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
      have hcoefficient : 0 ≤ δ + g := by linarith
      nlinarith [mul_nonneg hcoefficient
        (by positivity : 0 ≤ ((firstFailurePiece C i).dens : ℝ))]
  have hupper : a < (δ + g) * c + (k : ℝ) * g := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_lt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum_lt
    rwa [hsumPieces, hsumIntersections] at hsum_lt
  have hac : a ≤ c := by
    dsimp only [a, c]
    exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
  have hc : δ / 2 ≤ c := by
    dsimp only [a, c] at hlarge hac
    linarith [Parameters.η_le_δ_div_six k δ]
  have hcoef : 3 * e ≤ 6 * e - g := by
    dsimp only [e, g]
    linarith [Parameters.γ_le_three_mul_η k δ]
  have hleft :
      3 * e * (δ / 2) ≤ (6 * e - g) * c :=
    mul_le_mul hcoef hc (by positivity) (by linarith)
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hk
  have hright : (k : ℝ) * g ≤ δ * e ^ 2 := by
    have hdiv : g ≤ δ * e ^ 2 / (k : ℝ) := by
      dsimp only [g, e]
      unfold Parameters.γ
      exact min_le_left _ _
    simpa only [mul_comm] using (le_div_iff₀ hk_real).mp hdiv
  have hstrict : δ * e ^ 2 < 3 * e * (δ / 2) := by
    dsimp only [e]
    nlinarith [Parameters.η_le_δ_div_six k δ]
  have hgap : (6 * e - g) * c < (k : ℝ) * g := by
    dsimp only [a, c, e, g] at hweighted hupper
    nlinarith
  exact (not_lt_of_ge hleft) (hgap.trans_le hright |>.trans hstrict)

/-- The first-failure partition and its quantitative weighted averaging.

The complement of `intersection C` is partitioned by `firstFailurePiece C i`.  The two global
density estimates ensure that one piece is both large enough and has the required relative
`A`-density. -/
lemma exists_dense_firstFailurePiece {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  obtain ⟨hsumPieces, hsumIntersections⟩ :=
    firstFailurePiece_density_sums A C
  exact exists_dense_firstFailurePiece_of_density_sums hk hδ₀ hδ₁ A C hweighted
    hlarge hsumPieces hsumIntersections

/-- The Boolean reconstruction of a first-failure piece as an insensitive intersection.

Complement closure preserves the sensitivity pair at the failure index, while the universal
sets after that index impose no constraints. -/
lemma firstFailureFamily_facts {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    (∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j)) ∧
      IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i ∧
      Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint fun j ↦
        (firstFailurePiece C j : Set (ι → Fin (k + 1))) :=
  ⟨firstFailureFamily_isInsensitive C hC i,
    firstFailureFamily_intersection C i, firstFailurePiece_biUnion C,
    firstFailurePiece_pairwiseDisjoint C⟩

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k δ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  classical
  by_cases hlarge : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)
  · obtain ⟨V, hV⟩ := hlarge
    let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    let : DecidableEq (Fin m → Fin (k + 1)) := Classical.decEq _
    let D := fun _ : Fin k ↦ (Finset.univ : Finset (Fin m → Fin (k + 1)))
    have hD : IsInsensitive.intersection D = Finset.univ := by
      simpa only [IsInsensitive.intersection, D] using
        (Finset.inf_const (s := (Finset.univ : Finset (Fin k))) Finset.univ_nonempty
          (Finset.univ : Finset (Fin m → Fin (k + 1))))
    refine ⟨V, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp only [D, Finset.mem_univ]
    · rw [hD]
      norm_num
      nlinarith [Parameters.η_le_δ_div_six k δ,
        Parameters.γ_le_η_sq_div_two k δ, Parameters.η_pos hk hδ₀,
        sq_nonneg (1 - Parameters.η k δ)]
    · rw [hD]
      norm_num
      change δ + Parameters.γ k δ ≤ (Subspace.relativeDensity V A : ℝ)
      linarith [Parameters.γ_le_η_sq_div_two k δ]
  · have hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2 := by
      intro V
      exact lt_of_not_ge fun hV ↦ hlarge ⟨V, hV⟩
    obtain ⟨V, C, hC, hweighted, houtside⟩ :=
      exists_large_insensitive_intersection hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hn A hA
        hfree hsmall
    obtain ⟨i, hidense, hicorrelation⟩ :=
      exists_dense_firstFailurePiece hk hδ₀ hδ₁ (pullback V A) C hweighted
        houtside
    obtain ⟨hD, hintersection, _, _⟩ := firstFailureFamily_facts C hC i
    refine ⟨V, firstFailureFamily C i, hD, ?_, ?_⟩
    · rw [hintersection]
      exact hidense
    · rw [hintersection]
      exact hicorrelation

end DensityHalesJewett
