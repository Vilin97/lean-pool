/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

/-!
# Existence of filtration-adapted bases

This file constructs a basis adapted to a finite descending filtration of a
finite-dimensional vector space.  The construction is elementary: starting
at a zero layer, extend a linearly independent set one layer at a time, and
label each newly added vector by the layer at which it appears.  A final
sorting by decreasing labels gives the ordered `Fin` basis used by the
Artinian trace argument.
-/

namespace Stafford38.Characteristic.ArtinianAdaptedBasisExistence

open Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter

noncomputable section

universe u

section LinearFiltration

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Intermediate set-valued form of an adapted basis, valid from `start`
onwards. -/
private structure PartialAdaptedSet
    (F : ℕ → Submodule K V) (start : ℕ) where
  carrier : Set V
  independent : LinearIndependent K ((↑) : carrier → V)
  span_start : Submodule.span K carrier = F start
  level : carrier → ℕ
  start_le_level : ∀ i, start ≤ level i
  span_level : ∀ t, start ≤ t →
    F t = Submodule.span K (((↑) : carrier → V) '' {i | t ≤ level i})

private noncomputable def partialAtBottom
    (F : ℕ → Submodule K V) (hanti : Antitone F)
    (N : ℕ) (hN : F N = ⊥) :
    PartialAdaptedSet F N := by
  refine
    { carrier := ∅
      independent := linearIndependent_empty K V
      span_start := by simp [hN]
      level := fun i => False.elim i.property
      start_le_level := fun i => False.elim i.property
      span_level := ?_ }
  intro t hNt
  have ht : F t = ⊥ := by
    apply le_bot_iff.mp
    rw [← hN]
    exact hanti hNt
  have hempty : {i : (∅ : Set V) | t ≤ False.elim i.property} = ∅ := by
    ext i
    exact False.elim i.property
  simp [ht, hempty]

private noncomputable def partialStep
    (F : ℕ → Submodule K V) (hanti : Antitone F)
    (t : ℕ) (old : PartialAdaptedSet F (t + 1)) :
    PartialAdaptedSet F t := by
  classical
  let oldIn : old.carrier ⊆ (F t : Set V) := fun x hx =>
    hanti (Nat.le_succ t) (by
      rw [← old.span_start]
      exact Submodule.subset_span hx)
  have hOld : LinearIndepOn K id old.carrier :=
    linearIndependent_subtype_iff.mp old.independent
  let next : Set V := hOld.extend oldIn
  have holdNext : old.carrier ⊆ next :=
    hOld.subset_extend oldIn
  have hnextF : next ⊆ (F t : Set V) :=
    hOld.extend_subset oldIn
  have hind : LinearIndependent K ((↑) : next → V) := by
    exact linearIndependent_subtype_iff.mpr
      (hOld.linearIndepOn_extend oldIn)
  let lev : next → ℕ := fun i =>
    if hi : (i : V) ∈ old.carrier then old.level ⟨i, hi⟩ else t
  have hlev : ∀ i, t ≤ lev i := by
    intro i
    dsimp [lev]
    split_ifs with hi
    · exact le_trans (Nat.le_succ t) (old.start_le_level ⟨i, hi⟩)
    · exact le_rfl
  refine
    { carrier := next
      independent := hind
      span_start := ?_
      level := lev
      start_le_level := hlev
      span_level := ?_ }
  · apply le_antisymm
    · exact Submodule.span_le.mpr hnextF
    · exact hOld.subset_span_extend oldIn
  · intro u htu
    rcases Nat.eq_or_lt_of_le htu with rfl | htu'
    · have hall : (((↑) : next → V) '' {i | t ≤ lev i}) = next := by
        ext x
        constructor
        · rintro ⟨i, -, rfl⟩
          exact i.property
        · intro hx
          exact ⟨⟨x, hx⟩, hlev ⟨x, hx⟩, rfl⟩
      rw [hall]
      symm
      apply le_antisymm
      · exact Submodule.span_le.mpr hnextF
      · exact hOld.subset_span_extend oldIn
    · rw [old.span_level u (Nat.succ_le_iff.mpr htu')]
      apply congrArg (Submodule.span K)
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        let j : next := ⟨(i : V), holdNext i.property⟩
        refine ⟨j, ?_, rfl⟩
        simpa [lev, j, i.property] using hi
      · rintro ⟨i, hi, rfl⟩
        have hiOld : (i : V) ∈ old.carrier := by
          by_contra hn
          have : lev i = t := dif_neg hn
          change u ≤ lev i at hi
          rw [this] at hi
          exact (Nat.not_le_of_lt htu') hi
        refine ⟨⟨(i : V), hiOld⟩, ?_, rfl⟩
        simpa [lev, hiOld] using hi

private noncomputable def partialAtZero
    (F : ℕ → Submodule K V) (hanti : Antitone F)
    (N : ℕ) (hN : F N = ⊥) :
    PartialAdaptedSet F 0 :=
  Nat.decreasingInduction
    (motive := fun t _ => PartialAdaptedSet F t)
    (fun t _ old => partialStep F hanti t old)
    (partialAtBottom F hanti N hN)
    (Nat.zero_le N)

/-- Every finite descending filtration of a finite-dimensional vector space
has a `Fin`-indexed basis ordered by decreasing filtration level. -/
theorem exists_filtrationAdaptedBasis
    [FiniteDimensional K V]
    {n : ℕ} (hdim : Module.finrank K V = n + 1)
    (F : ℕ → Submodule K V)
    (hanti : Antitone F)
    (hzero : F 0 = ⊤)
    (heventually : ∃ N, F N = ⊥) :
    ∃ (b : Module.Basis (Fin (n + 1)) K V) (level : Fin (n + 1) → ℕ),
      Antitone level ∧
      ∀ t, F t = Submodule.span K (b '' {i | t ≤ level i}) := by
  classical
  obtain ⟨N, hN⟩ := heventually
  let data := partialAtZero F hanti N hN
  have hspanTop : Submodule.span K data.carrier = ⊤ := data.span_start.trans hzero
  let raw : Module.Basis data.carrier K V :=
    Module.Basis.mk data.independent (by simpa using hspanTop.ge)
  let : Fintype data.carrier := FiniteDimensional.fintypeBasisIndex raw
  have hcard : Fintype.card data.carrier = n + 1 := by
    rw [← hdim, ← Module.finrank_eq_card_basis raw]
  let rank : data.carrier ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (hcard.trans (Fintype.card_fin (n + 1)).symm)
  let key : data.carrier → (OrderDual ℕ ×ₗ Fin (n + 1)) :=
    fun i => toLex ((data.level i : OrderDual ℕ), rank i)
  have hkey : Function.Injective key := by
    intro i j hij
    apply rank.injective
    exact congrArg (fun z => (ofLex z).2) hij
  let : LinearOrder data.carrier := LinearOrder.lift' key hkey
  let sorted : Fin (n + 1) ≃o data.carrier :=
    Fintype.orderIsoFinOfCardEq data.carrier hcard
  let b : Module.Basis (Fin (n + 1)) K V := raw.reindex sorted.toEquiv.symm
  let level : Fin (n + 1) → ℕ := fun i => data.level (sorted i)
  refine ⟨b, level, ?_, ?_⟩
  · intro i j hij
    have hs : sorted i ≤ sorted j := sorted.monotone hij
    have hs' : key (sorted i) ≤ key (sorted j) := hs
    rw [Prod.Lex.toLex_le_toLex] at hs'
    rcases hs' with hs | ⟨hs, -⟩
    · exact Nat.le_of_lt hs
    · exact le_of_eq (congrArg OrderDual.ofDual hs).symm
  · intro t
    rw [data.span_level t (Nat.zero_le t)]
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨sorted.symm i, ?_, ?_⟩
      · simpa [level] using hi
      · simp [b, raw]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨sorted i, ?_, ?_⟩
      · simpa [level] using hi
      · simp [b, raw]

end LinearFiltration

section ArtinianApplication

variable {K R V : Type u}
variable [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
variable [IsArtinianRing R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
variable [FiniteDimensional K V]

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- Maximal-ideal powers on a finite-dimensional module have the adapted
basis required by the Artinian trace adapter. -/
theorem exists_maximalIdealFiltrationAdaptedBasis
    {n : ℕ} (hdim : Module.finrank K V = n + 1) :
    ∃ (b : Module.Basis (Fin (n + 1)) K V) (level : Fin (n + 1) → ℕ),
      IsMaximalIdealFiltrationAdapted 𝔪 b level := by
  let F : ℕ → Submodule K V := fun t =>
    ((𝔪 ^ t • (⊤ : Submodule R V)).restrictScalars K)
  have hanti : Antitone F := by
    intro a b hab
    exact (Submodule.restrictScalarsEmbedding K R V).monotone
      (Submodule.smul_mono (Ideal.pow_le_pow_right hab) le_rfl)
  have hzero : F 0 = ⊤ := by
    ext v
    simp [F]
  obtain ⟨N, hN⟩ :=
    Stafford38.Characteristic.ArtinianCoefficientField.maximalIdeal_isNilpotent
      (R := R)
  have hbottom : F N = ⊥ := by
    ext v
    simp [F, hN]
  obtain ⟨b, level, hlevel, hspan⟩ :=
    exists_filtrationAdaptedBasis hdim F hanti hzero ⟨N, hbottom⟩
  exact ⟨b, level, ⟨hlevel, hspan⟩⟩


end ArtinianApplication

end

end Stafford38.Characteristic.ArtinianAdaptedBasisExistence
