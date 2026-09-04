/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorelOn
import LeanPool.InfinitaryLogic.Descriptive.CountingDichotomy
import LeanPool.InfinitaryLogic.Descriptive.CodeTransport
import Mathlib.GroupTheory.Perm.Basic
/-!
# Finite-Carrier Counting via Permutation Orbits

This file proves that for structures on `Fin n`, isomorphism is the orbit
equivalence relation of `Equiv.Perm (Fin n)`, which is Borel (finite union of
graphs of continuous maps). Combined with the existing ℕ-tier result, this
gives a counting dichotomy for all countable models.

## Main Definitions

- `isoSetoidOn`: Isomorphism setoid on `ModelsOfOn (α := Fin n) φ`.
- `AllCodedIsoClasses`: Disjoint union of iso classes across all carrier tiers.

## Main Results

- `iso_iff_orbit`: Isomorphism of `Fin n`-structures = orbit of `Sym(Fin n)`.
- `isoSetoidOn_measurableSet`: The isomorphism relation on `Fin n`-models is Borel.
- `counting_fin_models_dichotomy`: Per-tier counting dichotomy.
- `allCodedIsoClasses_dichotomy`: Combined counting dichotomy for all countable models.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### Permutation action on finite-carrier structure space -/

/-- `Equiv.Perm (Fin n)` acts on `StructureSpaceOn L (Fin n)` by relabeling:
`(σ • c) ⟨R, v⟩ = c ⟨R, σ.symm ∘ v⟩`. -/
instance permSmul (n : ℕ) : SMul (Equiv.Perm (Fin n)) (StructureSpaceOn L (Fin n)) where
  smul σ c := fun ⟨R, v⟩ => c ⟨R, σ.symm ∘ v⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
@[simp]
private theorem perm_smul_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (c : StructureSpaceOn L (Fin n)) (R : Σ l, L.Relations l) (v : Fin R.1 → Fin n) :
    (σ • c) ⟨R, v⟩ = c ⟨R, σ.symm ∘ v⟩ := rfl

/-! ### Isomorphism = orbit equivalence -/

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Two `Fin n`-structures are L-isomorphic iff they lie in the same `Sym(Fin n)` orbit. -/
theorem iso_iff_orbit (n : ℕ) (c₁ c₂ : StructureSpaceOn L (Fin n)) :
    Nonempty (@Language.Equiv L (Fin n) (Fin n) c₁.toStructure c₂.toStructure) ↔
    ∃ σ : Equiv.Perm (Fin n), σ • c₁ = c₂ := by
  constructor
  · rintro ⟨e⟩
    set σ := @Language.Equiv.toEquiv L (Fin n) (Fin n) c₁.toStructure c₂.toStructure e
    refine ⟨σ, ?_⟩
    ext ⟨⟨l, R⟩, v⟩
    simp only [perm_smul_apply]
    have hrel := @Language.Equiv.map_rel' L (Fin n) (Fin n) c₁.toStructure c₂.toStructure
      e l R (σ.symm ∘ v)
    rw [StructureSpaceOn.relMap_toStructure c₂,
        StructureSpaceOn.relMap_toStructure c₁] at hrel
    simp only [Equiv.toFun_as_coe] at hrel
    have hsimp : (⇑σ) ∘ ⇑σ.symm ∘ v = v := by
      funext i; simp [Function.comp]
    rw [hsimp] at hrel
    cases h₁ : c₁ ⟨⟨l, R⟩, ⇑σ.symm ∘ v⟩ <;>
    cases h₂ : c₂ ⟨⟨l, R⟩, v⟩ <;> simp_all
  · rintro ⟨σ, hσ⟩
    refine ⟨@Language.Equiv.mk L (Fin n) (Fin n) c₁.toStructure c₂.toStructure σ
      (fun f => isEmptyElim f) (fun {l} R v => ?_)⟩
    rw [StructureSpaceOn.relMap_toStructure c₂,
        StructureSpaceOn.relMap_toStructure c₁]
    have := congr_fun hσ ⟨⟨l, R⟩, σ ∘ v⟩
    simp only [perm_smul_apply] at this
    have hsimp : σ.symm ∘ (σ : Fin n → Fin n) ∘ v = v := by
      funext i; simp [Function.comp]
    rw [show (⇑σ.symm ∘ ⇑σ ∘ v) = v from hsimp] at this
    simp only [Equiv.toFun_as_coe] at *
    exact ⟨fun h => by rwa [this], fun h => by rwa [← this]⟩

/-! ### Isomorphism setoid on finite-carrier models -/

/-- **The ambient isomorphism relation at carrier `Fin n`**: two codes are related iff the
structures they decode on `Fin n` are `L`-isomorphic.  Stated on all of
`StructureSpaceOn L (Fin n)`, with no reference to any sentence.

This mirrors `structureIsoSetoid` at the `ℕ` tier, and for the same reason: perfectness of a set
of codes must be a property of the ambient space, not of whichever refinement was chosen to make
one model class Polish. -/
private def structureIsoSetoidOn (L : Language.{u, v}) [L.IsRelational] (n : ℕ) :
    Setoid (StructureSpaceOn L (Fin n)) where
  r c₁ c₂ := Nonempty (@Language.Equiv L (Fin n) (Fin n)
    (StructureSpaceOn.toStructure c₁) (StructureSpaceOn.toStructure c₂))
  iseqv :=
    { refl := fun c => ⟨@Language.Equiv.refl L (Fin n) (StructureSpaceOn.toStructure c)⟩
      symm := fun {c₁ c₂} ⟨e⟩ =>
        ⟨@Language.Equiv.symm L (Fin n) (Fin n) c₁.toStructure c₂.toStructure e⟩
      trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
        ⟨@Language.Equiv.comp L (Fin n) (Fin n) c₁.toStructure c₂.toStructure
          (Fin n) c₃.toStructure e₂ e₁⟩ }

/-- The isomorphism setoid on models of φ with carrier `Fin n`: the ambient relation restricted
along the subtype inclusion.  That is its definition, not a theorem about it. -/
def isoSetoidOn (φ : L.Sentenceω) (n : ℕ) :
    Setoid ↥(ModelsOfOn (α := Fin n) φ) :=
  (structureIsoSetoidOn L n).comap Subtype.val

/-! ### Isomorphism relation is Borel on finite carriers -/

omit [L.IsRelational] [Countable ((l : ℕ) × L.Relations l)] in
/-- Each orbit map `c ↦ σ • c` is continuous on `StructureSpaceOn L (Fin n)`. -/
private theorem continuous_perm_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun c : StructureSpaceOn L (Fin n) => σ • c) := by
  apply continuous_pi
  intro ⟨R, v⟩
  exact continuous_apply (⟨R, σ.symm ∘ v⟩ : RelQueryOn L (Fin n))

/-- The isomorphism relation on `Fin n`-models is measurable.
It equals `⋃ σ : Perm(Fin n), graph(σ • ·)`, a finite union of closed sets. -/
private theorem isoSetoidOn_measurableSet (φ : L.Sentenceω) (n : ℕ) :
    MeasurableSet {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      (isoSetoidOn φ n).r p.1 p.2} := by
  -- The relation on the subtype is the preimage of the relation on the full space
  -- under the measurable subtype inclusion.
  -- Step 1: Express the relation as ⋃ σ, {p | σ • p.1.1 = p.2.1}
  have hset : {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      (isoSetoidOn φ n).r p.1 p.2} =
    ⋃ σ : Equiv.Perm (Fin n),
      {p | σ • p.1.1 = p.2.1} := by
    ext ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact iso_iff_orbit n c₁ c₂
  rw [hset]
  -- Step 2: Finite union of measurable sets is measurable
  apply MeasurableSet.iUnion
  intro σ
  -- Step 3: Each {p | σ • p.1.1 = p.2.1} is preimage of diagonal under
  --         (p ↦ (σ • p.1.1, p.2.1))
  have hgraph : {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      σ • p.1.1 = p.2.1} =
    (fun p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) =>
      (σ • p.1.1, p.2.1)) ⁻¹' {q : StructureSpaceOn L (Fin n) × StructureSpaceOn L (Fin n) |
        q.1 = q.2} := by
    ext p; simp [Set.mem_ofPred_eq]
  rw [hgraph]
  -- Step 4: The diagonal is closed, hence measurable
  exact isClosed_diagonal.measurableSet.preimage
    (((continuous_perm_smul n σ).comp
      (continuous_subtype_val.comp continuous_fst)).measurable.prodMk
        (continuous_subtype_val.comp continuous_snd).measurable)

/-! ### Per-tier counting dichotomy -/

/-- Per-tier counting dichotomy: for each n, the iso classes among `Fin n`-models
of φ are either ≤ ℵ₀ or = 2^ℵ₀. Does NOT need bounded Scott height. -/
theorem counting_fin_models_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    (φ : L.Sentenceω) (n : ℕ) :
    (#(Quotient (isoSetoidOn φ n)) ≤ ℵ₀) ∨
    (#(Quotient (isoSetoidOn φ n)) = Cardinal.continuum) := by
  have : StandardBorelSpace ↥(ModelsOfOn (α := Fin n) φ) :=
    (modelsOfOn_measurableSet φ).standardBorel
  exact silver (isoSetoidOn φ n) (isoSetoidOn_measurableSet φ n)

/-! ### Combined counting theorem -/

/-- The type of all coded isomorphism classes across all carrier tiers:
ℕ-models plus Fin n-models for each n. -/
def AllCodedIsoClasses (φ : L.Sentenceω) :=
  Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- **The finite tiers, summed**: their disjoint union has at most `ℵ₀ * bound` classes whenever
each single tier has at most `bound`.

There are countably many tiers, so this is the whole of the cardinal arithmetic the counting
theorems need on the finite side.  Stated once because three of them need it at two different
bounds (`ℵ₀` and `continuum`). -/
theorem mk_sigma_isoSetoidOn_le (φ : L.Sentenceω) (bound : Cardinal.{v})
    (hle : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ bound) :
    #(Σ n, Quotient (isoSetoidOn φ n)) ≤ ℵ₀ * bound :=
  calc #(Σ n, Quotient (isoSetoidOn φ n))
    = Cardinal.sum (fun n => #(Quotient (isoSetoidOn φ n))) := mk_sigma _
    _ ≤ Cardinal.lift.{v, 0} #ℕ * ⨆ i, Cardinal.lift.{0, v} (#(Quotient (isoSetoidOn φ i))) :=
      sum_le_lift_mk_mul_iSup_lift _
    _ = ℵ₀ * ⨆ i, #(Quotient (isoSetoidOn φ i)) := by
      rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
      congr 1; apply iSup_congr; intro i; exact Cardinal.lift_uzero _
    _ ≤ ℵ₀ * bound := by
      apply mul_le_mul_right
      exact ciSup_le hle

/-! ### Bridge theorems: coded classes represent all countable models -/

section Bridge

attribute [local instance] Classical.dec

variable {φ : L.Sentenceω}

-- The generic transport API `encodeViaEquiv` and its lemmas (`toStructure_encodeViaEquiv_eq`,
-- `encodeViaEquiv_models`, `encodeViaEquiv_iso`) were promoted to
-- `Descriptive/CodeTransport.lean` (`StructureSpaceOn` namespace); this section consumes them.
open StructureSpaceOn (encodeViaEquiv encodeViaEquiv_models encodeViaEquiv_iso
  toStructure_encodeViaEquiv_eq)

end Bridge

end Language

end FirstOrder
