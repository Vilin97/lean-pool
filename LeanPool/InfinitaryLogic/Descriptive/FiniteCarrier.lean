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
theorem perm_smul_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (c : StructureSpaceOn L (Fin n)) (R : Σ l, L.Relations l) (v : Fin R.1 → Fin n) :
    (σ • c) ⟨R, v⟩ = c ⟨R, σ.symm ∘ v⟩ := rfl

instance permMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (StructureSpaceOn L (Fin n)) where
  one_smul c := by ext ⟨R, v⟩; show c ⟨R, ⇑(1 : Equiv.Perm (Fin n)).symm ∘ v⟩ = c ⟨R, v⟩; congr 1
  mul_smul σ τ c := by
    ext ⟨R, v⟩
    show c ⟨R, ⇑(σ * τ).symm ∘ v⟩ = c ⟨R, ⇑τ.symm ∘ ⇑σ.symm ∘ v⟩
    congr 1

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
def structureIsoSetoidOn (L : Language.{u, v}) [L.IsRelational] (n : ℕ) :
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

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Membership in the pulled-back relation is membership in the ambient one. -/
theorem isoSetoidOn_r_iff {φ : L.Sentenceω} {n : ℕ} {c₁ c₂ : ↥(ModelsOfOn (α := Fin n) φ)} :
    (isoSetoidOn φ n).r c₁ c₂ ↔ (structureIsoSetoidOn L n).r c₁.1 c₂.1 := Iff.rfl

/-- `φ` has a perfect set of pairwise non-isomorphic models with carrier `Fin n`.

The finite tier is not decoration: an infinite language can have continuum-many `Fin n` models
while having no `ℕ`-models at all, so a counting dichotomy that only spoke about `ℕ`-models would
miss that case entirely. -/
def Sentenceω.HasPerfectSetOfPairwiseNonisomorphicFinModels (φ : L.Sentenceω) (n : ℕ) : Prop :=
  HasPerfectAntichainOn (structureIsoSetoidOn L n) (ModelsOfOn (α := Fin n) φ)

/-- The ambient half of the finite-tier route: a Cantor antichain on the model class in the
ambient topology gives a perfect set of pairwise non-isomorphic `Fin n`-models.

`StructureSpaceOn L (Fin n)` is metrizable but carries no chosen metric, so the `T2Space` instance
that `HasCantorAntichainOn.hasPerfectAntichainOn` needs is produced here rather than assumed; the
topology is unchanged, so the hypothesis still applies. -/
theorem Sentenceω.hasPerfectSetFin_of_ambient_cantorAntichain {φ : L.Sentenceω} {n : ℕ}
    (h : HasCantorAntichainOn (structureIsoSetoidOn L n) (ModelsOfOn (α := Fin n) φ)) :
    φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpaceOn L (Fin n))
  exact h.hasPerfectAntichainOn

/-- **The bridge to the quotient**: a perfect set of pairwise non-isomorphic `Fin n`-models gives
continuum-many isomorphism classes at that tier.

Mirrors the `ℕ`-tier bridge and for the same reason: the antichain lives in the ambient space
while the quotient is over the subtype, so the transversal is transported through the inclusion —
which is what `isoSetoidOn` being a `comap` licenses. -/
theorem Sentenceω.HasPerfectSetOfPairwiseNonisomorphicFinModels.continuum_le
    {φ : L.Sentenceω} {n : ℕ} (h : φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n) :
    Cardinal.continuum ≤ #(Quotient (isoSetoidOn φ n)) := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  have hinj : Function.Injective
      (fun x : P => Quotient.mk (isoSetoidOn φ n) ⟨x.1, hsub x.2⟩) := by
    intro x y hxy
    have hr : (isoSetoidOn φ n).r ⟨x.1, hsub x.2⟩ ⟨y.1, hsub y.2⟩ := Quotient.exact hxy
    exact Subtype.ext (hanti x.1 x.2 y.1 y.2 (isoSetoidOn_r_iff.mp hr))
  -- as at the `ℕ` tier: a metric is needed for the cardinality of a perfect set, and the upgrade
  -- supplies one without changing the topology, so `hperf` survives
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpaceOn L (Fin n))
  calc Cardinal.continuum = #P := (hperf.mk_eq_continuum hne).symm
    _ ≤ #(Quotient (isoSetoidOn φ n)) := Cardinal.mk_le_of_injective hinj

/-! ### Isomorphism relation is Borel on finite carriers -/

omit [L.IsRelational] [Countable ((l : ℕ) × L.Relations l)] in
/-- Each orbit map `c ↦ σ • c` is continuous on `StructureSpaceOn L (Fin n)`. -/
theorem continuous_perm_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun c : StructureSpaceOn L (Fin n) => σ • c) := by
  apply continuous_pi
  intro ⟨R, v⟩
  exact continuous_apply (⟨R, σ.symm ∘ v⟩ : RelQueryOn L (Fin n))

/-- The isomorphism relation on `Fin n`-models is measurable.
It equals `⋃ σ : Perm(Fin n), graph(σ • ·)`, a finite union of closed sets. -/
theorem isoSetoidOn_measurableSet (φ : L.Sentenceω) (n : ℕ) :
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
    (((continuous_perm_smul n σ).comp (continuous_subtype_val.comp continuous_fst)).measurable.prodMk
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

/-- Counting dichotomy for all countable models with bounded Scott height.
The type `AllCodedIsoClasses φ` faithfully represents all isomorphism classes of
countable models of φ (via the bridge theorems `codeModel`, `iso_of_codeModel_eq`,
`codeModel_surjective`).
This theorem states the dichotomy on its cardinality. -/
theorem allCodedIsoClasses_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    (#(AllCodedIsoClasses φ) ≤ ℵ₀) ∨
    (#(AllCodedIsoClasses φ) = Cardinal.continuum) := by
  -- Per-tier dichotomies
  have hN := counting_coded_models_dichotomy silver hα hbound
  have hFin := fun n => counting_fin_models_dichotomy silver φ n
  -- Sigma embedding: Quotient (isoSetoidOn φ n₀) ↪ Σ n, Quotient (isoSetoidOn φ n)
  have hEmbed : ∀ n₀, #(Quotient (isoSetoidOn φ n₀)) ≤
      #(Σ n, Quotient (isoSetoidOn φ n)) := fun n₀ =>
    ⟨⟨fun x => ⟨n₀, x⟩, fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩⟩
  -- Case split on whether any tier has continuum-many classes
  by_cases hc : (#(Quotient (isoSetoid φ)) = Cardinal.continuum) ∨
    ∃ n, #(Quotient (isoSetoidOn φ n)) = Cardinal.continuum
  · -- Some tier = continuum → total = continuum
    right
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.continuum :=
      hN.elim (·.trans aleph0_le_continuum) le_of_eq
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum :=
      fun n => (hFin n).elim (·.trans aleph0_le_continuum) le_of_eq
    show #(AllCodedIsoClasses φ) = Cardinal.continuum
    apply le_antisymm
    · -- Upper bound
      show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum
      rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      apply add_le_of_le aleph0_le_continuum hA_le
      calc #(Σ n, Quotient (isoSetoidOn φ n))
        ≤ ℵ₀ * Cardinal.continuum := mk_sigma_isoSetoidOn_le φ _ hFin_le
        _ = Cardinal.continuum := by
          rw [Cardinal.aleph0_mul_eq aleph0_le_continuum]
    · -- Lower bound
      rcases hc with hcA | ⟨n₀, hn₀⟩
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoid φ)) := hcA.symm
          _ ≤ _ := le_self_add
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoidOn φ n₀)) := hn₀.symm
          _ ≤ #(Σ n, Quotient (isoSetoidOn φ n)) := hEmbed n₀
          _ ≤ #(Quotient (isoSetoid φ)) + #(Σ n, Quotient (isoSetoidOn φ n)) :=
            self_le_add_left _ _
  · -- No tier = continuum → all ≤ ℵ₀ → total ≤ ℵ₀
    left
    push Not at hc
    obtain ⟨hcA, hcFin⟩ := hc
    have hA_le : #(Quotient (isoSetoid φ)) ≤ ℵ₀ := hN.resolve_right hcA
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ :=
      fun n => (hFin n).resolve_right (hcFin n)
    show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ ℵ₀
    rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    apply add_le_of_le le_rfl hA_le
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      ≤ ℵ₀ * ℵ₀ := mk_sigma_isoSetoidOn_le φ _ hFin_le
      _ = ℵ₀ := Cardinal.aleph0_mul_aleph0

/-! ### Bridge theorems: coded classes represent all countable models -/

section Bridge

attribute [local instance] Classical.dec

variable {φ : L.Sentenceω}

-- The generic transport API `encodeViaEquiv` and its lemmas (`toStructure_encodeViaEquiv_eq`,
-- `encodeViaEquiv_models`, `encodeViaEquiv_iso`) were promoted to
-- `Descriptive/CodeTransport.lean` (`StructureSpaceOn` namespace); this section consumes them.
open StructureSpaceOn (encodeViaEquiv encodeViaEquiv_models encodeViaEquiv_iso
  toStructure_encodeViaEquiv_eq)

/-- Map a countable model of φ to its coded iso class.
Uses `finite_or_infinite` to dispatch to the ℕ or `Fin n` tier. -/
noncomputable def codeModel
    {M : Type} [L.Structure M] [Countable M]
    (hφ : Sentenceω.Realize φ M) : AllCodedIsoClasses φ :=
  if hfin : Finite M then
    haveI := Fintype.ofFinite M
    let n := Fintype.card M
    let e : M ≃ Fin n := Fintype.equivFin M
    Sum.inr ⟨n, Quotient.mk (isoSetoidOn φ n)
      ⟨encodeViaEquiv e, encodeViaEquiv_models e hφ⟩⟩
  else
    haveI : Infinite M := not_finite_iff_infinite.mp hfin
    let e : M ≃ ℕ := (nonempty_equiv_of_countable (α := M) (β := ℕ)).some
    Sum.inl (Quotient.mk (isoSetoid φ)
      ⟨encodeViaEquiv e, encodeViaEquiv_models e hφ⟩)

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Branch equation for `codeModel` on a finite carrier.

Stated as a lemma because the unfolded body of `codeModel` is type-correct only at default
transparency (its membership proof needs `ModelsOfOn` unfolded), so `rw`/`simp` cannot select
the branch in place; term-mode `dite_eq_left` can. -/
private theorem codeModel_of_finite {M : Type} [L.Structure M] [Countable M]
    (hφ : Sentenceω.Realize φ M) (hfin : Finite M) :
    codeModel hφ = Sum.inr ⟨@Fintype.card M (Fintype.ofFinite M),
      Quotient.mk (isoSetoidOn φ _)
        ⟨encodeViaEquiv (@Fintype.equivFin M (Fintype.ofFinite M)),
          encodeViaEquiv_models _ hφ⟩⟩ :=
  dite_eq_left hfin

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Branch equation for `codeModel` on an infinite carrier. See `codeModel_of_finite` for why
this is a term-mode lemma rather than a `rw` on the unfolded definition. -/
private theorem codeModel_of_infinite {M : Type} [L.Structure M] [Countable M] [Infinite M]
    (hφ : Sentenceω.Realize φ M) (hfin : ¬Finite M) :
    codeModel hφ = Sum.inl (Quotient.mk (isoSetoid φ)
      ⟨encodeViaEquiv (nonempty_equiv_of_countable (α := M) (β := ℕ)).some,
        encodeViaEquiv_models _ hφ⟩) :=
  dite_eq_right hfin

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Compose L-equivs through encoding bijections to build iso between coded structures. -/
private theorem compose_encoded_iso
    {M N : Type} [L.Structure M] [L.Structure N] {α : Type}
    (e : @Language.Equiv L M N ‹_› ‹_›)
    (eM : M ≃ α) (eN : N ≃ α) :
    Nonempty (@Language.Equiv L α α
      (StructureSpaceOn.toStructure (encodeViaEquiv eM))
      (StructureSpaceOn.toStructure (encodeViaEquiv eN))) := by
  rw [toStructure_encodeViaEquiv_eq, toStructure_encodeViaEquiv_eq]
  -- Goal: Nonempty (@Language.Equiv L α α (inducedStructure eM) (inducedStructure eN))
  -- Build directly using Equiv.mk
  refine ⟨@Language.Equiv.mk L α α (Equiv.inducedStructure eM) (Equiv.inducedStructure eN)
    (eM.symm.trans (e.toEquiv.trans eN))
    (fun f _ => isEmptyElim ((‹L.IsRelational› _).false f))
    (fun {n} R v => ?_)⟩
  simp only [Equiv.inducedStructure_RelMap, Function.comp_def, Equiv.trans_apply, Equiv.toFun_as_coe]
  simp_rw [eN.symm_apply_apply]
  constructor
  · intro h; exact (e.map_rel' R (⇑eM.symm ∘ v)).mp (by convert h using 2; rfl)
  · intro h; convert (e.map_rel' R (⇑eM.symm ∘ v)).mpr h using 2; rfl

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- L-isomorphic countable models map to the same coded class. -/
theorem codeModel_eq_of_iso
    {M N : Type} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hφM : Sentenceω.Realize φ M) (hφN : Sentenceω.Realize φ N)
    (e : @Language.Equiv L M N ‹_› ‹_›) :
    codeModel hφM = codeModel hφN := by
  have hequiv := e.toEquiv
  by_cases hfinM : Finite M
  · -- M is finite → N is finite
    have hfinN : Finite N := Finite.of_equiv M hequiv
    have hcard : @Fintype.card M (Fintype.ofFinite M) = @Fintype.card N (Fintype.ofFinite N) :=
      @Fintype.card_congr M N (Fintype.ofFinite M) (Fintype.ofFinite N) hequiv
    rw [codeModel_of_finite hφM hfinM, codeModel_of_finite hφN hfinN]
    have h1 : ∀ (n : ℕ) (f : M ≃ Fin n) (g : N ≃ Fin n)
        (hf : @Sentenceω.Realize L φ _ (StructureSpaceOn.toStructure (encodeViaEquiv f)))
        (hg : @Sentenceω.Realize L φ _ (StructureSpaceOn.toStructure (encodeViaEquiv g))),
        Quotient.mk (isoSetoidOn φ n) ⟨encodeViaEquiv f, hf⟩ =
        Quotient.mk (isoSetoidOn φ n) ⟨encodeViaEquiv g, hg⟩ := by
      intro n f g hf hg
      apply Quotient.sound; show Nonempty _
      exact compose_encoded_iso e _ _
    suffices ∀ m (eqm : m = @Fintype.card M (Fintype.ofFinite M))
        (f : M ≃ Fin m) (g : N ≃ Fin (@Fintype.card N (Fintype.ofFinite N))),
        (Sum.inr ⟨m, Quotient.mk (isoSetoidOn φ m) ⟨encodeViaEquiv f,
            encodeViaEquiv_models f hφM⟩⟩ : AllCodedIsoClasses φ) =
        Sum.inr ⟨@Fintype.card N (Fintype.ofFinite N),
            Quotient.mk (isoSetoidOn φ _) ⟨encodeViaEquiv g,
            encodeViaEquiv_models g hφN⟩⟩ from
      this _ rfl _ _
    intro m eqm f g; subst eqm
    revert f; rw [hcard]; intro f
    congr 2
    exact h1 _ _ _ _ _
  · -- M is infinite → N is infinite
    have : Infinite M := not_finite_iff_infinite.mp hfinM
    have hfinN : ¬Finite N := fun h => hfinM (Finite.of_equiv N hequiv.symm)
    have : Infinite N := not_finite_iff_infinite.mp hfinN
    have hM_eq : codeModel hφM = Sum.inl
        ⟦⟨encodeViaEquiv (nonempty_equiv_of_countable (α := M) (β := ℕ)).some,
          encodeViaEquiv_models _ hφM⟩⟧ :=
      codeModel_of_infinite hφM hfinM
    have hN_eq : codeModel hφN = Sum.inl
        ⟦⟨encodeViaEquiv (nonempty_equiv_of_countable (α := N) (β := ℕ)).some,
          encodeViaEquiv_models _ hφN⟩⟧ :=
      codeModel_of_infinite hφN hfinN
    rw [hM_eq, hN_eq]
    congr 1
    apply Quotient.sound
    show Nonempty _
    exact compose_encoded_iso e _ _

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Models mapping to the same coded class are L-isomorphic.
The proof composes: `M ≃[L] carrier` (from `encodeViaEquiv_iso`), the carrier-carrier
L-isomorphism (extracted from the quotient equality in `h`), and `carrier ≃[L] N`
(from `encodeViaEquiv_iso`). -/
theorem iso_of_codeModel_eq
    {M N : Type} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hφM : Sentenceω.Realize φ M) (hφN : Sentenceω.Realize φ N)
    (h : codeModel hφM = codeModel hφN) :
    Nonempty (@Language.Equiv L M N ‹_› ‹_›) := by
  -- Compose M ≃[L] carrier ≃[L] carrier ≃[L] N via encodeViaEquiv_iso + quotient extraction.
  have compose {α : Type} {instα₁ instα₂ : L.Structure α}
      (iM : @Language.Equiv L M α ‹L.Structure M› instα₁)
      (q : @Language.Equiv L α α instα₁ instα₂)
      (iN : @Language.Equiv L N α ‹L.Structure N› instα₂) :
      Nonempty (@Language.Equiv L M N ‹_› ‹_›) :=
    -- inner : M ≃[L] α (instα₂)
    let inner := @Language.Equiv.comp L M α ‹L.Structure M› instα₁ α instα₂ q iM
    -- outer : M ≃[L] N
    ⟨@Language.Equiv.comp L M α ‹L.Structure M› instα₂ N ‹L.Structure N›
      (@Language.Equiv.symm L N α ‹L.Structure N› instα₂ iN) inner⟩
  by_cases hfinM : Finite M
  · -- Finite M → finite N: same compose pattern, Sigma-dependent extraction.
    have hfinN : Finite N := by
      by_contra hfN
      have : Infinite N := not_finite_iff_infinite.mp hfN
      rw [codeModel_of_finite hφM hfinM, codeModel_of_infinite hφN hfN] at h
      exact absurd h (by simp)
    -- Use the same pattern as codeModel_eq_of_iso finite branch:
    -- generalize over the cardinality and subst to unify Fin types.
    rw [codeModel_of_finite hφM hfinM, codeModel_of_finite hφN hfinN] at h
    have hSigma := Sum.inr.inj h
    have hcard : @Fintype.card M (Fintype.ofFinite M) =
        @Fintype.card N (Fintype.ofFinite N) := congrArg Sigma.fst hSigma
    suffices ∀ (m : ℕ) (eqm : m = @Fintype.card M (Fintype.ofFinite M))
        (f : M ≃ Fin m) (g : N ≃ Fin (@Fintype.card N (Fintype.ofFinite N)))
        (hq : (⟨m, Quotient.mk (isoSetoidOn φ m)
          ⟨encodeViaEquiv f, encodeViaEquiv_models f hφM⟩⟩ : Σ n, Quotient (isoSetoidOn φ n)) =
          ⟨@Fintype.card N (Fintype.ofFinite N), Quotient.mk (isoSetoidOn φ _)
          ⟨encodeViaEquiv g, encodeViaEquiv_models g hφN⟩⟩),
        Nonempty (@Language.Equiv L M N ‹_› ‹_›) by
      exact this _ rfl _ _ hSigma
    intro m eqm f g hq; subst eqm
    revert f hq; rw [hcard]; intro f hq
    have hq' : Quotient.mk (isoSetoidOn φ (@Fintype.card N (Fintype.ofFinite N)))
        ⟨encodeViaEquiv f, encodeViaEquiv_models f hφM⟩ =
        Quotient.mk (isoSetoidOn φ (@Fintype.card N (Fintype.ofFinite N)))
        ⟨encodeViaEquiv g, encodeViaEquiv_models g hφN⟩ :=
      eq_of_heq (Sigma.mk.inj hq).2
    obtain ⟨qIso⟩ := Quotient.exact hq'
    obtain ⟨iM⟩ := encodeViaEquiv_iso (L := L) (M := M) f
    obtain ⟨iN⟩ := encodeViaEquiv_iso (L := L) (M := N) g
    exact compose iM qIso iN
  · -- Infinite M → infinite N
    have : Infinite M := not_finite_iff_infinite.mp hfinM
    have hfinN : ¬Finite N := by
      intro hfN
      rw [codeModel_of_infinite hφM hfinM, codeModel_of_finite hφN hfN] at h
      exact absurd h (by simp)
    have : Infinite N := not_finite_iff_infinite.mp hfinN
    set eM : M ≃ ℕ := (nonempty_equiv_of_countable (α := M) (β := ℕ)).some
    set eN : N ≃ ℕ := (nonempty_equiv_of_countable (α := N) (β := ℕ)).some
    rw [codeModel_of_infinite hφM hfinM, codeModel_of_infinite hφN hfinN] at h
    obtain ⟨qIso⟩ := Quotient.exact (Sum.inl.inj h)
    obtain ⟨iM⟩ := encodeViaEquiv_iso (L := L) (M := M) eM
    obtain ⟨iN⟩ := encodeViaEquiv_iso (L := L) (M := N) eN
    exact compose iM qIso iN

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Every coded class is realized by some countable model. -/
theorem codeModel_surjective :
    ∀ q : AllCodedIsoClasses φ,
    ∃ (M : Type) (_ : L.Structure M) (_ : Countable M)
      (hφ : Sentenceω.Realize φ M), codeModel hφ = q := by
  -- Helper: given a code c on carrier α, decode it and show codeModel maps back
  -- to the same quotient class (up to the encoding isomorphism).
  intro q
  rcases q with ⟨qN⟩ | ⟨n, qFin⟩
  · -- ℕ branch: decode representative, ℕ with its toStructure is the model.
    refine Quotient.inductionOn qN fun ⟨c, hc⟩ => ?_
    -- Establish c.toStructure as the L.Structure instance on ℕ
    let instN : L.Structure ℕ := c.toStructure
    refine ⟨ℕ, instN, inferInstance, hc, ?_⟩
    -- Goal: codeModel hc = Sum.inl ⟦⟨c, hc⟩⟧
    -- codeModel hc takes dif_neg (Infinite ℕ) branch:
    --   Sum.inl ⟦⟨encodeViaEquiv e, _⟩⟧  where  e := (nonempty_equiv_of_countable).some
    -- We need: ⟦⟨encodeViaEquiv e, _⟩⟧ = ⟦⟨c, hc⟩⟧
    -- Strategy: show codeModel evaluates correctly, then use Quotient.sound
    have hInfN : ¬Finite ℕ := not_finite_iff_infinite.mpr inferInstance
    -- Prove the quotient iso in a standalone have (before unfold)
    set e := (nonempty_equiv_of_countable (α := ℕ) (β := ℕ)).some
    have hiso : @Quotient.mk _ (isoSetoid φ)
        ⟨encodeViaEquiv e, encodeViaEquiv_models e hc⟩ =
        @Quotient.mk _ (isoSetoid φ) ⟨c, hc⟩ := by
      apply Quotient.sound
      -- Need: Nonempty ((encodeViaEquiv e).toStructure ≃[L] c.toStructure)
      -- encodeViaEquiv_iso gives: Nonempty (ℕ_{instN} ≃[L] ℕ_{(encodeViaEquiv e).toStructure})
      -- .symm gives: Nonempty (ℕ_{(encodeViaEquiv e).toStructure} ≃[L] ℕ_{instN})
      -- instN = c.toStructure, so this is what we need
      obtain ⟨iso⟩ := encodeViaEquiv_iso (L := L) (M := ℕ) e
      exact ⟨@Language.Equiv.symm L ℕ ℕ instN
        (StructureSpaceOn.toStructure (encodeViaEquiv e)) iso⟩
    -- Now unfold codeModel and match
    rw [codeModel_of_infinite hc hInfN]
    exact congrArg Sum.inl hiso
  · -- Fin n branch: decode representative, Fin n with its toStructure is the model.
    refine Quotient.inductionOn qFin fun ⟨c, hc⟩ => ?_
    let instFin : L.Structure (Fin n) := c.toStructure
    refine ⟨Fin n, instFin, inferInstance, hc, ?_⟩
    -- Goal: codeModel hc = Sum.inr ⟨n, ⟦⟨c, hc⟩⟧⟩
    -- Fin n is finite, so codeModel takes the dif_pos branch
    -- After unfold: Sum.inr ⟨Fintype.card (Fin n), ⟦⟨encodeViaEquiv (equivFin (Fin n)), _⟩⟧⟩
    -- Need: card (Fin n) = n and quotient equality
    have : Finite (Fin n) := inferInstance
    rw [codeModel_of_finite hc (inferInstance : Finite (Fin n))]
    -- The unfolded codeModel uses Fintype.ofFinite (Fin n) internally.
    -- We need to match Fintype.card with n, handling the diamond.
    -- Use suffices to abstract over the cardinality and subst.
    set ftype := Fintype.ofFinite (Fin n)
    have hcard : @Fintype.card (Fin n) ftype = n :=
      (Subsingleton.elim ftype (Fin.fintype n)) ▸ Fintype.card_fin n
    -- Handle the Sigma dependency: need to transport from card(Fin n) to n
    suffices ∀ (m : ℕ) (eqm : m = @Fintype.card (Fin n) ftype)
        (f : Fin n ≃ Fin m),
        (Sum.inr ⟨m, @Quotient.mk _ (isoSetoidOn φ m)
          ⟨encodeViaEquiv f, encodeViaEquiv_models f hc⟩⟩ : AllCodedIsoClasses φ) =
        Sum.inr ⟨n, @Quotient.mk _ (isoSetoidOn φ n) ⟨c, hc⟩⟩ by
      exact this _ rfl _
    intro m eqm f; subst eqm
    revert f; rw [hcard]; intro f
    -- After revert/rw/intro: f : Fin n ≃ Fin n
    -- Need: Sum.inr ⟨n, ⟦⟨encodeViaEquiv f, _⟩⟧⟩ = Sum.inr ⟨n, ⟦⟨c, hc⟩⟧⟩
    -- Build the quotient iso
    have hqiso : @Quotient.mk _ (isoSetoidOn φ n)
        ⟨encodeViaEquiv f, encodeViaEquiv_models f hc⟩ =
        @Quotient.mk _ (isoSetoidOn φ n) ⟨c, hc⟩ := by
      apply Quotient.sound
      show Nonempty _
      obtain ⟨iso⟩ := encodeViaEquiv_iso (L := L) (M := Fin n) f
      exact ⟨@Language.Equiv.symm L (Fin n) (Fin n) instFin
        (StructureSpaceOn.toStructure (encodeViaEquiv f)) iso⟩
    exact congrArg (fun q => Sum.inr (Sigma.mk n q) : _ → AllCodedIsoClasses φ) hqiso

end Bridge

end Language

end FirstOrder
