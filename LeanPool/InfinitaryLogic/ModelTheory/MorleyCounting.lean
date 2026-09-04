/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.CountingCountable
import LeanPool.InfinitaryLogic.Descriptive.BFEquivBorel
/-!
# Morley's Counting Theorem via Scott-Height Stratification

This file proves the full Morley counting theorem: for any Lω₁ω sentence φ,
the number of isomorphism classes of countable models is either ≤ ℵ₁ or exactly
2^ℵ₀. The theorem is parametrized by the Silver–Burgess dichotomy
(`SilverBurgessDichotomy`), which the repository proves unconditionally
(`silverBurgessDichotomy` in `Conditional/GandyHarrington.lean`, via the
classical `G₀`-dichotomy route); supplying it makes the conclusion axiom-clean.

The proof stratifies by Scott height. For each α < ω₁, BFEquiv_α is a Borel
equivalence relation on ModelsOf φ, coarser than isomorphism. If any BFEquiv_α
has 2^ℵ₀ classes, iso has ≥ 2^ℵ₀ hence = 2^ℵ₀. If all have ≤ ℵ₀, then for
each α, the iso classes with height ≤ α inject into BFEquiv_α classes, giving
≤ ℵ₀ iso classes per stratum, hence ≤ ℵ₁ total over ω₁ strata.

## Main Result

- `morley_counting`: Morley counting theorem for all countable models, parametrized
  by `SilverBurgessDichotomy` (proved in this repository).
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### BFEquiv setoid on coded models -/

/-- The BFEquiv α equivalence relation on coded ℕ-models of φ (at the empty tuple). -/
private def bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Setoid ↥(ModelsOf φ) where
  r c₁ c₂ := @BFEquiv L ℕ c₁.1.toStructure ℕ c₂.1.toStructure α 0 Fin.elim0 Fin.elim0
  iseqv := by
    refine ⟨fun c => ?_, fun {c₁ c₂} h => ?_, fun {c₁ c₂ c₃} h₁ h₂ => ?_⟩
    · exact @BFEquiv.refl L ℕ c.1.toStructure 0 α Fin.elim0
    · exact @BFEquiv.symm L ℕ c₁.1.toStructure ℕ c₂.1.toStructure 0 α
        Fin.elim0 Fin.elim0 h
    · exact @BFEquiv.trans L ℕ c₁.1.toStructure ℕ c₂.1.toStructure
        ℕ c₃.1.toStructure (n := 0) (α := α)
        (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0) h₁ h₂

omit [Countable (Σ l, L.Relations l)] in
/-- Iso implies BFEquiv α: isoSetoid refines bfEquivSetoid. -/
private theorem isoSetoid_refines_bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})
    {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ → (bfEquivSetoid φ α).r c₁ c₂ := by
  intro ⟨e⟩
  unfold bfEquivSetoid
  simp only
  conv_rhs => rw [show (Fin.elim0 : Fin 0 → ℕ) = e ∘ Fin.elim0 from
    (comp_fin_elim0 e).symm]
  exact @equiv_implies_BFEquiv L ℕ ℕ c₁.1.toStructure c₂.1.toStructure e α 0 Fin.elim0

/-- The BFEquiv α relation on ModelsOf φ is measurable. -/
private theorem bfEquivSetoid_measurableSet (φ : L.Sentenceω) (α : Ordinal.{0})
    (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) |
      (bfEquivSetoid φ α).r p.1 p.2} := by
  -- The set is the preimage of BFEquivSet under the subtype inclusion
  have hset : {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (bfEquivSetoid φ α).r p.1 p.2} =
      (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) ⁻¹'
        (BFEquivSet (L := L) α 0 Fin.elim0 Fin.elim0) := by
    ext ⟨⟨c₁, _⟩, ⟨c₂, _⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, BFEquivSet]
    exact Iff.rfl
  rw [hset]
  exact ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))
    (bfEquivSet_measurableSet α hα 0 Fin.elim0 Fin.elim0)

/-- Per-level BFEquiv dichotomy. -/
private theorem bfEquiv_classes_dichotomy (silver : SilverBurgessDichotomy.{v})
    (φ : L.Sentenceω) (α : Ordinal.{0}) (hα : α < Ordinal.omega 1) :
    (#(Quotient (bfEquivSetoid φ α)) ≤ ℵ₀) ∨
    (#(Quotient (bfEquivSetoid φ α)) = Cardinal.continuum) :=
  silver (bfEquivSetoid φ α) (bfEquivSetoid_measurableSet φ α hα)

omit [Countable (Σ l, L.Relations l)] in
/-- The depth-`α` projection of isomorphism classes onto back-and-forth classes. -/
private def bfProj (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Quotient (isoSetoid φ) → Quotient (bfEquivSetoid φ α) :=
  Quotient.map id (fun _a _b h => isoSetoid_refines_bfEquivSetoid φ α h)



omit [Countable (Σ l, L.Relations l)] in
private theorem bfProj_surjective (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Function.Surjective (bfProj φ α) := fun q =>
  q.inductionOn fun c => ⟨Quotient.mk _ c, rfl⟩

omit [Countable (Σ l, L.Relations l)] in
/-- The depth-`α` projection of the isomorphism classes satisfying `P`: the range of `bfProj`
restricted to `P`. -/
private def bfProjRange (φ : L.Sentenceω) (P : Quotient (isoSetoid φ) → Prop) (α : Ordinal.{0}) :
    Set (Quotient (bfEquivSetoid φ α)) :=
  Set.range (fun q : {q : Quotient (isoSetoid φ) // P q} => bfProj φ α q.1)

omit [Countable (Σ l, L.Relations l)] in
private theorem mem_bfProjRange {φ : L.Sentenceω} {P : Quotient (isoSetoid φ) → Prop} {α : Ordinal.{0}}
    {x : Quotient (bfEquivSetoid φ α)} :
    x ∈ bfProjRange φ P α ↔ ∃ q : {q : Quotient (isoSetoid φ) // P q}, bfProj φ α q.1 = x :=
  Iff.rfl

omit [Countable (Σ l, L.Relations l)] in
/-- Refinement gives: #(BFEquiv α classes) ≤ #(iso classes). -/
private theorem bfEquiv_classes_le_iso_classes (φ : L.Sentenceω) (α : Ordinal.{0}) :
    #(Quotient (bfEquivSetoid φ α)) ≤ #(Quotient (isoSetoid φ)) :=
  Cardinal.mk_le_of_surjective (bfProj_surjective φ α)

/-! ### Height function on iso classes -/

/-- scottHeight lifted to the ℕ-model quotient. -/
private noncomputable def isoClassHeight {φ : L.Sentenceω}
    (q : Quotient (isoSetoid φ)) : Ordinal.{0} :=
  Quotient.lift
    (fun (c : ↥(ModelsOf φ)) =>
      letI : L.Structure ℕ := StructureSpace.toStructure c.1
      scottHeight (L := L) ℕ)
    (fun c₁ c₂ h => by
      obtain ⟨e⟩ := h
      exact @scottHeight_eq_of_equiv L _ _ ℕ (StructureSpace.toStructure c₁.1) _
        ℕ (StructureSpace.toStructure c₂.1) _ e) q

/-- Every ℕ-model iso class has height < ω₁. -/
private theorem isoClassHeight_lt_omega1 {φ : L.Sentenceω}
    (q : Quotient (isoSetoid φ)) :
    isoClassHeight q < Ordinal.omega 1 :=
  Quotient.inductionOn q fun c =>
    @scottHeight_lt_omega1 L _ _ ℕ (StructureSpace.toStructure c.1) _

/-! ### Morley counting: ℕ-coded models -/

/-- **Height comparison.**  Two coded models that are back-and-forth equivalent at a countable
depth `α` bounding the Scott height of the first are isomorphic.  This is the only place the
stratification argument consults the Scott height, and it is exposed so that variants of the
stratification (relativized to a subclass of isomorphism classes, or with weaker per-level
bounds) can reuse it. -/
private theorem bfEquiv_at_height_implies_iso {φ : L.Sentenceω} {c₁ c₂ : ↥(ModelsOf φ)}
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hht₁ : isoClassHeight (Quotient.mk (isoSetoid φ) c₁) ≤ α)
    (hBF : (bfEquivSetoid φ α).r c₁ c₂) :
    (isoSetoid φ).r c₁ c₂ := by
  -- isoClassHeight unfolds to scottHeight with c₁.1.toStructure
  have hstab : @StabilizesCompletely L ℕ c₁.1.toStructure α :=
    @scottHeight_le_implies_stabilizesCompletely_of L _ _
      countableRefinementHypothesis ℕ c₁.1.toStructure inferInstance (α := α) hht₁
  exact ⟨(@stabilization_bound_iso_eq_BFEquiv L _
    ℕ ℕ c₁.1.toStructure c₂.1.toStructure
    inferInstance inferInstance (α := α) hα hstab hBF).some⟩

omit [L.IsRelational] in
/-- **Every countable-carrier structure space has at most continuum-many points**: it is a
`Bool`-valued function space on a countable index.

Stated for an arbitrary countable carrier rather than for `ℕ` alone, since the finite tiers need
exactly the same bound at `Fin n`. -/
private theorem mk_structureSpaceOn_le_continuum {α : Type} [Countable α] :
    #(StructureSpaceOn L α) ≤ Cardinal.continuum := by
  -- `#(X → Bool) = 2 ^ #X ≤ 2 ^ ℵ₀ = continuum` once `X` is countable
  show #(RelQueryOn L α → Bool) ≤ _
  calc #(RelQueryOn L α → Bool)
      = Cardinal.lift.{v, 0} #Bool ^ Cardinal.lift.{0, v} #(RelQueryOn L α) :=
        Cardinal.mk_arrow _ _
    _ = (2 : Cardinal) ^ Cardinal.lift.{0, v} #(RelQueryOn L α) := by
        simp
    _ ≤ (2 : Cardinal) ^ ℵ₀ := by
        apply Cardinal.power_le_power_left (by norm_num : (2 : Cardinal) ≠ 0)
        rw [Cardinal.lift_le_aleph0]
        exact Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := Cardinal.two_power_aleph0

omit [L.IsRelational] in
/-- The cardinality of `StructureSpace L` is at most continuum. -/
private theorem mk_structureSpace_le_continuum :
    #(StructureSpace L) ≤ Cardinal.continuum := mk_structureSpaceOn_le_continuum

/-- **The Scott-height stratification bound, relativized.**  Let `P` be any collection of
isomorphism classes of coded models of `φ`.  If for every `α < ω₁` the depth-`α` back-and-forth
projection of `P` (`bfProjRange φ P α`) has size at most `ℵ₁`, then `P` has at most `ℵ₁` members.

The height-`α` classes in `P` inject into that range (`bfEquiv_at_height_implies_iso`), and the
union over the `ω₁` heights is bounded by `ℵ₁ · ℵ₁ = ℵ₁`.  Two things are deliberately weaker
than in the unrelativized statement: only the classes in `P` are counted at each level, and each
level is allowed `ℵ₁` rather than `ℵ₀` classes. -/
private theorem mk_isoSetoid_subtype_le_aleph_one (φ : L.Sentenceω)
    (P : Quotient (isoSetoid φ) → Prop)
    (hle : ∀ α : Ordinal.{0}, α < Ordinal.omega 1 → #(bfProjRange φ P α) ≤ Cardinal.aleph 1) :
    #{q : Quotient (isoSetoid φ) // P q} ≤ Cardinal.aleph 1 := by
  set Q' := {q : Quotient (isoSetoid φ) // P q}
  -- Fiber bound: for each α < ω₁, the height-α classes in P inject into the restricted range.
  have hfiber_le : ∀ α, α < Ordinal.omega 1 →
      #{ q : Q' // isoClassHeight q.1 = α } ≤ Cardinal.aleph 1 := by
    intro α hα
    have hinj : Function.Injective
        (fun (q : { q : Q' // isoClassHeight q.1 = α }) =>
          (⟨bfProj φ α q.1.1, mem_bfProjRange.mpr ⟨q.1, rfl⟩⟩ : bfProjRange φ P α)) := by
      intro ⟨⟨q₁, hP₁⟩, hq₁⟩ ⟨⟨q₂, hP₂⟩, hq₂⟩ heq
      apply Subtype.ext
      apply Subtype.ext
      have heq' : bfProj φ α q₁ = bfProj φ α q₂ := congrArg Subtype.val heq
      induction q₁ using Quotient.inductionOn with | _ c₁ =>
      induction q₂ using Quotient.inductionOn with | _ c₂ =>
      apply Quotient.sound
      have hBF : (bfEquivSetoid φ α).r c₁ c₂ := Quotient.exact heq'
      exact bfEquiv_at_height_implies_iso hα (hq₁ ▸ le_rfl) hBF
    calc #{ q : Q' // isoClassHeight q.1 = α }
        ≤ #(bfProjRange φ P α) := Cardinal.mk_le_of_injective hinj
      _ ≤ Cardinal.aleph 1 := hle α hα
  -- Q' is covered by the fibers over Iio ω₁; bound the union via mk_iUnion_le_lift.
  set fibers : Set.Iio (Ordinal.omega 1 : Ordinal.{0}) → Set Q' :=
    fun ⟨α, _⟩ => {q | isoClassHeight q.1 = α}
  have hQ_eq : (Set.univ : Set Q') ⊆ ⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})),
      fibers α := by
    intro q _
    exact Set.mem_iUnion.mpr ⟨⟨isoClassHeight q.1, isoClassHeight_lt_omega1 q.1⟩, rfl⟩
  have hQ_le : #Q' ≤ #(⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})), fibers α) := by
    rw [← Cardinal.mk_univ]
    exact Cardinal.mk_le_mk_of_subset hQ_eq
  have hbound := Cardinal.mk_iUnion_le_lift (α := Q')
    (ι := Set.Iio (Ordinal.omega 1 : Ordinal.{0})) fibers
  suffices h : Cardinal.lift.{1, v} #Q' ≤ Cardinal.aleph 1 by
    rwa [Cardinal.lift_le_aleph_one] at h
  calc Cardinal.lift.{1, v} #Q'
      ≤ Cardinal.lift.{1, v} #(⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})), fibers α) :=
        Cardinal.lift_le.mpr hQ_le
    _ ≤ Cardinal.lift.{v, 1} #(Set.Iio (Ordinal.omega 1 : Ordinal.{0})) *
          ⨆ (i : Set.Iio (Ordinal.omega 1 : Ordinal.{0})),
            Cardinal.lift.{1, v} #↑(fibers i) := hbound
    _ ≤ Cardinal.aleph 1 * Cardinal.aleph 1 := by
        apply mul_le_mul'
        · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Ordinal.card_omega,
            Cardinal.lift_aleph, Ordinal.lift_one]
        · have : Nonempty (Set.Iio (Ordinal.omega 1 : Ordinal.{0})) :=
            ⟨⟨0, Ordinal.omega_pos 1⟩⟩
          apply ciSup_le
          intro ⟨α, hα⟩
          rw [Cardinal.lift_le_aleph_one]
          exact hfiber_le α hα
    _ = Cardinal.aleph 1 := by simp only [Cardinal.aleph_mul_aleph, max_self]

/-- The relativized stratification bound with countable levels: if for every `α < ω₁` the
depth-`α` projection of `P` has countable range, then `P` has at most `ℵ₁` members. -/
private theorem mk_isoSetoid_subtype_le_aleph_one_of_countable_levels (φ : L.Sentenceω)
    (P : Quotient (isoSetoid φ) → Prop)
    (hle : ∀ α : Ordinal.{0}, α < Ordinal.omega 1 → #(bfProjRange φ P α) ≤ ℵ₀) :
    #{q : Quotient (isoSetoid φ) // P q} ≤ Cardinal.aleph 1 :=
  mk_isoSetoid_subtype_le_aleph_one φ P
    (fun α hα => (hle α hα).trans (Cardinal.aleph0_le_aleph 1))

/-- **The Scott-height stratification bound.**  If every back-and-forth level below `ω₁` has only
countably many classes, then isomorphism has at most `ℵ₁` classes.  This is the case `P := ⊤` of
`mk_isoSetoid_subtype_le_aleph_one_of_countable_levels`; both `morley_counting_coded` and the
witness-bearing route consume it, since the stratification argument is indifferent to how the
countability of each level was established. -/
private theorem mk_isoSetoid_quotient_le_aleph_one (φ : L.Sentenceω)
    (hle : ∀ α, α < Ordinal.omega 1 → #(Quotient (bfEquivSetoid φ α)) ≤ ℵ₀) :
    #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 := by
  have h := mk_isoSetoid_subtype_le_aleph_one_of_countable_levels φ (fun _ => True)
    (fun α hα => (Cardinal.mk_le_of_injective Subtype.val_injective).trans (hle α hα))
  rwa [Cardinal.mk_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at h

/-- Morley counting for ℕ-coded models: ≤ ℵ₁ or = 2^ℵ₀. -/
private theorem morley_counting_coded (silver : SilverBurgessDichotomy.{v}) (φ : L.Sentenceω) :
    (#(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1) ∨
    (#(Quotient (isoSetoid φ)) = Cardinal.continuum) := by
  -- Case split: does some BFEquiv_α level have continuum-many classes?
  by_cases hc : ∃ α, α < Ordinal.omega 1 ∧
    #(Quotient (bfEquivSetoid φ α)) = Cardinal.continuum
  · -- Case 1: Some BFEquiv_α has continuum classes → iso has continuum classes
    right
    obtain ⟨α, hα, hcont⟩ := hc
    apply le_antisymm
    · -- Upper bound: quotient ≤ type ≤ StructureSpace ≤ continuum
      calc #(Quotient (isoSetoid φ))
          ≤ #(↥(ModelsOf φ)) := Cardinal.mk_quotient_le
        _ ≤ #(StructureSpace L) := Cardinal.mk_subtype_le _
        _ ≤ Cardinal.continuum := mk_structureSpace_le_continuum
    · -- Lower bound: BFEquiv_α has continuum classes, and iso refines BFEquiv_α
      calc Cardinal.continuum = #(Quotient (bfEquivSetoid φ α)) := hcont.symm
        _ ≤ #(Quotient (isoSetoid φ)) := bfEquiv_classes_le_iso_classes φ α
  · -- Case 2: All BFEquiv_α have ≤ ℵ₀ classes → iso has ≤ ℵ₁ classes
    left
    push Not at hc
    exact mk_isoSetoid_quotient_le_aleph_one φ fun α hα =>
      (bfEquiv_classes_dichotomy silver φ α hα).resolve_right (hc α hα)

/-! ### Full Morley counting theorem -/

/-- **Morley's counting theorem** (conditional on Silver-Burgess):
the number of isomorphism classes of countable models of an Lω₁ω sentence
is either ≤ ℵ₁ or exactly 2^ℵ₀.

Combines the ℕ-tier (via Scott-height stratification + BFEquiv Borelness)
with finite-carrier tiers (via permutation orbits). -/
theorem morley_counting (silver : SilverBurgessDichotomy.{v}) (φ : L.Sentenceω) :
    (#(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1) ∨
    (#(AllCodedIsoClasses φ) = Cardinal.continuum) := by
  -- Per-tier dichotomies
  have hN := morley_counting_coded silver φ
  have hFin := fun n => counting_fin_models_dichotomy silver φ n
  -- Sigma embedding
  have hEmbed : ∀ n₀, #(Quotient (isoSetoidOn φ n₀)) ≤
      #(Σ n, Quotient (isoSetoidOn φ n)) := fun n₀ =>
    ⟨⟨fun x => ⟨n₀, x⟩, fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩⟩
  -- Case split: does any tier have continuum-many classes?
  by_cases hc : (#(Quotient (isoSetoid φ)) = Cardinal.continuum) ∨
    ∃ n, #(Quotient (isoSetoidOn φ n)) = Cardinal.continuum
  · -- Some tier = continuum → total = continuum
    right
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.continuum :=
      hN.elim (·.trans (Cardinal.aleph_one_le_continuum)) le_of_eq
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum :=
      fun n => (hFin n).elim (·.trans Cardinal.aleph0_le_continuum) le_of_eq
    show #(AllCodedIsoClasses φ) = Cardinal.continuum
    apply le_antisymm
    · -- Upper bound
      show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      apply Cardinal.add_le_of_le Cardinal.aleph0_le_continuum hA_le
      calc #(Σ n, Quotient (isoSetoidOn φ n))
        ≤ ℵ₀ * Cardinal.continuum := mk_sigma_isoSetoidOn_le φ _ hFin_le
        _ = Cardinal.continuum := Cardinal.aleph0_mul_eq Cardinal.aleph0_le_continuum
    · -- Lower bound
      rcases hc with hcA | ⟨n₀, hn₀⟩
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoid φ)) := hcA.symm
          _ ≤ _ := le_self_add
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoidOn φ n₀)) := hn₀.symm
          _ ≤ #(Σ n, Quotient (isoSetoidOn φ n)) := hEmbed n₀
          _ ≤ #(Quotient (isoSetoid φ)) + #(Σ n, Quotient (isoSetoidOn φ n)) :=
            self_le_add_left _ _
  · -- No tier = continuum → ℕ-tier ≤ ℵ₁, Fin-tiers ≤ ℵ₀ → total ≤ ℵ₁
    left
    push Not at hc
    obtain ⟨hcA, hcFin⟩ := hc
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 := hN.resolve_right hcA
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ :=
      fun n => (hFin n).resolve_right (hcFin n)
    show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.aleph 1
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    apply Cardinal.add_le_of_le (Cardinal.aleph0_le_aleph 1) hA_le
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      ≤ ℵ₀ * ℵ₀ := mk_sigma_isoSetoidOn_le φ _ hFin_le
      _ = ℵ₀ := Cardinal.aleph0_mul_aleph0
      _ ≤ Cardinal.aleph 1 := Cardinal.aleph0_le_aleph 1

end Language

end FirstOrder
