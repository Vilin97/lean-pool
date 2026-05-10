/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Learner
import LeanPool.FormalLearningTheory.Criterion
import LeanPool.FormalLearningTheory.Complexity
import LeanPool.FormalLearningTheory.Computation
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.ENat.Lattice

/-!
# Bridge Types: Connecting to Mathlib and Across Paradigms

Type infrastructure bridging our definitions to Mathlib types and connecting
paradigm-specific types:

| Bridge | Source | Target | Status |
|--------|--------|--------|--------|
| B₁ | ConceptClass X Bool | Set (Set X) | Lossless for Bool (proved) |
| B₂ | ConceptClass X Bool (Fintype) | Finset (Finset X) | NEW: connects to Mathlib |
| B₃ | Shatters (ours) | Finset.Shatters (Mathlib) | NEW: key bridge |
| B₄ | VCDim (ours) | Finset.vcDim (Mathlib K₁) | NEW: unlocks Sauer-Shelah |
| B₅ | IIDSample | MeasureTheory.ProbabilityMeasure | Direct |
| B₆ | WithTop ℕ | Ordinal | Embedding (ℕ∞ ↪ Ordinal) |
| B₇ | BatchLearner ↔ GoldLearner | Cross-paradigm | No common parent (BP₁) |
-/

universe u v

/-!
## B₁: Function-Class ↔ Set-Family Bridge (Set-level)

For Y = Bool, the map c ↦ {x | c x = true} is a bijection between
(X → Bool) and Set X. This is lossless because Bool-valued functions
are determined by their level sets.

For Y with |Y| > 2, this bridge doesn't apply directly (BP₄ boundary).
-/

/-- Convert a concept class (set of functions) to a set family (set of subsets). -/
def conceptClassToSetFamily (X : Type u) (C : ConceptClass X Bool) : Set (Set X) :=
  { S | ∃ c ∈ C, S = { x | c x = true } }

/-- Convert a set family back to a concept class. Requires classical choice. -/
noncomputable def setFamilyToConceptClass (X : Type u) (F : Set (Set X)) : ConceptClass X Bool :=
  { c : X → Bool | { x | c x = true } ∈ F }

/-- The round-trip is the identity for Bool-valued functions:
    distinct functions with the same level set get identified, but for Bool
    the level set determines the function. This is B₁'s losslessness proof. -/
theorem bridge_round_trip (X : Type u) (C : ConceptClass X Bool) :
    setFamilyToConceptClass X (conceptClassToSetFamily X C) = C := by
  apply Set.ext
  intro c
  simp only [setFamilyToConceptClass, conceptClassToSetFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c', hc', hEq⟩
    have hcc' : c = c' := by
      funext x
      have := Set.ext_iff.mp hEq x
      simp only [Set.mem_setOf_eq] at this
      cases hcx : c x <;> cases hc'x : c' x <;> simp_all
    rwa [hcc']
  · intro hc
    exact ⟨c, hc, rfl⟩

/-!
## B₂: Function-Class → Finset Family Bridge (Fintype-level)

This is the critical bridge to Mathlib's combinatorial shattering API.
Requires [Fintype X] and [DecidableEq X] to produce Finsets.

The concept c : X → Bool maps to conceptToFinset c = {x ∈ univ | c x = true}.
A finite concept class C : Finset (X → Bool) maps to
conceptClassToFinsetFamily C = C.image conceptToFinset.
-/

/-- Convert a concept (X → Bool) to its level set as a Finset.
    This is the atomic bridge from function-representation to set-representation. -/
def conceptToFinset {X : Type u} [Fintype X] [DecidableEq X] (c : X → Bool) : Finset X :=
  Finset.univ.filter (fun x => c x = true)

/-- Convert a finite concept class to a Finset family.
    Requires C to be a Finset (finite concept class). This is the source
    constraint: Mathlib's Finset.vcDim operates on finite families. -/
def conceptClassToFinsetFamily {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) : Finset (Finset X) :=
  C.image conceptToFinset

/-- The concept-to-finset map is injective: distinct Bool-valued functions
    produce distinct level sets. This ensures conceptClassToFinsetFamily
    preserves the cardinality of C. -/
theorem conceptToFinset_injective {X : Type u} [Fintype X] [DecidableEq X] :
    Function.Injective (conceptToFinset (X := X)) := by
  intro c₁ c₂ h
  funext x
  have : x ∈ conceptToFinset c₁ ↔ x ∈ conceptToFinset c₂ := by rw [h]
  simp only [conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases hc₁ : c₁ x <;> cases hc₂ : c₂ x <;> simp_all

/-!
## B₃: Shatters Bridge (ours ↔ Mathlib's Finset.Shatters)

Our Shatters: ∀ f : S → Bool, ∃ c ∈ C, ∀ x : S, c x = f x
   "every labeling of S is realized by some c ∈ C"

Mathlib's Finset.Shatters: ∀ t ⊆ S, ∃ u ∈ 𝒜, S ∩ u = t
   "every subset of S appears as S ∩ u for some u ∈ 𝒜"

The correspondence: labeling f ↔ subset {x ∈ S | f x = true}.
This equivalence holds because Bool has exactly two values.
-/

/-- Our Shatters is equivalent to Mathlib's Finset.Shatters through the
    conceptToFinset bridge.

    This is the KEY bridge theorem. It allows us to use Mathlib's
    Sauer-Shelah lemma (card_le_card_shatterer, card_shatterer_le_sum_vcDim)
    to prove bounds on our learning-theoretic growth function.

    Proof strategy:
    →: Given t ⊆ S, define labeling f(x) = (x ∈ t). Our Shatters gives c ∈ C
       with c|_S = f. Then S ∩ conceptToFinset c = S ∩ {x | c x} = {x ∈ S | f x} = t.
    ←: Given f : S → Bool, let t = S.filter(f). Mathlib gives u ∈ 𝒜 with S ∩ u = t.
       Since u = conceptToFinset c for some c ∈ C, we get c|_S = f. -/
theorem shatters_iff_finset_shatters {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    Shatters X (↑C : Set (X → Bool)) S ↔
      (conceptClassToFinsetFamily C).Shatters S := by
  constructor
  · -- (→) Our Shatters → Mathlib Shatters
    intro hShat t ht
    let f : ↥S → Bool := fun x => decide (↑x ∈ t)
    obtain ⟨c, hcC, hcf⟩ := hShat f
    have hcC' : c ∈ C := Finset.mem_coe.mp hcC
    refine ⟨conceptToFinset c, Finset.mem_image.mpr ⟨c, hcC', rfl⟩, ?_⟩
    ext x
    simp only [Finset.mem_inter, conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxS, hcx⟩
      have h := hcf ⟨x, hxS⟩
      -- h : c x = decide (x ∈ t), hcx : c x = true
      rw [hcx] at h
      exact decide_eq_true_eq.mp h.symm
    · intro hxt
      refine ⟨ht hxt, ?_⟩
      have h := hcf ⟨x, ht hxt⟩
      -- h : c x = decide (x ∈ t), hxt : x ∈ t
      simp only [f] at h
      rw [h, decide_eq_true_eq]; exact hxt
  · -- (←) Mathlib Shatters → Our Shatters
    intro hShat f
    -- Build t ⊆ S from f: the "true-set" of f within S
    -- Use Subtype.val on S.attach to avoid the membership proof issue
    let t : Finset X := (S.attach.filter (fun x => f x = true)).map
      ⟨Subtype.val, Subtype.val_injective⟩
    have htS : t ⊆ S := by
      intro x hx
      simp only [t, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coeFn_mk] at hx
      obtain ⟨⟨y, hyS⟩, _, rfl⟩ := hx
      exact hyS
    obtain ⟨u, huA, hSu⟩ := hShat htS
    simp only [conceptClassToFinsetFamily, Finset.mem_image] at huA
    obtain ⟨c, hcC, rfl⟩ := huA
    refine ⟨c, Finset.mem_coe.mpr hcC, ?_⟩
    intro ⟨x, hxS⟩
    -- From hSu: S ∩ conceptToFinset c = t
    -- x ∈ S, so: c x = true ↔ x ∈ t ↔ f ⟨x, hxS⟩ = true
    have hx_in_inter : x ∈ S ∩ conceptToFinset c ↔ x ∈ t := by
      constructor <;> intro h
      · exact (Finset.ext_iff.mp hSu x).mp h
      · exact (Finset.ext_iff.mp hSu x).mpr h
    have hx_in_t : x ∈ t ↔ f ⟨x, hxS⟩ = true := by
      simp only [t, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨y, hyS⟩, hfy, rfl⟩; exact hfy
      · intro hfx; exact ⟨⟨x, hxS⟩, hfx, rfl⟩
    have hx_cx : x ∈ S ∩ conceptToFinset c ↔ c x = true := by
      simp only [Finset.mem_inter, conceptToFinset, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨fun h => h.2, fun h => ⟨hxS, h⟩⟩
    -- Combine: c x = true ↔ f ⟨x, hxS⟩ = true
    have key : c x = true ↔ f ⟨x, hxS⟩ = true := by
      rw [← hx_cx, hx_in_inter, hx_in_t]
    cases hfx : f ⟨x, hxS⟩ <;> cases hcx : c x <;> simp_all

/-!
## B₄: VCDim Bridge (ours ↔ Mathlib's Finset.vcDim)

Our VCDim: ⨆ (S : Finset X) (_ : Shatters X C S), S.card : WithTop ℕ
Mathlib's Finset.vcDim: 𝒜.shatterer.sup card : ℕ

For [Fintype X], our VCDim is always finite (bounded by Fintype.card X),
so the WithTop ℕ value is actually a natural number.

This bridge unlocks the full Mathlib shattering API:
- card_le_card_shatterer (Pajor's variant of Sauer-Shelah)
- card_shatterer_le_sum_vcDim (growth function bound)
- shatterer_compress_subset_shatterer (compression properties)
- vcDim_compress_le (down-compression preserves VC dim)
-/

/-- Our VCDim equals Mathlib's Finset.vcDim (cast to WithTop ℕ) for finite types.

    This theorem connects our learning-theoretic VCDim (defined as a supremum
    over shattered sets in WithTop ℕ) to Mathlib's combinatorial vcDim (defined
    as shatterer.sup card in ℕ).

    The proof requires shatters_iff_finset_shatters plus the equivalence between
    iSup over Shatters-witnesses and Finset.sup over shatterer members. -/
theorem vcdim_eq_finset_vcdim {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) = ↑(Finset.vcDim (conceptClassToFinsetFamily C)) := by
  let 𝒜 := conceptClassToFinsetFamily C
  apply le_antisymm
  · -- VCDim ≤ ↑(Finset.vcDim 𝒜)
    -- Suffices to show: for each S with Shatters X ↑C S, S.card ≤ Finset.vcDim 𝒜
    apply iSup_le; intro S
    apply iSup_le; intro hS
    -- Convert: Shatters X ↑C S → 𝒜.Shatters S
    have hS' : 𝒜.Shatters S := (shatters_iff_finset_shatters C S).mp hS
    -- Mathlib: Shatters.card_le_vcDim
    exact WithTop.coe_le_coe.mpr hS'.card_le_vcDim
  · -- ↑(Finset.vcDim 𝒜) ≤ VCDim
    -- Strategy: show ↑n ≤ iSup where n = 𝒜.shatterer.sup card
    -- For each S ∈ 𝒜.shatterer, S.card ≤ n, and Shatters X ↑C S holds
    -- So if shatterer is nonempty, some S achieves the sup and ↑(S.card) ≤ VCDim
    -- If shatterer is empty, sup = 0 and ↑0 ≤ anything in WithTop ℕ
    simp only [Finset.vcDim, VCDim]
    by_cases h : 𝒜.shatterer.Nonempty
    · -- There exists S ∈ shatterer achieving the sup
      obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup _ h Finset.card
      change (↑(𝒜.shatterer.sup Finset.card) : WithTop ℕ) ≤ _
      rw [hmax]
      have hS' : Shatters X (↑C : Set (X → Bool)) S :=
        (shatters_iff_finset_shatters C S).mpr (Finset.mem_shatterer.mp hS)
      exact le_iSup₂_of_le S hS' le_rfl
    · -- shatterer is empty, so sup = 0 = ⊥ ≤ anything
      rw [Finset.not_nonempty_iff_eq_empty] at h
      change (↑(𝒜.shatterer.sup Finset.card) : WithTop ℕ) ≤ _
      rw [h, Finset.sup_empty]
      exact bot_le

/-- VCDim is finite for finite concept classes over finite domains.
    This is a consequence of the bridge: Finset.vcDim is always finite (it's ℕ). -/
@[nolint unusedArguments]
theorem vcdim_finite_of_fintype {X : Type u}
    (hX : Fintype X) (hdec : DecidableEq X) (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) < ⊤ := by
  letI := hX
  letI := hdec
  rw [vcdim_eq_finset_vcdim (X := X) C]
  exact WithTop.coe_lt_top _

/-!
## B₃': Restriction Bridge (concept class restricted to a subset)

For Sauer-Shelah quantitative: we need to restrict a concept class C to an
m-element set S, producing a FINITE family of subsets of S. Then apply
Mathlib's `card_le_card_shatterer` + `card_shatterer_le_sum_vcDim`.

The restriction of C to S:
  C|_S = { c ∩ S : c ∈ C } as a Finset (Finset S)
       = { conceptToFinset(c) ∩ S : c ∈ C.image (· ∘ Subtype.val) }

Since S is Finset X (finite), C|_S is a finite family over Finset S.
-/

/-- Restrict a concept (X → Bool) to a Finset S, producing a function S → Bool. -/
def restrictToFinset {X : Type u} (c : X → Bool) (S : Finset X) : ↥S → Bool :=
  fun ⟨x, _⟩ => c x

/-- Restrict a finite concept class to a Finset S.
    Produces a Finset of functions S → Bool (the distinct restrictions). -/
def restrictConceptClass {X : Type u} [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) : Finset (↥S → Bool) :=
  C.image (fun c => restrictToFinset c S)

/-- The number of distinct restrictions is our GrowthFunction.
    GrowthFunction X C m = max over m-element S of |C|_S|.
    This lemma connects GrowthFunction to the restriction operation. -/
@[nolint unusedArguments]
theorem growthFunction_le_card_restrict {X : Type u} [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    (restrictConceptClass C S).card ≤ C.card := by
  exact Finset.card_image_le

/-- Sauer-Shelah via Mathlib: |C|_S| ≤ Σ_{i ≤ d} C(|S|, i).
    The proof chain:
    1. Convert C|_S to a Finset family over S (conceptToFinset on restrictions)
    2. Apply card_le_card_shatterer: |𝒜| ≤ |𝒜.shatterer|
    3. Apply card_shatterer_le_sum_vcDim: |𝒜.shatterer| ≤ Σ C(|S|, i) for i ≤ vcDim(𝒜)
    4. Show vcDim(𝒜) ≤ d (restriction doesn't increase VCDim)
    This requires building the S-local Finset family from C|_S. -/
-- Convert Finset (↥S → Bool) to Finset (Finset ↥S). Each f maps to {x | f x = true}.
def funcToSubsetFamily {X : Type u} [DecidableEq X] (S : Finset X)
    (fs : Finset (↥S → Bool)) : Finset (Finset ↥S) :=
  fs.image (fun f => Finset.univ.filter (fun x => f x = true))

-- The map f ↦ univ.filter (f · = true) is injective on Bool-valued functions.
@[nolint unusedArguments]
private theorem funcToSubset_injective {X : Type u} (S : Finset X) :
    Function.Injective (fun (f : ↥S → Bool) => Finset.univ.filter (fun x => f x = true)) := by
  intro f g h
  funext x
  have hmem := Finset.ext_iff.mp h x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  cases hf : f x <;> cases hg : g x <;> simp_all

-- If 𝒜 = funcToSubsetFamily S (restrictConceptClass C S) shatters T ⊆ ↥S,
-- then conceptClassToFinsetFamily C shatters T.map Subtype.val ⊆ X.
-- This is the key structural lemma for bounding vcDim of the restricted family.
private theorem restrict_shatters_lift {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X)
    (T : Finset ↥S)
    (hT : (funcToSubsetFamily S (restrictConceptClass C S)).Shatters T) :
    (conceptClassToFinsetFamily C).Shatters (T.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  -- Need: ∀ t ⊆ T.map val, ∃ u ∈ conceptClassToFinsetFamily C, (T.map val) ∩ u = t
  intro t ht
  -- Pull t back to a subset of T in ↥S
  -- t ⊆ T.map val, so each element of t is Subtype.val of some element of T
  -- Define t' : Finset ↥S as the preimage
  let t' : Finset ↥S := T.filter (fun x => ↑x ∈ t)
  have ht'T : t' ⊆ T := Finset.filter_subset _ _
  -- Use hT to get A ∈ 𝒜 with T ∩ A = t'
  obtain ⟨A, hA, hTA⟩ := hT ht'T
  -- A ∈ funcToSubsetFamily S (restrictConceptClass C S) means
  -- A = univ.filter (fun x => f x = true) for some f ∈ restrictConceptClass C S
  simp only [funcToSubsetFamily, restrictConceptClass, Finset.mem_image] at hA
  obtain ⟨f, ⟨c, hcC, rfl⟩, rfl⟩ := hA
  -- hTA : T ∩ univ.filter (fun x => restrictToFinset c S x = true) = t'
  -- restrictToFinset c S = fun ⟨x, _⟩ => c x, so this is T ∩ {x | c ↑x = true}
  simp only [restrictToFinset] at hTA
  -- Now hTA : T ∩ univ.filter (fun x => c ↑x = true) = t'
  refine ⟨conceptToFinset c, Finset.mem_image.mpr ⟨c, hcC, rfl⟩, ?_⟩
  ext y
  simp only [Finset.mem_inter, Finset.mem_map, Function.Embedding.coeFn_mk,
    conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Key helper: membership in T ∩ filter ↔ membership in t'
  have mem_iff : ∀ (z : ↥S), z ∈ T ∩ Finset.univ.filter (fun x => c ↑x = true) ↔ z ∈ t' := by
    intro z; constructor
    · intro h; exact hTA ▸ h
    · intro h; exact hTA ▸ h
  constructor
  · -- y ∈ (T.map val) ∩ {x | c x = true} → y ∈ t
    rintro ⟨⟨⟨x, hxS⟩, hxT, rfl⟩, hcx⟩
    have hx_in : (⟨x, hxS⟩ : ↥S) ∈ T ∩ Finset.univ.filter (fun x => c ↑x = true) := by
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxT, hcx⟩
    have hx_t' := (mem_iff _).mp hx_in
    simp only [t', Finset.mem_filter] at hx_t'
    exact hx_t'.2
  · -- y ∈ t → y ∈ (T.map val) ∩ {x | c x = true}
    intro hyt
    have hyS : y ∈ S := by
      have := ht hyt
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at this
      obtain ⟨⟨_, hxS⟩, _, rfl⟩ := this
      exact hxS
    have hyT : (⟨y, hyS⟩ : ↥S) ∈ T := by
      have := ht hyt
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at this
      obtain ⟨⟨z, hzS⟩, hzT, hzy⟩ := this
      have : (⟨y, hyS⟩ : ↥S) = ⟨z, hzS⟩ := Subtype.ext hzy.symm
      rw [this]; exact hzT
    constructor
    · exact ⟨⟨y, hyS⟩, hyT, rfl⟩
    · have hy_t' : (⟨y, hyS⟩ : ↥S) ∈ t' := by
        simp only [t', Finset.mem_filter]
        exact ⟨hyT, hyt⟩
      have := (mem_iff ⟨y, hyS⟩).mpr hy_t'
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2

-- vcDim of the restricted family ≤ vcDim of the original family.
private theorem vcDim_restrict_le {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    Finset.vcDim (funcToSubsetFamily S (restrictConceptClass C S)) ≤
      Finset.vcDim (conceptClassToFinsetFamily C) := by
  -- vcDim = shatterer.sup card. Need: for each T ∈ 𝒜.shatterer, T.card ≤ vcDim(C_finset)
  simp only [Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs : (funcToSubsetFamily S (restrictConceptClass C S)).Shatters T :=
    Finset.mem_shatterer.mp hT
  have hLift := restrict_shatters_lift C S T hTs
  have hCard : (T.map ⟨Subtype.val, Subtype.val_injective⟩).card = T.card :=
    Finset.card_map _
  calc T.card = (T.map ⟨Subtype.val, Subtype.val_injective⟩).card := hCard.symm
    _ ≤ Finset.vcDim (conceptClassToFinsetFamily C) := hLift.card_le_vcDim

theorem card_restrict_le_sauer_shelah_bound {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X)
    (d : ℕ) (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) :
    (restrictConceptClass C S).card ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  -- Let 𝒜 = funcToSubsetFamily S (restrictConceptClass C S) : Finset (Finset ↥S)
  set 𝒜 := funcToSubsetFamily S (restrictConceptClass C S) with h𝒜_def
  -- Step 1: (restrictConceptClass C S).card = 𝒜.card (funcToSubset_injective)
  have h1 : (restrictConceptClass C S).card ≤ 𝒜.card := by
    simp only [h𝒜_def, funcToSubsetFamily]
    rw [Finset.card_image_of_injective _ (funcToSubset_injective S)]
  -- Step 2: 𝒜.card ≤ 𝒜.shatterer.card (Mathlib: card_le_card_shatterer)
  have h2 : 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
  -- Step 3: 𝒜.shatterer.card ≤ ∑ k ∈ Iic 𝒜.vcDim, C(Fintype.card ↥S, k)
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ 𝒜
  -- Step 4: vcDim(𝒜) ≤ d
  have h4 : 𝒜.vcDim ≤ d := by
    rw [← hd]; exact vcDim_restrict_le C S
  -- Step 5: Fintype.card ↥S = S.card
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  -- Step 6: ∑ k ∈ Iic n, ... ≤ ∑ k ∈ range (d+1), ... when n ≤ d
  -- Iic n = range (n+1) for ℕ, and n ≤ d means range(n+1) ⊆ range(d+1)
  -- So ∑ k ∈ Iic n, C(S.card, k) ≤ ∑ k ∈ range(d+1), C(S.card, k)
  calc (restrictConceptClass C S).card
      ≤ 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h4
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]

/-- Bridge lemma: GrowthFunction ≤ Sauer-Shelah bound.
    This is the full Sauer-Shelah via Mathlib, packaged for PAC.lean assembly.
    The proof factors through:
    1. For each S with |S| = m: ncard(restrictions) = (traceFamily C S).card
    2. card_le_card_shatterer + card_shatterer_le_sum_vcDim from Mathlib
    3. vcDim(traceFamily C S) ≤ vcDim(C) ≤ d (restriction preserves VCDim)
    4. sSup of uniform bound ≤ bound -/
-- Helper: the set of restrictions represented by `C` has ncard equal to
-- `(restrictConceptClass C S).card`.
@[nolint unusedArguments]
private theorem ncard_restrictions_eq_card {X : Type u} [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) :
    ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)),
        ∀ x : ↥S, c ↑x = f x } : Set (↥S → Bool)).ncard =
      (restrictConceptClass C S).card := by
  -- The set equals ↑(restrictConceptClass C S) as a Set
  have hEq : { f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } =
      ↑(restrictConceptClass C S) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_coe, restrictConceptClass, Finset.mem_image,
      Finset.mem_coe]
    constructor
    · rintro ⟨c, hcC, hcf⟩
      refine ⟨c, hcC, funext fun ⟨x, hx⟩ => ?_⟩
      -- Goal: restrictToFinset c S ⟨x, hx⟩ = f ⟨x, hx⟩
      -- restrictToFinset c S ⟨x, hx⟩ = c x by definition
      -- hcf ⟨x, hx⟩ : c ↑⟨x, hx⟩ = f ⟨x, hx⟩, i.e. c x = f ⟨x, hx⟩
      exact hcf ⟨x, hx⟩
    · rintro ⟨c, hcC, rfl⟩
      exact ⟨c, hcC, fun ⟨x, hx⟩ => rfl⟩
  rw [hEq, Set.ncard_coe_finset]

-- Helper: For each S with |S| = m, ncard of restrictions ≤ Sauer-Shelah bound
private theorem ncard_restrictions_le_bound {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) :
    ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  rw [ncard_restrictions_eq_card]
  exact card_restrict_le_sauer_shelah_bound C S d hd

theorem growth_function_le_sauer_shelah {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (d : ℕ)
    (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) (m : ℕ) (_hm : d ≤ m) :
    GrowthFunction X (↑C : Set (X → Bool)) m ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction
  set B := ∑ i ∈ Finset.range (d + 1), Nat.choose m i
  -- The sSup is over Set.range of a function from { S // S.card = m } to ℕ
  -- Each value is ncard { f | ... } which we've bounded
  -- Use: sSup of a set bounded by B is ≤ B
  -- For ℕ (ConditionallyCompleteLinearOrderBot): sSup ∅ = 0 ≤ B, and if nonempty use csSup_le
  -- Use csSup_le': show B is an upper bound of the range
  apply csSup_le'
  intro n hn
  obtain ⟨⟨S, hSm⟩, rfl⟩ := hn
  change ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard ≤ B
  calc ({ f : ↥S → Bool | ∃ c ∈ (↑C : Set (X → Bool)), ∀ x : ↥S, c ↑x = f x } : Set _).ncard
      ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := ncard_restrictions_le_bound C S d hd
    _ = B := by rw [hSm]

/-!
## B₅: IIDSample ↔ ProbabilityMeasure Bridge (K₃: MeasureTheory)
-/

/-- Extract the probability measure from an IID sample.
    Direct bridge — no information loss. -/
def iidSampleToProbMeasure (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.Measure (X × Y) :=
  S.distribution

/-- The IIDSample distribution is a probability measure. -/
instance iidSampleIsProbability (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.IsProbabilityMeasure S.distribution :=
  S.isProbability

/-!
## B₆: WithTop ℕ ↪ Ordinal Bridge (BP₂)
-/

/-- Embedding of WithTop ℕ into Ordinal.
    n ↦ n, ⊤ ↦ ω.
    This is injective but NOT surjective: ordinals ≥ ω+1 have no preimage. -/
noncomputable def withTopNatToOrdinal : WithTop ℕ → Ordinal
  | some n => (n : Ordinal)
  | none => Ordinal.omega0

/-- The embedding preserves order. -/
theorem withTopNatToOrdinal_mono :
    ∀ a b : WithTop ℕ, a ≤ b → withTopNatToOrdinal a ≤ withTopNatToOrdinal b := by
  intro a b hab
  match a, b with
  | some n, some m =>
    simp only [withTopNatToOrdinal]
    exact Nat.cast_le.mpr (WithTop.coe_le_coe.mp hab)
  | some n, none =>
    simp only [withTopNatToOrdinal]
    exact le_of_lt (Ordinal.natCast_lt_omega0 n)
  | none, none =>
    exact le_refl _
  | none, some m =>
    exact absurd hab (WithTop.not_top_le_coe m)

/-- VCDim embeds into OrdinalVCDim via this bridge.
    Γ₂₇ RESOLVED: uniform ω-bound BddAbove (from Ordinal.lean) makes le_ciSup_of_le
    work for all ordinal-valued nat-cast iSup. The bridge is paradigm-invariant. -/
theorem vcdim_to_ordinal_vcdim (X : Type u)
    (C : ConceptClass X Bool) :
    withTopNatToOrdinal (VCDim X C) ≤ OrdinalVCDim X C := by
  haveI : Nonempty (Finset X) := ⟨∅⟩
  rcases hv : VCDim X C with _ | n
  · -- INFINITE CASE: VCDim X C = ⊤, withTopNatToOrdinal ⊤ = ω
    simp only [withTopNatToOrdinal]
    rw [Ordinal.omega0_le]
    intro m
    obtain ⟨S, hS_lt⟩ := (iSup_eq_top _).mp (show VCDim X C = ⊤ from hv)
      (↑m) (WithTop.coe_lt_top m)
    have hS_shat : Shatters X C S := by
      by_contra hns
      exact absurd hS_lt (not_lt.mpr (by
        haveI : IsEmpty (Shatters X C S) := ⟨hns⟩
        simp))
    rw [iSup_pos hS_shat] at hS_lt
    calc (↑m : Ordinal) ≤ ↑S.card :=
          Nat.cast_le.mpr (le_of_lt (by exact_mod_cast hS_lt))
      _ ≤ ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal) :=
          le_ciSup (ordinalVCDim_inner_bddAbove X C S) hS_shat
      _ ≤ OrdinalVCDim X C :=
          le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S le_rfl
  · -- FINITE CASE: VCDim X C = ↑n, withTopNatToOrdinal (↑n) = (n : Ordinal)
    simp only [withTopNatToOrdinal]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact bot_le
    · -- n > 0: extract witness via contradiction (same as VCDim_embed_ordinal)
      have ⟨S₀, hS₀_shat, hS₀_card⟩ : ∃ S₀, Shatters X C S₀ ∧ S₀.card = n := by
        by_contra h_none
        push Not at h_none
        have : ∀ S, Shatters X C S → S.card ≤ n - 1 := by
          intro S hS
          have hle : S.card ≤ n := by
            have : (S.card : WithTop ℕ) ≤ ↑n := by
              calc (S.card : WithTop ℕ)
                  ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
                    le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                      (S.card : WithTop ℕ)) S hS
                _ = ↑n := hv
            exact WithTop.coe_le_coe.mp this
          have hne := h_none S hS
          omega
        have hbound : VCDim X C ≤ ↑(n - 1) := by
          apply iSup₂_le
          intro S hS
          exact WithTop.coe_le_coe.mpr (this S hS)
        rw [hv] at hbound
        have : n ≤ n - 1 := WithTop.coe_le_coe.mp hbound
        omega
      calc (↑n : Ordinal) = ↑S₀.card := by exact_mod_cast hS₀_card.symm
        _ ≤ ⨆ (_ : Shatters X C S₀), ((S₀.card : ℕ) : Ordinal) :=
            le_ciSup (ordinalVCDim_inner_bddAbove X C S₀) hS₀_shat
        _ ≤ OrdinalVCDim X C :=
            le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S₀ le_rfl

/-!
## B₇: Cross-Paradigm Learner Bridges (BP₁ boundary)

These bridges are LIMITED by BP₁: there is no lossless conversion between
paradigm-specific learner types. But there are LOSSY conversions in one direction:
Online → PAC is possible (every online learner induces a PAC learner).
PAC → Online is NOT possible in general.
Gold → PAC is NOT possible in general.
-/

/-- An online learner induces a batch learner: run the online algorithm on the
    sample in any order, return the final hypothesis. -/
-- (online_learning strictly_stronger pac_learning: the one-way bridge)
noncomputable def onlineToBatch (X : Type u) (Y : Type v)
    (OL : OnlineLearner X Y) : BatchLearner X Y where
  hypotheses := Set.univ -- online learner's implicit hypothesis space
  learn := fun {_m} S =>
    let finalState := (List.ofFn S).foldl (fun s p => OL.update s p.1 p.2) OL.init
    fun x => OL.predict finalState x
  output_in_H := fun _ => Set.mem_univ _

/-- Bayesian learners can be viewed as batch learners by forgetting the prior. -/
def bayesianToBatch (X : Type u) (Y : Type v) [MeasurableSpace X]
    (BL : BayesianLearner X Y) : BatchLearner X Y where
  hypotheses := BL.hypotheses
  learn := BL.learnMAP
  output_in_H := BL.output_in_H

/-!
## Complexity Measure Bridges
-/

-- Quantitative VCDim bound from compression scheme size.
-- Γ₇₃ RESOLVED: CompressionScheme parameterized by C with realizability guard.
-- Proof: pigeonhole counting — compress is injective on labelings of any
-- shattered set (by compress_injective_on_labelings), but the number of
-- compressed subsets of size ≤ k from a 2n-element ground set is at most
-- (k+1)·(2n)^k.  At n = 2(k+1)² the exponential 2^n exceeds this polynomial,
-- giving a contradiction.  Hence no set of size ≥ 2(k+1)² is shattered.
-- The explicit polynomial bound is 2(k+1)² − 1.
theorem compression_bounds_vcdim (X : Type u)
    (C : ConceptClass X Bool) (cs : CompressionScheme X Bool C)
    (hcs : 0 < cs.size) :
    VCDim X C ≤ ↑(2 * (cs.size + 1) * (cs.size + 1) - 1) := by
  set k := cs.size with hk_def
  set N := 2 * (k + 1) * (k + 1) with hN_def
  -- Suffices: every shattered set has card < N, i.e., card ≤ N - 1
  unfold VCDim
  apply iSup₂_le
  intro S hS
  -- Show S.card ≤ N - 1 by contradiction: assume S.card ≥ N
  by_contra h_big
  push Not at h_big
  -- h_big : ↑(N - 1) < ↑S.card, so N ≤ S.card
  have hN_le : N ≤ S.card := by
    have : (N - 1 : ℕ) < S.card := by exact_mod_cast h_big
    omega
  -- Classical reasoning for DecidableEq
  haveI : DecidableEq X := Classical.decEq X
  -- Take subset T ⊆ S with |T| = N
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hN_le
  -- T is shattered (subset of shattered set)
  have hT_shatt : Shatters X C T := by
    intro f
    -- Extend f to a labeling on S
    let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
    obtain ⟨c, hcC, hcg⟩ := hS g
    refine ⟨c, hcC, ?_⟩
    intro ⟨x, hx⟩
    have hxS : x ∈ S := hT_sub hx
    have := hcg ⟨x, hxS⟩
    simp only [g, hx, dite_true] at this
    exact this
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  -- Enumerate T injectively
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  -- Build sample from labeling
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  -- Every labeling of T is C-realizable (T is shattered)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    refine ⟨c, hcC, fun i => ?_⟩
    have := hcf' (eqv i)
    simp only [f', pts] at this ⊢
    rw [show T.equivFin (eqv i) = i from T.equivFin.apply_symm_apply i] at this
    exact this
  -- compress ∘ mkSample is injective
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Target: subsets of T ×ˢ {true,false} of size ≤ k
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := A.powerset.filter (fun S => S.card ≤ k) with htarget_def
  -- Each compressed set lands in target
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_range : (p : X × Bool) ∈ Set.range (mkSample f) :=
        hsub (Finset.mem_coe.mpr hp)
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      exact ⟨by rw [show p.1 = pts i from (congr_arg Prod.fst hi).symm]; exact (eqv i).2,
             Finset.mem_univ _⟩
    · have := cs.compress_small (mkSample f); omega
  -- Source cardinality: 2^n
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  -- Target bound: |target| ≤ (k+1)·(2n)^k
  have hA_card : A.card = 2 * n := by
    simp [hA_def, Finset.card_product]; ring
  have h_target_le : target.card ≤ (k + 1) * (2 * n) ^ k := by
    calc target.card
        ≤ (Finset.range (k + 1)).sum (fun j => (A.powersetCard j).card) := by
          have : target ⊆ (Finset.range (k + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S' hS'
            simp only [htarget_def, Finset.mem_filter, Finset.mem_powerset] at hS'
            simp only [Finset.mem_biUnion, Finset.mem_range]
            exact ⟨S'.card, by omega, Finset.mem_powersetCard.mpr ⟨hS'.1, rfl⟩⟩
          exact (Finset.card_le_card this).trans Finset.card_biUnion_le
      _ = (Finset.range (k + 1)).sum (fun j => (2 * n).choose j) := by
          simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (k + 1)).sum (fun _ => (2 * n) ^ k) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ k := by
                exact Nat.pow_le_pow_right
                  (by rw [hn_eq, hN_def]; positivity) (by omega)
      _ = (k + 1) * (2 * n) ^ k := by simp [Finset.sum_const, Finset.card_range]
  -- Key inequality: (k+1)·(2n)^k < 2^n at n = 2(k+1)²
  -- Inline exp_beats_poly_at: (k+1)·(4(k+1)²)^k < 2^(2(k+1)²)
  have h_exp_beats : (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k <
      2 ^ (2 * (k + 1) * (k + 1)) := by
    have h1 : k + 1 ≤ 2 ^ k := by
      induction k with
      | zero => omega
      | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                       _ = 2 ^ (k + 1) := by ring
    have hsimp : 2 * (2 * (k + 1) * (k + 1)) = 4 * (k + 1) ^ 2 := by ring
    rw [hsimp]
    have hpow : (4 * (k + 1) ^ 2) ^ k = 2 ^ (2 * k) * (k + 1) ^ (2 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [hpow]
    rw [show (k + 1) * (2 ^ (2 * k) * (k + 1) ^ (2 * k)) =
      2 ^ (2 * k) * (k + 1) ^ (2 * k + 1) from by ring]
    have hrhs : 2 * (k + 1) * (k + 1) = 2 * (k + 1) ^ 2 := by ring
    rw [hrhs]
    have h2 : (k + 1) ^ (2 * k + 1) ≤ (2 ^ k) ^ (2 * k + 1) :=
      Nat.pow_le_pow_left h1 _
    rw [← pow_mul] at h2
    calc 2 ^ (2 * k) * (k + 1) ^ (2 * k + 1)
        ≤ 2 ^ (2 * k) * 2 ^ (k * (2 * k + 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (2 * k + k * (2 * k + 1)) := by rw [← pow_add]
      _ = 2 ^ (2 * k ^ 2 + 3 * k) := by ring_nf
      _ < 2 ^ (2 * (k + 1) ^ 2) := by
          apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
          nlinarith
  have h_target_lt : target.card < 2 ^ n := by
    calc target.card ≤ (k + 1) * (2 * n) ^ k := h_target_le
      _ = (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k := by rw [hn_eq]
      _ < 2 ^ (2 * (k + 1) * (k + 1)) := h_exp_beats
      _ = 2 ^ n := by rw [hn_eq]
  -- Pigeonhole: more labelings (2^n) than target slots → contradiction with injectivity
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt
        (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))

attribute [nolint unusedArguments] conceptToFinset restrictConceptClass
