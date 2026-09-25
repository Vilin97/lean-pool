/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.TheoremQuant
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceOrderIso
import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor
import LeanPool.RegtsSevenster.RS.StatementConverse
import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughEdgeCut
import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedCutDispatch
import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedAgreement

/-!
# The final chain: assembling the factorization

The closing assembly of the converse, built entirely from
unconditional inputs: the **closed identification**.  On a closed
fragment every subset is all-internal, so its chord diagram is
empty (`labelChords_of_allInternal`) — one fibre — and the
canonical choice value agrees with the choice-free Definition 5
value (`EdgeSubset.throughValueC_eq_mixedValue`).  Independence
across boundary pairings is not needed, there being no boundary.
-/

namespace RS



/-! ## The closed identification, unconditional -/

/-- The canonical constrained value agrees with the Definition 5
value on closed Eulerian subsets — unconditionally: closed chord
diagrams are empty, so all canonical data share one fibre. -/
theorem EdgeSubset.throughValueC_eq_mixedValue {W : ClosedFragment}
    (F : EdgeSubset W) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (Fin 0))
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hE : F.Eulerian)
    (hint : ∀ f ∈ F.flags,
      ∃ v : W.Vertex, W.attach f = Sum.inl v) :
    F.throughValueC h st hbnd = F.mixedValue h := by
  obtain ⟨⟨κ, o⟩⟩ := F.exists_transition_orientation hE hint
  have hcanon : EdgeSubset.PathCanonical o.toRel :=
    EdgeSubset.pathCanonical_of_allInternal
      (F.allInternal_of_closed) _
  have hne : Nonempty F.CanonData :=
    ⟨⟨κ.toRelTransitionSystem, o.toRel, hcanon⟩⟩
  calc F.throughValueC h st hbnd
      = F.signedValueAt h st hbnd (Classical.choice hne).1 :=
        F.throughValueC_eq_signedValueAt h st hbnd hne
    _ = F.signedValueAt h st hbnd κ.toRelTransitionSystem :=
        F.signedValueAt_of_labelChords_eq_pairing h st hbnd
          (by rw [EdgeSubset.labelChords_of_allInternal
              (F.allInternal_of_closed),
            EdgeSubset.labelChords_of_allInternal
              (F.allInternal_of_closed)])
    _ = EdgeSubset.pathSign κ.toRelTransitionSystem *
          F.throughSummand h st hbnd o.toRel
            κ.toRelTransitionSystem.openCircuitCount :=
        EdgeSubset.signedValueAt_eq h st hbnd o.toRel hcanon
    _ = F.mixedSummand h o := by
        rw [EdgeSubset.pathSign_of_allInternal
            (F.allInternal_of_closed), one_mul]
        exact F.throughSummand_eq_mixedSummand h st hbnd o
    _ = F.mixedValue h :=
        (EdgeSubset.mixedValue_eq_summand_open F h o).symm

/-! ## Membership characterizations (any fragment) -/

/-- Membership in the internal flags, unfolded: a participating flag
attached to a vertex. -/
theorem mem_internalFlags_iff {γ : Type} {W : Fragment γ}
    {F : EdgeSubset W} {f : W.Flag} :
    f ∈ F.internalFlags ↔ f ∈ F.flags ∧
      ∃ v : W.Vertex, W.attach f = Sum.inl v :=
  Finset.mem_filter

section SumToolbox

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}

/-! ## Attachment over the union (mirrors `DisjSubsetSplit`) -/

/-- A left flag is internally attached in the union exactly when it
is internally attached in the left component. -/
theorem attach_inl_vertex_iff {g : W₁.Flag} :
    (∃ v : (W₁.disjUnion W₂).Vertex,
        (W₁.disjUnion W₂).attach (Sum.inl g) = Sum.inl v) ↔
      ∃ w : W₁.Vertex, W₁.attach g = Sum.inl w := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl w => exact ⟨w, attach_inl_eq_inl.mp hv⟩
    | inr w => exact absurd hv attach_inl_ne_inr
  · rintro ⟨w, hw⟩
    exact ⟨Sum.inl w, attach_inl_eq_inl.mpr hw⟩

/-- A right flag is internally attached in the union exactly when it
is internally attached in the right component. -/
theorem attach_inr_vertex_iff {g : W₂.Flag} :
    (∃ v : (W₁.disjUnion W₂).Vertex,
        (W₁.disjUnion W₂).attach (Sum.inr g) = Sum.inl v) ↔
      ∃ w : W₂.Vertex, W₂.attach g = Sum.inl w := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl w => exact absurd hv attach_inr_ne_inl
    | inr w => exact ⟨w, attach_inr_eq_inr.mp hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨Sum.inr w, attach_inr_eq_inr.mpr hw⟩

end SumToolbox
/-! ## Parity of the open orbit data

The edge pairing reverses walk orbits: it is a fixed-point-free
involution of the periodic flags conjugating the walk permutation
to its inverse.  Consequently both the nontrivial cycles and the
fixed points of the walk permutation pair up, and the orbit total
entering `openCircuitCount` is even. -/

section Parity

open EdgeSubset

variable {γ : Type} {W : Fragment γ} {F : EdgeSubset W}

end Parity
/-! ## Componentwise relative transition systems -/

section ProdSystems

open EdgeSubset

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}
  {F : EdgeSubset (W₁.disjUnion W₂)}

/-! ### Restriction to the components -/

/-- The left component of a union system's match on a left flag,
chosen arbitrarily off the internal flags. -/
noncomputable def leftDescend (κ : F.RelTransitionSystem)
    (g : W₁.Flag) : W₁.Flag :=
  Sum.elim id (fun _ => g) (κ.match_ (Sum.inl g))

/-- The right component of a union system's match on a right flag,
chosen arbitrarily off the internal flags. -/
noncomputable def rightDescend (κ : F.RelTransitionSystem)
    (g : W₂.Flag) : W₂.Flag :=
  Sum.elim (fun _ => g) id (κ.match_ (Sum.inr g))

/-- On an internal left flag, the union system's match is the left
descent, injected. -/
theorem leftDescend_spec (κ : F.RelTransitionSystem)
    {g : W₁.Flag} (hg : g ∈ (leftSub F).internalFlags) :
    κ.match_ (Sum.inl g) = Sum.inl (leftDescend κ g) := by
  have hgU : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags :=
    inl_mem_internal.mpr hg
  obtain ⟨w, hw⟩ := (leftSub F).attach_internal_of_mem hg
  have hvert := κ.match_vertex _ hgU (Sum.inl w)
    (attach_inl_eq_inl.mpr hw)
  rcases hm : κ.match_ (Sum.inl g) with g' | g'
  · unfold leftDescend
    rw [hm]
    rfl
  · rw [hm] at hvert
    exact absurd hvert attach_inr_ne_inl

/-- On an internal right flag, the union system's match is the right
descent, injected. -/
theorem rightDescend_spec (κ : F.RelTransitionSystem)
    {g : W₂.Flag} (hg : g ∈ (rightSub F).internalFlags) :
    κ.match_ (Sum.inr g) = Sum.inr (rightDescend κ g) := by
  have hgU : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags :=
    inr_mem_internal.mpr hg
  obtain ⟨w, hw⟩ := (rightSub F).attach_internal_of_mem hg
  have hvert := κ.match_vertex _ hgU (Sum.inr w)
    (attach_inr_eq_inr.mpr hw)
  rcases hm : κ.match_ (Sum.inr g) with g' | g'
  · rw [hm] at hvert
    exact absurd hvert attach_inl_ne_inr
  · unfold rightDescend
    rw [hm]
    rfl

/-- The left descent of an internal left flag is again internal. -/
theorem leftDescend_mem (κ : F.RelTransitionSystem)
    {g : W₁.Flag} (hg : g ∈ (leftSub F).internalFlags) :
    leftDescend κ g ∈ (leftSub F).internalFlags := by
  have h := κ.match_mem _ (inl_mem_internal.mpr hg)
  rw [leftDescend_spec κ hg] at h
  exact inl_mem_internal.mp h

/-- The right descent of an internal right flag is again internal. -/
theorem rightDescend_mem (κ : F.RelTransitionSystem)
    {g : W₂.Flag} (hg : g ∈ (rightSub F).internalFlags) :
    rightDescend κ g ∈ (rightSub F).internalFlags := by
  have h := κ.match_mem _ (inr_mem_internal.mpr hg)
  rw [rightDescend_spec κ hg] at h
  exact inr_mem_internal.mp h

/-! ### Circuit count additivity -/

/-- A left flag is periodic for the product system exactly when it is
periodic for the left factor: the walk never crosses components. -/
theorem inl_mem_periodic {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem} {g : W₁.Flag} :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈
        (prodRel (F := F) κ₁ κ₂).periodicFlags ↔
      g ∈ κ₁.periodicFlags := by
  constructor
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      (prodRel κ₁ κ₂).mem_periodicFlags.mp h
    refine κ₁.mem_periodicFlags.mpr
      ⟨inl_mem_internal.mp hint, n, hn1, ?_, ?_⟩
    · intro j hj
      have hc := hcont j hj
      rw [iterWalk_prodRel_inl κ₁ κ₂ g j, pairing_inl] at hc
      exact inl_mem_internal.mp hc
    · have hh := hper
      rw [iterWalk_prodRel_inl κ₁ κ₂ g n] at hh
      exact Sum.inl.inj hh
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      κ₁.mem_periodicFlags.mp h
    refine (prodRel κ₁ κ₂).mem_periodicFlags.mpr
      ⟨inl_mem_internal.mpr hint, n, hn1, ?_, ?_⟩
    · intro j hj
      rw [iterWalk_prodRel_inl κ₁ κ₂ g j, pairing_inl]
      exact inl_mem_internal.mpr (hcont j hj)
    · rw [iterWalk_prodRel_inl κ₁ κ₂ g n, hper]

/-- A right flag is periodic for the product system exactly when it is
periodic for the right factor. -/
theorem inr_mem_periodic {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem} {g : W₂.Flag} :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈
        (prodRel (F := F) κ₁ κ₂).periodicFlags ↔
      g ∈ κ₂.periodicFlags := by
  constructor
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      (prodRel κ₁ κ₂).mem_periodicFlags.mp h
    refine κ₂.mem_periodicFlags.mpr
      ⟨inr_mem_internal.mp hint, n, hn1, ?_, ?_⟩
    · intro j hj
      have hc := hcont j hj
      rw [iterWalk_prodRel_inr κ₁ κ₂ g j, pairing_inr] at hc
      exact inr_mem_internal.mp hc
    · have hh := hper
      rw [iterWalk_prodRel_inr κ₁ κ₂ g n] at hh
      exact Sum.inr.inj hh
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      κ₂.mem_periodicFlags.mp h
    refine (prodRel κ₁ κ₂).mem_periodicFlags.mpr
      ⟨inr_mem_internal.mpr hint, n, hn1, ?_, ?_⟩
    · intro j hj
      rw [iterWalk_prodRel_inr κ₁ κ₂ g j, pairing_inr]
      exact inr_mem_internal.mpr (hcont j hj)
    · rw [iterWalk_prodRel_inr κ₁ κ₂ g n, hper]

/-- The product system's periodic flags are the disjoint sum of the
two factors' periodic flags. -/
noncomputable def periodicSumEquiv (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    {f : (W₁.disjUnion W₂).Flag //
        f ∈ (prodRel (F := F) κ₁ κ₂).periodicFlags} ≃
      ({g : W₁.Flag // g ∈ κ₁.periodicFlags} ⊕
        {g : W₂.Flag // g ∈ κ₂.periodicFlags}) where
  toFun x :=
    match x with
    | ⟨Sum.inl g, h⟩ => Sum.inl ⟨g, inl_mem_periodic.mp h⟩
    | ⟨Sum.inr g, h⟩ => Sum.inr ⟨g, inr_mem_periodic.mp h⟩
  invFun x :=
    match x with
    | Sum.inl ⟨g, h⟩ => ⟨Sum.inl g, inl_mem_periodic.mpr h⟩
    | Sum.inr ⟨g, h⟩ => ⟨Sum.inr g, inr_mem_periodic.mpr h⟩
  left_inv x := by
    rcases x with ⟨f, h⟩
    cases f <;> rfl
  right_inv x := by
    rcases x with ⟨g, h⟩ | ⟨g, h⟩ <;> rfl

/-- Under that identification the product system's walk permutation is
the sum of the two factors' walk permutations. -/
theorem walkPermPeriodic_prodRel (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    (prodRel (F := F) κ₁ κ₂).walkPermPeriodic =
      (periodicSumEquiv κ₁ κ₂).symm.permCongr
        (Equiv.sumCongr κ₁.walkPermPeriodic κ₂.walkPermPeriodic) := by
  ext ⟨f, hf⟩
  cases f with
  | inl g => rfl
  | inr g => rfl

end ProdSystems
/-! ## The through-product factorization -/

section ThroughSplit

open EdgeSubset

variable {α β : Type}

end ThroughSplit
/-! ## Componentwise colourings -/

section ColourSplit

open EdgeSubset

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}
  {F : EdgeSubset (W₁.disjUnion W₂)}

/-- A left flag outside a union subset is outside its left
restriction. -/
theorem notmem_left {g : W₁.Flag}
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags) :
    g ∉ (leftSub F).flags :=
  fun h => hg (mem_leftSub_flags.mp h)

/-- Conversely, a left flag outside the left restriction is outside the
union subset. -/
theorem notmem_left' {g : W₁.Flag}
    (hg : g ∉ (leftSub F).flags) :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags :=
  fun h => hg (mem_leftSub_flags.mpr h)

/-- A right flag outside a union subset is outside its right
restriction. -/
theorem notmem_right {g : W₂.Flag}
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags) :
    g ∉ (rightSub F).flags :=
  fun h => hg (mem_rightSub_flags.mp h)

/-- Conversely, a right flag outside the right restriction is outside
the union subset. -/
theorem notmem_right' {g : W₂.Flag}
    (hg : g ∉ (rightSub F).flags) :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags :=
  fun h => hg (mem_rightSub_flags.mpr h)

/-! ### Joining even colourings -/

/-- The underlying map of the join of two even colourings: each
non-participating flag takes its own component's colour. -/
noncomputable def joinEvenVal {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} → Fin k :=
  fun f => match f with
  | ⟨Sum.inl g, hg⟩ => ψ₁.val ⟨g, notmem_left hg⟩
  | ⟨Sum.inr g, hg⟩ => ψ₂.val ⟨g, notmem_right hg⟩

/-- The join reads the left colouring at a left flag. -/
theorem joinEvenVal_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (g : W₁.Flag)
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags)
    (hg' : g ∉ (leftSub F).flags) :
    joinEvenVal ψ₁ ψ₂ ⟨Sum.inl g, hg⟩ = ψ₁.val ⟨g, hg'⟩ := rfl

/-- The join reads the right colouring at a right flag. -/
theorem joinEvenVal_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (g : W₂.Flag)
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags)
    (hg' : g ∉ (rightSub F).flags) :
    joinEvenVal ψ₁ ψ₂ ⟨Sum.inr g, hg⟩ = ψ₂.val ⟨g, hg'⟩ := rfl

/-- The join of two component even colourings as an even colouring of
the union subset. -/
noncomputable def joinEven {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) : F.EvenColouring k :=
  ⟨joinEvenVal ψ₁ ψ₂, by
    rintro ⟨f, hf⟩
    cases f with
    | inl g =>
      have hgL : g ∉ (leftSub F).flags := notmem_left hf
      exact ((joinEvenVal_inl ψ₁ ψ₂ (W₁.pairing g)
          (F.pairing_not_mem hf)
          ((leftSub F).pairing_not_mem hgL)).trans
        (ψ₁.prop ⟨g, hgL⟩)).trans
        (joinEvenVal_inl ψ₁ ψ₂ g hf hgL).symm
    | inr g =>
      have hgR : g ∉ (rightSub F).flags := notmem_right hf
      exact ((joinEvenVal_inr ψ₁ ψ₂ (W₂.pairing g)
          (F.pairing_not_mem hf)
          ((rightSub F).pairing_not_mem hgR)).trans
        (ψ₂.prop ⟨g, hgR⟩)).trans
        (joinEvenVal_inr ψ₁ ψ₂ g hf hgR).symm⟩

/-- Even colourings of a union subset are pairs of even colourings of
the two restrictions. -/
noncomputable def joinEvenEquiv (F : EdgeSubset (W₁.disjUnion W₂)) (k : ℕ) :
    ((leftSub F).EvenColouring k × (rightSub F).EvenColouring k) ≃
      F.EvenColouring k where
  toFun p := joinEven p.1 p.2
  invFun ψ :=
    (⟨fun g => ψ.val ⟨Sum.inl g.val, notmem_left' g.prop⟩,
      fun g => by
        exact ψ.prop ⟨Sum.inl g.val, notmem_left' g.prop⟩⟩,
     ⟨fun g => ψ.val ⟨Sum.inr g.val, notmem_right' g.prop⟩,
      fun g => by
        exact ψ.prop ⟨Sum.inr g.val, notmem_right' g.prop⟩⟩)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (funext fun g => rfl)
    · exact Subtype.ext (funext fun g => rfl)
  right_inv ψ := by
    refine Subtype.ext (funext fun f => ?_)
    rcases f with ⟨f, hf⟩
    cases f <;> rfl

/-! ### Joining core odd colourings -/

/-- The underlying map of the join of two core odd colourings: each
core flag takes its own component's colour. -/
noncomputable def joinCoreVal {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    {f : (W₁.disjUnion W₂).Flag // f ∈ F.coreFlags} → Fin (2 * ℓ) :=
  fun f => match f with
  | ⟨Sum.inl g, hg⟩ => φ₁.val ⟨g, inl_mem_core.mp hg⟩
  | ⟨Sum.inr g, hg⟩ => φ₂.val ⟨g, inr_mem_core.mp hg⟩

/-- The core join reads the left colouring at a left flag. -/
theorem joinCoreVal_inl {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags)
    (hg' : g ∈ (leftSub F).coreFlags) :
    joinCoreVal φ₁ φ₂ ⟨Sum.inl g, hg⟩ = φ₁.val ⟨g, hg'⟩ := rfl

/-- The core join reads the right colouring at a right flag. -/
theorem joinCoreVal_inr {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags)
    (hg' : g ∈ (rightSub F).coreFlags) :
    joinCoreVal φ₁ φ₂ ⟨Sum.inr g, hg⟩ = φ₂.val ⟨g, hg'⟩ := rfl

/-- The join of two component core odd colourings as a core odd
colouring of the union subset. -/
noncomputable def joinCore {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    F.CoreOddColouring ℓ :=
  ⟨joinCoreVal φ₁ φ₂, by
    rintro ⟨f, hf⟩
    cases f with
    | inl g =>
      have hgL : g ∈ (leftSub F).coreFlags := inl_mem_core.mp hf
      exact ((joinCoreVal_inl φ₁ φ₂ (W₁.pairing g)
          (F.pairing_mem_coreFlags hf)
          ((leftSub F).pairing_mem_coreFlags hgL)).trans
        (φ₁.prop ⟨g, hgL⟩)).trans
        (joinCoreVal_inl φ₁ φ₂ g hf hgL).symm
    | inr g =>
      have hgR : g ∈ (rightSub F).coreFlags := inr_mem_core.mp hf
      exact ((joinCoreVal_inr φ₁ φ₂ (W₂.pairing g)
          (F.pairing_mem_coreFlags hf)
          ((rightSub F).pairing_mem_coreFlags hgR)).trans
        (φ₂.prop ⟨g, hgR⟩)).trans
        (joinCoreVal_inr φ₁ φ₂ g hf hgR).symm⟩

/-- Core odd colourings of a union subset are pairs of core odd
colourings of the two restrictions. -/
noncomputable def joinCoreEquiv (F : EdgeSubset (W₁.disjUnion W₂)) (ℓ : ℕ) :
    ((leftSub F).CoreOddColouring ℓ ×
        (rightSub F).CoreOddColouring ℓ) ≃
      F.CoreOddColouring ℓ where
  toFun p := joinCore p.1 p.2
  invFun φ :=
    (⟨fun g => φ.val ⟨Sum.inl g.val, inl_mem_core.mpr g.prop⟩,
      fun g => by
        exact φ.prop ⟨Sum.inl g.val, inl_mem_core.mpr g.prop⟩⟩,
     ⟨fun g => φ.val ⟨Sum.inr g.val, inr_mem_core.mpr g.prop⟩,
      fun g => by
        exact φ.prop ⟨Sum.inr g.val, inr_mem_core.mpr g.prop⟩⟩)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (funext fun g => rfl)
    · exact Subtype.ext (funext fun g => rfl)
  right_inv φ := by
    refine Subtype.ext (funext fun f => ?_)
    rcases f with ⟨f, hf⟩
    cases f <;> rfl

/-! ### Boundary-match transfer -/

/-- A join of even colourings meets the union's boundary constraint
exactly when both components meet theirs. -/
theorem genEvenBoundaryMatch_join {k ℓ : ℕ}
    {st : GenBoundaryState k ℓ (α ⊕ β)}
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    genEvenBoundaryMatch F st hbnd (joinEven ψ₁ ψ₂) ↔
      (genEvenBoundaryMatch (leftSub F) (fun a => st (Sum.inl a))
          hbnd₁ ψ₁ ∧
        genEvenBoundaryMatch (rightSub F) (fun b => st (Sum.inr b))
          hbnd₂ ψ₂) := by
  constructor
  · intro hm
    constructor
    · intro a c hst
      have h0 := hm (Sum.inl a) c hst
      exact (joinEvenVal_inl ψ₁ ψ₂ (W₁.boundaryFlag a)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inl a) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₁ a c hst)).symm.trans h0
    · intro b c hst
      have h0 := hm (Sum.inr b) c hst
      exact (joinEvenVal_inr ψ₁ ψ₂ (W₂.boundaryFlag b)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inr b) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₂ b c hst)).symm.trans h0
  · rintro ⟨h₁, h₂⟩ i c hst
    cases i with
    | inl a =>
      exact (joinEvenVal_inl ψ₁ ψ₂ (W₁.boundaryFlag a)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inl a) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₁ a c hst)).trans
        (h₁ a c hst)
    | inr b =>
      exact (joinEvenVal_inr ψ₁ ψ₂ (W₂.boundaryFlag b)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inr b) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₂ b c hst)).trans
        (h₂ b c hst)

/-- A join of core odd colourings meets the union's boundary
constraint exactly when both components meet theirs. -/
theorem coreOddBoundaryMatch_join {k ℓ : ℕ}
    {st : GenBoundaryState k ℓ (α ⊕ β)}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st (joinCore φ₁ φ₂) ↔
      ((leftSub F).coreOddBoundaryMatch (fun a => st (Sum.inl a)) φ₁ ∧
        (rightSub F).coreOddBoundaryMatch (fun b => st (Sum.inr b))
          φ₂) := by
  constructor
  · intro hm
    constructor
    · intro a c hst hcore
      have h0 := hm (Sum.inl a) c hst (inl_mem_core.mpr hcore)
      exact (joinCoreVal_inl φ₁ φ₂ (W₁.boundaryFlag a)
        (inl_mem_core.mpr hcore) hcore).symm.trans h0
    · intro b c hst hcore
      have h0 := hm (Sum.inr b) c hst (inr_mem_core.mpr hcore)
      exact (joinCoreVal_inr φ₁ φ₂ (W₂.boundaryFlag b)
        (inr_mem_core.mpr hcore) hcore).symm.trans h0
  · rintro ⟨h₁, h₂⟩ i c hst hcore
    cases i with
    | inl a =>
      exact (joinCoreVal_inl φ₁ φ₂ (W₁.boundaryFlag a) hcore
        (inl_mem_core.mp hcore)).trans
        (h₁ a c hst (inl_mem_core.mp hcore))
    | inr b =>
      exact (joinCoreVal_inr φ₁ φ₂ (W₂.boundaryFlag b) hcore
        (inr_mem_core.mp hcore)).trans
        (h₂ b c hst (inr_mem_core.mp hcore))

/-! ### Even colour multisets at component vertices -/

/-- The left injection embeds the left restriction's
non-participating flags into the union's. -/
noncomputable def leftComplEmb (F : EdgeSubset (W₁.disjUnion W₂)) :
    {g : W₁.Flag // g ∉ (leftSub F).flags} ↪
      {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} :=
  ⟨fun g => ⟨Sum.inl g.val, notmem_left' g.prop⟩,
   fun _g _g' h =>
     Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))⟩

/-- The right injection embeds the right restriction's
non-participating flags into the union's. -/
noncomputable def rightComplEmb (F : EdgeSubset (W₁.disjUnion W₂)) :
    {g : W₂.Flag // g ∉ (rightSub F).flags} ↪
      {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} :=
  ⟨fun g => ⟨Sum.inr g.val, notmem_right' g.prop⟩,
   fun _g _g' h =>
     Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))⟩

/-- At a left vertex, the join's colour multiset over the flags there
is the left colouring's. -/
theorem evenColours_aux_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₁.Vertex)
    (S : Finset {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags})
    (T : Finset {g : W₁.Flag // g ∉ (leftSub F).flags})
    (hS : ∀ x, x ∈ S ↔
      (W₁.disjUnion W₂).attach x.val = Sum.inl (Sum.inl v))
    (hT : ∀ y, y ∈ T ↔ W₁.attach y.val = Sum.inl v) :
    S.val.map (joinEven ψ₁ ψ₂).val = T.val.map ψ₁.val := by
  have hset : S = T.map (leftComplEmb F) := by
    ext x
    rw [hS x]
    constructor
    · intro hatt
      rcases x with ⟨f, hf⟩
      cases f with
      | inl g =>
        exact Finset.mem_map.mpr ⟨⟨g, notmem_left hf⟩,
          (hT _).mpr (attach_inl_eq_inl.mp hatt), Subtype.ext rfl⟩
      | inr g => exact absurd hatt attach_inr_ne_inl
    · intro hx
      obtain ⟨g, hg, hmap⟩ := Finset.mem_map.mp hx
      rw [← hmap]
      exact attach_inl_eq_inl.mpr ((hT g).mp hg)
  rw [hset, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun g hg =>
    joinEvenVal_inl ψ₁ ψ₂ g.val (notmem_left' g.prop) g.prop

/-- At a right vertex, the join's colour multiset over the flags there
is the right colouring's. -/
theorem evenColours_aux_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₂.Vertex)
    (S : Finset {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags})
    (T : Finset {g : W₂.Flag // g ∉ (rightSub F).flags})
    (hS : ∀ x, x ∈ S ↔
      (W₁.disjUnion W₂).attach x.val = Sum.inl (Sum.inr v))
    (hT : ∀ y, y ∈ T ↔ W₂.attach y.val = Sum.inl v) :
    S.val.map (joinEven ψ₁ ψ₂).val = T.val.map ψ₂.val := by
  have hset : S = T.map (rightComplEmb F) := by
    ext x
    rw [hS x]
    constructor
    · intro hatt
      rcases x with ⟨f, hf⟩
      cases f with
      | inl g => exact absurd hatt attach_inl_ne_inr
      | inr g =>
        exact Finset.mem_map.mpr ⟨⟨g, notmem_right hf⟩,
          (hT _).mpr (attach_inr_eq_inr.mp hatt), Subtype.ext rfl⟩
    · intro hx
      obtain ⟨g, hg, hmap⟩ := Finset.mem_map.mp hx
      rw [← hmap]
      exact attach_inr_eq_inr.mpr ((hT g).mp hg)
  rw [hset, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun g hg =>
    joinEvenVal_inr ψ₁ ψ₂ g.val (notmem_right' g.prop) g.prop

/-- The join's even colours at a left vertex are the left
colouring's. -/
theorem evenColoursAt_join_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₁.Vertex) :
    F.evenColoursAt (joinEven ψ₁ ψ₂) (Sum.inl v) =
      (leftSub F).evenColoursAt ψ₁ v := by
  unfold EdgeSubset.evenColoursAt
  refine evenColours_aux_inl ψ₁ ψ₂ v _ _ ?_ ?_
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The join's even colours at a right vertex are the right
colouring's. -/
theorem evenColoursAt_join_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₂.Vertex) :
    F.evenColoursAt (joinEven ψ₁ ψ₂) (Sum.inr v) =
      (rightSub F).evenColoursAt ψ₂ v := by
  unfold EdgeSubset.evenColoursAt
  refine evenColours_aux_inr ψ₁ ψ₂ v _ _ ?_ ?_
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### In-flag lists at component vertices -/

/-- At a left vertex, the product orientation's in-flags are the left
factor's, injected — up to the enumeration order. -/
theorem relInFlagsAt_join_perm_inl {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) (v : W₁.Vertex) :
    (F.relInFlagsAt (prodOrient o₁ o₂) (Sum.inl v)).Perm
      (((leftSub F).relInFlagsAt o₁ v).map Sum.inl) := by
  let := (W₁.disjUnion W₂).flagOrder
  let := W₁.flagOrder
  let := Classical.dec
  apply Multiset.coe_eq_coe.mp
  unfold EdgeSubset.relInFlagsAt
  refine Eq.trans (Finset.sort_eq _ _) ?_
  refine Eq.trans ?_ (Multiset.map_coe Sum.inl _)
  refine Eq.trans ?_
    (congrArg (Multiset.map Sum.inl) (Finset.sort_eq _ _)).symm
  refine (Multiset.Nodup.ext (Finset.nodup _)
    (Multiset.Nodup.map Sum.inl_injective (Finset.nodup _))).mpr ?_
  intro f
  constructor
  · intro hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hf)
    cases f with
    | inl g =>
      refine Multiset.mem_map.mpr ⟨g, ?_, rfl⟩
      exact Finset.mem_val.mpr (Finset.mem_filter.mpr
        ⟨mem_leftSub_flags.mpr h.1,
          attach_inl_eq_inl.mp h.2.1, h.2.2⟩)
    | inr g =>
      exact absurd h.2.1 attach_inr_ne_inl
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hg)
    exact Finset.mem_val.mpr (Finset.mem_filter.mpr
      ⟨mem_leftSub_flags.mp h.1,
        attach_inl_eq_inl.mpr h.2.1, h.2.2⟩)

/-- At a right vertex, the product orientation's in-flags are the
right factor's, injected — up to the enumeration order. -/
theorem relInFlagsAt_join_perm_inr {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) (v : W₂.Vertex) :
    (F.relInFlagsAt (prodOrient o₁ o₂) (Sum.inr v)).Perm
      (((rightSub F).relInFlagsAt o₂ v).map Sum.inr) := by
  let := (W₁.disjUnion W₂).flagOrder
  let := W₂.flagOrder
  let := Classical.dec
  apply Multiset.coe_eq_coe.mp
  unfold EdgeSubset.relInFlagsAt
  refine Eq.trans (Finset.sort_eq _ _) ?_
  refine Eq.trans ?_ (Multiset.map_coe Sum.inr _)
  refine Eq.trans ?_
    (congrArg (Multiset.map Sum.inr) (Finset.sort_eq _ _)).symm
  refine (Multiset.Nodup.ext (Finset.nodup _)
    (Multiset.Nodup.map Sum.inr_injective (Finset.nodup _))).mpr ?_
  intro f
  constructor
  · intro hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hf)
    cases f with
    | inl g =>
      exact absurd h.2.1 attach_inl_ne_inr
    | inr g =>
      refine Multiset.mem_map.mpr ⟨g, ?_, rfl⟩
      exact Finset.mem_val.mpr (Finset.mem_filter.mpr
        ⟨mem_rightSub_flags.mpr h.1,
          attach_inr_eq_inr.mp h.2.1, h.2.2⟩)
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hg)
    exact Finset.mem_val.mpr (Finset.mem_filter.mpr
      ⟨mem_rightSub_flags.mp h.1,
        attach_inr_eq_inr.mpr h.2.1, h.2.2⟩)

/-- An injected left in-flag is an internal flag of the union
subset. -/
theorem mem_internal_of_mem_map_inl
    {κ₁ : (leftSub F).RelTransitionSystem} {o₁ : κ₁.Orientation}
    {v : W₁.Vertex} {f : (W₁.disjUnion W₂).Flag}
    (hf : f ∈ ((leftSub F).relInFlagsAt o₁ v).map Sum.inl) :
    f ∈ F.internalFlags := by
  obtain ⟨g, hgl, rfl⟩ := List.mem_map.mp hf
  exact inl_mem_internal.mpr
    ((leftSub F).mem_internal_of_mem_relInFlagsAt hgl)

/-- An injected right in-flag is an internal flag of the union
subset. -/
theorem mem_internal_of_mem_map_inr
    {κ₂ : (rightSub F).RelTransitionSystem} {o₂ : κ₂.Orientation}
    {v : W₂.Vertex} {f : (W₁.disjUnion W₂).Flag}
    (hf : f ∈ ((rightSub F).relInFlagsAt o₂ v).map Sum.inr) :
    f ∈ F.internalFlags := by
  obtain ⟨g, hgl, rfl⟩ := List.mem_map.mp hf
  exact inr_mem_internal.mpr
    ((rightSub F).mem_internal_of_mem_relInFlagsAt hgl)

/-! ### `pmap` helpers (mirrors `MixedPartition`) -/

/-- `List.pmap` respects permutations. -/
theorem perm_pmap' {β' γ' : Type*} {p : β' → Prop}
    (f : ∀ b, p b → γ') {l₁ l₂ : List β'} (hp : l₁.Perm l₂) :
    ∀ (H₁ : ∀ b ∈ l₁, p b) (H₂ : ∀ b ∈ l₂, p b),
      (l₁.pmap f H₁).Perm (l₂.pmap f H₂) := by
  induction hp with
  | nil => exact fun _ _ => List.Perm.refl _
  | cons b _ ih => exact fun _ _ => List.Perm.cons _ (ih _ _)
  | swap x y l => exact fun _ _ => List.Perm.swap _ _ _
  | trans hp₁ _ ih₁ ih₂ =>
    exact fun H₁ H₂ =>
      (ih₁ H₁ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb))).trans
        (ih₂ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb)) H₂)

/-- Two `pmap`-then-`flatMap` passes over one list agree when they
agree elementwise. -/
theorem pmap_flatMap_congr' {β' β₁ β₂ γ' : Type*}
    {p₁ p₂ : β' → Prop} (f₁ : ∀ b, p₁ b → β₁) (f₂ : ∀ b, p₂ b → β₂)
    (G₁ : β₁ → List γ') (G₂ : β₂ → List γ') (l : List β')
    (H₁ : ∀ b ∈ l, p₁ b) (H₂ : ∀ b ∈ l, p₂ b)
    (hpt : ∀ b ∈ l, ∀ h₁ h₂, G₁ (f₁ b h₁) = G₂ (f₂ b h₂)) :
    (l.pmap f₁ H₁).flatMap G₁ = (l.pmap f₂ H₂).flatMap G₂ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.pmap, List.flatMap_cons]
    rw [hpt a List.mem_cons_self _ _,
      ih _ _ (fun b hb => hpt b (List.mem_cons_of_mem _ hb))]

/-! ### Vertex-local core data at component vertices -/

/-- The join's odd sign at a left internal flag is the left
factor's. -/
theorem coreOddSignFn_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg' : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (leftSub F).internalFlags) :
    F.coreOddSignFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inl g, hg'⟩ =
      (leftSub F).coreOddSignFn κ₁ φ₁ ⟨g, hg⟩ := rfl

/-- The join's odd sign at a right internal flag is the right
factor's. -/
theorem coreOddSignFn_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg' : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (rightSub F).internalFlags) :
    F.coreOddSignFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inr g, hg'⟩ =
      (rightSub F).coreOddSignFn κ₂ φ₂ ⟨g, hg⟩ := rfl

/-- The join's odd pair at a left internal flag is the left factor's,
injected. -/
theorem coreOddPairFn_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg' : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (leftSub F).internalFlags) :
    F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inl g, hg'⟩ =
      (leftSub F).coreOddPairFn κ₁ φ₁ ⟨g, hg⟩ := rfl

/-- The join's odd pair at a right internal flag is the right
factor's, injected. -/
theorem coreOddPairFn_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg' : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (rightSub F).internalFlags) :
    F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inr g, hg'⟩ =
      (rightSub F).coreOddPairFn κ₂ φ₂ ⟨g, hg⟩ := rfl

/-- The join's odd-pairing sign at a left vertex is the left
factor's. -/
theorem coreOddSignAt_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₁.Vertex) :
    F.coreOddSignAt (prodOrient o₁ o₂) (joinCore φ₁ φ₂)
        (Sum.inl v) =
      (leftSub F).coreOddSignAt o₁ φ₁ v := by
  unfold EdgeSubset.coreOddSignAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inl o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inl hg)
  refine ((hstep.map (F.coreOddSignFn (prodRel κ₁ κ₂)
    (joinCore φ₁ φ₂))).prod_eq).trans (congrArg List.prod ?_)
  refine Eq.trans (List.map_pmap _) ?_
  refine Eq.trans (List.pmap_map _) ?_
  exact Eq.trans (List.pmap_congr_left _
    (fun a ha h₁ h₂ => coreOddSignFn_join_inl φ₁ φ₂ a h₁ h₂))
    (List.map_pmap _).symm

/-- The join's odd-pairing sign at a right vertex is the right
factor's. -/
theorem coreOddSignAt_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₂.Vertex) :
    F.coreOddSignAt (prodOrient o₁ o₂) (joinCore φ₁ φ₂)
        (Sum.inr v) =
      (rightSub F).coreOddSignAt o₂ φ₂ v := by
  unfold EdgeSubset.coreOddSignAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inr o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inr hg)
  refine ((hstep.map (F.coreOddSignFn (prodRel κ₁ κ₂)
    (joinCore φ₁ φ₂))).prod_eq).trans (congrArg List.prod ?_)
  refine Eq.trans (List.map_pmap _) ?_
  refine Eq.trans (List.pmap_map _) ?_
  exact Eq.trans (List.pmap_congr_left _
    (fun a ha h₁ h₂ => coreOddSignFn_join_inr φ₁ φ₂ a h₁ h₂))
    (List.map_pmap _).symm

/-- The vertex functional's odd evaluation at a left vertex reads the
left factor's odd list. -/
theorem evalOdd_coreOddListAt_join_inl {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₁.Vertex) :
    h.evalOdd μ (F.coreOddListAt (prodOrient o₁ o₂)
        (joinCore φ₁ φ₂) (Sum.inl v)) =
      h.evalOdd μ ((leftSub F).coreOddListAt o₁ φ₁ v) := by
  unfold EdgeSubset.coreOddListAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inl o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inl hg)
  have h1 := h.evalOdd_flatMap_perm μ
    (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂))
    (fun _ => rfl) hstep []
  simp only [List.nil_append] at h1
  refine h1.trans (congrArg (h.evalOdd μ) ?_)
  refine Eq.trans (congrArg
    (fun l' => l'.flatMap
      (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)))
    (List.pmap_map _)) ?_
  exact pmap_flatMap_congr' _ _ _ _ _ _ _
    (fun a ha h₁ h₂ => coreOddPairFn_join_inl φ₁ φ₂ a h₁ h₂)

/-- The vertex functional's odd evaluation at a right vertex reads the
right factor's odd list. -/
theorem evalOdd_coreOddListAt_join_inr {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₂.Vertex) :
    h.evalOdd μ (F.coreOddListAt (prodOrient o₁ o₂)
        (joinCore φ₁ φ₂) (Sum.inr v)) =
      h.evalOdd μ ((rightSub F).coreOddListAt o₂ φ₂ v) := by
  unfold EdgeSubset.coreOddListAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inr o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inr hg)
  have h1 := h.evalOdd_flatMap_perm μ
    (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂))
    (fun _ => rfl) hstep []
  simp only [List.nil_append] at h1
  refine h1.trans (congrArg (h.evalOdd μ) ?_)
  refine Eq.trans (congrArg
    (fun l' => l'.flatMap
      (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)))
    (List.pmap_map _)) ?_
  exact pmap_flatMap_congr' _ _ _ _ _ _ _
    (fun a ha h₁ h₂ => coreOddPairFn_join_inr φ₁ φ₂ a h₁ h₂)

/-! ### The colouring-sum factorization -/

/-- The even-colouring equivalence is the join. -/
theorem joinEvenEquiv_apply {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    joinEvenEquiv F k (ψ₁, ψ₂) = joinEven ψ₁ ψ₂ := rfl

/-- The core-colouring equivalence is the join. -/
theorem joinCoreEquiv_apply {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    joinCoreEquiv F ℓ (φ₁, φ₂) = joinCore φ₁ φ₂ := rfl

/-- A product over the union's vertices splits into the two
components' products. -/
theorem prod_vertex_split (X : (W₁.disjUnion W₂).Vertex → ℂ) :
    ∏ v : (W₁.disjUnion W₂).Vertex, X v =
      (∏ v : W₁.Vertex, X (Sum.inl v)) *
        ∏ v : W₂.Vertex, X (Sum.inr v) :=
  Fintype.prod_sum_type X

end ColourSplit
/-! ## The canonical-value migration

The corrected (canonical) constrained value pins a path-canonical
orientation and weights it by the Pfaffian chord-diagram sign.  The
factorization migrates: the product of two path-canonical component
orientations is path-canonical for the union (chains stay
componentwise), and cross-component chords never interleave under
any order placing every left label below every right label, so the
crossing count — hence the path sign — is additive. -/

section CanonMigration

open EdgeSubset

variable {α β : Type}

/-! ### The product system's chain matching -/

/-- The boundary label of a left-summand boundary flag. -/
theorem boundaryLabel_inl
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag}
    (hb : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (leftSub F).boundaryFlags) :
    F.boundaryLabel hb = Sum.inl ((leftSub F).boundaryLabel hb') := by
  refine EdgeSubset.boundaryLabel_eq_of_attach hb ?_
  change ((W₁.attach g).map Sum.inl Sum.inl) =
    Sum.inr (Sum.inl ((leftSub F).boundaryLabel hb'))
  rw [EdgeSubset.attach_boundaryLabel hb']
  rfl

/-- The boundary label of a right-summand boundary flag. -/
theorem boundaryLabel_inr
    {W₁ : Fragment α} {W₂ : Fragment β} {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag}
    (hb : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.boundaryFlags)
    (hb' : g ∈ (rightSub F).boundaryFlags) :
    F.boundaryLabel hb = Sum.inr ((rightSub F).boundaryLabel hb') := by
  refine EdgeSubset.boundaryLabel_eq_of_attach hb ?_
  change ((W₂.attach g).map Sum.inr Sum.inr) =
    Sum.inr (Sum.inr ((rightSub F).boundaryLabel hb'))
  rw [EdgeSubset.attach_boundaryLabel hb']
  rfl

end CanonMigration

end RS
