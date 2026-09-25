/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalIndependence
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence

/-!
# All-internal agreement: Eulerian independence outright

A standard `TransitionSystem` on an edge subset forces every
participating flag to be internally attached (`attach_internal`),
so the subset is all-internal even inside an open fragment.  This
file generalizes the closed-fragment agreement chain of
`ClosedAgreement.lean` from `Fragment (Fin 0)` to arbitrary
fragments under `allInternal`: through-edges vanish, the core
colouring is the full odd colouring, and the open circuit count is
the standard circuit count.

The genuinely new ingredient is the boundary state.  On an open
fragment the even boundary match is *not* vacuous: it pins the even
colouring at the (non-participating) boundary flags.  Instead, each
even colouring `ψ` induces the all-even state `evenState ψ`
recording its boundary values; the even boundary match for
`evenState ψ₀` holds exactly on the fibre
`{ψ | evenState ψ = evenState ψ₀}`, and the mixed summand
decomposes fibrewise into through summands over the finitely many
realized states.  Applying the unconditional all-internal
independence (`throughSummand_independence_of_allInternal`) fibre
by fibre proves the Eulerian-independence interface outright.  No
state is ever chosen — every state used is manufactured from an
existing even colouring — so no `(k, ℓ) = (0, 0)` edge case arises.
-/

namespace RS



variable {α : Type} {W : Fragment α}

namespace EdgeSubset

variable {F : EdgeSubset W}

/-! ## Vacuous through-data on all-internal subsets -/

/-- On an all-internal subset, every participating flag attaches to
an internal vertex. -/
theorem attach_inl_of_allInternal (hall : F.allInternal) {f : W.Flag}
    (hf : f ∈ F.flags) : ∃ v : W.Vertex, W.attach f = Sum.inl v :=
  F.attach_internal_of_mem (mem_internalFlags_of_allInternal hall hf)

/-- On an all-internal subset, there are no through-flags. -/
theorem throughFlags_eq_empty_of_allInternal (hall : F.allInternal) :
    F.throughFlags = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  unfold EdgeSubset.throughFlags at hf
  rw [Finset.mem_filter] at hf
  obtain ⟨hfl, ⟨i, hi⟩, -⟩ := hf
  obtain ⟨v, hv⟩ := attach_inl_of_allInternal hall hfl
  rw [hv] at hi
  cases hi

/-- On an all-internal subset, the core flags are the full flags. -/
theorem coreFlags_eq_flags_of_allInternal (hall : F.allInternal) :
    F.coreFlags = F.flags := by
  ext f
  rw [F.mem_coreFlags_iff]
  exact ⟨fun hf => hf.1, fun hf =>
    ⟨hf, Or.inl (attach_inl_of_allInternal hall hf)⟩⟩

/-- On an all-internal subset, the through product is `1`. -/
theorem throughProduct_one_of_allInternal [LinearOrder α]
    (hall : F.allInternal) {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ α) :
    F.throughProduct st = 1 := by
  unfold EdgeSubset.throughProduct
  apply Finset.prod_eq_one
  intro f _
  exact absurd f.prop
    (Finset.eq_empty_iff_forall_notMem.mp
      (throughFlags_eq_empty_of_allInternal hall) f.val)

/-- On an all-internal subset, no boundary flag participates. -/
theorem boundaryFlag_notMem_of_allInternal (hall : F.allInternal)
    (i : α) : W.boundaryFlag i ∉ F.flags := by
  intro hmem
  obtain ⟨v, hv⟩ := attach_inl_of_allInternal hall hmem
  rw [W.attach_boundaryFlag i] at hv
  cases hv

/-! ## The boundary state of an even colouring -/

/-- The all-even boundary state recording an even colouring's
values at the boundary flags. -/
noncomputable def evenState (hall : F.allInternal) {k : ℕ} (ℓ : ℕ)
    (ψ : F.EvenColouring k) : GenBoundaryState k ℓ α :=
  fun i => Sum.inl (ψ.val ⟨W.boundaryFlag i,
    boundaryFlag_notMem_of_allInternal hall i⟩)

/-- The state of an even colouring satisfies the boundary subset
matching condition. -/
theorem evenState_matches (hall : F.allInternal) {k : ℕ} (ℓ : ℕ)
    (ψ : F.EvenColouring k) :
    genBoundarySubsetMatches W F.flags (evenState hall ℓ ψ) := by
  intro i
  constructor
  · intro hmem
    exact absurd hmem (boundaryFlag_notMem_of_allInternal hall i)
  · rintro ⟨c, hc⟩
    simp [evenState] at hc

/-- The core odd boundary match holds vacuously at an even
state. -/
theorem coreOddBoundaryMatch_evenState (hall : F.allInternal)
    {k ℓ : ℕ} (ψ₀ : F.EvenColouring k)
    (φ : F.CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch (evenState hall ℓ ψ₀) φ := by
  intro i c hst _
  simp [evenState] at hst

/-- The even boundary match at the state of `ψ₀` holds exactly on
the fibre of `ψ₀`. -/
theorem genEvenBoundaryMatch_evenState_iff (hall : F.allInternal)
    {k ℓ : ℕ} (ψ₀ ψ : F.EvenColouring k) :
    genEvenBoundaryMatch F (evenState hall ℓ ψ₀)
        (evenState_matches hall ℓ ψ₀) ψ ↔
      evenState hall ℓ ψ = evenState hall ℓ ψ₀ := by
  constructor
  · intro hm
    funext i
    exact congrArg Sum.inl (hm i (ψ₀.val ⟨W.boundaryFlag i,
      boundaryFlag_notMem_of_allInternal hall i⟩) rfl)
  · intro he i c hst
    exact Sum.inl.inj ((congrFun he i).trans hst)

/-! ## The colouring equivalence -/

/-- On an all-internal subset, the core odd colouring type is
equivalent to the full odd colouring type, via
`coreFlags = flags`. -/
noncomputable def coreOddEquivAll (hall : F.allInternal) (ℓ : ℕ) :
    F.CoreOddColouring ℓ ≃ F.OddColouring ℓ where
  toFun φ :=
    ⟨fun f => φ.val ⟨f.val,
        (coreFlags_eq_flags_of_allInternal hall).symm ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val,
         (coreFlags_eq_flags_of_allInternal hall).symm ▸ f.prop⟩)⟩
  invFun φ :=
    ⟨fun f => φ.val ⟨f.val,
        coreFlags_eq_flags_of_allInternal hall ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val,
         coreFlags_eq_flags_of_allInternal hall ▸ f.prop⟩)⟩
  left_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))
  right_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))

/-! ## Vertex-local data agreement -/

/-- On an all-internal subset, the core odd pairs along a list are
the odd pairs of the transported colouring. -/
private theorem flatMap_coreOddPairFn_allInternal (hall : F.allInternal)
    {ℓ : ℕ} (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ) :
    ∀ (l : List W.Flag)
      (h1 : ∀ f ∈ l, f ∈ F.internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.flags),
      (l.attachWith (· ∈ F.internalFlags) h1).flatMap
        (F.coreOddPairFn κ.toRelTransitionSystem φ_core) =
      (l.attachWith (· ∈ F.flags) h2).flatMap
        (F.oddPairFn κ (coreOddEquivAll hall ℓ φ_core))
  | [], _, _ => rfl
  | a :: as, h1, h2 => by
    rw [List.attachWith_cons, List.attachWith_cons,
      List.flatMap_cons, List.flatMap_cons]
    rw [flatMap_coreOddPairFn_allInternal hall κ φ_core as
      (fun f hf => h1 f (List.mem_cons_of_mem a hf))
      (fun f hf => h2 f (List.mem_cons_of_mem a hf))]
    rfl

/-- On an all-internal subset, the core odd signs along a list are
the odd signs of the transported colouring. -/
private theorem map_coreOddSignFn_allInternal (hall : F.allInternal)
    {ℓ : ℕ} (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ) :
    ∀ (l : List W.Flag)
      (h1 : ∀ f ∈ l, f ∈ F.internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.flags),
      (l.attachWith (· ∈ F.internalFlags) h1).map
        (F.coreOddSignFn κ.toRelTransitionSystem φ_core) =
      (l.attachWith (· ∈ F.flags) h2).map
        (F.oddSignFn κ (coreOddEquivAll hall ℓ φ_core))
  | [], _, _ => rfl
  | a :: as, h1, h2 => by
    rw [List.attachWith_cons, List.attachWith_cons,
      List.map_cons, List.map_cons]
    rw [map_coreOddSignFn_allInternal hall κ φ_core as
      (fun f hf => h1 f (List.mem_cons_of_mem a hf))
      (fun f hf => h2 f (List.mem_cons_of_mem a hf))]
    rfl

/-- `coreOddListAt` at `φ_core` agrees with `oddListAt` at
`coreOddEquivAll φ_core`. -/
theorem coreOddListAt_eq_of_allInternal (hall : F.allInternal)
    {ℓ : ℕ} {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ_core : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddListAt o.toRel φ_core v =
    F.oddListAt o (coreOddEquivAll hall ℓ φ_core) v := by
  unfold coreOddListAt oddListAt
  change ((F.inFlagsAt o v).attachWith (· ∈ F.internalFlags)
      _).flatMap _ =
    ((F.inFlagsAt o v).attachWith (· ∈ F.flags) _).flatMap _
  exact flatMap_coreOddPairFn_allInternal hall κ φ_core
    (F.inFlagsAt o v) _ _

/-- `coreOddSignAt` at `φ_core` agrees with `oddSignAt` at
`coreOddEquivAll φ_core`. -/
theorem coreOddSignAt_eq_of_allInternal (hall : F.allInternal)
    {ℓ : ℕ} {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ_core : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o.toRel φ_core v =
    F.oddSignAt o (coreOddEquivAll hall ℓ φ_core) v := by
  unfold coreOddSignAt oddSignAt
  change (((F.inFlagsAt o v).attachWith (· ∈ F.internalFlags)
      _).map _).prod =
    (((F.inFlagsAt o v).attachWith (· ∈ F.flags) _).map _).prod
  exact congrArg List.prod
    (map_coreOddSignFn_allInternal hall κ φ_core
      (F.inFlagsAt o v) _ _)

/-! ## Circuit count agreement -/

/-- The open circuit count of a standard transition system's
relative system equals the standard circuit count. -/
theorem openCircuitCount_toRel (κ : F.TransitionSystem) :
    κ.toRelTransitionSystem.openCircuitCount = κ.circuitCount := by
  rw [openCircuitCount_of_allInternal κ.toRelTransitionSystem
      (allInternal_of_transition κ),
    relTransition_circuitCount_eq κ]

/-! ## The through summand at an even state -/

/-- **Fibre bridge**: the through summand at the state of `ψ₀`
equals the circuit-signed colouring sum over the fibre of `ψ₀`. -/
theorem throughSummand_evenState [LinearOrder α]
    (hall : F.allInternal) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (ψ₀ : F.EvenColouring k) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    F.throughSummand h (evenState hall ℓ ψ₀)
        (evenState_matches hall ℓ ψ₀) o.toRel
        κ.toRelTransitionSystem.openCircuitCount =
      ((-1 : ℂ) ^ κ.circuitCount) *
        ∑ ψ : F.EvenColouring k,
          if evenState hall ℓ ψ = evenState hall ℓ ψ₀ then
            ∑ φ : F.OddColouring ℓ,
              ∏ v : W.Vertex,
                ((F.oddSignAt o φ v : ℂ) *
                  h.evalOdd (F.evenColoursAt ψ v)
                    (F.oddListAt o φ v))
          else 0 := by
  unfold EdgeSubset.throughSummand
  rw [openCircuitCount_toRel κ,
    throughProduct_one_of_allInternal hall (evenState hall ℓ ψ₀),
    mul_one]
  congr 1
  refine Finset.sum_congr rfl fun ψ _ => ?_
  by_cases hm : genEvenBoundaryMatch F (evenState hall ℓ ψ₀)
      (evenState_matches hall ℓ ψ₀) ψ
  · rw [ite_eq_left hm,
      ite_eq_left ((genEvenBoundaryMatch_evenState_iff hall ψ₀ ψ).mp hm)]
    refine Fintype.sum_equiv (coreOddEquivAll hall ℓ)
      (fun φ_core =>
        if F.coreOddBoundaryMatch (evenState hall ℓ ψ₀) φ_core then
          ∏ v : W.Vertex,
            ((F.coreOddSignAt o.toRel φ_core v : ℂ) *
              h.evalOdd (F.evenColoursAt ψ v)
                (F.coreOddListAt o.toRel φ_core v))
        else (0 : ℂ))
      (fun φ =>
        ∏ v : W.Vertex,
          ((F.oddSignAt o φ v : ℂ) *
            h.evalOdd (F.evenColoursAt ψ v)
              (F.oddListAt o φ v)))
      (fun φ_core => ?_)
    rw [ite_eq_left (coreOddBoundaryMatch_evenState hall ψ₀ φ_core)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [coreOddSignAt_eq_of_allInternal hall o φ_core v,
      coreOddListAt_eq_of_allInternal hall o φ_core v]
  · rw [ite_eq_right hm, ite_eq_right (fun he => hm
      ((genEvenBoundaryMatch_evenState_iff hall ψ₀ ψ).mpr he))]

/-! ## The fibre decomposition of the mixed summand -/

/-- **Fibre decomposition**: the mixed summand is the sum over the
realized boundary states of the fibre sums. -/
theorem mixedSummand_eq_fibre_sum (hall : F.allInternal)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    F.mixedSummand h o =
      ∑ st ∈ Finset.univ.image (evenState hall ℓ),
        ((-1 : ℂ) ^ κ.circuitCount) *
          ∑ ψ : F.EvenColouring k,
            if evenState hall ℓ ψ = st then
              ∑ φ : F.OddColouring ℓ,
                ∏ v : W.Vertex,
                  ((F.oddSignAt o φ v : ℂ) *
                    h.evalOdd (F.evenColoursAt ψ v)
                      (F.oddListAt o φ v))
            else 0 := by
  unfold EdgeSubset.mixedSummand
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun ψ _ => Finset.mem_image_of_mem (evenState hall ℓ)
      (Finset.mem_univ ψ))
    (fun ψ : F.EvenColouring k =>
      ∑ φ : F.OddColouring ℓ,
        ∏ v : W.Vertex,
          ((F.oddSignAt o φ v : ℂ) *
            h.evalOdd (F.evenColoursAt ψ v)
              (F.oddListAt o φ v)))]
  exact Finset.sum_congr rfl fun st _ => Finset.sum_filter _ _

end EdgeSubset

/-! ## The Eulerian-independence interface, proved -/

/-- **Eulerian independence** (Regts–Sevenster arXiv:1807.04494,
Proposition 3, as a theorem): the Definition 5 mixed summand of an
edge subset does not depend on the choice of transition system and
orientation. -/
theorem eulerianIndependence : EulerianIndependence := by
  intro α W F k ℓ h κ κ' o o'
  let : LinearOrder α := IsWellOrder.linearOrder WellOrderingRel
  have hall : F.allInternal := EdgeSubset.allInternal_of_transition κ
  rw [EdgeSubset.mixedSummand_eq_fibre_sum hall h o,
    EdgeSubset.mixedSummand_eq_fibre_sum hall h o']
  refine Finset.sum_congr rfl fun st hst => ?_
  obtain ⟨ψ₀, -, rfl⟩ := Finset.mem_image.mp hst
  rw [← EdgeSubset.throughSummand_evenState hall h ψ₀ o,
    ← EdgeSubset.throughSummand_evenState hall h ψ₀ o']
  exact EdgeSubset.throughSummand_independence_of_allInternal hall h
    (EdgeSubset.evenState hall ℓ ψ₀)
    (EdgeSubset.evenState_matches hall ℓ ψ₀)
    κ.toRelTransitionSystem κ'.toRelTransitionSystem
    o.toRel o'.toRel

end RS
