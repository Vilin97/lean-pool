/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathCanon
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence

/-!
# Closed-fragment agreement: throughMixedPartitionAt = mixedPartition

For a closed fragment (`Fragment (Fin 0)`), every quantifier
`∀ i : Fin 0, ...` is vacuously true.  This makes the through-edge
corrections trivial — there are no boundary flags, so
`throughFlags = ∅`, `coreFlags = flags`, `throughProduct = 1`, and
the boundary-match conditions all hold vacuously.  The corrected
constrained partition value therefore equals the unconstrained
Definition 5 value.

This is the base case of the converse's factorization induction.
-/

@[expose] public section

namespace RS



variable {W : ClosedFragment}

/-! ## Vacuous boundary conditions on closed fragments -/

/-- On a closed fragment, no flag is boundary-attached. -/
theorem EdgeSubset.allInternal_of_closed (F : EdgeSubset W) :
    F.allInternal := by
  change F.boundaryFlags = ∅
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  exact Fin.elim0 (F.attach_boundary_of_mem hf).choose

/-- On a closed fragment, the core flags equal the full flags. -/
theorem EdgeSubset.coreFlags_eq_flags (F : EdgeSubset W) :
    F.coreFlags = F.flags := by
  ext f
  rw [F.mem_coreFlags_iff]
  exact ⟨fun ⟨hf, _⟩ => hf, fun hf => ⟨hf, Or.inl (by
    rcases ha : W.attach f with v | i
    · exact ⟨v, rfl⟩
    · exact Fin.elim0 i)⟩⟩

/-- On a closed fragment, the through product is 1: each
through-flag's factor is 1 because `W.attach f` always lands in
`Sum.inl`. -/
theorem EdgeSubset.throughProduct_one [LinearOrder (Fin 0)]
    (F : EdgeSubset W) {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (Fin 0)) :
    F.throughProduct st = 1 := by
  unfold EdgeSubset.throughProduct
  apply Finset.prod_eq_one
  intro ⟨f, _⟩ _
  rcases ha : W.attach f with v | i
  · rcases hb : W.attach (W.pairing f) with w | j
    · rfl
    · exact Fin.elim0 j
  · exact Fin.elim0 i

/-- On a closed fragment, every even colouring satisfies the
even boundary match. -/
theorem genEvenBoundaryMatch_closed (F : EdgeSubset W)
    {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (Fin 0))
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (ψ : F.EvenColouring k) :
    genEvenBoundaryMatch F st hbnd ψ :=
  fun i => Fin.elim0 i

/-- On a closed fragment, every core odd colouring satisfies the
core odd boundary match. -/
theorem EdgeSubset.coreOddBoundaryMatch_closed (F : EdgeSubset W)
    {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ (Fin 0))
    (φ : F.CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st φ :=
  fun i => Fin.elim0 i

/-! ## The colouring equivalence -/

/-- On a closed fragment, the core odd colouring type is equivalent
to the full odd colouring type, via `coreFlags = flags`. -/
noncomputable def EdgeSubset.coreOddEquiv (F : EdgeSubset W) (ℓ : ℕ) :
    F.CoreOddColouring ℓ ≃ F.OddColouring ℓ where
  toFun φ :=
    ⟨fun f => φ.val ⟨f.val,
        F.coreFlags_eq_flags.symm ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val, F.coreFlags_eq_flags.symm ▸ f.prop⟩)⟩
  invFun φ :=
    ⟨fun f => φ.val ⟨f.val,
        F.coreFlags_eq_flags ▸ f.prop⟩,
     fun f => (congrArg φ.val (Subtype.ext rfl)).trans
       (φ.prop ⟨f.val, F.coreFlags_eq_flags ▸ f.prop⟩)⟩
  left_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))
  right_inv φ := Subtype.ext (funext fun _ =>
    congrArg φ.val (Subtype.ext rfl))

/-! ## Vertex-local data agreement -/

/-- On a closed fragment, `coreOddPairFn` at `φ_core` agrees with
`oddPairFn` at `coreOddEquiv φ_core`. -/
theorem EdgeSubset.coreOddPairFn_eq (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddPairFn κ.toRelTransitionSystem φ_core f =
    F.oddPairFn κ (F.coreOddEquiv ℓ φ_core)
      ⟨f.val, mem_flags_of_internalFlags F f.prop⟩ := by
  unfold coreOddPairFn oddPairFn coreOddEquiv
  rfl

/-- On a closed fragment, `coreOddSignFn` at `φ_core` agrees with
`oddSignFn` at `coreOddEquiv φ_core`. -/
theorem EdgeSubset.coreOddSignFn_eq (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddSignFn κ.toRelTransitionSystem φ_core f =
    F.oddSignFn κ (F.coreOddEquiv ℓ φ_core)
      ⟨f.val, mem_flags_of_internalFlags F f.prop⟩ := by
  unfold coreOddSignFn oddSignFn coreOddEquiv
  rfl

/-- On a closed fragment, the core odd pairs along a list are the
odd pairs of the transported colouring. -/
private theorem flatMap_coreOddPairFn_closed
    {W : ClosedFragment} {F : EdgeSubset W} {ℓ : ℕ}
    (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ) :
    ∀ (l : List W.Flag)
      (h1 : ∀ f ∈ l, f ∈ F.internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.flags),
      (l.attachWith (· ∈ F.internalFlags) h1).flatMap
        (F.coreOddPairFn κ.toRelTransitionSystem φ_core) =
      (l.attachWith (· ∈ F.flags) h2).flatMap
        (F.oddPairFn κ (F.coreOddEquiv ℓ φ_core))
  | [], _, _ => rfl
  | a :: as, h1, h2 => by
    rw [List.attachWith_cons, List.attachWith_cons,
      List.flatMap_cons, List.flatMap_cons]
    rw [flatMap_coreOddPairFn_closed κ φ_core as
      (fun f hf => h1 f (List.mem_cons_of_mem a hf))
      (fun f hf => h2 f (List.mem_cons_of_mem a hf))]
    rfl

/-- On a closed fragment, the core odd signs along a list are the
odd signs of the transported colouring. -/
private theorem map_coreOddSignFn_closed
    {W : ClosedFragment} {F : EdgeSubset W} {ℓ : ℕ}
    (κ : F.TransitionSystem)
    (φ_core : F.CoreOddColouring ℓ) :
    ∀ (l : List W.Flag)
      (h1 : ∀ f ∈ l, f ∈ F.internalFlags)
      (h2 : ∀ f ∈ l, f ∈ F.flags),
      (l.attachWith (· ∈ F.internalFlags) h1).map
        (F.coreOddSignFn κ.toRelTransitionSystem φ_core) =
      (l.attachWith (· ∈ F.flags) h2).map
        (F.oddSignFn κ (F.coreOddEquiv ℓ φ_core))
  | [], _, _ => rfl
  | a :: as, h1, h2 => by
    rw [List.attachWith_cons, List.attachWith_cons,
      List.map_cons, List.map_cons]
    rw [map_coreOddSignFn_closed κ φ_core as
      (fun f hf => h1 f (List.mem_cons_of_mem a hf))
      (fun f hf => h2 f (List.mem_cons_of_mem a hf))]
    rfl

/-- On a closed fragment, `coreOddListAt` at `φ_core` agrees with
`oddListAt` at `coreOddEquiv φ_core`. -/
theorem EdgeSubset.coreOddListAt_eq (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ_core : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddListAt o.toRel φ_core v =
    F.oddListAt o (F.coreOddEquiv ℓ φ_core) v := by
  unfold coreOddListAt oddListAt
  -- relInFlagsAt o.toRel v = inFlagsAt o v  (by rfl from relInFlagsAt_toRel)
  change ((F.inFlagsAt o v).attachWith (· ∈ F.internalFlags)
      _).flatMap _ =
    ((F.inFlagsAt o v).attachWith (· ∈ F.flags) _).flatMap _
  exact flatMap_coreOddPairFn_closed κ φ_core (F.inFlagsAt o v) _ _

/-- On a closed fragment, `coreOddSignAt` at `φ_core` agrees with
`oddSignAt` at `coreOddEquiv φ_core`. -/
theorem EdgeSubset.coreOddSignAt_eq (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ_core : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o.toRel φ_core v =
    F.oddSignAt o (F.coreOddEquiv ℓ φ_core) v := by
  unfold coreOddSignAt oddSignAt
  change (((F.inFlagsAt o v).attachWith (· ∈ F.internalFlags)
      _).map _).prod =
    (((F.inFlagsAt o v).attachWith (· ∈ F.flags) _).map _).prod
  exact congrArg List.prod
    (map_coreOddSignFn_closed κ φ_core (F.inFlagsAt o v) _ _)

/-! ## Circuit count agreement -/

/-- On a closed fragment, the open circuit count of the relative
transition system equals the standard circuit count. -/
theorem EdgeSubset.openCircuitCount_eq_circuitCount (F : EdgeSubset W)
    (κ : F.TransitionSystem) :
    κ.toRelTransitionSystem.openCircuitCount = κ.circuitCount := by
  rw [openCircuitCount_of_allInternal κ.toRelTransitionSystem
        F.allInternal_of_closed,
    relTransition_circuitCount_eq κ]

/-! ## The per-subset summand agreement -/

/-- On a closed fragment, the through summand at an Eulerian
subset equals the standard mixed summand. -/
theorem EdgeSubset.throughSummand_eq_mixedSummand
    [LinearOrder (Fin 0)]
    (F : EdgeSubset W) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (Fin 0))
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    F.throughSummand h st hbnd o.toRel
      κ.toRelTransitionSystem.openCircuitCount =
    F.mixedSummand h o := by
  classical
  unfold EdgeSubset.throughSummand EdgeSubset.mixedSummand
  rw [F.openCircuitCount_eq_circuitCount κ]
  rw [F.throughProduct_one st]
  rw [mul_one]
  congr 1
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ite_eq_left (genEvenBoundaryMatch_closed F st hbnd ψ)]
  refine (Fintype.sum_equiv (F.coreOddEquiv ℓ)
    (fun φ_core =>
      if F.coreOddBoundaryMatch st φ_core then
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
    (fun φ_core => ?_))
  rw [ite_eq_left (F.coreOddBoundaryMatch_closed st φ_core)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [F.coreOddSignAt_eq o φ_core v,
    F.coreOddListAt_eq o φ_core v]

end RS
