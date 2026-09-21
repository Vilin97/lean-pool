/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Basic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Division
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ConvexQuotient
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ArchimedeanQuotient
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.CoinitialComplete

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The surreals fill cuts between small families

Between any two small families of surreals separated by the order there is a surreal, namely the
one born from those families as its option sets. This is the simplicity theorem in the form the
completeness criterion of `ConwayRefinement.Topology.Order.CoinitialComplete`
consumes, and it is restricted to *small* families for the reason that makes the restriction
essential rather than
technical: a surreal has a set of options, so no construction reaches across a family the size of
the ordinals.

That restriction is exactly why the surreals themselves are not Cauchy complete — the positive
surreals have no small coinitial family, so a Cauchy filter can outrun every small cut — and why
the route to a complete group runs through a quotient. `FillsCuts.of_surjective` carries the
conclusion below to such a quotient; supplying the small coinitial family there is separate work.
-/

universe u

public section

namespace Surreal

/-- **The simplicity theorem for small cuts.** Two small sets of surreals with every member of the
first below every member of the second are strictly separated by a surreal. -/
@[blueprint "thm:surreal-simplicity-small-cuts"
  (phase := "Surreal numbers and omnific integers")
  (title := "The simplicity theorem for small cuts")
  (statement := /--
    Let $L,R\subseteq\mathbf{No}_u$ be small sets.  If $l<r$ for every
    $l\in L$ and $r\in R$, then there is $x\in\mathbf{No}_u$ such
    that
    \[
      l<x<r
    \]
    for every $l\in L$ and $r\in R$.
  -/)
  (proof := /--
    Form the surreal $\{L\mid R\}$.  The separation hypothesis makes this a
    valid Conway cut, and the simplicity theorem places it strictly above
    every left option and strictly below every right option.  Smallness keeps
    both option sets in the same universe.
  -/)]
theorem exists_between_small_sets (L R : Set Surreal.{u})
    [Small.{u} L] [Small.{u} R] (hLR : ∀ l ∈ L, ∀ r ∈ R, l < r) :
    ∃ x : Surreal.{u}, (∀ l ∈ L, l < x) ∧ ∀ r ∈ R, x < r :=
  ⟨!{L | R}, fun _ hl ↦ lt_ofSets_of_mem_left (H := hLR) hl,
    fun _ hr ↦ ofSets_lt_of_mem_right (H := hLR) hr⟩

/-- Small families separated by the surreal order satisfy the weak cut-filling property. -/
theorem fillsCuts {ι : Type u} [Small.{u} ι] : FillsCuts ι Surreal.{u} := by
  rw [fillsCuts_iff]
  intro L R hLR
  have hsep : ∀ x ∈ Set.range L, ∀ y ∈ Set.range R, x < y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hLR i j
  obtain ⟨x, hxL, hxR⟩ := exists_between_small_sets (Set.range L) (Set.range R) hsep
  exact ⟨x, fun i ↦ (hxL _ ⟨i, rfl⟩).le, fun j ↦ (hxR _ ⟨j, rfl⟩).le⟩

/-- **A convex quotient of the surreals fills cuts.** The projection is monotone and reflects the
strict order, so cut filling descends from the surreals to the quotient — where, unlike in the
surreals themselves, a small coinitial family of positive elements can exist. -/
theorem fillsCuts_quotient {ι : Type u} [Small.{u} ι] (H : AddSubgroup Surreal.{u}) [H.IsConvex] :
    FillsCuts ι (Surreal.{u} ⧸ H) :=
  FillsCuts.of_surjective (QuotientAddGroup.mk_surjective (s := H))
    (fun _ _ h ↦ ConvexQuotient.mk_le_mk h) (fun _ _ h ↦ ConvexQuotient.lt_of_mk_lt_mk h)
    Surreal.fillsCuts

/-- **A convex quotient of the surreals with a small coinitial family is Cauchy complete.** All
three inputs of the completeness criterion are now in hand: cut filling descends from the simplicity
theorem, halving descends from division in the surreals, and the coinitial family is what the
quotient is taken to obtain.

The uniform structure is the one the order topology induces on the quotient; it is left as a
hypothesis so that no instance is imposed on `Surreal ⧸ H` here. -/
theorem completeSpace_quotient {ι : Type u} [Small.{u} ι] [Nonempty ι]
    (H : AddSubgroup Surreal.{u}) [H.IsConvex]
    [UniformSpace (Surreal.{u} ⧸ H)] [IsUniformAddGroup (Surreal.{u} ⧸ H)]
    [OrderTopology (Surreal.{u} ⧸ H)]
    (ε : ι → Surreal.{u} ⧸ H) (hε : ∀ i, 0 < ε i)
    (hcoinitial : ∀ c : Surreal.{u} ⧸ H, 0 < c → ∃ i, ε i ≤ c) :
    CompleteSpace (Surreal.{u} ⧸ H) :=
  completeSpace_of_coinitial_of_exists_half ε hε hcoinitial
    (fun _ hc ↦ ConvexQuotient.exists_half_of_pos
      (fun x hx ↦ ⟨x / 2, half_pos hx, add_halves x⟩) hc)
    (Surreal.fillsCuts_quotient H)

/-- **Cauchy completeness at a limit of Archimedean classes.** If a small nonempty family of finite
Archimedean classes has no least member in the magnitude order, quotienting the surreals by their
common closed-ball tail is Cauchy complete. The canonical positive representatives of the classes
form the required coinitial family in the quotient. -/
theorem completeSpace_tailQuotient
    (T : Set (FiniteArchimedeanClass Surreal.{u})) [Small.{u} T] [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [UniformSpace (Surreal.{u} ⧸ FiniteArchimedeanClass.tailKernel T)]
    [IsUniformAddGroup (Surreal.{u} ⧸ FiniteArchimedeanClass.tailKernel T)]
    [OrderTopology (Surreal.{u} ⧸ FiniteArchimedeanClass.tailKernel T)] :
    CompleteSpace (Surreal.{u} ⧸ FiniteArchimedeanClass.tailKernel T) := by
  letI : Nonempty (Shrink.{u} T) :=
    ⟨equivShrink T (Classical.arbitrary T)⟩
  exact completeSpace_quotient (FiniteArchimedeanClass.tailKernel T)
    (fun i : Shrink.{u} T ↦
      (FiniteArchimedeanClass.positiveRepresentative ((equivShrink T).symm i).1 : Surreal))
    (fun i ↦ FiniteArchimedeanClass.quotient_positiveRepresentative_pos hT
      ((equivShrink T).symm i))
    (fun _ hx ↦ by
      obtain ⟨c, hc⟩ := FiniteArchimedeanClass.exists_quotient_positiveRepresentative_le hx
      exact ⟨equivShrink T c, by simpa using hc⟩)

end Surreal
