/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.Closures
public import LeanPool.MisereGames.Misere.Hereditary.MaintenanceProviso
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.Directed

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

/-- A universe is closed under addition, options, negation, and dicotic construction. -/
class Universe (IsAmbient : G → Prop) (A : G → Prop) extends
    ClosedUnderAdd A, Hereditary A, ClosedUnderNeg A, ClosedUnderDicotic IsAmbient A where
  zero_mem : A 0
  isAmbient_of_mem {g : G} : A g → IsAmbient g

/-- A universe in the long ambient space. -/
class LongUniverse (A : G → Prop) extends Universe IsLong A

/-- A universe in the short ambient space. -/
class ShortUniverse (A : G → Prop) extends Universe IsShort A

instance : LongUniverse (IsLong : G → Prop) where
  has_add _ _ _ _ := isLong _
  has_option _ _ := isLong _
  neg_of _ := isLong _
  closed_dicotic _ _ _ _ _ _ _ _ _ := isLong _
  zero_mem := isLong _
  isAmbient_of_mem _ := isLong _

instance : ShortUniverse (IsShort (G := G)) where
  zero_mem := Short.zero
  isAmbient_of_mem := id

namespace Universe

omit [Form G] in
private theorem sInf_mem_of_forall_mem {IsAmbient : G → Prop} {S : Set (Set.Iic IsAmbient)}
    {g : G} (hAmbient : IsAmbient g) (hS : ∀ A ∈ S, A.1 g) :
    ((sInf S : Set.Iic IsAmbient) : G → Prop) g := by
  rw [Set.Iic.coe_sInf, Pi.inf_apply]
  refine ⟨hAmbient, ?_⟩
  simp only [sInf_apply, iInf_Prop_eq]
  rintro ⟨_, A, hAS, hA⟩
  exact hA ▸ hS A hAS

omit [Form G] in
private theorem mem_of_sInf_mem {IsAmbient : G → Prop} {S : Set (Set.Iic IsAmbient)}
    {A : Set.Iic IsAmbient} (hAS : A ∈ S) {g : G}
    (hg : ((sInf S : Set.Iic IsAmbient) : G → Prop) g) : A.1 g := by
  rw [Set.Iic.coe_sInf, Pi.inf_apply] at hg
  have hg' : sInf (Subtype.val '' S) g := hg.2
  simp only [sInf_apply, iInf_Prop_eq] at hg'
  exact hg' ⟨(A : G → Prop), A, hAS, rfl⟩

/--
An intersection of universes is a universe.
-/
theorem sInf_closed (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {S : Set (Set.Iic IsAmbient)}
    (hS : ∀ A ∈ S, Universe IsAmbient (A : G → Prop)) :
    Universe IsAmbient ((sInf S : Set.Iic IsAmbient) : G → Prop) where
  has_add g h hg hh := by
    refine sInf_mem_of_forall_mem
      (ClosedUnderAdd.has_add g h ((sInf S).2 g hg) ((sInf S).2 h hh)) ?_
    intro U hUS
    haveI : Universe IsAmbient (U : G → Prop) := hS U hUS
    exact ClosedUnderAdd.has_add g h (mem_of_sInf_mem hUS hg) (mem_of_sInf_mem hUS hh)
  has_option hg h := by
    refine sInf_mem_of_forall_mem (Hereditary.has_option ((sInf S).2 _ hg) h) ?_
    intro U hUS
    haveI : Universe IsAmbient (U : G → Prop) := hS U hUS
    exact Hereditary.has_option (mem_of_sInf_mem hUS hg) h
  neg_of hg := by
    refine sInf_mem_of_forall_mem (ClosedUnderNeg.neg_of ((sInf S).2 _ hg)) ?_
    intro U hUS
    haveI : Universe IsAmbient (U : G → Prop) := hS U hUS
    exact ClosedUnderNeg.neg_of (mem_of_sInf_mem hUS hg)
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    refine sInf_mem_of_forall_mem hAmbient ?_
    intro U hUS
    haveI : Universe IsAmbient (U : G → Prop) := hS U hUS
    exact ClosedUnderDicotic.closed_dicotic B C
      (fun b hb => mem_of_sInf_mem hUS (hB b hb))
      (fun c hc => mem_of_sInf_mem hUS (hC c hc)) hBne hCne hAmbient
  zero_mem := by
    refine sInf_mem_of_forall_mem (Universe.zero_mem IsAmbient (A := IsAmbient)) ?_
    intro U hUS
    haveI : Universe IsAmbient (U : G → Prop) := hS U hUS
    exact Universe.zero_mem IsAmbient (A := (U : G → Prop))
  isAmbient_of_mem hg :=
    (sInf S).2 _ hg

/--
The closure operator for finding the universal closure of a given set (in the
context of a given ambient).
Sends a bounded predicate to the smallest `Universe IsAmbient` containing it.
-/
noncomputable abbrev closureOperator (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient] :
    ClosureOperator (Set.Iic IsAmbient) :=
  ClosureOperator.ofCompletePred
    (fun A : Set.Iic IsAmbient => Universe IsAmbient (A : G → Prop)) fun _ hS =>
      sInf_closed IsAmbient hS

/--
The universal closure of a given set (within the context of a given ambient).
-/
noncomputable abbrev closureBounded (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    (A : Set.Iic IsAmbient) : Set.Iic IsAmbient :=
  closureOperator IsAmbient A

/--
The universal closure of a given set (within the context of a given ambient).
-/
noncomputable abbrev closure (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    (A : G → Prop) (hA : A ≤ IsAmbient) : G → Prop :=
  closureBounded IsAmbient ⟨A, hA⟩

theorem subset_closure (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A : G → Prop} (hA : A ≤ IsAmbient) : A ≤ closure IsAmbient A hA :=
  (closureOperator IsAmbient).le_closure ⟨A, hA⟩

theorem mem_closure_of_mem (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A : G → Prop} {g : G} (hA : A ≤ IsAmbient) (hg : A g) : closure IsAmbient A hA g :=
  subset_closure IsAmbient hA g hg

theorem closure_le_ambient (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A : G → Prop} (hA : A ≤ IsAmbient) : closure IsAmbient A hA ≤ IsAmbient :=
  (closureBounded IsAmbient ⟨A, hA⟩).2

instance closure_universe (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A : G → Prop} (hA : A ≤ IsAmbient) : Universe IsAmbient (closure IsAmbient A hA) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator IsAmbient).isClosed_closure ⟨A, hA⟩

theorem closure_min (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A B : G → Prop} (hA : A ≤ IsAmbient) (hAB : A ≤ B) [Universe IsAmbient B] :
    closure IsAmbient A hA ≤ B :=
  ClosureOperator.closure_min (c := closureOperator IsAmbient)
    (x := ⟨A, hA⟩)
    (y := ⟨B, fun _ => Universe.isAmbient_of_mem⟩)
    hAB (by
      simpa only [ClosureOperator.ofCompletePred_isClosed] using
        (inferInstance : Universe IsAmbient B))

theorem closure_le (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A B : G → Prop} (hA : A ≤ IsAmbient) [Universe IsAmbient B] :
    closure IsAmbient A hA ≤ B ↔ A ≤ B :=
  ⟨(subset_closure IsAmbient hA).trans, fun hAB => closure_min IsAmbient hA hAB⟩

theorem closure_mono (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient]
    {A B : G → Prop} {hA : A ≤ IsAmbient} {hB : B ≤ IsAmbient} (hAB : A ≤ B) :
    closure IsAmbient A hA ≤ closure IsAmbient B hB :=
  (closure_le IsAmbient hA).mpr (hAB.trans (subset_closure IsAmbient hB))

/--
The intersection of universes is a universe, with ambient space the
intersection of the ambient spaces.
-/
theorem iInter {ι : Sort*} (IsAmbient A : ι → G → Prop)
    [∀ i, Universe (IsAmbient i) (A i)] :
    Universe (fun g => ∀ i, IsAmbient i g) (fun g => ∀ i, A i g) where
  has_add g h hg hh i :=
    ClosedUnderAdd.has_add g h (hg i) (hh i)
  has_option hg h i :=
    Hereditary.has_option (hg i) h
  neg_of hg i :=
    ClosedUnderNeg.neg_of (hg i)
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient i :=
    ClosedUnderDicotic.closed_dicotic B C
      (fun b hb => hB b hb i) (fun c hc => hC c hc i) hBne hCne (hAmbient i)
  zero_mem i :=
    Universe.zero_mem (IsAmbient i) (A := A i)
  isAmbient_of_mem hg i :=
    Universe.isAmbient_of_mem (hg i)

/--
The union of a nonempty directed family of universes is a universe, with
ambient space the union of the ambient spaces.

The directedness is componentwise on the family of ordered pairs `(A i,
IsAmbient i)`. We require the hypothesis that, if the Left and Right options
lie in the union, and the form from dicotic closure lies in the union of the
ambient spaces, then there exists a universe containing all of the options, and
whose ambient space contains the relevant form. This extra hypothesis supplies
the common index needed for dicotic closure.
-/
theorem iUnion_of_directed {ι : Sort*} [Nonempty ι] (IsAmbient A : ι → G → Prop)
    [∀ i, Universe (IsAmbient i) (A i)]
    (h_directed : Directed
      (r := fun P Q : (G → Prop) × (G → Prop) => P.1 ≤ Q.1 ∧ P.2 ≤ Q.2)
      (fun i => (A i, IsAmbient i)))
    (h_options : ∀ (B C : Set G) [Small B] [Small C],
      (∀ b ∈ B, ∃ i, A i b) → (∀ c ∈ C, ∃ i, A i c) →
      B.Nonempty → C.Nonempty → (∃ i, IsAmbient i (!{B | C} : G)) →
      ∃ i, (∀ b ∈ B, A i b) ∧ (∀ c ∈ C, A i c) ∧ IsAmbient i (!{B | C} : G)) :
    Universe (fun g => ∃ i, IsAmbient i g) (fun g => ∃ i, A i g) where
  has_add g h hg hh := by
    obtain ⟨i, hi⟩ := hg
    obtain ⟨j, hj⟩ := hh
    obtain ⟨k, hik, hjk⟩ := h_directed i j
    exact ⟨k, ClosedUnderAdd.has_add g h (hik.1 g hi) (hjk.1 h hj)⟩
  has_option hg h := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Hereditary.has_option hi h⟩
  neg_of hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, ClosedUnderNeg.neg_of hi⟩
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    obtain ⟨i, hBi, hCi, hAmbienti⟩ := h_options B C hB hC hBne hCne hAmbient
    exact ⟨i, ClosedUnderDicotic.closed_dicotic B C hBi hCi hBne hCne hAmbienti⟩
  zero_mem := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Universe.zero_mem (IsAmbient i) (A := A i)⟩
  isAmbient_of_mem hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Universe.isAmbient_of_mem hi⟩

/--
A specialised version of `Universe.iUnion_of_directed` in which every universe
has the same ambient space.
-/
theorem iUnion_of_directed_of_fixed_ambient {ι : Sort*} [Nonempty ι]
    (IsAmbient : G → Prop) (A : ι → G → Prop) [∀ i, Universe IsAmbient (A i)]
    (h_directed : Directed (r := (· ≤ ·)) A)
    (h_options : ∀ (B C : Set G) [Small B] [Small C],
      (∀ b ∈ B, ∃ i, A i b) → (∀ c ∈ C, ∃ i, A i c) →
      B.Nonempty → C.Nonempty → IsAmbient (!{B | C} : G) →
      ∃ i, (∀ b ∈ B, A i b) ∧ (∀ c ∈ C, A i c)) :
    Universe IsAmbient (fun g => ∃ i, A i g) where
  has_add g h hg hh := by
    obtain ⟨i, hi⟩ := hg
    obtain ⟨j, hj⟩ := hh
    obtain ⟨k, hik, hjk⟩ := h_directed i j
    exact ⟨k, ClosedUnderAdd.has_add g h (hik g hi) (hjk h hj)⟩
  has_option hg h := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, Hereditary.has_option hi h⟩
  neg_of hg := by
    obtain ⟨i, hi⟩ := hg
    exact ⟨i, ClosedUnderNeg.neg_of hi⟩
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    obtain ⟨i, hBi, hCi⟩ := h_options B C hB hC hBne hCne hAmbient
    exact ⟨i, ClosedUnderDicotic.closed_dicotic B C hBi hCi hBne hCne hAmbient⟩
  zero_mem := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Universe.zero_mem IsAmbient (A := A i)⟩
  isAmbient_of_mem hg := by
    obtain ⟨i, hi⟩ := hg
    exact Universe.isAmbient_of_mem hi

omit [Form G] in
private theorem exists_directed_upper_of_finite {ι : Sort*} [Nonempty ι] (A : ι → G → Prop)
    (h_directed : Directed (r := (· ≤ ·)) A)
    {S : Set G} (hS : S.Finite) (h_mem : ∀ g ∈ S, ∃ i, A i g) :
    ∃ i, ∀ g ∈ S, A i g := by
  obtain ⟨T, ⟨i, rfl⟩, hST⟩ :=
    h_directed.directedOn_range.exists_mem_subset_of_finite_of_subset_sUnion
      (Set.range_nonempty A) hS (fun g hg => by
        obtain ⟨i, hi⟩ := h_mem g hg
        exact Set.mem_sUnion_of_mem hi (Set.mem_range_self i))
  exact ⟨i, hST⟩

end Universe

namespace LongUniverse

/--
The smallest long universe containing `A`.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  Universe.closure IsLong A (fun _ _ => isLong _)

instance closure_universe (A : G → Prop) : LongUniverse (closure A) where
  toUniverse :=
    Universe.closure_universe IsLong (A := A) (fun _ _ => isLong _)

theorem closure_le {A B : G → Prop} [LongUniverse B] : closure A ≤ B ↔ A ≤ B :=
  Universe.closure_le IsLong (fun _ _ => isLong _)

end LongUniverse

namespace ShortUniverse

/--
The smallest short universe containing `A`.
-/
noncomputable abbrev closure (A : G → Prop) (hA : A ≤ IsShort) : G → Prop :=
  Universe.closure (IsShort (G := G)) A hA

instance closure_universe {A : G → Prop} (hA : A ≤ IsShort) :
    ShortUniverse (closure A hA) where
  toUniverse :=
    Universe.closure_universe (IsShort (G := G)) hA

theorem closure_le {A B : G → Prop} (hA : A ≤ IsShort) [ShortUniverse B] :
    closure A hA ≤ B ↔ A ≤ B :=
  Universe.closure_le (IsShort (G := G)) hA

/--
The union of a nonempty directed family of short universes is a short universe.
-/
theorem iUnion_of_directed {ι : Sort*} [Nonempty ι] (A : ι → G → Prop)
    [∀ i, ShortUniverse (A i)]
    (h_directed : Directed (r := (· ≤ ·)) A) :
    ShortUniverse (fun g => ∃ i, A i g) where
  toUniverse :=
    Universe.iUnion_of_directed_of_fixed_ambient IsShort A h_directed
      (fun B C _ _ hB hC _ _ hShort => by
        have hBfin : B.Finite := by
          simpa [Form.moves_ofSets] using Short.finite_moves Player.left hShort
        have hCfin : C.Finite := by
          simpa [Form.moves_ofSets] using Short.finite_moves Player.right hShort
        obtain ⟨i, hi⟩ := Universe.exists_directed_upper_of_finite A h_directed hBfin hB
        obtain ⟨j, hj⟩ := Universe.exists_directed_upper_of_finite A h_directed hCfin hC
        obtain ⟨k, hik, hjk⟩ := h_directed i j
        exact ⟨k, fun b hb => hik b (hi b hb), fun c hc => hjk c (hj c hc)⟩)

end ShortUniverse

end

end MisereGames
