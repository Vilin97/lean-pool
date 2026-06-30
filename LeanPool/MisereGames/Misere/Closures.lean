/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Form.Short
public import Mathlib.Order.Closure

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

/-- Closure under nonempty dicotic set construction inside an ambient predicate. -/
class ClosedUnderDicotic (IsAmbient : G → Prop) (A : G → Prop) where
  closed_dicotic (B C : Set G) [Small B] [Small C]
      (hB : ∀ b ∈ B, A b) (hC : ∀ c ∈ C, A c) :
    B.Nonempty → C.Nonempty → IsAmbient (!{B | C} : G) → A (!{B | C} : G)

/-- Closure under nonempty dicotic construction in the long ambient space. -/
abbrev ClosedUnderLongDicotic (A : G → Prop) :=
  ClosedUnderDicotic IsLong A

/-- Closure under nonempty dicotic construction in the short ambient space. -/
abbrev ClosedUnderShortDicotic (A : G → Prop) :=
  ClosedUnderDicotic IsShort A

instance : ClosedUnderAdd (IsShort (G := G)) where
  has_add _ _ := Short.add

instance : Hereditary (IsShort (G := G)) where
  has_option := Short.isOption

instance : ClosedUnderDicotic (IsShort (G := G)) (IsShort (G := G)) where
  closed_dicotic _ _ _ _ _ _ _ _ hShort := hShort

namespace Form.ClosedUnderAdd

theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderAdd A) : ClosedUnderAdd (sInf S) where
  has_add g h hg hh := by
    simp only [sInf_apply, iInf_Prop_eq] at hg hh ⊢
    intro P
    haveI : ClosedUnderAdd (fun x => P.1 x) := hS P P.2
    exact ClosedUnderAdd.has_add g h (hg P) (hh P)

/--
The closure operator for finding the smallest additively closed set containing
the given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => ClosedUnderAdd A) fun _ hS =>
    sInf_closed hS

/--
The additive closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A

theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A

theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg

instance closure_closed (A : G → Prop) : ClosedUnderAdd (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A

theorem add_mem_closure {A : G → Prop} {g h : G}
    (hg : closure A g) (hh : closure A h) : closure A (g + h) :=
  ClosedUnderAdd.has_add g h hg hh

theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [ClosedUnderAdd B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simpa only [ClosureOperator.ofCompletePred_isClosed] using
      (inferInstance : ClosedUnderAdd B))

theorem closure_le {A B : G → Prop} [ClosedUnderAdd B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩

theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))

end Form.ClosedUnderAdd

namespace Form

namespace Hereditary

theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, Hereditary A) : Hereditary (sInf S) where
  has_option hg h := by
    simp only [sInf_apply, iInf_Prop_eq] at hg ⊢
    intro P
    haveI : Hereditary (fun x => P.1 x) := hS P P.2
    exact Hereditary.has_option (hg P) h

/--
The closure operator for finding the smallest hereditary set containing the
given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => Hereditary A) fun _ hS =>
    sInf_closed hS

/--
The hereditary closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A

theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A

theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg

instance closure_closed (A : G → Prop) : Hereditary (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A

theorem has_option_mem_closure {A : G → Prop} {g g' : G}
    (hg : closure A g) (h : Moves.IsOption g' g) : closure A g' :=
  Hereditary.has_option hg h

theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [Hereditary B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simpa only [ClosureOperator.ofCompletePred_isClosed] using
      (inferInstance : Hereditary B))

theorem closure_le {A B : G → Prop} [Hereditary B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩

theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))

end Hereditary

namespace ClosedUnderNeg

theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderNeg A) : ClosedUnderNeg (sInf S) where
  neg_of hg := by
    simp only [sInf_apply, iInf_Prop_eq] at hg ⊢
    intro P
    haveI : ClosedUnderNeg (fun x => P.1 x) := hS P P.2
    exact ClosedUnderNeg.neg_of (hg P)

/--
The closure operator for finding the smallest conjugate closed set containing
the given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => ClosedUnderNeg A) fun _ hS =>
    sInf_closed hS

/--
The conjugate closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A

theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A

theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg

instance closure_closed (A : G → Prop) : ClosedUnderNeg (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A

theorem neg_mem_closure {A : G → Prop} {g : G} (hg : closure A g) : closure A (-g) :=
  ClosedUnderNeg.neg_of hg

theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [ClosedUnderNeg B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simpa only [ClosureOperator.ofCompletePred_isClosed] using
      (inferInstance : ClosedUnderNeg B))

theorem closure_le {A B : G → Prop} [ClosedUnderNeg B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩

theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))

end ClosedUnderNeg

end Form

namespace ClosedUnderDicotic

theorem sInf_closed (IsAmbient : G → Prop) {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderDicotic IsAmbient A) :
    ClosedUnderDicotic IsAmbient (sInf S) where
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    simp only [sInf_apply, iInf_Prop_eq] at hB hC ⊢
    intro P
    haveI : ClosedUnderDicotic IsAmbient (fun x => P.1 x) := hS P P.2
    exact ClosedUnderDicotic.closed_dicotic B C
      (fun b hb => hB b hb P) (fun c hc => hC c hc P) hBne hCne hAmbient

/--
The closure operator for finding the smallest dicotically closed set (given the
ambient context) containing the given set.
-/
noncomputable abbrev closureOperator (IsAmbient : G → Prop) : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred
    (fun A : G → Prop => ClosedUnderDicotic IsAmbient A) fun _ hS =>
      sInf_closed IsAmbient hS

/--
The dicotic closure (within the ambient context) of a given set.
-/
noncomputable abbrev closure (IsAmbient : G → Prop) (A : G → Prop) : G → Prop :=
  closureOperator IsAmbient A

theorem subset_closure (IsAmbient : G → Prop) (A : G → Prop) :
    A ≤ closure IsAmbient A :=
  (closureOperator IsAmbient).le_closure A

theorem mem_closure_of_mem {IsAmbient A : G → Prop} {g : G} (hg : A g) :
    closure IsAmbient A g :=
  subset_closure IsAmbient A g hg

instance closure_closed (IsAmbient : G → Prop) (A : G → Prop) :
    ClosedUnderDicotic IsAmbient (closure IsAmbient A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator IsAmbient).isClosed_closure A

theorem dicotic_mem_closure {IsAmbient A : G → Prop} (B C : Set G) [Small B] [Small C]
    (hB : ∀ b ∈ B, closure IsAmbient A b) (hC : ∀ c ∈ C, closure IsAmbient A c)
    (hBne : B.Nonempty) (hCne : C.Nonempty) (hAmbient : IsAmbient (!{B | C} : G)) :
    closure IsAmbient A (!{B | C} : G) :=
  ClosedUnderDicotic.closed_dicotic B C hB hC hBne hCne hAmbient

theorem closure_min {IsAmbient A B : G → Prop} (hAB : A ≤ B)
    [ClosedUnderDicotic IsAmbient B] : closure IsAmbient A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator IsAmbient) hAB (by
    simpa only [ClosureOperator.ofCompletePred_isClosed] using
      (inferInstance : ClosedUnderDicotic IsAmbient B))

theorem closure_le {IsAmbient A B : G → Prop} [ClosedUnderDicotic IsAmbient B] :
    closure IsAmbient A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure IsAmbient A).trans, fun h => closure_min h⟩

theorem closure_mono {IsAmbient A B : G → Prop} (hAB : A ≤ B) :
    closure IsAmbient A ≤ closure IsAmbient B :=
  closure_min (hAB.trans (subset_closure IsAmbient B))

end ClosedUnderDicotic

end

end MisereGames
