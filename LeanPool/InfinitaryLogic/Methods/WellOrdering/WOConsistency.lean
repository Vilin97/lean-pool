/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.ClosureFields
import LeanPool.InfinitaryLogic.Methods.WellOrdering.BaseMember
/-!
# The bundled consistency property and completion endpoint (issue #12, packaging)

The fifteen closure theorems package directly into the kernel's `ConsistencyPropertyEqOn`
over the enumeration universe rooted at the lifted sentence, and the fair enumeration turns
the infinite initial member `Bφ` into a Henkin-complete extension.

**Boundaries** (kept deliberately visible):
* `WOMem` is used **only** for the stage family (`woConsistencyProperty.sets`);
* the infinite initial member is `baseDiagram φ lt` (accepted by the fair enumeration —
  the frozen D4 member shape);
* the completed union is **not** claimed to satisfy `WOMem` or to belong to the family —
  the endpoint returns only containment and `HenkinComplete`;
* `HasWellOrderedChains` enters **only** through `baseDiagram_mem`;
* countability enters **only** at the fair-enumeration invocation, never in the fifteen
  closure lemmas.

Step 5 consumes the returned `S` opaquely: the quotient term model realizes the lifted root,
`q ↦ [ratConst q]` maps the rationals, and membership of every positive diagram atom supplies
`RelPreserving`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} (φ : L.Sentenceω) (lt : L.Relations 2)

/-- **The well-ordering consistency property**: the `WOMem` stage family, bundled — each
kernel field is one of the fifteen closure theorems. -/
def woConsistencyProperty :
    ConsistencyPropertyEqOn (GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
      (φ.mapLanguage (L.lhomWithConstants ℕ))) where
  sets := {S | WOMem φ lt S}
  subset_U := fun _ hS => hS.subset_U
  C0_no_falsum := fun _ hS => hS.no_falsum
  C0_no_contradiction := fun _ hS => hS.no_contradiction
  C1_imp := fun _ hS ψ₁ ψ₂ h => hS.C1_imp ψ₁ ψ₂ h
  C1_neg_imp := fun _ hS ψ₁ ψ₂ h => hS.C1_neg_imp ψ₁ ψ₂ h
  C2_not_not := fun _ hS ψ h => hS.C2_not_not ψ h
  C3_iInf := fun _ hS φs h k => hS.C3_iInf φs h k
  C3_neg_iInf := fun _ hS φs h => hS.C3_neg_iInf φs h
  C4_iSup := fun _ hS φs h => hS.C4_iSup φs h
  C4_neg_iSup := fun _ hS φs h k => hS.C4_neg_iSup φs h k
  eq_refl := fun _ hS c => hS.eq_refl c
  eq_symm := fun _ hS a b h => hS.eq_symm a b h
  eq_trans := fun _ hS a b d h₁ h₂ => hS.eq_trans a b d h₁ h₂
  rel_congr := fun _ hS l R g i b h₁ h₂ => hS.rel_congr l R g i b h₁ h₂
  all_inst := fun _ hS ψ h c => hS.all_inst ψ h c
  neg_all_witness := fun _ hS ψ h => hS.neg_all_witness ψ h

/-- **The completion endpoint** (consumer-facing): under the well-ordered-chains hypothesis
and the relational-core countability, a Henkin-complete set containing the base diagram
exists.  Step 5 consumes `S` opaquely. -/
theorem exists_henkinComplete_baseDiagram [Countable (Σ l, L.Relations l)]
    (h : HasWellOrderedChains φ lt) :
    ∃ S : Set L[[ℕ]].Sentenceω,
      baseDiagram φ lt ⊆ S ∧
      HenkinComplete (GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
        (φ.mapLanguage (L.lhomWithConstants ℕ))) S := by
  have : Countable ↥(GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
      (φ.mapLanguage (L.lhomWithConstants ℕ))) := genU_countable.to_subtype
  obtain ⟨Sstar, hsub, -, hcomp⟩ := exists_henkinComplete
    (P := woConsistencyProperty φ lt)
    (S₀ := ⟨baseDiagram φ lt, baseDiagram_mem h⟩)
  exact ⟨Sstar, hsub, hcomp⟩

end FirstOrder.Language
