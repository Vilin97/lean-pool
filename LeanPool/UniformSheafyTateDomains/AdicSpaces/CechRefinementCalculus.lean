/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CechCohomology

/-!
# The Čech refinement calculus (T634: Wedhorn Appendix A, all degrees)

The refinement-independence and comparison machinery for the abstract Čech
complex of `CechCohomology.lean`, towards Wedhorn Propositions A.2/A.3 in all
degrees:

* functoriality of the refinement cochain maps (`Refinement.id`, `.comp`);
* compatibility with the augmentation;
* the **prism homotopy** between the cochain maps of two refinements
  (`Refinement.prism`, `prism_identity…`): the Čech-level reason
  `Ȟ q (τ•)` is independent of the choice of refinement map
  ([Wedhorn] l.5282 "is independent of the choice of τ");
* **Remark A.2** ([Wedhorn] l.5311): covers that refine each other have
  transferring acyclicity.
-/

@[expose] public section

noncomputable
section

open Filter Topology

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} [Fintype ι] {κ : Type v} [Fintype κ] {μ : Type v} [Fintype μ]

namespace Refinement

/-- The identity refinement. -/
def idRefinement (U : FiniteCover X ι) : Refinement U U where
  map := id
  subset _ := le_refl _

/-- Composition of refinements. -/
def comp {W : FiniteCover X μ} {V : FiniteCover X κ} {U : FiniteCover X ι}
    (s : Refinement W V) (r : Refinement V U) : Refinement W U where
  map := r.map ∘ s.map
  subset j := (s.subset j).trans (r.subset (s.map j))

/-- The identity refinement induces the identity cochain map. -/
theorem cochainMap_id (U : FiniteCover X ι) (F : AbPresheaf X) (q : ℕ)
    (f : CechCochain F U q) :
    (idRefinement U).cochainMap F q f = f := by
  funext σ
  exact F.res_id (f σ)

/-- Cochain maps are functorial in the refinement. -/
theorem cochainMap_comp {W : FiniteCover X μ} {V : FiniteCover X κ}
    {U : FiniteCover X ι} (s : Refinement W V) (r : Refinement V U)
    (F : AbPresheaf X) (q : ℕ) (f : CechCochain F U q) :
    (s.comp r).cochainMap F q f = s.cochainMap F q (r.cochainMap F q f) := by
  funext σ
  show F.res _ (f ((r.map ∘ s.map) ∘ σ)) =
    F.res _ (F.res _ (f (r.map ∘ (s.map ∘ σ))))
  rw [F.res_comp]
  rfl

/-- Cochain maps intertwine the augmentations. -/
theorem cochainMap_cechAug {V : FiniteCover X κ} {U : FiniteCover X ι}
    (r : Refinement V U) (F : AbPresheaf X) (x : F.obj Set.univ) :
    r.cochainMap F 0 (cechAug F U x) = cechAug F V x := by
  funext σ
  show F.res _ (F.res _ x) = F.res _ x
  rw [F.res_comp]

end Refinement

end
