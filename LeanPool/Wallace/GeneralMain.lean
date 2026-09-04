/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.TorsionFreeCoordinate
import LeanPool.Wallace.RationalAssembly
import LeanPool.Wallace.PackageTransport

/-!
# The main theorem for every torsion-free Abelian group of cardinality continuum

This module closes the scope gap between the canonical rational construction and the exact main
theorem stated in the paper.  The rational character package is pulled back along the
coordinatization embedding from Section 2.  Its prescribed basis limits lie in the embedded
group by construction, so no new fusion or set-theoretic hypothesis is needed.
-/

open Cardinal

namespace Wallace

noncomputable section

namespace RationalCoordinatization

variable {G : Type} [AddCommGroup G]

/-- Pull the fully constructed rational character package back to a coordinatized group. -/
def fullCharacterPackage (K : RationalCoordinatization G) : FullCharacterPackage G :=
  RationalAssembly.fullCharacterPackage.pullback
    K.embedding K.embedding_injective
    (fun s ↦ K.basisPreimage
      (RationalTriangularPreprocess.codeIndex
        (RationalAssembly.fullCharacterPackage.embeddedCode
          K.embedding K.embedding_injective s)))
    (fun s ↦ by
      simpa [RationalAssembly.fullCharacterPackage,
        RationalTriangularPreprocess.codeBasisVector] using
        K.embedding_basisPreimage
          (RationalTriangularPreprocess.codeIndex
            (RationalAssembly.fullCharacterPackage.embeddedCode
              K.embedding K.embedding_injective s)))

/-- Every group with the paper's rational coordinatization inherits the complete topology
conclusion from the unconditional rational construction. -/
theorem hasMainGroupTopology (K : RationalCoordinatization G) :
    HasMainGroupTopology G :=
  K.fullCharacterPackage.hasMainGroupTopology

end RationalCoordinatization

/-- **Formal counterpart of the paper's main theorem.**  Every torsion-free Abelian group of
cardinality continuum admits a Hausdorff countably compact group topology in which every
convergent sequence is eventually constant.  The formal conclusion additionally records a
compatible totally bounded uniform group structure.  `Wallace.Audit` records the standard
classical Lean foundations used by the proof. -/
theorem torsionFreeAbelianGroup_mainTheorem
    (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (hcard : #G = 𝔠) : HasMainGroupTopology G :=
  (RationalCoordinatization.ofCardinalityContinuum hcard).hasMainGroupTopology

/-- The exact paper-level projection of the main theorem, with only the properties printed in
the theorem statement and no additional uniform-space fields exposed. -/
theorem torsionFreeAbelianGroup_mainTheorem_exact
    (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (hcard : #G = 𝔠) :
    ∃ topology : TopologicalSpace G,
      @IsTopologicalAddGroup G topology _ ∧
      @T2Space G topology ∧
      @CountablyCompactSpace G topology ∧
      (∀ (s : ℕ → G) (x : G),
        Filter.Tendsto s Filter.atTop (@nhds G topology x) →
          ∀ᶠ n in Filter.atTop, s n = x) := by
  obtain ⟨topology, _uniformity, _hcompat, _huniformGroup,
    htopologicalGroup, hT2, hcompact, _htotallyBounded, hsequences⟩ :=
      torsionFreeAbelianGroup_mainTheorem G hcard
  exact ⟨topology, htopologicalGroup, hT2, hcompact, hsequences⟩

/-- The Baer--Specker group has cardinality continuum. -/
theorem mk_baerSpeckerGroup : #(ℕ → ℤ) = 𝔠 := by
  rw [Cardinal.mk_arrow, Cardinal.mk_int, Cardinal.mk_nat]
  simp

/-- The Baer--Specker specialization highlighted in the abstract and introduction. -/
theorem baerSpeckerGroup_mainTheorem : HasMainGroupTopology (ℕ → ℤ) :=
  torsionFreeAbelianGroup_mainTheorem (ℕ → ℤ) mk_baerSpeckerGroup

end

end Wallace
