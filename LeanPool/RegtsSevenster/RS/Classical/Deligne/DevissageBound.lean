/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeNormalise
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModSchurSummand
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixWhiskerAll
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29State

/-!
# The dévissage counts are bounded

A killing diagram bounds the two counts of a dévissage state.
The killing is whiskered by the base and read as module-level
vanishing for the free module on the object; the decomposition
carries it to the mixed free part; and there the nonvanishing of
the mixed sum forces the diagram to contain the cell recording
the two counts.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The counts of a dévissage state are bounded by the killing
diagram.** -/
theorem devissage_bound
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine D) (X : D) {lam : YoungDiagram}
    (hcard : lam.card ≠ 0) (hkill : SchurKilled P X lam)
    (st : DevissageState D L X) :
    st.units + st.lines ≤ 2 * lam.card := by
  letI := st.monObj
  letI := st.comm
  have h1 : (st.base ◁ (permAlg X lam.card (P.e lam) :
      tensorPow D X lam.card ⟶ tensorPow D X lam.card)) = 0 := by
    rw [show (permAlg X lam.card (P.e lam) :
        tensorPow D X lam.card ⟶ tensorPow D X lam.card) = 0
      from hkill]
    exact MonoidalPreadditive.whiskerLeft_zero
  have h2 : ModSchurKilled st.base (freeMod st.base X).X P lam :=
    modPowAlg_eq_zero st.base X lam.card hcard (P.e lam) h1
  obtain ⟨e⟩ := st.decomp
  have h3 : ModSchurKilled st.base
      (freeMod st.base (L.mix st.units st.lines)).X P lam :=
    ModSchurKilled.of_biprod_left st.base _ _ P
      (ModSchurKilled.of_modIso st.base e.symm P h2)
  have h4 : (st.base ◁ (permAlg (L.mix st.units st.lines) lam.card
      (P.e lam) : tensorPow D (L.mix st.units st.lines) lam.card ⟶
        tensorPow D (L.mix st.units st.lines) lam.card)) = 0 :=
    whisker_permAlg_eq_zero st.base (L.mix st.units st.lines)
      lam.card hcard (P.e lam) h3
  have hW : ∀ k : ℕ,
      𝟙 (st.base ⊗ tensorPow D L.obj k) ≠ 0 := fun k =>
    L.whisker_tensorPow_id_ne_zero st.unit_ne_zero k
  have hcell : ((st.units, st.lines) : ℕ × ℕ) ∈ lam := by
    by_contra hc
    exact L.whisker_permAlg_mix_ne_zero' P P₀ st.base st.units
      st.lines hW hc h4
  obtain ⟨hr, hs⟩ := cell_lt_card hcell
  omega

end RS
