/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.CWComplex.Basic
public import LeanPool.WhiteheadTheorem.Defs
import LeanPool.WhiteheadTheorem.Compressible.WeakEquiv
import Mathlib.Tactic.Measurability.Init

/-!
# LeanPool.WhiteheadTheorem.Basic

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Basic`.
-/

@[expose] public section


open CategoryTheory

universe u

theorem WhiteheadTheorem (X Y : CWComplex.{u}) (f : (X : TopCat.{u}) ⟶ Y) :
    IsWeakHomotopyEquiv f.hom → IsHomotopyEquiv f.hom := by
  intro hf
  obtain ⟨g, hgf⟩ := hf.CWComplex_induced_map_surjective Y (𝟙 _)
  have hfgf : (f ≫ g ≫ f).hom.Homotopic f.hom :=
    hgf.comp (ContinuousMap.Homotopic.refl f.hom)
  use
    { toFun := f.hom
      invFun := g.hom
      left_inv := hf.CWComplex_induced_map_injective X (f ≫ g) (𝟙 _) hfgf
      right_inv := hgf }
