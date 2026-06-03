/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Compressible.CWComplex
import LeanPool.WhiteheadTheorem.Compressible.Defs
import LeanPool.WhiteheadTheorem.Compressible.Disk
import LeanPool.WhiteheadTheorem.Compressible.WeakEquiv
import LeanPool.WhiteheadTheorem.CWComplex.Basic
import LeanPool.WhiteheadTheorem.CWComplex.IProd.Def
import LeanPool.WhiteheadTheorem.CWComplex.IProd.Iso
import LeanPool.WhiteheadTheorem.Defs
import LeanPool.WhiteheadTheorem.Exponential
import LeanPool.WhiteheadTheorem.HEP.Cofibration
import LeanPool.WhiteheadTheorem.HEP.Cube
import LeanPool.WhiteheadTheorem.HEP.CubeJar
import LeanPool.WhiteheadTheorem.HEP.Retract
import LeanPool.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Algebra
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Compression
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import LeanPool.WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap
import LeanPool.WhiteheadTheorem.Shapes.Disk
import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
import LeanPool.WhiteheadTheorem.Shapes.Jar
import LeanPool.WhiteheadTheorem.Shapes.MappingCylinder
import LeanPool.WhiteheadTheorem.Shapes.Maps
import LeanPool.WhiteheadTheorem.Shapes.Pushout
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval

/-!
# LeanPool.WhiteheadTheorem.Basic

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Basic`.
-/


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

-- #print axioms WhiteheadTheorem
