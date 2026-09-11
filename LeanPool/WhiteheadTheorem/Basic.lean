/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.Auxiliary
public import LeanPool.WhiteheadTheorem.Compressible.CWComplex
public import LeanPool.WhiteheadTheorem.Compressible.Defs
public import LeanPool.WhiteheadTheorem.Compressible.Disk
public import LeanPool.WhiteheadTheorem.Compressible.WeakEquiv
public import LeanPool.WhiteheadTheorem.CWComplex.Basic
public import LeanPool.WhiteheadTheorem.CWComplex.IProd.Def
public import LeanPool.WhiteheadTheorem.CWComplex.IProd.Iso
public import LeanPool.WhiteheadTheorem.Defs
public import LeanPool.WhiteheadTheorem.Exponential
public import LeanPool.WhiteheadTheorem.HEP.Cofibration
public import LeanPool.WhiteheadTheorem.HEP.Cube
public import LeanPool.WhiteheadTheorem.HEP.CubeJar
public import LeanPool.WhiteheadTheorem.HEP.Retract
public import LeanPool.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
public import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Algebra
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Compression
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
public import LeanPool.WhiteheadTheorem.Shapes.Cube
public import LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap
public import LeanPool.WhiteheadTheorem.Shapes.Disk
public import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
public import LeanPool.WhiteheadTheorem.Shapes.Jar
public import LeanPool.WhiteheadTheorem.Shapes.MappingCylinder
public import LeanPool.WhiteheadTheorem.Shapes.Maps
public import LeanPool.WhiteheadTheorem.Shapes.Pushout
public import LeanPool.WhiteheadTheorem.Shapes.UnitInterval

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
