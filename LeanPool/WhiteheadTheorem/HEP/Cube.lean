/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.CWComplex.Basic
import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
import LeanPool.WhiteheadTheorem.HEP.Cofibration

/-!
In this file, the homotopy extension property (HEP) of the pair $(I^n, ∂I^n)$
is derived from the HEP of $(D^n, ∂D^n)$.
-/

open CategoryTheory TopCat
open scoped Topology unitInterval


/--
```
  ∂𝔻 n ---φ---> ∂I^n ------h---> C(I, Y)
  |       ≃       |                |
  i               ι            pathStart
  |               |                |
  v       ≃       v                v
  𝔻 n ----Φ--> I^ (Fin n) ---f---> Y
```
-/
instance Cube.boundaryIncl_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom (Cube.boundaryIncl n) where
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePair n) _⟩

instance Cube.boundaryIncl_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <| (Cube.boundaryIncl n).prodMap (ContinuousMap.id I) := by
  change IsCofibration <| TopCat.ofHom <| (TopCat.ofHom <| Cube.boundaryIncl n).hom.prodMap _
  apply IsCofibration.prod_unitInterval

theorem Cube.boundaryIncl_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (Cube.boundaryIncl n) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (Cube.boundaryIncl_isCofibration n) (TopCat.of Y)

theorem Cube.boundaryIncl_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((Cube.boundaryIncl n).prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (Cube.boundaryIncl_prod_unitInterval_isCofibration n) (TopCat.of Y)


/-!
The universe-polymorphic version of the above theorems
-/

namespace TopCat

universe u

instance cubeBoundaryIncl_isCofibration (n : ℕ) :
    IsCofibration (cubeBoundaryIncl.{u} n) where
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePairULift n) _⟩

instance cubeBoundaryIncl_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <|
    (cubeBoundaryIncl.{u} n).hom.prodMap (ContinuousMap.id I) := by
  apply IsCofibration.prod_unitInterval

theorem cubeBoundaryIncl_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (cubeBoundaryIncl.{u} n).hom Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (cubeBoundaryIncl_isCofibration n) (TopCat.of Y)

theorem cubeBoundaryIncl_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((cubeBoundaryIncl n).hom.prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (cubeBoundaryIncl_prod_unitInterval_isCofibration n) (TopCat.of Y)

end TopCat
