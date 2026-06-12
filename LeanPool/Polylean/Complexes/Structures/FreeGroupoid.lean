/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.Complexes.Structures.Groupoid

namespace LeanPool.Polylean

universe u vq vg

namespace FreeGroupoid

/-- The definition of a free groupoid with basis `Q`. -/
class Struct {S : Sort u} (Q : Quiver.{u, vq} S) (G : Groupoid.{u, vg} S) where
  /-- Map each generating quiver edge into the generated groupoid. -/
  map : {X Y : S} → Q.hom X Y → G.hom X Y
  /-- Extend a quiver pre-functor out of the basis to a groupoid functor. -/
  inducedMap : {S' : Sort u} → {G' : Groupoid.{u, vg} S'} →
      Quiver.PreFunctor Q G'.toQuiver → Groupoid.Functor G G'

/-- The inclusion of a quiver into a groupoid generated freely by it. -/
def ι {S : Sort u} (Q : Quiver.{u, vq} S) (G : Groupoid.{u, vg} S)
    [FreeGroupoid.Struct Q G] :
    Quiver.PreFunctor Q G.toQuiver :=
  { obj := id, map := FreeGroupoid.Struct.map }

end FreeGroupoid

/-- The universal property characterizing a free groupoid on a quiver. -/
class FreeGroupoid {S : Sort u} (Q : Quiver.{u, vq} S) (G : Groupoid.{u, vg} S) extends
    _root_.LeanPool.Polylean.FreeGroupoid.Struct Q G where
  induced_extends : {S' : Sort u} → {G' : Groupoid.{u, vg} S'} →
      (φ : Quiver.PreFunctor Q G'.toQuiver) →
        Quiver.PreFunctor.comp (_root_.LeanPool.Polylean.FreeGroupoid.ι Q G)
          (inducedMap φ).toPreFunctor = φ
  induced_unique : {S' : Sort u} → {G' : Groupoid.{u, vg} S'} →
      (Φ Ψ : Groupoid.Functor G G') →
        Quiver.PreFunctor.comp (_root_.LeanPool.Polylean.FreeGroupoid.ι Q G) Φ.toPreFunctor =
        Quiver.PreFunctor.comp (_root_.LeanPool.Polylean.FreeGroupoid.ι Q G) Ψ.toPreFunctor →
          Φ = Ψ

end LeanPool.Polylean
