/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
/-!
# Everywhere-unramified towers of number fields

This file combines finite-prime and infinite-place unramifiedness and
records its tower and intermediate-field properties.
-/

open scoped NumberField

universe u v w

/-- A number-field extension is everywhere unramified when it is
unramified at every finite prime and at every infinite place. -/
structure IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop where
  /-- The extension is unramified at every finite prime. -/
  finitePlaces : IsUnramifiedAtFinitePlaces K L
  /-- The extension is unramified at every infinite place. -/
  infinitePlaces : IsUnramifiedAtInfinitePlaces K L

namespace IsEverywhereUnramified

/-- The identity extension is everywhere unramified. -/
theorem refl
    (K : Type u) [Field K] [NumberField K] :
    IsEverywhereUnramified K K where
  finitePlaces :=
    IsUnramifiedAtFinitePlaces.refl K
  infinitePlaces :=
    inferInstance

variable
    {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]

/-- Everywhere-unramified extensions are transitive in towers. -/
theorem trans
    (hkK : IsEverywhereUnramified k K)
    (hKF : IsEverywhereUnramified K F) :
    IsEverywhereUnramified k F where
  finitePlaces :=
    IsUnramifiedAtFinitePlaces.trans
      hkK.finitePlaces hKF.finitePlaces
  infinitePlaces := by
    let : IsUnramifiedAtInfinitePlaces k K :=
      hkK.infinitePlaces
    let : IsUnramifiedAtInfinitePlaces K F :=
      hKF.infinitePlaces
    exact
      IsUnramifiedAtInfinitePlaces.trans k K F

/-- If the top of a number-field tower is everywhere unramified over
the bottom, then it is everywhere unramified over the intermediate
field. -/
theorem top
    (hkF : IsEverywhereUnramified k F) :
    IsEverywhereUnramified K F where
  finitePlaces :=
    IsUnramifiedAtFinitePlaces.top hkF.finitePlaces
  infinitePlaces := by
    let : IsUnramifiedAtInfinitePlaces k F :=
      hkF.infinitePlaces
    exact
      IsUnramifiedAtInfinitePlaces.top k K F

/-- If the top of a number-field tower is everywhere unramified over
the bottom, then the intermediate field is everywhere unramified over
the bottom. -/
theorem bot
    (hkF : IsEverywhereUnramified k F) :
    IsEverywhereUnramified k K where
  finitePlaces :=
    IsUnramifiedAtFinitePlaces.bot hkF.finitePlaces
  infinitePlaces := by
    let : IsUnramifiedAtInfinitePlaces k F :=
      hkF.infinitePlaces
    exact
      IsUnramifiedAtInfinitePlaces.bot k K F

end IsEverywhereUnramified
