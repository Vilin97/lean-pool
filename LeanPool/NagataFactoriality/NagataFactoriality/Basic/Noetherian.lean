/-
Copyright (c) 2026 Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import LeanPool.NagataFactoriality.NagataFactoriality.Basic.Divisibility

namespace NagataFactoriality

theorem hasFactorization_of_noetherian {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α := by
  infer_instance

theorem IsNoetherianRing.hasFactorization {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : WfDvdMonoid α := by
  letI := h
  exact hasFactorization_of_noetherian (α := α)

end NagataFactoriality
