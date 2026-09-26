/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
public import LeanPool.NagataFactoriality.NagataFactoriality.Basic.Divisibility


/-!
# Noetherian

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

theorem hasFactorization_of_noetherian {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α := by
  infer_instance

theorem IsNoetherianRing.hasFactorization {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : WfDvdMonoid α := by
  let := h
  exact hasFactorization_of_noetherian (α := α)

end NagataFactoriality
