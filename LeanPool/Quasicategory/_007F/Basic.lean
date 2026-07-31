/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory._007F.Nondegenerate

namespace SSet

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

noncomputable
abbrev σ.s (i : Σₗ (b : Fin n), Fin b.succ) :
    Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (σ.simplex i)

noncomputable abbrev τ.t (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (τ.simplex i)

noncomputable
def σ.subcomplex (i : Σₗ (b : Fin n), Fin b.succ) := Subcomplex.ofSimplex (σ.simplex i)

noncomputable
def τ.subcomplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := Subcomplex.ofSimplex (τ.simplex i)

instance (i : Σₗ (b : Fin n), Fin b.succ) : Mono (σ.s i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (σ.nonDegenerateEquiv.toFun i).2

instance (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Mono (τ.t i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (τ.nonDegenerateEquiv i).2

end SSet
