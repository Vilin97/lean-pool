/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Local
/-!
# Compiled finite/free collection stage of the profinite-unit decomposition
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open LocalFieldTheory.Padic

/-- Collect the finite and torsion-free coordinates of the local product. -/
noncomputable def finiteFreeSplit :
    ((p : Nat.Primes) →
      padicUnitFiniteFactor p.1 × Multiplicative ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ×
      CyclotomicFinitePart where
  toFun x := (fun p => (x p).2, fun p => (x p).1)
  invFun x p := (x.2 p, x.1 p)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_pi fun p =>
      continuous_snd.comp (continuous_apply p)).prodMk
        (continuous_pi fun p =>
          continuous_fst.comp (continuous_apply p))
  continuous_invFun :=
    continuous_pi fun p =>
      ((continuous_apply p).comp continuous_snd).prodMk
        ((continuous_apply p).comp continuous_fst)

end KummerTheory.ProfiniteUnitDecomposition.Internal
