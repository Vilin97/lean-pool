/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionBridge
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Transfer of AdicCompletion results to UniformSpace.Completion

Using the bridge `adicCompletionRingEquiv : Completion R ≃+* AdicCompletion I R`,
transfer Mathlib's exactness, injectivity, and flatness results from
`AdicCompletion` to `UniformSpace.Completion` for rings with I-adic topology.

## Main results

* `completion_flat` : `Completion R` is flat over `R` (for noetherian `R`)
-/

@[expose] public section

namespace AdicCompletionBridge

variable {R : Type*} [CommRing R] (I : Ideal R)
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The completion of a noetherian ring with I-adic topology is flat over R.
Transfers `AdicCompletion.flat_of_isNoetherian` via the bridge. -/
theorem completion_flat (hadic : IsAdic I) [IsNoetherianRing R] :
    Module.Flat R (UniformSpace.Completion R) := by
  have : Module.Flat R (AdicCompletion I R) :=
    AdicCompletion.flat_of_isNoetherian I
  let e := adicCompletionRingEquiv I hadic
  have he_smul : ∀ (r : R) (x : UniformSpace.Completion R),
      e (r • x) = r • e x := by
    intro r x
    rw [Algebra.smul_def, Algebra.smul_def, e.map_mul]
    congr 1
    exact AbstractCompletion.compare_coe
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic) r
  exact Module.Flat.of_linearEquiv
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := he_smul }

end AdicCompletionBridge
