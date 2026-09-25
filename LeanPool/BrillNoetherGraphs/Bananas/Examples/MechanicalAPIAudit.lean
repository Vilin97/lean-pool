/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI
import LeanPool.BrillNoetherGraphs.Bananas.Theta.EvenlyMarkedThetaKGeneral

/-!
# Mechanical API audit for two remaining statement targets

This file is intentionally disjoint from `Statements.lean` and the shared
library.  It records the strongest reductions available from the current API;
the remaining hypotheses are the graph-specific arithmetic/counting lemmas.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! ## Evenly marked theta: the generic transmission reduction -/

theorem evenlyMarkedTheta_kGeneral_of_torsion_and_count
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β) (k : ℕ)
    (hEven : EvenlyMarkedTheta B α β i j)
    (hk : TorsionWitness
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k)
    (hCount : ∀ D : CFDiv B.graph, ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) D τ ∧
      IsKAffine k τ ∧
      kInversionCount k τ ≤ Int.toNat (genus B.graph)) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k := by
  let M := mark B.graph (strandVertex B α i) (strandVertex B β j)
  have hsub : AllSubmodular M := by
    simpa [M] using evenlyMarkedTheta_allSubmodular B α β i j hEven
  refine ⟨?_, hsub, ?_⟩
  · simpa [M] using hk
  · intro D
    obtain ⟨τ, hτ, hAffine, hCountτ⟩ := hCount D
    exact ⟨τ, hτ, hAffine,
      kInversions_finite_of_torsionWitness_and_isKAffine hk hAffine,
      hCountτ⟩

/-! The generic API can also discharge the per-divisor existence/finiteness
part from torsion and submodularity, but not the genus inversion bound. -/

theorem evenlyMarkedTheta_affine_existence_audit
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β) (k : ℕ)
    (hEven : EvenlyMarkedTheta B α β i j)
    (hk : TorsionWitness
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k)
    (D : CFDiv B.graph) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation
        (mark B.graph (strandVertex B α i) (strandVertex B β j)) D τ ∧
      IsKAffine k τ ∧
      (kInversions k τ).Finite := by
  let M := mark B.graph (strandVertex B α i) (strandVertex B β j)
  exact exists_affine_transmission_of_allSubmodular
    (graphConnected B) hk (by
      simpa [M] using evenlyMarkedTheta_allSubmodular B α β i j hEven) D

/-! ## Cross one-off: what the generic APIs actually yield -/

theorem cross_oneOff_affine_existence_audit
    {g k : ℕ} (_hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (_hαβ : α ≠ β) (hα : 1 < B.length α) (hβ : 1 < B.length β)
    (hsub : AllSubmodular
      (mark B.graph (strandVertex B α ⟨1, by omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩)))
    (hk : TorsionWitness
      (mark B.graph (strandVertex B α ⟨1, by omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩)) k)
    (E : CFDiv B.graph) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation
        (mark B.graph (strandVertex B α ⟨1, by omega⟩)
          (strandVertex B β ⟨B.length β - 1, by omega⟩)) E τ ∧
      IsKAffine k τ ∧
      (kInversions k τ).Finite := by
  exact exists_affine_transmission_of_allSubmodular
    (graphConnected B) hk hsub E

/-! This is the exact missing strengthening for the both-off target
(`cor-bothOffMax`, Corollary 4.31): the current API supplies the preceding
theorem, but no way to choose a divisor `E` or to prove the displayed lower
bound for its permutation.  Concretely, what is missing is a proof of

```text
∃ (E : CFDiv B.graph) (τ : ℤ → ℤ),
  IsTransmissionPermutation (mark B.graph u v) E τ ∧ IsKAffine k τ ∧
  Nat.choose g 2 + g / (B.length β - 1) ≤ kInversionCount k τ
```

for `u = v_{α,1}`, `v = v_{β,n_β-1}`.  This was previously recorded as a
theorem taking that statement as a hypothesis and returning it unchanged
(`P → P`), which asserts nothing; it is stated here as a comment instead. -/

end Bananas
