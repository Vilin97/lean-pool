/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarCompose
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarThinSlabsEndpoints

/-!
# Relative subdivision collars for arbitrary endpoint levels

The explicit one-step collar is iterated by the abstract collar-composition operation. Reversing
one such stack supplies a collar from a common refinement down to the independently prescribed
upper endpoint. Composing the lower stack with that reversed upper stack gives a genuine
endpoint-identified affine collar for any two subdivision levels.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionEndpointCollar

open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarReverse

variable {p : Nat}

/-- Existential bookkeeping wrapper for the common and time-refinement levels of a collar. -/
structure Witness (hp : Nat.Prime p) (N₀ N₁ : Nat) where
  /-- The common spatial subdivision level of the endpoint collar. -/
  commonLevel : Nat
  /-- The time-refinement level of the endpoint collar. -/
  timeLevel : Nat
  /-- The endpoint-identified relative affine collar at the chosen levels. -/
  collar : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ commonLevel timeLevel

/-- Equal-level identity collar, represented by one unrefined thin slab. -/
noncomputable def identityWitness
    (hp : Nat.Prime p) (N : Nat) : Witness hp N N where
  commonLevel := N
  timeLevel := 1
  collar := RelativeCollarThinSlabsEndpoints.endpointIdentifiedCollar hp N 1 (by omega)

/-- One-step subdivision witness. -/
noncomputable def oneStepWitness
    (hp : Nat.Prime p) (N : Nat) : Witness hp N (N + 1) where
  commonLevel := N + 1
  timeLevel := 0
  collar := RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar hp N

/-- Reverse an existential collar witness. -/
noncomputable def reverseWitness
    {hp : Nat.Prime p} {N₀ N₁ : Nat}
    (C : Witness hp N₀ N₁) : Witness hp N₁ N₀ where
  commonLevel := C.commonLevel
  timeLevel := C.timeLevel
  collar := reverseEndpointCollar C.collar

/-- Compose two existential collar witnesses. -/
noncomputable def composeWitness
    {hp : Nat.Prime p} {N₀ Nmid N₁ : Nat}
    (C : Witness hp N₀ Nmid) (D : Witness hp Nmid N₁) :
    Witness hp N₀ N₁ where
  commonLevel := max C.commonLevel D.commonLevel
  timeLevel := C.timeLevel + D.timeLevel + 1
  collar := endpointIdentifiedCollar C.collar D.collar

/-- Iterate the one-step cylinder `k` times. -/
noncomputable def forwardWitness
    (hp : Nat.Prime p) (N : Nat) :
    (k : Nat) → Witness hp N (N + k)
  | 0 => by simpa using identityWitness hp N
  | k + 1 => by
      simpa [Nat.add_assoc] using
        composeWitness (forwardWitness hp N k) (oneStepWitness hp (N + k))

/-- A forward subdivision collar between any ordered pair of levels. -/
noncomputable def orderedWitness
    (hp : Nat.Prime p) (N M : Nat) (hNM : N ≤ M) : Witness hp N M :=
  cast (congrArg (fun k => Witness hp N k) (Nat.add_sub_cancel' hNM))
    (forwardWitness hp N (M - N))

/-- Relative subdivision collar through any preselected common refinement level. -/
noncomputable def endpointWitnessAt
    (hp : Nat.Prime p) (N₀ N₁ M : Nat)
    (h₀ : N₀ ≤ M) (h₁ : N₁ ≤ M) : Witness hp N₀ N₁ :=
  let lower : Witness hp N₀ M := orderedWitness hp N₀ M h₀
  let upper : Witness hp N₁ M := orderedWitness hp N₁ M h₁
  composeWitness lower (reverseWitness upper)

/-- Relative subdivision collar for arbitrary independent endpoint levels. -/
noncomputable def endpointWitness
    (hp : Nat.Prime p) (N₀ N₁ : Nat) : Witness hp N₀ N₁ :=
  endpointWitnessAt hp N₀ N₁ (max N₀ N₁)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Existence of a genuine endpoint-identified relative affine collar for arbitrary levels. -/
theorem relativeAffineCollarExists
    (hp : Nat.Prime p) (N₀ N₁ : Nat) :
    ∃ (M L : Nat), RelativeAffineCollarExists hp N₀ N₁ M L :=
  ⟨(endpointWitness hp N₀ N₁).commonLevel,
    (endpointWitness hp N₀ N₁).timeLevel,
    ⟨(endpointWitness hp N₀ N₁).collar⟩⟩

end RelativeSubdivisionEndpointCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
