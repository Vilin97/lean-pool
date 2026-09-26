/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Complement

/-!
# Separators from locally constant obstruction values

A mod-prime zero count is naturally defined only away from the projected zero set.  If that count
is locally constant on the complement, takes one value along the bottom boundary, and takes a
different value along the top boundary, then its value classes split the complement into the two
open regions required by `TopBottomComplement`.

This construction avoids any local path-connectedness assumption on the base hyperspace.
-/

@[expose] public section

namespace NRR

variable {X I : Type*} [TopologicalSpace X]
variable {carrier : Set (X × SignedInterval)}

/-- A locally constant invariant on the complement of a proposed separator carrier. -/
structure ComplementObstructionValue
    (X : Type*) [TopologicalSpace X]
    (carrier : Set (X × SignedInterval))
    (I : Type*) where
  /-- Value of the obstruction at a point outside the carrier. -/
  value : ∀ z : X × SignedInterval, z ∈ carrierᶜ → I
  /-- Value selecting the lower side. -/
  lowerValue : I
  /-- Every complement point has an ambient open neighborhood, still in the complement, on which
  the obstruction value is constant. -/
  locally_constant :
    ∀ (z : X × SignedInterval) (hz : z ∈ carrierᶜ),
      ∃ (U : Set (X × SignedInterval)) (hUout : U ⊆ carrierᶜ),
        IsOpen U ∧ z ∈ U ∧
          ∀ (w : X × SignedInterval) (hw : w ∈ U),
            value w (hUout hw) = value z hz
  /-- The bottom boundary is outside the carrier. -/
  bottom_outside : signedBottom X ⊆ carrierᶜ
  /-- The top boundary is outside the carrier. -/
  top_outside : signedTop X ⊆ carrierᶜ
  /-- The obstruction has the selected lower value at every bottom point. -/
  bottom_value :
    ∀ x : X,
      value (x, SignedInterval.left) (bottom_outside rfl) = lowerValue
  /-- The obstruction differs from the lower value at every top point. -/
  top_value_ne :
    ∀ x : X,
      value (x, SignedInterval.right) (top_outside rfl) ≠ lowerValue

namespace ComplementObstructionValue

variable (D : ComplementObstructionValue X carrier I)

/-- Complement points carrying the distinguished lower value. -/
def lower : Set (X × SignedInterval) :=
  {z | ∃ hz : z ∈ carrierᶜ, D.value z hz = D.lowerValue}

/-- Complement points carrying any other value. -/
def upper : Set (X × SignedInterval) :=
  {z | ∃ hz : z ∈ carrierᶜ, D.value z hz ≠ D.lowerValue}

/-- The lower value class is open in the ambient cylinder. -/
theorem isOpen_lower : IsOpen D.lower := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hz with ⟨hzout, hzvalue⟩
  obtain ⟨U, hUout, hUopen, hzU, hconst⟩ := D.locally_constant z hzout
  refine Filter.mem_of_superset (hUopen.mem_nhds hzU) ?_
  intro w hw
  have hwout : w ∈ carrierᶜ := hUout hw
  refine ⟨hwout, ?_⟩
  calc
    D.value w hwout = D.value z hzout := by
      simpa using hconst w hw
    _ = D.lowerValue := hzvalue

/-- The union of all other value classes is open in the ambient cylinder. -/
theorem isOpen_upper : IsOpen D.upper := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hz with ⟨hzout, hzvalue⟩
  obtain ⟨U, hUout, hUopen, hzU, hconst⟩ := D.locally_constant z hzout
  refine Filter.mem_of_superset (hUopen.mem_nhds hzU) ?_
  intro w hw
  have hwout : w ∈ carrierᶜ := hUout hw
  refine ⟨hwout, ?_⟩
  intro hwvalue
  apply hzvalue
  calc
    D.value z hzout = D.value w hwout := by
      symm
      simpa using hconst w hw
    _ = D.lowerValue := hwvalue

/-- The two value regions are disjoint. -/
theorem disjoint_lower_upper : Disjoint D.lower D.upper := by
  refine Set.disjoint_left.2 ?_
  intro z hzlower hzupper
  rcases hzlower with ⟨hzout₁, hvalue⟩
  rcases hzupper with ⟨hzout₂, hne⟩
  apply hne
  simpa using hvalue

/-- The complement is exactly the union of the two value regions. -/
theorem compl_eq : carrierᶜ = D.lower ∪ D.upper := by
  ext z
  constructor
  · intro hzout
    by_cases hvalue : D.value z hzout = D.lowerValue
    · exact Or.inl ⟨hzout, hvalue⟩
    · exact Or.inr ⟨hzout, hvalue⟩
  · intro hz
    rcases hz with hzlower | hzupper
    · exact hzlower.1
    · exact hzupper.1

/-- Bottom points belong to the lower value region. -/
theorem bottom_subset_lower : signedBottom X ⊆ D.lower := by
  rintro ⟨x, y⟩ hy
  change y = SignedInterval.left at hy
  subst y
  exact ⟨D.bottom_outside rfl, D.bottom_value x⟩

/-- Top points belong to the upper value region. -/
theorem top_subset_upper : signedTop X ⊆ D.upper := by
  rintro ⟨x, y⟩ hy
  change y = SignedInterval.right at hy
  subst y
  exact ⟨D.top_outside rfl, D.top_value_ne x⟩

/-- A locally constant obstruction value constructs the required complement decomposition. -/
def toTopBottomComplement : TopBottomComplement X carrier where
  lower := D.lower
  upper := D.upper
  isOpen_lower := D.isOpen_lower
  isOpen_upper := D.isOpen_upper
  disjoint_lower_upper := D.disjoint_lower_upper
  compl_eq := D.compl_eq
  bottom_subset_lower := D.bottom_subset_lower
  top_subset_upper := D.top_subset_upper

/-- Adding closedness of the carrier gives a top--bottom separator. -/
def toTopBottomSeparator
    (hcarrier : IsClosed carrier) : TopBottomSeparator X :=
  D.toTopBottomComplement.toSeparator hcarrier

end ComplementObstructionValue

end NRR
