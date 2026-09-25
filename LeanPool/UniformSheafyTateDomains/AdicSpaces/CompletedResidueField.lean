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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Completed Residue Fields of the Adic Spectrum

For a Huber pair `(A, A⁺)` and a point `v ∈ Spa(A, A⁺)`, the *completed residue field*
at `v` is the completion of `Frac(A / supp(v))` with respect to the valuation topology
induced by `v`.

## Main definitions

* `ValuationSpectrum.quotientValuation` : The valuation on `A ⧸ supp(v)` induced by `v`.
* `ValuationSpectrum.residueFieldValuation` : The extension to `FractionRing (A ⧸ supp(v))`.
* `ValuationSpectrum.completedResidueField A x` : The completed residue field at a point
  `x ∈ Spa(A, A⁺)`, defined as `Valuation.Completion` of the residue field valuation.

## Construction

Given `v ∈ Spv(A)`:
1. Extract the canonical valuation from `v.toValuativeRel`.
2. Push to `A ⧸ supp(v)` via `Valuation.onQuot`.
3. Extend to `FractionRing (A ⧸ supp(v))` via `Valuation.extendToLocalization`.
4. Complete via `Valuation.Completion`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Section 2.4
-/

@[expose] public section

universe u

namespace ValuationSpectrum

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### The residue valuation -/

/-- The quotient ring `A ⧸ supp(v)` for a point of the valuation spectrum. -/
abbrev residueRing (v : Spv A) := A ⧸ v.supp

/-- The quotient `A ⧸ supp(v)` is an integral domain (since `supp(v)` is prime). -/
instance residueRing.instIsDomain (v : Spv A) : IsDomain (residueRing A v) :=
  Ideal.Quotient.isDomain v.supp

/-- The value group associated to a point of the valuation spectrum. -/
abbrev valueGroup (v : Spv A) :=
  @ValuativeRel.ValueGroupWithZero A _ v.toValuativeRel

/-- The canonical valuation associated to a point of the valuation spectrum. -/
noncomputable def canonicalValuation (v : Spv A) :
    Valuation A (valueGroup A v) :=
  @ValuativeRel.valuation A _ v.toValuativeRel

/-- The valuation on `A ⧸ supp(v)` induced by the canonical valuation of `v`. The
canonical valuation on `A` has `supp(v)` in its kernel, so it descends to the quotient. -/
noncomputable def quotientValuation (v : Spv A) :
    Valuation (residueRing A v) (valueGroup A v) :=
  (canonicalValuation A v).onQuot (le_of_eq
    (@ValuativeRel.supp_eq_valuation_supp A _ v.toValuativeRel))

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- Nonzero elements of `A ⧸ supp(v)` have nonzero valuation. This follows from the
fact that the quotient valuation has trivial support (`Ideal.map_quotient_self`). -/
theorem quotientValuation_ne_zero (v : Spv A)
    {s : residueRing A v} (hs : s ≠ 0) : (quotientValuation A v) s ≠ 0 := by
  -- Use induction on the quotient: s = mk a for some a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  intro h
  apply hs
  -- quotientValuation maps mk a to canonicalValuation a
  -- So canonicalValuation a = 0, meaning a ∈ supp
  have : (canonicalValuation A v) a = 0 := h
  have hmem : a ∈ (canonicalValuation A v).supp := (Valuation.mem_supp_iff _ _).mpr this
  rw [show (canonicalValuation A v).supp = v.supp from
    (@ValuativeRel.supp_eq_valuation_supp A _ v.toValuativeRel).symm] at hmem
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem

/-- The valuation on `FractionRing (A ⧸ supp(v))` extending the quotient valuation. -/
noncomputable def residueFieldValuation (v : Spv A) :
    Valuation (FractionRing (residueRing A v)) (valueGroup A v) :=
  (quotientValuation A v).extendToLocalization
    (fun s hs => by
      simp only [Ideal.primeCompl, Submonoid.mem_mk]
      exact quotientValuation_ne_zero A v (nonZeroDivisors.ne_zero hs))
    (FractionRing (residueRing A v))

/-! ### The completed residue field -/

variable [PlusSubring A]

/-- The completed residue field at a point of the adic spectrum.

For `x ∈ Spa(A, A⁺)`, this is the completion of `FractionRing (A ⧸ supp(x))` with
respect to the valuation topology induced by `x`. -/
noncomputable def completedResidueField (x : ↥(Spa A A⁺)) : Type u :=
  (residueFieldValuation A x.val).Completion

/-- The completed residue field carries a commutative ring structure
(inherited from the uniform completion of the valued fraction field). -/
noncomputable instance completedResidueField.instCommRing
    (x : ↥(Spa A A⁺)) : CommRing (completedResidueField A x) := by
  simp only [completedResidueField, Valuation.Completion]
  infer_instance

end ValuationSpectrum
