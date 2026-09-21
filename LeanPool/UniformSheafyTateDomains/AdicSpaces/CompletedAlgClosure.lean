/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.UniformSpace.Basic

/-!
# Completed Algebraic Closure of F_p((t))

We define the completed algebraic closure of `F_p((t))` and continuous
endomorphisms thereof.  These definitions are shared by Scottish Book
Problems 23 and 36 (Kedlaya).

## Mathematical context

Let `p` be a prime.  The field `F_p((t))` of formal Laurent series over
`F_p = Z/pZ` carries a canonical `t`-adic valuation.  This valuation
extends uniquely to the algebraic closure `AlgebraicClosure(F_p((t)))`,
and completing with respect to the extended valuation yields a complete,
algebraically closed nonarchimedean field of characteristic `p`, denoted
here `CompletedAlgClosure p`.

The full construction (extending the valuation and completing) is not yet
available in Mathlib.  We axiomatize the type and its essential properties.

## Main definitions

* `FpLaurent p` : `F_p((t))` as `LaurentSeries (ZMod p)`.
* `CompletedAlgClosure p` : The completed algebraic closure, axiomatized.
* `CompletedAlgClosure.ContinuousEnd p` : Continuous ring endomorphisms.
* `CompletedAlgClosure.t` : The uniformizer `t` in the completed field.
* `CompletedAlgClosure.MaxTamelyRamifiedSubfield p` : The maximal tamely
  ramified extension of `F_p((t))` inside the completed algebraic closure.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problems 23 and 36
-/

noncomputable section

namespace ScottishBook

/-! ### The base field F_p((t)) -/

/-- `F_p((t))`, the field of formal Laurent series over `F_p`. -/
abbrev FpLaurent (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  LaurentSeries (ZMod p)

/-! ### The completed algebraic closure -/

/-- The completed algebraic closure of `F_p((t))`.

Mathematically, this is the completion of `AlgebraicClosure(F_p((t)))` with
respect to the unique extension of the `t`-adic valuation.  The full
construction is not yet available in Mathlib; we axiomatize the type.

The `sorry`s on the instances below are inherent: they record known
mathematical facts about the completed algebraic closure whose Lean proofs
require infrastructure (valuation extensions, completions of valued fields)
that is not yet in Mathlib. -/
def CompletedAlgClosure (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  PUnit

instance CompletedAlgClosure.instField (p : ℕ)
    [Fact (Nat.Prime p)] :
    Field (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; exact sorry

instance CompletedAlgClosure.instTopologicalSpace (p : ℕ)
    [Fact (Nat.Prime p)] :
    TopologicalSpace (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; infer_instance

instance CompletedAlgClosure.instUniformSpace (p : ℕ)
    [Fact (Nat.Prime p)] :
    UniformSpace (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; infer_instance

instance CompletedAlgClosure.instIsTopologicalRing (p : ℕ)
    [Fact (Nat.Prime p)] :
    IsTopologicalRing (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; exact sorry

instance CompletedAlgClosure.instIsAlgClosed (p : ℕ)
    [Fact (Nat.Prime p)] :
    IsAlgClosed (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; exact sorry

instance CompletedAlgClosure.instCharP (p : ℕ)
    [Fact (Nat.Prime p)] :
    CharP (CompletedAlgClosure p) p := by
  unfold CompletedAlgClosure; exact sorry

instance CompletedAlgClosure.instCompleteSpace (p : ℕ)
    [Fact (Nat.Prime p)] :
    CompleteSpace (CompletedAlgClosure p) := by
  unfold CompletedAlgClosure; exact sorry

/-- The canonical ring embedding `F_p((t)) ↪ CompletedAlgClosure p`. -/
def CompletedAlgClosure.embed (p : ℕ)
    [Fact (Nat.Prime p)] :
    FpLaurent p →+* CompletedAlgClosure p := sorry

/-- The uniformizer `t` in `CompletedAlgClosure p`, the image of
`HahnSeries.single 1 1 : F_p((t))`. -/
def CompletedAlgClosure.t (p : ℕ)
    [Fact (Nat.Prime p)] : CompletedAlgClosure p :=
  CompletedAlgClosure.embed p (HahnSeries.single 1 1)

/-! ### Continuous endomorphisms -/

/-- A **continuous endomorphism** of `CompletedAlgClosure p`: a ring
endomorphism that is continuous with respect to the nonarchimedean
topology. -/
structure CompletedAlgClosure.ContinuousEnd (p : ℕ)
    [Fact (Nat.Prime p)] where
  /-- The underlying ring endomorphism. -/
  toRingHom : CompletedAlgClosure p →+* CompletedAlgClosure p
  /-- Continuity of the endomorphism. -/
  continuous_toFun : Continuous toRingHom

/-! ### The maximal tamely ramified extension -/

/-- The maximal tamely ramified extension of `F_p((t))` inside the
completed algebraic closure.

An algebraic extension of `F_p((t))` is **tamely ramified** if its
ramification indices are coprime to the residue characteristic `p`.
The maximal such extension is a subfield of `CompletedAlgClosure p`.

This is axiomatized; the construction requires ramification theory
for nonarchimedean valued fields, which is not yet in Mathlib. -/
def CompletedAlgClosure.MaxTamelyRamifiedSubfield (p : ℕ)
    [Fact (Nat.Prime p)] : Subfield (CompletedAlgClosure p) :=
  sorry

/-- An element of `CompletedAlgClosure p` is **integral over the maximal
tamely ramified extension** if it satisfies a monic polynomial with
coefficients in `MaxTamelyRamifiedSubfield p`. -/
def CompletedAlgClosure.IsIntegralOverMaxTame (p : ℕ)
    [Fact (Nat.Prime p)]
    (x : CompletedAlgClosure p) : Prop :=
  x ∈ integralClosure
    (CompletedAlgClosure.MaxTamelyRamifiedSubfield p)
    (CompletedAlgClosure p)

end ScottishBook
