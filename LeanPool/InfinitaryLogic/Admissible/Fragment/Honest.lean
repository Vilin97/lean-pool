/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Admissible.Family
import LeanPool.InfinitaryLogic.Lomega1omega.Fragment
/-!
# The honest admissible fragment (issue #18)

A **purely syntactic wrapper**: an ordinary `Fragment`, closed upward under exactly the conjunctions
and disjunctions named by *certified* coded families.

Deliberately absent:

* **no `height`** — whether it belongs to the presentation or is derived is unsettled, and a field
  here would permit a fragment whose height disagreed with its presentation's;
* **no compactness data** — compactness is a theorem with hypotheses, proved externally.  That is
  what makes "a theorem named Barwise compactness merely projects a field" structurally impossible
  rather than merely observed.

This does **not** wrap the legacy `AdmissibleFragmentCore`, which an honest HF fragment provably
cannot instantiate: its `closed_iInf`/`closed_iSup` are *upward* over arbitrary external ℕ-families.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

/-- **An admissible fragment**: an ordinary `Fragment`, closed *upward* under the conjunctions and
disjunctions named by **certified** coded families — and under nothing else.

Parameterized by the **family view**.  This file imports only `Admissible/Family.lean`, so the
syntax interface cannot mention theory decoding or `Sigma1`: the separation is by import, not by
convention.  A richer presentation is used here through its `toFamilyPresentation` projection. -/
structure AdmissibleFragment {L : Language.{u, v}}
    (P : FamilyPresentation.{u, v, uCode, uIndex} L) extends Fragment L where
  iInf_coded_mem : ∀ {n : ℕ} (F : CodedFamily P n),
    (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet) →
      (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet
  iSup_coded_mem : ∀ {n : ℕ} (F : CodedFamily P n),
    (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet) →
      (⟨n, codedISup F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet

end FirstOrder.Language
