/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# Euler-normality surjectivity on a right quotient

This file isolates the quotient argument used in the Stafford proof. A right
ideal is a submodule of the regular right module, encoded as an
`Aᵐᵒᵖ`-submodule of `A`.
-/

namespace Stafford38.EulerSurjectivity

variable {A : Type*} [Ring A]

/-- A right ideal, represented as a submodule of the regular right module. -/
abbrev RightIdeal (A : Type*) [Ring A] := Submodule Aᵐᵒᵖ A

/-- The additive quotient by a right ideal, with its induced right action. -/
abbrev RightQuotient (I : RightIdeal A) := A ⧸ I

/-- The quotient class of a ring element. -/
def qmk (I : RightIdeal A) (a : A) : RightQuotient I :=
  Submodule.Quotient.mk a

/-- Right multiplication on the quotient. -/
def rightMul (I : RightIdeal A) (a : A) (q : RightQuotient I) :
    RightQuotient I :=
  MulOpposite.op a • q

lemma qmk_right_mul (I : RightIdeal A) (a b : A) :
    qmk I (a * b) = rightMul I b (qmk I a) := by
  exact Submodule.Quotient.mk_smul I (MulOpposite.op b) a

/-- Elements whose quotient classes have representatives in `R`. -/
def ReducesTo (I : RightIdeal A) (R : Subring A) (a : A) : Prop :=
  ∃ r : R, qmk I a = qmk I (r : A)

/-- Right multipliers preserving the classes represented by `R`. -/
def preservers (I : RightIdeal A) (R : Subring A) : Subring A where
  carrier := {a | ∀ r : R, ReducesTo I R ((r : A) * a)}
  zero_mem' := by
    intro r
    exact ⟨0, by simp [ReducesTo, qmk]⟩
  one_mem' := by
    intro r
    exact ⟨r, by simp [ReducesTo]⟩
  add_mem' := by
    intro a b ha hb r
    obtain ⟨s, hs⟩ := ha r
    obtain ⟨t, ht⟩ := hb r
    refine ⟨s + t, ?_⟩
    simpa [ReducesTo, mul_add, qmk, Submodule.Quotient.mk_add] using
      congrArg₂ (· + ·) hs ht
  neg_mem' := by
    intro a ha r
    obtain ⟨s, hs⟩ := ha r
    refine ⟨-s, ?_⟩
    simpa [ReducesTo, qmk] using congrArg Neg.neg hs
  mul_mem' := by
    intro a b ha hb r
    obtain ⟨s, hs⟩ := ha r
    obtain ⟨t, ht⟩ := hb s
    refine ⟨t, ?_⟩
    have hright := congrArg (rightMul I b) hs
    rw [← qmk_right_mul, ← qmk_right_mul] at hright
    simpa [mul_assoc] using hright.trans ht

lemma subring_le_preservers (I : RightIdeal A) (R : Subring A) :
    R ≤ preservers I R := by
  intro a ha r
  exact ⟨r * ⟨a, ha⟩, rfl⟩

/--
The quotient form of the positive Euler argument.

The relation `1 + U*x ∈ I`, normality `x*R ⊆ R*x`, the Euler element
`E = x*p ∈ R`, and generation of `A` by `R` and `p` imply that right
multiplication by `x` is onto `A/I`.
-/
theorem rightMul_surjective_of_euler_normal
    (I : RightIdeal A) (R : Subring A) (x p : A)
    (hnormal : ∀ r : R, ∃ s : R, x * (r : A) = (s : A) * x)
    (hE : x * p ∈ R)
    (hresidue : ∃ U : R, 1 + (U : A) * x ∈ I)
    (hgenerate : Subring.closure ((R : Set A) ∪ {p}) = ⊤) :
    Function.Surjective (rightMul I x) := by
  obtain ⟨U, hU⟩ := hresidue

  have hp : p ∈ preservers I R := by
    intro r
    obtain ⟨s, hs⟩ := hnormal r
    refine ⟨-(U * s * ⟨x * p, hE⟩), ?_⟩
    apply (Submodule.Quotient.eq I).2
    have hmem := I.smul_mem (MulOpposite.op ((r : A) * p)) hU
    change (1 + (U : A) * x) * ((r : A) * p) ∈ I at hmem
    convert hmem using 1
    all_goals simp only [Subring.coe_neg, Subring.coe_mul]
    calc
      (r : A) * p - -((U : A) * (s : A) * (x * p)) =
          (r : A) * p + (U : A) * ((s : A) * x) * p := by noncomm_ring
      _ = (r : A) * p + (U : A) * (x * (r : A)) * p := by rw [hs]
      _ = (1 + (U : A) * x) * ((r : A) * p) := by noncomm_ring

  have hall : preservers I R = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    apply Subring.closure_le.2
    intro a ha
    rcases ha with ha | rfl
    · exact subring_le_preservers I R ha
    · simpa using hp

  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I q
  have ha : a ∈ preservers I R := by
    rw [hall]
    trivial
  obtain ⟨r, hr⟩ := ha (1 : R)
  have har : qmk I a = qmk I (r : A) := by simpa using hr
  obtain ⟨s, hs⟩ := hnormal r
  refine ⟨qmk I (-((U : A) * (s : A))), ?_⟩
  change rightMul I x (qmk I (-((U : A) * (s : A)))) = qmk I a
  rw [har, ← qmk_right_mul]
  apply (Submodule.Quotient.eq I).2
  have hmem := I.smul_mem (MulOpposite.op (r : A)) hU
  change (1 + (U : A) * x) * (r : A) ∈ I at hmem
  have hmemneg := I.neg_mem hmem
  change -((1 + (U : A) * x) * (r : A)) ∈ I at hmemneg
  convert hmemneg using 1
  calc
    (-((U : A) * (s : A))) * x - (r : A) =
        -((r : A) + (U : A) * ((s : A) * x)) := by noncomm_ring
    _ = -((r : A) + (U : A) * (x * (r : A))) := by rw [hs]
    _ = -((1 + (U : A) * x) * (r : A)) := by noncomm_ring


end Stafford38.EulerSurjectivity
