/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Four-factor refinement

This file defines the binary four-factor refinement property for a commutative monoid and relates
it to Mathlib's predicates `IsPrimal` and `DecompositionMonoid`. This is the algebraic form of
Conway's refinement conjecture in *On Numbers and Games*, page 46, and in LM24,
Conjecture 1.1.1(2).

The equivalence itself is Cohn, Theorem 2.2, in its four-factor case. Cohn shows that an
integrally closed domain is Schreier — every element primal — exactly when any two factorisations
of an element admit a common refinement, and the forward direction of his proof is the four-factor
argument reproduced below. The name "primal" is his; "pre-Schreier", for the same condition
without integral closure, is Zafrullah's. What follows drops the domain and integral-closure
hypotheses and keeps the binary case, which is what the refinement conjecture needs.

For commutative monoids with zero, cancellation away from zero is needed only in the reverse
implication from primality to four-factor refinement. The zero case uses the absence of zero
divisors supplied by `IsCancelMulZero`. These generic equivalences do not assert that the omnific
integers satisfy either equivalent property; that specialization remains Conway's refinement
conjecture.
-/

universe u

public section

/-- A commutative monoid has four-factor refinement if every equality `a * b = c * d` admits
elements `e`, `f`, `g`, and `h` such that
`a = e * f`, `b = g * h`, `c = e * g`, and `d = f * h`. -/
def HasFourFactorRefinement (R : Type u) [CommMonoid R] : Prop :=
  ∀ a b c d : R, a * b = c * d →
    ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

/-- The defining condition for four-factor refinement. -/
theorem hasFourFactorRefinement_def {R : Type u} [CommMonoid R] :
    HasFourFactorRefinement R ↔
      ∀ a b c d : R, a * b = c * d →
        ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  (Iff.rfl)

namespace HasFourFactorRefinement

variable {R : Type u} [CommMonoid R]

/-- Four-factor refinement is preserved by a multiplicative equivalence. -/
theorem map_mulEquiv {S : Type*} [CommMonoid S]
    (hR : HasFourFactorRefinement R) (e : R ≃* S) : HasFourFactorRefinement S := by
  rw [hasFourFactorRefinement_def]
  intro a b c d habcd
  have hsource : e.symm a * e.symm b = e.symm c * e.symm d := by
    simpa only [map_mul] using congrArg e.symm habcd
  obtain ⟨f, g, h, i, haf, hbg, hch, hdi⟩ := hR _ _ _ _ hsource
  exact ⟨e f, e g, e h, e i,
    by simpa only [map_mul, e.apply_symm_apply] using congrArg e haf,
    by simpa only [map_mul, e.apply_symm_apply] using congrArg e hbg,
    by simpa only [map_mul, e.apply_symm_apply] using congrArg e hch,
    by simpa only [map_mul, e.apply_symm_apply] using congrArg e hdi⟩

/-- Obtain four refinement factors from an equality of two products. -/
theorem refine (hR : HasFourFactorRefinement R) {a b c d : R} (h : a * b = c * d) :
    ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  hasFourFactorRefinement_def.mp hR a b c d h

/-- Every element of a commutative monoid with four-factor refinement is primal. -/
theorem isPrimal (hR : HasFourFactorRefinement R) (a : R) : IsPrimal a := by
  intro b c hadvd
  obtain ⟨q, hq⟩ := hadvd
  obtain ⟨e, f, g, h, ha, _, hb, hc⟩ := hR.refine hq.symm
  exact ⟨e, f, ⟨g, hb⟩, ⟨h, hc⟩, ha⟩

/-- A commutative monoid with four-factor refinement is a decomposition monoid. -/
theorem decompositionMonoid (hR : HasFourFactorRefinement R) : DecompositionMonoid R :=
  ⟨hR.isPrimal⟩

end HasFourFactorRefinement

/-- Multiplicatively equivalent commutative monoids have four-factor refinement simultaneously. -/
theorem MulEquiv.hasFourFactorRefinement_iff
    {R : Type u} {S : Type*} [CommMonoid R] [CommMonoid S] (e : R ≃* S) :
    HasFourFactorRefinement R ↔ HasFourFactorRefinement S :=
  ⟨fun h ↦ h.map_mulEquiv e, fun h ↦ h.map_mulEquiv e.symm⟩

section CancelMulZero

variable {R : Type u} [CommMonoidWithZero R] [IsCancelMulZero R]

/-- A product equality with one nonzero primal factor has a four-factor refinement. -/
theorem exists_fourFactorRefinement_of_isPrimal
    {a b c d : R} (ha0 : a ≠ 0) (ha : IsPrimal a) (habcd : a * b = c * d) :
    ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  have hadvd : a ∣ c * d := ⟨b, habcd.symm⟩
  obtain ⟨e, f, hec, hfd, haef⟩ := ha hadvd
  obtain ⟨g, hcg⟩ := hec
  obtain ⟨h, hdh⟩ := hfd
  refine ⟨e, f, g, h, haef, ?_, hcg, hdh⟩
  apply mul_left_cancel₀ ha0
  calc
    a * b = c * d := habcd
    _ = (e * g) * (f * h) := by rw [hcg, hdh]
    _ = (e * f) * (g * h) := by ac_rfl
    _ = a * (g * h) := by rw [← haef]

/-- Splice an equation-local refinement of one factor with primality of the complementary factor.
If `a = t * w`, the retained factor `t` has been split as `e * f` with `e ∣ c` and `f ∣ d`,
and `w` is primal, then the original divisibility `a ∣ c * d` has a primal refinement. -/
theorem exists_primalRefinement_of_factor_refinement
    {a b c d t w e f : R} (ha0 : a ≠ 0) (hab : a * b = c * d)
    (hatw : a = t * w) (htef : t = e * f) (hec : e ∣ c) (hfd : f ∣ d)
    (hw : IsPrimal w) :
    ∃ a₁ a₂, a₁ ∣ c ∧ a₂ ∣ d ∧ a = a₁ * a₂ := by
  obtain ⟨g, hcg⟩ := hec
  obtain ⟨h, hdh⟩ := hfd
  have ht0 : t ≠ 0 := fun ht ↦ ha0 (by rw [hatw, ht, zero_mul])
  have hwdiv : w ∣ g * h := by
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ ht0
    calc
      t * (g * h) = (e * f) * (g * h) := by rw [htef]
      _ = (e * g) * (f * h) := by ac_rfl
      _ = c * d := by rw [← hcg, ← hdh]
      _ = a * b := hab.symm
      _ = t * (w * b) := by rw [hatw]; ac_rfl
  obtain ⟨w₁, w₂, ⟨u, hgu⟩, ⟨v, hhv⟩, hww⟩ := hw hwdiv
  refine ⟨e * w₁, f * w₂, ⟨u, ?_⟩, ⟨v, ?_⟩, ?_⟩
  · rw [hcg, hgu]
    ac_rfl
  · rw [hdh, hhv]
    ac_rfl
  · rw [hatw, htef, hww]
    ac_rfl

/-- A commutative decomposition monoid with cancellation away from zero has four-factor
refinement. -/
theorem hasFourFactorRefinement_of_decompositionMonoid [DecompositionMonoid R] :
    HasFourFactorRefinement R := by
  intro a b c d hab
  by_cases ha : a = 0
  · subst a
    have hcd : c * d = 0 := by simpa using hab.symm
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hcd with rfl | rfl
    · exact ⟨0, d, b, 1, by simp⟩
    · exact ⟨c, 0, 1, b, by simp⟩
  · have hadvd : a ∣ c * d := ⟨b, hab.symm⟩
    obtain ⟨e, f, hec, hfd, haef⟩ := DecompositionMonoid.primal a hadvd
    obtain ⟨g, hcg⟩ := hec
    obtain ⟨h, hdh⟩ := hfd
    refine ⟨e, f, g, h, haef, ?_, hcg, hdh⟩
    apply mul_left_cancel₀ ha
    calc
      a * b = c * d := hab
      _ = (e * g) * (f * h) := by rw [hcg, hdh]
      _ = (e * f) * (g * h) := by ac_rfl
      _ = a * (g * h) := by rw [← haef]

/-- Four-factor refinement is equivalent to primality of every element. -/
theorem hasFourFactorRefinement_iff_forall_isPrimal :
    HasFourFactorRefinement R ↔ ∀ a : R, IsPrimal a := by
  constructor
  · exact fun hR a ↦ hR.isPrimal a
  · intro h
    letI : DecompositionMonoid R := ⟨h⟩
    exact hasFourFactorRefinement_of_decompositionMonoid

/-- Four-factor refinement is equivalent to the decomposition-monoid property. -/
theorem hasFourFactorRefinement_iff_decompositionMonoid :
    HasFourFactorRefinement R ↔ DecompositionMonoid R := by
  rw [hasFourFactorRefinement_iff_forall_isPrimal, decompositionMonoid_iff]

end CancelMulZero

namespace Subring

variable {R : Type u} [CommRing R]

/-- Four-factor refinement in a subring is equivalent to ambient refinement with all four
factors retained in the subring. -/
theorem hasFourFactorRefinement_iff (S : Subring R) :
    HasFourFactorRefinement S ↔
      ∀ a b c d : R, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a * b = c * d →
        ∃ e f g h : R,
          e ∈ S ∧ f ∈ S ∧ g ∈ S ∧ h ∈ S ∧
            a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  constructor
  · intro hS a b c d ha hb hc hd habcd
    obtain ⟨e, f, g, h, hA, hB, hC, hD⟩ :=
      hS.refine (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩) (d := ⟨d, hd⟩)
        (Subtype.ext habcd)
    exact ⟨e, f, g, h, e.2, f.2, g.2, h.2,
      congrArg Subtype.val hA, congrArg Subtype.val hB,
      congrArg Subtype.val hC, congrArg Subtype.val hD⟩
  · intro hS a b c d habcd
    obtain ⟨e, f, g, h, he, hf, hg, hh, hA, hB, hC, hD⟩ :=
      hS a b c d a.2 b.2 c.2 d.2 (congrArg Subtype.val habcd)
    exact ⟨⟨e, he⟩, ⟨f, hf⟩, ⟨g, hg⟩, ⟨h, hh⟩,
      Subtype.ext hA, Subtype.ext hB, Subtype.ext hC, Subtype.ext hD⟩

/-- A decomposition subring refines every ambient product equality whose four entries lie in
the subring. -/
theorem exists_fourFactorRefinement_of_decompositionMonoid
    (S : Subring R) [IsDomain S] [DecompositionMonoid S]
    {a b c d : R} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (habcd : a * b = c * d) :
    ∃ e f g h : R,
      e ∈ S ∧ f ∈ S ∧ g ∈ S ∧ h ∈ S ∧
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  exact (hasFourFactorRefinement_iff S).mp
    hasFourFactorRefinement_of_decompositionMonoid a b c d ha hb hc hd habcd

end Subring
