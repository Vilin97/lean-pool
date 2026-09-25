/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Tactic.Linarith



/-!
# Order Unit Spaces

An **order unit space** (V, V⁺, 1) is a real ordered vector space with a distinguished
order unit.  Two honesty notes on this encoding: the domination field below is the
*order-unit* boundedness property (`a ≤ r • 1`), not the full Archimedean condition;
and the carried `NormedAddCommGroup`/`NormedSpace` structure is an independent normed
structure, not derived here as the order-unit norm.

## Main definitions

* `OrderUnitSpace` — typeclass for ordered real vector spaces with an order unit
  (order-unit boundedness)
* `OrderUnitSpace.IsEffect` — predicate for the effect space [0, 1]_V

## References

* Alfsen-Shultz, Geometry of State Spaces of Operator Algebras
* van de Wetering, arXiv:1803.11139
-/

@[expose] public section

noncomputable section

/-- An order unit space is a real vector space with a partial order compatible
    with addition and a distinguished order unit (order-unit boundedness; see the
    `archimedean` field note). -/
class OrderUnitSpace (V : Type*) extends
    NormedAddCommGroup V,
    NormedSpace ℝ V,
    PartialOrder V where
  /-- Addition respects order on the left. -/
  add_le_add_left : ∀ (a b : V), a ≤ b → ∀ c, c + a ≤ c + b
  /-- The order unit. -/
  ousUnit : V
  /-- Nonneg scalar mult is monotone. -/
  smul_nonneg_mono : ∀ (r : ℝ), 0 ≤ r → ∀ {a b : V}, a ≤ b → r • a ≤ r • b
  /-- The order unit is positive. -/
  ousUnit_nonneg : (0 : V) ≤ ousUnit
  /-- **Order-unit boundedness** (the order-unit axiom): every element is dominated
      by some nonnegative scalar multiple of the unit, `a ≤ r • 1`.  This is the
      order-unit property, weaker than the full Archimedean condition; the field name
      is retained for continuity. -/
  archimedean : ∀ a : V, ∃ r : ℝ, 0 ≤ r ∧ a ≤ r • ousUnit

namespace OrderUnitSpace

variable {V : Type*} [OrderUnitSpace V]

/-- The distinguished order unit of an order unit space. -/
scoped notation "𝟙" => OrderUnitSpace.ousUnit (V := _)

-- Ordered group lemmas derived from add_le_add_left

theorem add_le_add_right' {a b : V} (h : a ≤ b) (c : V) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact add_le_add_left a b h c

theorem neg_le_neg {a b : V} (h : a ≤ b) : -b ≤ -a := by
  have h1 := add_le_add_right' h (-b)
  rw [add_neg_cancel] at h1
  have h2 := add_le_add_right' h1 (-a)
  simp? [add_assoc, add_neg_cancel, zero_add, add_zero] at h2
  exact h2

theorem neg_nonneg_of_nonpos {a : V} (h : a ≤ 0) : (0 : V) ≤ -a := by
  have := neg_le_neg h
  simp? at this
  exact this

theorem neg_nonpos_of_nonneg {a : V} (h : (0 : V) ≤ a) : -a ≤ 0 := by
  have := neg_le_neg h
  simp? at this
  exact this

theorem sub_nonneg_of_le {a b : V} (h : a ≤ b) : (0 : V) ≤ b - a := by
  have h1 := add_le_add_right' h (-a)
  rw [add_neg_cancel] at h1
  rwa [sub_eq_add_neg]

theorem sub_le_self_of_nonneg {b : V} {a : V} (h : (0 : V) ≤ a) : b - a ≤ b := by
  rw [sub_eq_add_neg]
  have h1 : -a ≤ 0 := neg_nonpos_of_nonneg h
  have h2 := add_le_add_left (-a) (0 : V) h1 b
  rwa [add_zero] at h2

theorem le_add_of_nonneg_right {a b : V} (h : (0 : V) ≤ b) : a ≤ a + b := by
  have h1 := add_le_add_left (0 : V) b h a
  rw [add_zero] at h1
  exact h1

-- Effect space

/-- An effect is an element `a` with `0 ≤ a ≤ 𝟙`. -/
def IsEffect (a : V) : Prop := (0 : V) ≤ a ∧ a ≤ 𝟙

/-- The converse of `sub_nonneg_of_le`: a nonnegative difference gives an inequality. -/
theorem le_of_sub_nonneg {a b : V} (h : (0 : V) ≤ b - a) : a ≤ b := by
  have h1 := add_le_add_left 0 (b - a) h a
  rw [add_zero, add_sub_cancel] at h1
  exact h1

/-- Subtracting a fixed element preserves order. -/
theorem sub_le_sub_right' {a b : V} (h : a ≤ b) (c : V) : a - c ≤ b - c := by
  refine le_of_sub_nonneg ?_
  have hrw : (b - c) - (a - c) = b - a := by abel
  rw [hrw]
  exact sub_nonneg_of_le h

/-- Subtracting from a fixed element reverses order. -/
theorem sub_le_sub_left' {a b : V} (h : a ≤ b) (c : V) : c - b ≤ c - a := by
  refine le_of_sub_nonneg ?_
  have hrw : (c - a) - (c - b) = b - a := by abel
  rw [hrw]
  exact sub_nonneg_of_le h

/-- A nonpositive difference gives an inequality. -/
theorem le_of_sub_nonpos {a b : V} (h : a - b ≤ 0) : a ≤ b := by
  refine le_of_sub_nonneg ?_
  have h1 : (0 : V) ≤ -(a - b) := neg_nonneg_of_nonpos h
  have hrw : -(a - b) = b - a := by abel
  rwa [hrw] at h1

/-- **Monotonicity in the SCALAR**: on a nonnegative element, a larger scalar gives a
larger multiple.  (`smul_nonneg_mono` is monotonicity in the *element*; this is the
companion the class was missing, and the direct-sum carrier's order-unit bound needs it
to compare against `max r₁ r₂`.) -/
theorem smul_le_smul_of_le_of_nonneg {r s : ℝ} (hrs : r ≤ s) {a : V}
    (ha : (0 : V) ≤ a) : r • a ≤ s • a := by
  apply le_of_sub_nonneg
  rw [← sub_smul]
  have h := smul_nonneg_mono (s - r) (by linarith) ha
  rwa [smul_zero] at h

theorem isEffect_zero : IsEffect (0 : V) :=
  ⟨le_refl 0, ousUnit_nonneg⟩

theorem isEffect_unit : IsEffect (𝟙 : V) :=
  ⟨ousUnit_nonneg, le_refl 𝟙⟩

/-- The orthocomplement `𝟙 - a` of an effect is an effect. -/
theorem IsEffect.ortho {a : V} (h : IsEffect a) :
    IsEffect (𝟙 - a) :=
  ⟨sub_nonneg_of_le h.2, sub_le_self_of_nonneg h.1⟩

/-- Two effects are orthogonal if `a + b ≤ 𝟙`. -/
def AreOrthogonal (a b : V) : Prop := a + b ≤ 𝟙

/-- A sharp effect (projective unit) is an effect `p` with no nonzero
    effect below both `p` and `𝟙 - p`. -/
def IsSharp (p : V) : Prop :=
  IsEffect p ∧ ∀ (a : V), IsEffect a → a ≤ p → a ≤ 𝟙 - p → a = 0

/-- Sum of nonneg elements is nonneg. -/
theorem add_nonneg {a b : V} (ha : (0 : V) ≤ a) (hb : (0 : V) ≤ b) :
    (0 : V) ≤ a + b :=
  le_trans ha (le_add_of_nonneg_right hb)

/-- Addition of effects whose sum is bounded. -/
theorem IsEffect.add_of_le_unit {a b : V} (ha : IsEffect a) (hb : IsEffect b)
    (hab : a + b ≤ 𝟙) : IsEffect (a + b) :=
  ⟨add_nonneg ha.1 hb.1, hab⟩

/-! ## The effects span, and linear maps are determined on them

The textbook route proves the spanning property through the order-unit *norm* — if `‖v‖ ≤ ½`
then `0 ≤ ½𝟙 + v ≤ 𝟙`, so the effects contain a ball about `½𝟙`.  That route needs the
carried norm to *be* the order-unit norm, which this class deliberately does not
assert (see the class docstring), and needs the Archimedean property proper rather than
the order-unit boundedness the `archimedean` field carries.

The two conclusions — that the effects span and that linear maps agreeing on effects are
equal — do not need either.  They follow from order-unit boundedness alone, which is what is
proved here: strictly more general than the norm route, and available at exactly this class's
own strength.  The ball clause itself is *not* formalized; it is the textbook route, not its
content. -/

/-- Nonnegative scalars preserve nonnegativity. -/
theorem smul_nonneg' {r : ℝ} (hr : 0 ≤ r) {a : V} (ha : (0 : V) ≤ a) :
    (0 : V) ≤ r • a := by
  have h := smul_nonneg_mono r hr ha
  rwa [smul_zero] at h

/-- A scalar in `[0,1]` times an effect is an effect. -/
theorem isEffect_smul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : V} (ha : IsEffect a) :
    IsEffect (r • a) := by
  refine ⟨smul_nonneg' hr0 ha.1, ?_⟩
  calc r • a ≤ (1 : ℝ) • a := smul_le_smul_of_le_of_nonneg hr1 ha.1
    _ = a := one_smul ℝ a
    _ ≤ 𝟙 := ha.2

/-- A scalar in `[0,1]` times the unit is an effect. -/
theorem isEffect_smul_unit {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsEffect (r • (𝟙 : V)) :=
  isEffect_smul hr0 hr1 isEffect_unit

/-- **The spanning clause.**  The effects span the whole space.  Proof from
order-unit boundedness only: bound `x` above by `r • 𝟙` and `-x` above by `s • 𝟙`, so
that `x + s • 𝟙` is nonnegative and below `(r+s) • 𝟙`; rescaling by
`c = r + s + 1 > 0` lands it in the effects, and `x = c • (that) - s • 𝟙` with `𝟙`
itself an effect. -/
theorem span_isEffect_eq_top :
    Submodule.span ℝ {a : V | IsEffect a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨r, hr0, hr⟩ := archimedean x
  obtain ⟨s, hs0, hs⟩ := archimedean (-x)
  set c : ℝ := r + s + 1 with hc
  have hcpos : (0 : ℝ) < c := by positivity
  -- `x + s • 𝟙` is nonnegative
  have hxs_nonneg : (0 : V) ≤ x + s • 𝟙 := by
    have h := add_le_add_left (-x) (s • 𝟙) hs x
    rwa [add_neg_cancel] at h
  -- and bounded by `c • 𝟙`
  have hxs_le : x + s • 𝟙 ≤ c • (𝟙 : V) := by
    calc x + s • 𝟙 ≤ r • 𝟙 + s • 𝟙 := add_le_add_right' hr _
      _ = (r + s) • (𝟙 : V) := (add_smul r s 𝟙).symm
      _ ≤ c • (𝟙 : V) :=
          smul_le_smul_of_le_of_nonneg (by rw [hc]; linarith) ousUnit_nonneg
  -- so its `c`-rescaling is an effect
  have hy : IsEffect (c⁻¹ • (x + s • 𝟙)) := by
    refine ⟨smul_nonneg' (le_of_lt (inv_pos.mpr hcpos)) hxs_nonneg, ?_⟩
    have h := smul_nonneg_mono c⁻¹ (le_of_lt (inv_pos.mpr hcpos)) hxs_le
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul] at h
  -- and `x` is a combination of it and the unit
  have hx : x = c • (c⁻¹ • (x + s • 𝟙)) - s • 𝟙 := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
    abel
  rw [hx]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span hy))
    (Submodule.smul_mem _ _ (Submodule.subset_span isEffect_unit))

/-- **The extensionality clause.**  Two linear maps agreeing on the effects are
equal.  This is what the spanning property is normally put to use for. -/
theorem linearMap_eq_of_eq_on_effects {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f g : V →ₗ[ℝ] W) (h : ∀ a : V, IsEffect a → f a = g a) : f = g :=
  LinearMap.ext_on span_isEffect_eq_top (fun a ha => h a ha)

/-- **The Archimedean property**, in the sense the standard definition of an order unit space
carries and this class does not.

The class's `archimedean` field is order-unit *boundedness* only — every element is under
*some* multiple of the unit.  This is the genuine Archimedean squeeze: an element under
*every* positive multiple of the unit is nonpositive.  The two are different, and the
difference is what a homogeneity argument consumes at its last step.

★ It is supplied as an explicit `Prop` rather than added to the class, so that any theorem
needing it says so in its own statement.  Nothing is given up by that: the Archimedean property
*is* part of the standard definition of an order unit space — not a stand-in for a cited
result — so a theorem proved under it is proved at the standard generality. -/
def IsArchimedean (V : Type*) [OrderUnitSpace V] : Prop :=
  ∀ x : V, (∀ ε : ℝ, 0 < ε → x ≤ ε • ousUnit) → x ≤ 0

/-- The textbook Archimedean order-unit condition in its `ℕ` form (Alfsen–Shultz,
Paulsen–Tomforde): `n • x ≤ 𝟙` for every positive `n` forces `x ≤ 0`. -/
def IsArchNat (V : Type*) [OrderUnitSpace V] : Prop :=
  ∀ x : V, (∀ n : ℕ, 0 < n → (n : ℝ) • x ≤ (𝟙 : V)) → x ≤ 0

theorem archNat_of_arch {V : Type*} [OrderUnitSpace V] (h : IsArchimedean V) :
    IsArchNat V := by
  intro x hx
  refine h x ?_
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have h2 := smul_nonneg_mono ((n : ℝ))⁻¹ (by positivity) (hx n hn0)
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hnpos), one_smul] at h2
  have h3 : ((n : ℝ))⁻¹ ≤ ε := by
    rw [div_lt_iff₀ hε] at hn
    rw [inv_eq_one_div, div_le_iff₀ hnpos]
    nlinarith
  exact le_trans h2 (smul_le_smul_of_le_of_nonneg h3 ousUnit_nonneg)

theorem arch_of_archNat {V : Type*} [OrderUnitSpace V] (h : IsArchNat V) :
    IsArchimedean V := by
  intro x hx
  refine h x ?_
  intro n hn0
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have h2 := smul_nonneg_mono ((n : ℝ)) (le_of_lt hnpos) (hx ((n : ℝ))⁻¹ (by positivity))
  rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hnpos), one_smul] at h2

/-- **`IsArchimedean` is exactly the textbook notion — neither stronger nor weaker.**

This matters for honesty, not for any proof.  A theorem proved under `IsArchimedean` is claimed
to hold at the standard generality of an order unit space, on the grounds that the Archimedean
property is *part of the standard definition* rather than a stand-in for a cited result.  That
defence is only as good as the claim that this `Prop` is the standard condition — so here it
is, machine-checked in both directions against the `ℕ` form. -/
theorem arch_iff {V : Type*} [OrderUnitSpace V] : IsArchimedean V ↔ IsArchNat V :=
  ⟨archNat_of_arch, arch_of_archNat⟩

end OrderUnitSpace
