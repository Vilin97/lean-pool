/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module
public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Notation.Indicator
public import LeanPool.PFR.AddCombi.Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.NNReal.Star

public import LeanPool.PFR.AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pointwise.Finset.Density
public import Mathlib.Analysis.Complex.Basic

/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `conv`: Discrete convolution of two functions in the compact normalisation
* `dconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/


open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G H K L : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section Semifield
variable [Semifield K] [CharZero K] {f g : G → K}

/-- Compact convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b + c = a`. -/
@[expose]
public
def conv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2

@[inherit_doc] infixl:71 " ∗ " => conv

public
lemma conv_apply (f g : G → K) (a : G) :
    (f ∗ g) a = 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl





















public
lemma conv_comm (f g : G → K) : f ∗ g = g ∗ f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])















public
lemma conv_eq_expect_sub (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f (a - t) * g t := by
  rw [conv_apply]
  refine expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
    ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop

public
lemma conv_eq_expect_add (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f (a + t) * g (-t) :=
  (conv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

public
lemma conv_eq_expect_sub' (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f t * g (a - t) := by
  rw [conv_comm, conv_eq_expect_sub]; grind



public
lemma conv_apply_add (f g : G → K) (a b : G) : (f ∗ g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (conv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc]

















variable [StarRing K]

/-- Compact difference convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b - c = a`. -/
@[expose]
public
def dconv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

@[inherit_doc] infixl:71 " ○ " => dconv





@[simp]
public
lemma conv_conjneg (f g : G → K) : f ∗ conjneg g = f ○ g :=
  funext fun a ↦ expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
    (fun x y _ _ h ↦ by grind) fun x hx ↦
      ⟨(x.1, -x.2), by grind, by simp⟩







@[simp]
public
lemma conj_conv (f g : G → K) : conj (f ∗ g) = conj f ∗ conj g :=
  funext fun a ↦ by simp only [Pi.conj_apply, conv_apply, map_expect, map_mul]

@[simp]
public
lemma conj_dconv (f g : G → K) : conj (f ○ g) = conj f ○ conj g := by
  simp_rw [← conv_conjneg, conj_conv, conjneg_conj]

public
lemma IsSelfAdjoint.conv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ g) :=
  (conj_conv _ _).trans <| congr_arg₂ _ hf hg

public
lemma IsSelfAdjoint.dconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ○ g) :=
  (conj_dconv _ _).trans <| congr_arg₂ _ hf hg

























--TODO: Can we generalise to star ring homs?
-- lemma map_dconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ g) a) : ℝ) = ((↑) ∘ f ○ (↑) ∘ g) a := by
--   simp_rw [dconv_apply, NNReal.coe_expect, NNReal.coe_mul, starRingEnd_apply, star_trivial,
--     Function.comp_apply]

public
lemma dconv_eq_expect_add (f g : G → K) (a : G) : (f ○ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  simp [← conv_conjneg, conv_eq_expect_add]

public
lemma dconv_eq_expect_sub (f g : G → K) (a : G) : (f ○ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  simp [← conv_conjneg, conv_eq_expect_sub']





public
lemma expect_dconv_mul (f g h : G → K) :
    𝔼 a, (f ○ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

public
lemma expect_dconv (f g : G → K) : 𝔼 a, (f ○ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1









public
lemma dconv_indicator_one (f : G → K) (s : Finset G) :
    f ○ 𝟭_[s] = (∑ a ∈ s, τ (-a) f) /ℚ Fintype.card G := by
  ext; simp [dconv_eq_expect_add, Set.indicator_apply, expect]

public
lemma indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = (s ∩ (a +ᵥ t)).dens := by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

public
lemma indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = s.addConvolution (-t) a / card G := by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp

public
lemma expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) a = s.dens * t.dens := by
  simp [expect_dconv, Set.conj_indicator_one_apply]; simp [← Pi.one_def]

public
lemma expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) x ^ 2 = E[s, t] := by
  suffices
      ∑ x, #{yz ∈ s ×ˢ t | yz.1 - yz.2 = x} ^ 2 =
        #{x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2} by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm

end Semifield

section Field
variable [Field K] [CharZero K]










variable [StarRing K]










end Field

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)









end RCLike

namespace Complex
variable (f g : G → ℝ) (a : G)









end Complex

namespace NNReal
variable (f g : G → ℝ≥0) (a : G)









end NNReal
