/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import LeanPool.HopfieldNet.Tools.ComputableReal.SpecialFunctions.Sqrt
import LeanPool.HopfieldNet.Tools.ComputableReal.IsComputable

#exit

/- Type class stating that `x:ℂ` has a ComputableℝSeq for its real and imaginary parts.
Note that we can't define this as `IsComputable x.re`+`IsComputable x.im`, because then
(if `x` is a noncomputable expression), this will be a noncomputable expression. -/
-- class IsComputableℂ (x : ℂ) : Type where
--     re : ComputableℝSeq
--     im : ComputableℝSeq
--     -- prop_re : re.val = x.re
--     -- prop_im : im.val = x.im]
class IsComputableℂ (x : ℂ) : Type where
    re : IsComputable x.re
    im : IsComputable x.im

namespace IsComputableℂ

open ComplexConjugate

/-- Turns one `IsComputableℂ` into another one, given a proof that they're equal. This is directly
analogous to `decidable_of_iff`, as a way to avoid `Eq.rec` on data-carrying instances. -/
def lift_eq {x y : ℂ} (h : x = y) [hx : IsComputableℂ x] : IsComputableℂ y :=
  ⟨hx.1.lift_eq (congrArg _ h), hx.2.lift_eq (congrArg _ h)⟩

--We'll need some version of this once we want nontrivial functions, like exp/sin.

-- def lift (fr : ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq)
--     (h : ∀ a, (fs a).val = fr a.val) :
--     IsComputable x → IsComputable (fr x) :=
--   fun ⟨sx, hsx⟩ ↦ ⟨fs sx, hsx ▸ h sx⟩

-- def lift₂ (fr : ℝ → ℝ → ℝ) (fs : ComputableℝSeq → ComputableℝSeq → ComputableℝSeq)
--     (h : ∀a b, (fs a b).val = fr a.val b.val) :
--     IsComputable x → IsComputable y → IsComputable (fr x y) :=
--   fun ⟨sx, hsx⟩ ⟨sy, hsy⟩ ↦ ⟨fs sx sy, hsx ▸ hsy ▸ h sx sy⟩

variable (x y : ℂ) [hx : IsComputableℂ x] [hy : IsComputableℂ y]

variable (r : ℝ) [hr : IsComputable r]

instance instComputableRe : IsComputable x.re :=
  hx.re

instance instComputableIm : IsComputable x.im :=
  hx.im

instance instComputableRI [hi : IsComputable i] : IsComputableℂ ⟨r, i⟩ :=
  ⟨hr, hi⟩

instance instComputableI : IsComputableℂ .I :=
  ⟨inferInstanceAs (IsComputable 0), inferInstanceAs (IsComputable 1)⟩

instance instComputableNat (n : ℕ) : IsComputableℂ n :=
  ⟨inferInstanceAs (IsComputable n), inferInstanceAs (IsComputable 0)⟩

instance instComputableInt (z : ℤ) : IsComputableℂ z :=
  ⟨inferInstanceAs (IsComputable z), inferInstanceAs (IsComputable 0)⟩

--TODO drop noncomputable when bump mathlib
noncomputable instance instComputableRat (q : ℚ) : IsComputableℂ q :=
  ⟨inferInstanceAs (IsComputable q), inferInstanceAs (IsComputable 0)⟩

instance instComputableReal : IsComputableℂ r :=
  ⟨hr, inferInstanceAs (IsComputable 0)⟩

instance instComputableOfNat0 : IsComputableℂ
    (@OfNat.ofNat.{0} ℂ 0 (@Zero.toOfNat0.{0} ℂ inferInstance)) :=
  ⟨inferInstanceAs (IsComputable 0), inferInstanceAs (IsComputable 0)⟩

instance instComputableOfNat1 : IsComputableℂ
    (@OfNat.ofNat.{0} ℂ 1 (@One.toOfNat1.{0} ℂ inferInstance)) :=
  ⟨inferInstanceAs (IsComputable 1), inferInstanceAs (IsComputable 0)⟩

instance instComputableOfNatAtLeastTwo (n : ℕ) [n.AtLeastTwo] : IsComputableℂ ofNat(n) :=
  ⟨inferInstanceAs (IsComputable n), inferInstanceAs (IsComputable 0)⟩

instance instComputableNeg : IsComputableℂ (-x) :=
  ⟨let _ := hx.1; inferInstanceAs (IsComputable (-x.re)),
  let _ := hx.2; inferInstanceAs (IsComputable (-x.im))⟩

instance instComputableAdd : IsComputableℂ (x + y) :=
  ⟨let _ := hx.1; let _ := hy.1; inferInstanceAs (IsComputable (x.re + y.re)),
  let _ := hx.2; let _ := hy.2; inferInstanceAs (IsComputable (x.im + y.im))⟩

instance instComputableSub : IsComputableℂ (x - y) :=
  ⟨let _ := hx.1; let _ := hy.1; inferInstanceAs (IsComputable (x.re - y.re)),
  let _ := hx.2; let _ := hy.2; inferInstanceAs (IsComputable (x.im - y.im))⟩

/-
TODO: Multiplication uses each component, twice; this means that long product expressions
  of complex numbers experience an exponential slowdown. Since we don't do any kind of caching,
  the correct solution would be to make `IsComputableℂ` actually carry a `ℕ → QInterval × QInterval`
  for evaluation, together with proofs that each half is a `ComputableℝSeq`. (Or to define more
  new types, like a `ComputableℂSeq` that captures all this.)
-/
@[inline]
instance instComputableMul : IsComputableℂ (x * y) :=
  let _ := hx.1;
  let _ := hy.1;
  let _ := hx.2;
  let _ := hy.2;
  ⟨inferInstanceAs (IsComputable (_ - _)), inferInstanceAs (IsComputable (_ + _))⟩

instance instComputableNatPow (n : ℕ) : IsComputableℂ (x ^ n) := by
  /- TODO do this by exponentation by squaring -/
  induction n
  · rw [pow_zero]
    infer_instance
  · rw [pow_succ]
    infer_instance

/-
This could be just `inferInstanceAs (IsComputable (_ + _))`, because `Complex.normSq`
is defeq to `x.re * x.re + x.im * x.im`. But doing that naively means we evaluate `x.re`
and `x.im` each twice. If (when?) we get a faster implementation of natpow, this will
be more efficient.
-/
instance instComputableNormSq : IsComputable (Complex.normSq x) :=
  .lift_eq (x := x.re ^ 2 + x.im ^ 2) (by rw [Complex.normSq, pow_two, pow_two]; rfl)
    inferInstance

instance instComputableStar : IsComputableℂ (conj x) :=
  ⟨hx.1, let _ := hx.2; inferInstanceAs (IsComputable (-x.im))⟩

instance instComputableInv : IsComputableℂ (x⁻¹) :=
  ⟨let _ := hx.1; .lift_eq (Complex.inv_re x).symm inferInstance,
  let _ := hx.2; .lift_eq (Complex.inv_im x).symm inferInstance⟩

instance instComputableDiv : IsComputableℂ (x / y) :=
  inferInstanceAs (IsComputableℂ (_ * _))

instance instComputableZPow (z : ℤ) : IsComputableℂ (x ^ z) :=
  z.casesOn
    (fun a ↦ inferInstanceAs (IsComputableℂ (x ^ a)))
    (fun a ↦ inferInstanceAs (IsComputableℂ (x ^ a.succ)⁻¹))

noncomputable instance instComputableNSMul (n : ℕ) : IsComputableℂ (n • x) :=
   ⟨let _ := hx.1; .lift_eq (Complex.re_nsmul n x).symm inferInstance,
  let _ := hx.2; .lift_eq (Complex.im_nsmul n x).symm inferInstance⟩

--Need it to pick the right instance for the smul. Probably a better way to do this
attribute [-instance] Complex.instNormedAddCommGroup in
attribute [-instance] Complex.instNormedField in
attribute [-instance] Complex.instDenselyNormedField in
attribute [-instance] Complex.instRCLike in
instance instComputableZSMul (z : ℤ) : IsComputableℂ (z • x) :=
   ⟨let _ := hx.1; .lift_eq (Complex.re_zsmul z x).symm inferInstance,
  let _ := hx.2; .lift_eq (Complex.im_zsmul z x).symm inferInstance⟩

--TODO: Can't find a way to make this computable (it really wants to use Complex.instField)
noncomputable instance instComputableQSMul (q : ℚ) : IsComputableℂ (q • x) :=
  lift_eq (Rat.smul_def q x).symm
  --Alternative:
  --  ⟨let _ := hx.1; .lift_eq (Complex.re_qsmul q x).symm inferInstance,
  -- let _ := hx.2; .lift_eq (Complex.im_qsmul q x).symm inferInstance⟩

instance instComputableInner : IsComputable (inner x y) := sorry
  --inferInstanceAs (IsComputable (Complex.re (conj x * y)))

instance instComputableNorm : IsComputable ‖x‖ :=
  inferInstanceAs (IsComputable (√(Complex.normSq x)))

instance instComputableNNNorm : IsComputable ‖x‖₊ :=
  instComputableNorm x

/-
To prove that two complex numbers are not equal, we could use `ext`, but it's better to
compute a series for Complex.normSq. Otherwise `Real.sqrt 2 + I` and `Real.sqrt 2 - I`
will never be comparable, because comparing the real parts will never terminate; but
comparing the the norm of their difference will eventually be lower bounded.
-/
instance instDecidableEq : Decidable (x = y) :=
  decidable_of_decidable_of_iff (p := Complex.normSq (x - y) = 0)
    (by rw [Complex.normSq_eq_zero, sub_eq_zero])

open ComplexOrder in
instance instDecidableLE : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (_ ∧ _))

open ComplexOrder in
instance instDecidableLT : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ ∧ _))

example : (1 + Complex.I) * (1 - Complex.I : ℂ) = 2 := by
  native_decide

example : ‖Complex.I‖ ≠ (1 / 2) := by
  native_decide
