/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.Composition.CayleyDickson
import LeanPool.CompositionAlgebras.Composition.Instances


/-!
# The three base identifications

`CD ℝ ≃ ℂ`, `CD ℂ ≃ ℍ` and `CD ℍ ≃ 𝕆`, each as an isomorphism of composition algebras.

These are item (3) of the three things that turning Hurwitz's *dimension* theorem into
Hurwitz's *classification* needs: (1) the external `CD` functor, built in
`Composition/CayleyDickson.lean`; (2) a transport lemma identifying `CD D` with the internal
double `double A u` of `Composition/Doubling.lean`; and (3) these three. ★ Item (2) is **not**
in this file: it is `CompEmb.double` in `Composition/Classification.lean`, which also assembles
all three items into `hurwitz_classification`. This file proves only the base cases.

## Main definitions

* `CompositionAlgebra.IsCompIso` — an isomorphism of composition algebras: an `ℝ`-linear
  equivalence preserving the unit, the product **and the norm form**.
* `cdRealEquiv : CD ℝ ≃ₗ[ℝ] ℂ`, `cdComplexEquiv : CD ℂ ≃ₗ[ℝ] ℍ[ℝ]`,
  `cdQuaternionEquiv : CD ℍ[ℝ] ≃ₗ[ℝ] Octonion`.

## The octonion identification

★ The third is the only one that needed searching. This tree's `Octonion` is built from a
hard-coded Fano multiplication table (`Octonions.lean`, `Octonion.mul`), not from a doubling,
so matching it against `CD ℍ[ℝ]` means choosing a correspondence between the doubled basis
`1, i, j, k, ℓ, iℓ, jℓ, kℓ` and `e₀, …, e₇` and then checking all 8 × 8 basis products.

The correspondence used below is

```
(a, b) ↦ (a.re, a.imI, a.imJ, b.re, a.imK, b.imJ, -b.imK, b.imI)
```

i.e. `1 ↦ e₀`, `i ↦ e₁`, `j ↦ e₂`, `k ↦ e₄`, `ℓ ↦ e₃`, `iℓ ↦ e₇`, `jℓ ↦ e₅`, `kℓ ↦ -e₆`.
It was found by enumerating the signed correspondences determined by the images of `i`, `j`
and `ℓ` and testing each against the table; **1344 of the 2744 candidates work**, and none of
them is sign-free. The one above is among the 147 that flip exactly one sign.

★ **Read the scope of that count exactly.** The enumeration ranges over the *monomial*
correspondences — those sending each of `1, i, j, k, ℓ, iℓ, jℓ, kℓ` to a signed basis vector —
and it is complete for those, since multiplicativity determines the other five images from the
images of `i`, `j` and `ℓ`, and each of those has 14 possibilities. It says nothing about
isomorphisms `CD ℍ[ℝ] ≃ 𝕆` in general: `Aut(𝕆) = G₂` is 14-dimensional, so almost none of them
are monomial. "No sign-free correspondence" means no sign-free *monomial* one.

★ Note what this does *not* say: the search establishes that the two products agree, not that
the labelling is canonical. A different Fano convention would produce a different
correspondence, and nothing downstream depends on which one is used.

## Scope

Substrate for the classification: it supplies the three base identifications the
doubling chain is renamed along.
-/

open CompositionAlgebra
open scoped Quaternion

namespace CompositionAlgebra

universe u v

/-- An **isomorphism of composition algebras**: an `ℝ`-linear equivalence preserving the unit,
the product and the norm form.

★ The norm clause is not redundant *bookkeeping* — it is carried because everything downstream
needs it and because `sq_eq`'s argument that the product already determines `N` is not
formalized in this tree. Carrying it makes every statement below strictly stronger than the
unit-and-product-only notion. -/
structure IsCompIso {C : Type u} {D : Type v}
    [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
    [CompositionAlgebra C]
    [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
    [CompositionAlgebra D]
    (f : C ≃ₗ[ℝ] D) : Prop where
  /-- The unit is preserved. -/
  map_one : f 1 = 1
  /-- The product is preserved. -/
  map_mul : ∀ x y : C, f (x * y) = f x * f y
  /-- The norm form is preserved. -/
  map_nf : ∀ x : C, nf (f x) = nf x

end CompositionAlgebra

/-! ### The conjugation on the three associative carriers -/

@[simp] theorem Real.cstar_eq (r : ℝ) : cstar r = r := by
  have h : ip r (1 : ℝ) = r := by change r * 1 = r; ring
  rw [cstar_apply, h]; simp; ring

@[simp] theorem Complex.cstar_eq (z : ℂ) : cstar z = ⟨z.re, -z.im⟩ := by
  have h : ip z (1 : ℂ) = z.re := by change z.re * 1 + z.im * 0 = z.re; ring
  rw [cstar_apply, h]
  apply Complex.ext <;> simp
  ring

theorem Quaternion.cstar_eq (q : ℍ[ℝ]) :
    cstar q = ⟨q.re, -q.imI, -q.imJ, -q.imK⟩ := by
  have h : ip q (1 : ℍ[ℝ]) = q.re := by
    change q.re * 1 + q.imI * 0 + q.imJ * 0 + q.imK * 0 = q.re
    ring
  rw [cstar_apply, h]
  ext <;> simp
  ring

/-! The four *components* of the quaternionic conjugation, and not `Quaternion.cstar_eq`, are
what carries the `simp` normal form.

★ This is not a stylistic choice. Mathlib's `Quaternion.re_mul` and its three companions are
`simp` lemmas keyed on `(a * b).re`, and they fail to fire when the first factor is a structure
literal. With `Quaternion.cstar_eq` marked `@[simp]`, these two behave differently —

```
example (a b : ℍ[ℝ]) : (a * b).re = a.re*b.re - a.imI*b.imI - a.imJ*b.imJ - a.imK*b.imK := by
  simp
example (a b : ℍ[ℝ]) : (cstar a * b).re = a.re*b.re + a.imI*b.imI + a.imJ*b.imJ + a.imK*b.imK := by
  simp; ring
```

— the first closes, and the second leaves `({ re := a.re, imI := -a.imI, … } * b).re` for
`ring`, which cannot touch it. Rewriting `cstar` componentwise keeps the product's arguments
atomic, so the four Mathlib lemmas fire and the octonion `map_mul` below reduces to
coordinates. -/

@[simp] theorem Quaternion.cstar_re (q : ℍ[ℝ]) : (cstar q).re = q.re := by
  rw [Quaternion.cstar_eq]

@[simp] theorem Quaternion.cstar_imI (q : ℍ[ℝ]) : (cstar q).imI = -q.imI := by
  rw [Quaternion.cstar_eq]

@[simp] theorem Quaternion.cstar_imJ (q : ℍ[ℝ]) : (cstar q).imJ = -q.imJ := by
  rw [Quaternion.cstar_eq]

@[simp] theorem Quaternion.cstar_imK (q : ℍ[ℝ]) : (cstar q).imK = -q.imK := by
  rw [Quaternion.cstar_eq]

/-! ### The norm forms of `ℍ` and `𝕆`, in coordinates

`Composition/Instances.lean` supplies `Real.nf_eq` and `Complex.nf_eq`; these are the two
missing companions. -/

theorem Quaternion.nf_eq (q : ℍ[ℝ]) :
    nf q = q.re * q.re + q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK := rfl

theorem Octonion.nf_eq (o : Octonion) :
    nf o = o.coords 0 * o.coords 0 + o.coords 1 * o.coords 1 + o.coords 2 * o.coords 2 +
      o.coords 3 * o.coords 3 + o.coords 4 * o.coords 4 + o.coords 5 * o.coords 5 +
      o.coords 6 * o.coords 6 + o.coords 7 * o.coords 7 := by
  change Octonion.octIp o o = _
  simp [Octonion.octIp, Fin.sum_univ_eight]

namespace CompositionAlgebra

/-! ### `CD ℝ ≃ ℂ` -/

/-- The double of `ℝ` is `ℂ`. -/
def cdRealEquiv : CD ℝ ≃ₗ[ℝ] ℂ where
  toFun x := ⟨x.fst, x.snd⟩
  map_add' x y := by apply Complex.ext <;> simp
  map_smul' r x := by apply Complex.ext <;> simp
  invFun z := CD.mk z.re z.im
  left_inv x := by apply CD.ext <;> rfl
  right_inv z := by apply Complex.ext <;> rfl

@[simp] theorem cdRealEquiv_re (x : CD ℝ) : (cdRealEquiv x).re = x.fst := rfl
@[simp] theorem cdRealEquiv_im (x : CD ℝ) : (cdRealEquiv x).im = x.snd := rfl

theorem cdRealEquiv_isCompIso : IsCompIso cdRealEquiv where
  map_one := by apply Complex.ext <;> simp
  map_mul x y := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_nf x := rfl

/-! ### `CD ℂ ≃ ℍ` -/

/-- The double of `ℂ` is `ℍ`. -/
def cdComplexEquiv : CD ℂ ≃ₗ[ℝ] ℍ[ℝ] where
  toFun x := ⟨x.fst.re, x.fst.im, x.snd.re, x.snd.im⟩
  map_add' x y := by ext <;> rfl
  map_smul' r x := by
    -- ★ `show` realigns the `SMul` on `ℍ[ℝ]`: the one carried by `Module ℝ ℍ[ℝ]` is a
    -- different *term* from `Quaternion.instSMul`, so the componentwise simp lemmas do not
    -- match the goal as stated. They are definitionally equal, which is all `show` needs.
    change (⟨(r • x).fst.re, (r • x).fst.im, (r • x).snd.re, (r • x).snd.im⟩ : ℍ[ℝ])
        = r • (⟨x.fst.re, x.fst.im, x.snd.re, x.snd.im⟩ : ℍ[ℝ])
    ext <;> simp
  invFun q := CD.mk ⟨q.re, q.imI⟩ ⟨q.imJ, q.imK⟩
  left_inv x := by apply CD.ext <;> apply Complex.ext <;> rfl
  right_inv q := by ext <;> rfl

@[simp] theorem cdComplexEquiv_re (x : CD ℂ) : (cdComplexEquiv x).re = x.fst.re := rfl
@[simp] theorem cdComplexEquiv_imI (x : CD ℂ) : (cdComplexEquiv x).imI = x.fst.im := rfl
@[simp] theorem cdComplexEquiv_imJ (x : CD ℂ) : (cdComplexEquiv x).imJ = x.snd.re := rfl
@[simp] theorem cdComplexEquiv_imK (x : CD ℂ) : (cdComplexEquiv x).imK = x.snd.im := rfl

theorem cdComplexEquiv_isCompIso : IsCompIso cdComplexEquiv where
  map_one := by ext <;> simp
  map_mul x y := by
    ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_nf x := by
    rw [CD.nf_eq, Quaternion.nf_eq, Complex.nf_eq, Complex.nf_eq]
    simp only [cdComplexEquiv_re, cdComplexEquiv_imI, cdComplexEquiv_imJ, cdComplexEquiv_imK]
    ring

/-! ### `CD ℍ ≃ 𝕆` -/

/-- The double of `ℍ` is `𝕆`, along the correspondence found by the basis search described in
the module docstring. -/
def cdQuaternionEquiv : CD ℍ[ℝ] ≃ₗ[ℝ] Octonion where
  toFun x := ⟨![x.fst.re, x.fst.imI, x.fst.imJ, x.snd.re,
                x.fst.imK, x.snd.imJ, -x.snd.imK, x.snd.imI]⟩
  map_add' x y := by ext i; fin_cases i <;> first | rfl | exact neg_add _ _
  map_smul' r x := by
    change (⟨![(r • x).fst.re, (r • x).fst.imI, (r • x).fst.imJ, (r • x).snd.re,
             (r • x).fst.imK, (r • x).snd.imJ, -(r • x).snd.imK, (r • x).snd.imI]⟩ : Octonion)
        = r • (⟨![x.fst.re, x.fst.imI, x.fst.imJ, x.snd.re,
             x.fst.imK, x.snd.imJ, -x.snd.imK, x.snd.imI]⟩ : Octonion)
    ext i; fin_cases i <;> simp
  invFun o := CD.mk ⟨o.coords 0, o.coords 1, o.coords 2, o.coords 4⟩
                    ⟨o.coords 3, o.coords 7, o.coords 5, -o.coords 6⟩
  left_inv x := by apply CD.ext <;> ext <;> first | rfl | exact neg_neg _
  right_inv o := by ext i; fin_cases i <;> first | rfl | exact neg_neg _

@[simp] theorem cdQuaternionEquiv_coords (x : CD ℍ[ℝ]) :
    (cdQuaternionEquiv x).coords = ![x.fst.re, x.fst.imI, x.fst.imJ, x.snd.re,
      x.fst.imK, x.snd.imJ, -x.snd.imK, x.snd.imI] := rfl

theorem cdQuaternionEquiv_isCompIso : IsCompIso cdQuaternionEquiv where
  map_one := by ext i; fin_cases i <;> simp [Octonion.one_def, Octonion.one]
  map_mul x y := by
    change (_ : Octonion) = Octonion.mul _ _
    ext i; fin_cases i <;>
      simp [Octonion.mul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul] <;> ring
  map_nf x := by
    rw [CD.nf_eq, Octonion.nf_eq, Quaternion.nf_eq, Quaternion.nf_eq]
    simp [cdQuaternionEquiv_coords]
    ring

end CompositionAlgebra
