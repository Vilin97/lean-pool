/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.OctonionTrace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


/-!
# The octonions as a real vector space

`CompositionAlgebras/Octonions.lean` gives `Octonion` bare `Zero`/`Add`/`Neg`/`SMul ℝ` and
`Mul` instances and no bundled algebraic class (no `AddCommGroup`, no `Module`).  This file
supplies `AddCommGroup Octonion`, `Module ℝ Octonion`, `FiniteDimensional ℝ Octonion`,
`finrank ℝ 𝕆 = 8`, linearity of conjugation, and the Euclidean form `octIp`.

Every module data field is the pre-existing instance on the nose, so no `+`, `•` or `0` in
the octonion file changes meaning and its `@[simp]` coordinate lemmas keep firing.  They live
here rather than in `Octonions.lean` only to keep that file untouched.

`Composition/Instances.lean` needs exactly this: without `AddCommGroup` and `Module ℝ` there
is no `Module ℝ Octonion` for `CompositionAlgebra Octonion` to be stated over.

## Main definitions

* `Octonion.octIp` -- the Euclidean inner product on `𝕆`
* `Octonion.coordsEquiv` -- `𝕆 ≃ₗ[ℝ] (Fin 8 → ℝ)`

## Main results

* `Octonion.octIp_eq_re` -- `⟨x, y⟩ = re (x * conj y)`, the bridge to `OctonionTrace.lean`
* `Octonion.re_three_cyc` -- cyclic invariance of `re ((x y) z)`
* `Octonion.finrank_eq_eight` -- `finrank ℝ 𝕆 = 8`
-/

noncomputable section

/-! ## `Octonion` as an `ℝ`-module -/

namespace Octonion

instance instAddCommGroup : AddCommGroup Octonion where
  add := (· + ·)
  add_assoc a b c := by ext i; exact add_assoc _ _ _
  zero := 0
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add a := by ext i; exact zero_add _
  add_zero a := by ext i; exact add_zero _
  neg := Neg.neg
  neg_add_cancel a := by ext i; exact neg_add_cancel _
  add_comm a b := by ext i; exact add_comm _ _

instance instModule : Module ℝ Octonion where
  smul := (· • ·)
  one_smul a := by ext i; exact one_mul _
  mul_smul r s a := by ext i; exact mul_assoc _ _ _
  smul_zero r := by ext i; exact mul_zero _
  smul_add r a b := by ext i; exact mul_add _ _ _
  add_smul r s a := by ext i; exact add_mul _ _ _
  zero_smul a := by ext i; exact zero_mul _

@[simp] theorem conj_zero : conj (0 : Octonion) = 0 := by
  ext i; simp only [conj, zero_coords]; split_ifs <;> simp

/-- Conjugation is additive. -/
@[simp] theorem conj_add (x y : Octonion) : conj (x + y) = conj x + conj y := by
  ext i; simp only [conj, add_coords]; split_ifs <;> ring

/-- Conjugation is `ℝ`-homogeneous; with `conj_add`, `conj` is `ℝ`-linear. -/
@[simp] theorem conj_smul (r : ℝ) (x : Octonion) : conj (r • x) = r • conj x := by
  ext i; simp only [conj, smul_coords]; split_ifs <;> ring

@[simp] theorem mul_zero' (x : Octonion) : mul x 0 = 0 := by
  ext i; fin_cases i <;> simp [mul]

@[simp] theorem zero_mul' (x : Octonion) : mul 0 x = 0 := by
  ext i; fin_cases i <;> simp [mul]

/-! ### The Euclidean inner product on `𝕆`

`octIp x y = ∑ᵢ xᵢ yᵢ` is the standard positive-definite form.  `octIp_eq_re` identifies it
with the trace form `re (x * conj y)` of `OctonionTrace.lean`, which is how the cyclic identities
there reach the trace form on hermitian octonionic matrices. -/

/-- The Euclidean inner product on the octonions. -/
def octIp (x y : Octonion) : ℝ := ∑ i, x.coords i * y.coords i

theorem octIp_comm (x y : Octonion) : octIp x y = octIp y x := by
  simp only [octIp]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[simp] theorem octIp_add_left (x y z : Octonion) :
    octIp (x + y) z = octIp x z + octIp y z := by
  simp only [octIp, add_coords, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem octIp_smul_left (r : ℝ) (x y : Octonion) :
    octIp (r • x) y = r * octIp x y := by
  simp only [octIp, smul_coords, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem octIp_add_right (x y z : Octonion) :
    octIp x (y + z) = octIp x y + octIp x z := by
  rw [octIp_comm, octIp_add_left, octIp_comm y x, octIp_comm z x]

@[simp] theorem octIp_smul_right (r : ℝ) (x y : Octonion) :
    octIp x (r • y) = r * octIp x y := by
  rw [octIp_comm, octIp_smul_left, octIp_comm y x]

@[simp] theorem octIp_zero_left (x : Octonion) : octIp 0 x = 0 := by simp [octIp]

@[simp] theorem octIp_zero_right (x : Octonion) : octIp x 0 = 0 := by simp [octIp]

theorem octIp_self_nonneg (x : Octonion) : 0 ≤ octIp x x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem octIp_self_eq_zero {x : Octonion} (h : octIp x x = 0) : x = 0 := by
  ext i
  have hle : x.coords i * x.coords i ≤ octIp x x :=
    Finset.single_le_sum (f := fun j => x.coords j * x.coords j)
      (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  have : x.coords i * x.coords i = 0 := by
    linarith [mul_self_nonneg (x.coords i)]
  simpa using mul_self_eq_zero.mp this

/-- The Euclidean inner product is the trace form: `⟨x, y⟩ = re (x * conj y)`.
This is the bridge to `OctonionTrace.lean`. -/
theorem octIp_eq_re (x y : Octonion) : octIp x y = re (mul x (conj y)) := by
  simp [octIp, re, mul, conj, Fin.sum_univ_eight]

/-- Cyclic invariance of the real part of a triple product.  `re_mul_assoc` moves the bracket,
`re_mul_comm` rotates the factors. -/
theorem re_three_cyc (x y z : Octonion) :
    re (mul (mul x y) z) = re (mul (mul y z) x) := by
  rw [re_mul_assoc, re_mul_comm]

/-- Cyclic rotation of a conjugated triple, in the `octIp` vocabulary the trace form on
hermitian octonionic matrices is written in.  This and `octIp_conj_cyc'` are the only
octonionic input that form's Euclidean hypothesis needs. -/
theorem octIp_conj_cyc (a b c : Octonion) :
    octIp (mul (conj a) (conj b)) c = octIp (mul (conj b) (conj c)) a := by
  rw [octIp_eq_re, octIp_eq_re]
  exact re_three_cyc (conj a) (conj b) (conj c)

/-- Cyclic rotation the other way. -/
theorem octIp_conj_cyc' (a b c : Octonion) :
    octIp (mul (conj a) (conj b)) c = octIp (mul (conj c) (conj a)) b := by
  rw [octIp_conj_cyc, octIp_conj_cyc]

/-- Coordinates of an octonion, as a linear equivalence with `Fin 8 → ℝ`. -/
def coordsEquiv : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun a := a.coords
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨c⟩
  left_inv a := by cases a; rfl
  right_inv c := rfl

instance instFiniteDimensional : FiniteDimensional ℝ Octonion :=
  Module.Finite.equiv coordsEquiv.symm

/-- The octonions are 8-dimensional over `ℝ`. -/
theorem finrank_eq_eight : Module.finrank ℝ Octonion = 8 := by
  rw [coordsEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end Octonion
