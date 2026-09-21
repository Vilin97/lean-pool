/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.PolynomialSpaces

/-!
# Affine restriction spaces and the Hilbert function

This file implements blueprint node **F02** of the lower-bound side of the sharp finite-field
Nikodym exponent.

For an ideal `I` of `P_d = MvPolynomial (Fin d) K` we define

* `Nikodym.LowerBound.restrictionSpace I t`: the image `V_I(t)` of `P_{d,≤t}` in `P_d ⧸ I`,
  a finite-dimensional `K`-subspace of the quotient algebra;
* `Nikodym.LowerBound.hilbert I t`: the affine Hilbert function `H_I(t) = dim_K V_I(t)`.

We prove finite dimensionality (`instModuleFiniteRestrictionSpace`), monotonicity in `t`
(`restrictionSpace_mono`, `hilbert_mono`), the trivial bound `hilbert_le : H_I(t) ≤ (t+d).choose d`,
the values `hilbert_bot : H_{(0)}(t) = (t+d).choose d` and `hilbert_top : H_{P_d}(t) = 0`, and the
representative lemmas `exists_repr_of_mem_restrictionSpace` and `exists_notMem_of_ne_zero`
(a nonzero element of `V_I(t)` has a representative in `P_{d,≤t} \ I`).

Only the finite-dimensional image is ever given a `finrank`; the full coordinate ring `P_d ⧸ I`
need not be finite-dimensional.
-/

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint F02: the restriction space `V_I(t) = im (P_{d,≤t} → P_d ⧸ I)`, the image of the
polynomials of total degree at most `t` in the quotient algebra `P_d ⧸ I`. -/
noncomputable def restrictionSpace (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    Submodule K (MvPolynomial (Fin d) K ⧸ I) :=
  (restrictTotalDegree (Fin d) K t).map (Ideal.Quotient.mkₐ K I).toLinearMap

/-- Blueprint F02: the affine Hilbert function `H_I(t) = dim_K V_I(t)`. -/
noncomputable def hilbert (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) : ℕ :=
  Module.finrank K (restrictionSpace I t)

variable {I : Ideal (MvPolynomial (Fin d) K)} {t : ℕ}

/-- Blueprint F02: `V_I(t)` is finite-dimensional, being the image of `P_{d,≤t}`. -/
instance instModuleFiniteRestrictionSpace (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    Module.Finite K (restrictionSpace I t) :=
  inferInstanceAs (Module.Finite K
    ((restrictTotalDegree (Fin d) K t).map (Ideal.Quotient.mkₐ K I).toLinearMap))

/-- Blueprint F02: membership in `V_I(t)`. -/
theorem mem_restrictionSpace_iff {v : MvPolynomial (Fin d) K ⧸ I} :
    v ∈ restrictionSpace I t ↔
      ∃ f ∈ restrictTotalDegree (Fin d) K t, Ideal.Quotient.mk I f = v :=
  Submodule.mem_map

/-- Blueprint F02: the class of a polynomial of total degree at most `t` lies in `V_I(t)`. -/
theorem mem_restrictionSpace_mk {f : MvPolynomial (Fin d) K} (hf : f.totalDegree ≤ t) :
    Ideal.Quotient.mk I f ∈ restrictionSpace I t :=
  Submodule.mem_map_of_mem (mem_restrictTotalDegree_iff.mpr hf)

/-- Blueprint F02: the class of an element of `P_{d,≤t}` lies in `V_I(t)`. -/
theorem mk_mem_restrictionSpace {f : MvPolynomial (Fin d) K}
    (hf : f ∈ restrictTotalDegree (Fin d) K t) :
    Ideal.Quotient.mk I f ∈ restrictionSpace I t :=
  Submodule.mem_map_of_mem hf

/-- Blueprint F02: every element of `V_I(t)` has a representative in `P_{d,≤t}`. -/
theorem exists_repr_of_mem_restrictionSpace {v : MvPolynomial (Fin d) K ⧸ I}
    (hv : v ∈ restrictionSpace I t) :
    ∃ f ∈ restrictTotalDegree (Fin d) K t, Ideal.Quotient.mk I f = v :=
  mem_restrictionSpace_iff.mp hv

/-- Blueprint F02: a nonzero element of `V_I(t)` has a representative in `P_{d,≤t} \ I`. -/
theorem exists_notMem_of_ne_zero {v : MvPolynomial (Fin d) K ⧸ I}
    (hv : v ∈ restrictionSpace I t) (hv0 : v ≠ 0) :
    ∃ f ∈ restrictTotalDegree (Fin d) K t, f ∉ I ∧ Ideal.Quotient.mk I f = v := by
  obtain ⟨f, hf, rfl⟩ := exists_repr_of_mem_restrictionSpace hv
  refine ⟨f, hf, fun hfI ↦ hv0 ?_, rfl⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfI

/-- Blueprint F02: `V_I(t)` increases with `t`. -/
theorem restrictionSpace_mono {s t : ℕ} (h : s ≤ t) :
    restrictionSpace I s ≤ restrictionSpace I t :=
  Submodule.map_mono (restrictTotalDegree_mono h)

/-- Blueprint F02: the restriction space of the unit ideal is zero. -/
theorem restrictionSpace_top (t : ℕ) :
    restrictionSpace (⊤ : Ideal (MvPolynomial (Fin d) K)) t = ⊥ :=
  haveI : Subsingleton (MvPolynomial (Fin d) K ⧸ (⊤ : Ideal (MvPolynomial (Fin d) K))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  Submodule.eq_bot_of_subsingleton

/-- Blueprint F02: the Hilbert function is monotone in `t`. -/
theorem hilbert_mono {s t : ℕ} (h : s ≤ t) : hilbert I s ≤ hilbert I t :=
  Submodule.finrank_mono (restrictionSpace_mono h)

/-- Blueprint F02: `H_I(t) ≤ dim_K P_{d,≤t} = (t + d).choose d`. -/
theorem hilbert_le (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert I t ≤ (t + d).choose d := by
  rw [← finrank_restrictTotalDegree (K := K) (d := d) t]
  exact Submodule.finrank_map_le _ _

/-- Blueprint F02: the quotient map by the zero ideal is injective. -/
theorem mk_bot_injective :
    Function.Injective (Ideal.Quotient.mkₐ K (⊥ : Ideal (MvPolynomial (Fin d) K))).toLinearMap := by
  intro f g hfg
  simpa only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_bot,
    sub_eq_zero] using hfg

/-- Blueprint F02: `H_{(0)}(t) = (t + d).choose d`. -/
theorem hilbert_bot (t : ℕ) :
    hilbert (⊥ : Ideal (MvPolynomial (Fin d) K)) t = (t + d).choose d := by
  rw [← finrank_restrictTotalDegree (K := K) (d := d) t]
  exact (Submodule.equivMapOfInjective _ mk_bot_injective _).finrank_eq.symm

/-- Blueprint F02: `H_{P_d}(t) = 0`. -/
theorem hilbert_top (t : ℕ) : hilbert (⊤ : Ideal (MvPolynomial (Fin d) K)) t = 0 := by
  rw [hilbert, restrictionSpace_top, finrank_bot]

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
