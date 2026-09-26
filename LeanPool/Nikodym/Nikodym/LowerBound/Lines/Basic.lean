/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs

/-!
# Parametrized lines and their prime ideals

This file implements blueprint node **F04** of the lower-bound side of the sharp finite-field
Nikodym exponent.

For an anchor `b : Fin d → K` and a direction `v : Fin d → K` we define

* `Nikodym.LowerBound.lineRes b v : MvPolynomial (Fin d) K →ₐ[K] Polynomial K`, the restriction
  `res_{b,v} : X i ↦ b i + v i • T` of a polynomial to the parametrized line `T ↦ b + T v`;
* `Nikodym.LowerBound.lineIdeal b v = ker (res_{b,v})`, the ideal `λ_{b,v}` of the line;
* `Nikodym.LowerBound.lineQuotEquiv : P_d ⧸ λ_{b,v} ≃ₐ[K] K[T]` for `v ≠ 0`;
* `Nikodym.LowerBound.LineIn I b v`, the statement `I ≤ λ_{b,v}` that the line lies on `I`.

The main results are surjectivity of `res_{b,v}` for `v ≠ 0` (`lineRes_surjective`), primality of
`λ_{b,v}` (`lineIdeal_isPrime`), the degree bound `natDegree_lineRes_le : deg (res f) ≤ deg f`, the
Hilbert function `hilbert_lineIdeal : H_{λ_{b,v}}(t) = t + 1`, the evaluation formula
`lineRes_eval : (res f)(a) = f(b + a v)` with its consequence `lineIdeal_le_pointIdeal`, the
characterization `lineIdeal_le_pointIdeal_iff : λ_{b,v} ≤ 𝔪ₓ ↔ ∃ a, x = b + a v`, and the
reparametrization invariance `lineIdeal_eq_of_reparam : λ_{b + a v, c v} = λ_{b,v}` for `c ≠ 0`.

The finite field `F` enters only through the coordinate lift `Nikodym.LowerBound.liftPt`
(`x ↦ algebraMap F K ∘ x`) at the end of the file, together with the descent lemma
`exists_eq_add_smul_of_lineIdeal_liftPt_le`: if the `K`-line through `liftPt b` with direction
`liftPt v` passes through `liftPt x`, then `x = b + a • v` for some `a : F`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint F04: a nonzero vector has a nonzero coordinate. -/
theorem exists_ne_zero_of_ne_zero {v : Fin d → K} (hv : v ≠ 0) : ∃ i, v i ≠ 0 :=
  Function.ne_iff.mp hv

/-! ### The restriction homomorphism -/

section LineRes

/-- Blueprint F04: the restriction `res_{b,v} : P_d → K[T]`, `X i ↦ b i + v i • T`, of a
polynomial to the parametrized line `T ↦ b + T v`. -/
noncomputable def lineRes (b v : Fin d → K) : MvPolynomial (Fin d) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun i ↦ Polynomial.C (b i) + Polynomial.C (v i) * Polynomial.X

variable (b v : Fin d → K)

/-- Blueprint F04: `res_{b,v} (X i) = b i + v i • T`. -/
@[simp]
theorem lineRes_X (i : Fin d) :
    lineRes b v (X i) = Polynomial.C (b i) + Polynomial.C (v i) * Polynomial.X :=
  aeval_X _ i

/-- Blueprint F04: `res_{b,v}` fixes constants. -/
theorem lineRes_C (a : K) : lineRes b v (C a) = Polynomial.C a := by
  rw [lineRes, aeval_C, Polynomial.algebraMap_eq]

/-- Blueprint F04: the polynomial `(X i - b i) / v i`, which restricts to the parameter `T` on
the line whenever `v i ≠ 0`. -/
noncomputable def lineParam (i : Fin d) : MvPolynomial (Fin d) K :=
  C (v i)⁻¹ * (X i - C (b i))

/-- Blueprint F04: `res_{b,v}` maps `lineParam b v i` to `T` when `v i ≠ 0`. -/
theorem lineRes_lineParam {i : Fin d} (hi : v i ≠ 0) :
    lineRes b v (lineParam b v i) = Polynomial.X := by
  rw [lineParam, map_mul, map_sub, lineRes_C, lineRes_X, lineRes_C, add_sub_cancel_left,
    ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hi, Polynomial.C_1, one_mul]

/-- Blueprint F04: `lineParam b v i` has total degree at most `1`. -/
theorem totalDegree_lineParam_le (i : Fin d) : (lineParam b v i).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_X i).le
  · rw [totalDegree_C]
    exact Nat.zero_le _

/-- Blueprint F04: `res_{b,v}` is surjective when `v ≠ 0`: the parameter `T` is the image of
`(X i - b i) / v i` for any `i` with `v i ≠ 0`. -/
theorem lineRes_surjective {v : Fin d → K} (hv : v ≠ 0) : Function.Surjective (lineRes b v) := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
  intro p
  refine ⟨Polynomial.aeval (lineParam b v i) p, ?_⟩
  rw [← Polynomial.aeval_algHom_apply, lineRes_lineParam b v hi, Polynomial.aeval_X_left_apply]

end LineRes

/-! ### The line ideal -/

section LineIdeal

/-- Blueprint F04: the line ideal `λ_{b,v} = ker (res_{b,v})`. -/
noncomputable def lineIdeal (b v : Fin d → K) : Ideal (MvPolynomial (Fin d) K) :=
  RingHom.ker (lineRes b v)

variable {b v : Fin d → K}

/-- Blueprint F04: `f ∈ λ_{b,v}` iff `res_{b,v} f = 0`. -/
theorem mem_lineIdeal {f : MvPolynomial (Fin d) K} : f ∈ lineIdeal b v ↔ lineRes b v f = 0 :=
  RingHom.mem_ker

/-- Blueprint F04: `λ_{b,v}` is a prime ideal (the kernel of a homomorphism into the domain
`K[T]`). -/
theorem lineIdeal_isPrime (b v : Fin d → K) : (lineIdeal b v).IsPrime :=
  RingHom.ker_isPrime (lineRes b v)

/-- Blueprint F04: `λ_{b,v}` is a proper ideal. -/
theorem lineIdeal_ne_top (b v : Fin d → K) : lineIdeal b v ≠ ⊤ :=
  RingHom.ker_ne_top (lineRes b v)

/-- Blueprint F04: `P_d ⧸ λ_{b,v} ≃ K[T]` for `v ≠ 0`, induced by `res_{b,v}`. -/
noncomputable def lineQuotEquiv (b : Fin d → K) (hv : v ≠ 0) :
    (MvPolynomial (Fin d) K ⧸ lineIdeal b v) ≃ₐ[K] Polynomial K :=
  Ideal.quotientKerAlgEquivOfSurjective (lineRes_surjective b hv)

/-- Blueprint F04: `lineQuotEquiv` is induced by `res_{b,v}`. -/
@[simp]
theorem lineQuotEquiv_mk (b : Fin d → K) (hv : v ≠ 0) (f : MvPolynomial (Fin d) K) :
    lineQuotEquiv b hv (Ideal.Quotient.mk (lineIdeal b v) f) = lineRes b v f :=
  rfl

end LineIdeal

/-! ### Degree bounds and the Hilbert function -/

section Degree

variable (b v : Fin d → K)

/-- Blueprint F04: `deg (res_{b,v} (monomial α a)) ≤ |α|`. -/
theorem natDegree_lineRes_monomial_le (α : Fin d →₀ ℕ) (a : K) :
    (lineRes b v (monomial α a)).natDegree ≤ α.degree := by
  rw [lineRes, aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod, Finsupp.degree_apply]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine Polynomial.natDegree_pow_le.trans ?_
  calc α i * (Polynomial.C (b i) + Polynomial.C (v i) * Polynomial.X).natDegree
      ≤ α i * 1 := by
        refine Nat.mul_le_mul_left _ ?_
        rw [add_comm]
        exact Polynomial.natDegree_linear_le
    _ = α i := mul_one _

/-- Blueprint F04: `deg (res_{b,v} f) ≤ deg f`. -/
theorem natDegree_lineRes_le (f : MvPolynomial (Fin d) K) :
    (lineRes b v f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun α hα ↦ ?_
  exact (natDegree_lineRes_monomial_le b v α _).trans (le_totalDegree hα)

/-- Blueprint F04: `res_{b,v}` maps `P_{d,≤t}` into the polynomials of degree `< t + 1`. -/
theorem lineRes_mem_degreeLT {t : ℕ} {f : MvPolynomial (Fin d) K}
    (hf : f ∈ restrictTotalDegree (Fin d) K t) :
    lineRes b v f ∈ Polynomial.degreeLT K (t + 1) := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_le_of_natDegree_le
    ((natDegree_lineRes_le b v f).trans (mem_restrictTotalDegree_iff.mp hf))).trans_lt ?_
  exact_mod_cast Nat.lt_succ_self t

/-- Blueprint F04: `res_{b,v} (P_{d,≤t}) ≤ K[T]_{<t+1}`. -/
theorem lineRes_restrictTotalDegree_le (t : ℕ) :
    (restrictTotalDegree (Fin d) K t).map (lineRes b v).toLinearMap ≤
      Polynomial.degreeLT K (t + 1) := by
  rw [Submodule.map_le_iff_le_comap]
  intro f hf
  exact lineRes_mem_degreeLT b v hf

/-- Blueprint F04: for `v ≠ 0`, `res_{b,v} (P_{d,≤t}) = K[T]_{<t+1}`: the powers `T ^ j`, `j ≤ t`,
are the images of `lineParam b v i ^ j`, which have total degree at most `j`. -/
theorem map_lineRes_restrictTotalDegree {v : Fin d → K} (hv : v ≠ 0) (t : ℕ) :
    (restrictTotalDegree (Fin d) K t).map (lineRes b v).toLinearMap =
      Polynomial.degreeLT K (t + 1) := by
  classical
  refine le_antisymm (lineRes_restrictTotalDegree_le b v t) ?_
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
  rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
  intro p hp
  rw [Finset.coe_image, Set.mem_image] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  rw [Finset.mem_coe, Finset.mem_range] at hj
  refine Submodule.mem_map.mpr ⟨lineParam b v i ^ j, ?_, ?_⟩
  · rw [mem_restrictTotalDegree_iff]
    refine (totalDegree_pow _ _).trans ?_
    calc j * (lineParam b v i).totalDegree ≤ j * 1 :=
          Nat.mul_le_mul_left _ (totalDegree_lineParam_le b v i)
      _ ≤ t := by omega
  · rw [AlgHom.toLinearMap_apply, map_pow, lineRes_lineParam b v hi]

/-- Blueprint F04: the isomorphism `P_d ⧸ λ_{b,v} ≃ K[T]` carries `V_{λ_{b,v}}(t)` onto
`K[T]_{<t+1}`. -/
theorem map_restrictionSpace_lineQuotEquiv {v : Fin d → K} (hv : v ≠ 0) (t : ℕ) :
    (restrictionSpace (lineIdeal b v) t).map
        ((lineQuotEquiv b hv).toLinearEquiv : MvPolynomial (Fin d) K ⧸ lineIdeal b v →ₗ[K]
          Polynomial K) =
      Polynomial.degreeLT K (t + 1) := by
  rw [restrictionSpace, ← Submodule.map_comp, ← map_lineRes_restrictTotalDegree b hv t]
  rfl

/-- Blueprint F04: `dim_K K[T]_{<n} = n`. -/
theorem finrank_degreeLT (n : ℕ) : Module.finrank K (Polynomial.degreeLT K n) = n := by
  rw [(Polynomial.degreeLTEquiv K n).finrank_eq, Module.finrank_fin_fun]

/-- Blueprint F04: `H_{λ_{b,v}}(t) = t + 1` for `v ≠ 0`. -/
theorem hilbert_lineIdeal {v : Fin d → K} (hv : v ≠ 0) (t : ℕ) :
    hilbert (lineIdeal b v) t = t + 1 := by
  rw [hilbert, ← LinearEquiv.finrank_map_eq (lineQuotEquiv b hv).toLinearEquiv,
    map_restrictionSpace_lineQuotEquiv b hv t, finrank_degreeLT]

/-- Blueprint F04: `H_{λ_{b,v}}(t) ≤ t + 1` for `v ≠ 0`. -/
theorem hilbert_lineIdeal_le {v : Fin d → K} (hv : v ≠ 0) (t : ℕ) :
    hilbert (lineIdeal b v) t ≤ t + 1 :=
  (hilbert_lineIdeal b hv t).le

/-- Blueprint F04: `t + 1 ≤ H_{λ_{b,v}}(t)` for `v ≠ 0`. -/
theorem le_hilbert_lineIdeal {v : Fin d → K} (hv : v ≠ 0) (t : ℕ) :
    t + 1 ≤ hilbert (lineIdeal b v) t :=
  (hilbert_lineIdeal b hv t).ge

end Degree

/-! ### Lines on an ideal -/

section LineIn

/-- Blueprint F04: the line `T ↦ b + T v` lies on the ideal `I` if `I ≤ λ_{b,v}`, i.e. every
`f ∈ I` restricts to the zero polynomial (a polynomial identity on the whole `K`-line, not merely
vanishing at finitely many points). -/
def LineIn (I : Ideal (MvPolynomial (Fin d) K)) (b v : Fin d → K) : Prop :=
  I ≤ lineIdeal b v

variable {I : Ideal (MvPolynomial (Fin d) K)} {b v : Fin d → K}

/-- Blueprint F04: the line lies on `I` iff every element of `I` restricts to zero. -/
theorem lineIn_iff : LineIn I b v ↔ ∀ f ∈ I, lineRes b v f = 0 := by
  simp only [LineIn, SetLike.le_def, mem_lineIdeal]

/-- Blueprint F04: `LineIn I b v` unfolds to `I ≤ λ_{b,v}`. -/
theorem LineIn.le (h : LineIn I b v) : I ≤ lineIdeal b v :=
  h

/-- Blueprint F04: lines on `I` are lines on every smaller ideal. -/
theorem LineIn.mono {J : Ideal (MvPolynomial (Fin d) K)} (hJI : J ≤ I) (h : LineIn I b v) :
    LineIn J b v :=
  hJI.trans h

end LineIn

/-! ### Points on the line -/

section Points

variable (b v : Fin d → K)

/-- Blueprint F04: `(res_{b,v} f)(a) = f(b + a v)`. -/
theorem lineRes_eval (f : MvPolynomial (Fin d) K) (a : K) :
    (lineRes b v f).eval a = eval (b + a • v) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, lineRes_X, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Blueprint F04: the line `T ↦ b + T v` passes through its points: `λ_{b,v} ≤ 𝔪_{b + a v}`. -/
theorem lineIdeal_le_pointIdeal (a : K) : lineIdeal b v ≤ pointIdeal (b + a • v) := by
  intro f hf
  rw [mem_pointIdeal, ← lineRes_eval, mem_lineIdeal.mp hf, Polynomial.eval_zero]

/-- Blueprint F04: the anchor lies on the line: `λ_{b,v} ≤ 𝔪_b`. -/
theorem lineIdeal_le_pointIdeal_self : lineIdeal b v ≤ pointIdeal b := by
  simpa using lineIdeal_le_pointIdeal b v 0

/-- Blueprint F04: the polynomials `v i • (X j - b j) - v j • (X i - b i)` lie in `λ_{b,v}`. -/
theorem lineForm_mem_lineIdeal (i j : Fin d) :
    C (v i) * (X j - C (b j)) - C (v j) * (X i - C (b i)) ∈ lineIdeal b v := by
  rw [mem_lineIdeal]
  simp only [map_sub, map_mul, lineRes_C, lineRes_X, add_sub_cancel_left]
  ring

/-- Blueprint F04: if `λ_{b,v} ≤ 𝔪ₓ` and `v ≠ 0`, then `x` lies on the line: `x = b + a v` for some
`a : K`. -/
theorem exists_eq_add_smul_of_lineIdeal_le_pointIdeal {v : Fin d → K} (hv : v ≠ 0)
    {x : Fin d → K} (h : lineIdeal b v ≤ pointIdeal x) : ∃ a : K, x = b + a • v := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
  refine ⟨(x i - b i) / v i, funext fun j ↦ ?_⟩
  have hj := mem_pointIdeal.mp (h (lineForm_mem_lineIdeal b v i j))
  simp only [map_sub, map_mul, eval_C, eval_X, sub_eq_zero] at hj
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hj

/-- Blueprint F04: for `v ≠ 0`, `λ_{b,v} ≤ 𝔪ₓ` iff `x` lies on the line `T ↦ b + T v`. -/
theorem lineIdeal_le_pointIdeal_iff {v : Fin d → K} (hv : v ≠ 0) {x : Fin d → K} :
    lineIdeal b v ≤ pointIdeal x ↔ ∃ a : K, x = b + a • v := by
  refine ⟨exists_eq_add_smul_of_lineIdeal_le_pointIdeal b hv, ?_⟩
  rintro ⟨a, rfl⟩
  exact lineIdeal_le_pointIdeal b v a

end Points

/-! ### Reparametrization -/

section Reparam

variable (b v : Fin d → K)

/-- Blueprint F04: reparametrizing the line by `T ↦ a + c T` composes the restriction with the
degree-one polynomial `a + c T`. -/
theorem lineRes_reparam (a c : K) (f : MvPolynomial (Fin d) K) :
    lineRes (b + a • v) (c • v) f =
      (lineRes b v f).comp (Polynomial.C a + Polynomial.C c * Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, Polynomial.add_comp]
  | mul_X p i hp =>
    simp only [map_mul, hp, lineRes_X, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.C_comp,
      Polynomial.X_comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring

/-- Blueprint F04: `λ_{b,v} ≤ λ_{b + a v, c v}` for all `a c : K`. -/
theorem lineIdeal_le_lineIdeal_reparam (a c : K) :
    lineIdeal b v ≤ lineIdeal (b + a • v) (c • v) := by
  intro f hf
  rw [mem_lineIdeal, lineRes_reparam, mem_lineIdeal.mp hf, Polynomial.zero_comp]

/-- Blueprint F04: `λ_{b + a v, c v} = λ_{b,v}` for `c ≠ 0`: the line ideal only depends on the
affine line, not on its parametrization. -/
theorem lineIdeal_eq_of_reparam (a c : K) (hc : c ≠ 0) :
    lineIdeal (b + a • v) (c • v) = lineIdeal b v := by
  refine le_antisymm ?_ (lineIdeal_le_lineIdeal_reparam b v a c)
  have h1 : (b + a • v) + (-a / c) • (c • v) = b := by
    rw [smul_smul, neg_div, neg_mul, div_mul_cancel₀ _ hc, neg_smul, add_neg_cancel_right]
  have h2 : c⁻¹ • (c • v) = v := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have := lineIdeal_le_lineIdeal_reparam (b + a • v) (c • v) (-a / c) c⁻¹
  rwa [h1, h2] at this

end Reparam

/-! ### Lifting finite-field coordinates -/

section Lift

variable {F : Type*} [Field F] [Algebra F K]

/-- Blueprint F04: the coordinatewise lift `ι : F^d → K^d` along `algebraMap F K`. -/
def liftPt (x : Fin d → F) : Fin d → K := fun i ↦ algebraMap F K (x i)

variable (K)

/-- Blueprint F04: `liftPt x i = algebraMap F K (x i)`. -/
@[simp]
theorem liftPt_apply (x : Fin d → F) (i : Fin d) : liftPt (K := K) x i = algebraMap F K (x i) :=
  rfl

/-- Blueprint F04: `liftPt` is additive. -/
theorem liftPt_add (x y : Fin d → F) : liftPt (K := K) (x + y) = liftPt x + liftPt y := by
  ext i
  simp

/-- Blueprint F04: `liftPt` is compatible with scalars. -/
theorem liftPt_smul (a : F) (v : Fin d → F) :
    liftPt (K := K) (a • v) = algebraMap F K a • liftPt v := by
  ext i
  simp

/-- Blueprint F04: `liftPt 0 = 0`. -/
@[simp]
theorem liftPt_zero : liftPt (K := K) (0 : Fin d → F) = 0 := by
  ext i
  simp

/-- Blueprint F04: `liftPt` is injective, since `algebraMap F K` is a field homomorphism. -/
theorem liftPt_injective : Function.Injective (liftPt (K := K) (d := d) (F := F)) := by
  intro x y hxy
  ext i
  exact (algebraMap F K).injective (congrFun hxy i)

variable {K}

/-- Blueprint F04: the lift of a nonzero direction is nonzero. -/
theorem liftPt_ne_zero {v : Fin d → F} (hv : v ≠ 0) : liftPt (K := K) v ≠ 0 := by
  intro h
  exact hv (liftPt_injective K (h.trans (liftPt_zero K).symm))

/-- Blueprint F04: if the `K`-line through `ι(b)` with direction `ι(v)` (with `v ≠ 0`) passes
through `ι(x)`, then the parameter lies in `F`: `x = b + a • v` for some `a : F`. -/
theorem exists_eq_add_smul_of_liftPt_eq {b v x : Fin d → F} (hv : v ≠ 0) {a : K}
    (h : liftPt x = liftPt b + a • liftPt (K := K) v) : ∃ a : F, x = b + a • v := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
  have hi' : algebraMap F K (v i) ≠ 0 := (map_ne_zero _).mpr hi
  have ha : a = algebraMap F K ((x i - b i) / v i) := by
    have := congrFun h i
    simp only [liftPt_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [map_div₀, map_sub, eq_div_iff hi', this]
    ring
  refine ⟨(x i - b i) / v i, liftPt_injective K ?_⟩
  rw [h, ha, liftPt_add, liftPt_smul]

/-- Blueprint F04: if `λ_{ι(b),ι(v)} ≤ 𝔪_{ι(x)}` with `v ≠ 0`, then `x = b + a • v` for some
`a : F`. -/
theorem exists_eq_add_smul_of_lineIdeal_liftPt_le {b v x : Fin d → F} (hv : v ≠ 0)
    (h : lineIdeal (liftPt (K := K) b) (liftPt v) ≤ pointIdeal (liftPt x)) :
    ∃ a : F, x = b + a • v := by
  obtain ⟨a, ha⟩ := exists_eq_add_smul_of_lineIdeal_le_pointIdeal _ (liftPt_ne_zero hv) h
  exact exists_eq_add_smul_of_liftPt_eq hv ha

end Lift

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
