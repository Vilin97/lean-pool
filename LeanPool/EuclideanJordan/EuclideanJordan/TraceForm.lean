/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Spectral
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection



/-!
# The Jordan trace form

`τ(x, y) := tr(L_{x ∘ y})`, where `L_c` is the Jordan multiplication operator
    `EuclideanJordan/Peirce.lean`
carries as `mulL`.  On a finite-dimensional formally real Jordan algebra this form is symmetric,
**associative** (`τ(x ∘ y, z) = τ(y, x ∘ z)`) and **positive definite** — which is to say, it makes
such an algebra Euclidean without any inner product having been supplied.

## Why this file exists

`EuclideanJordan/Order.lean`'s Euclidean section — `inner_mul_self_nonneg_of_idem`,
    `inner_left_coeff`,
`nonneg_coeff_of_isSoS`, `isArchimedean_ofBilinear`, `isSoS_iff_exists_sq` — takes the associativity
of the **ambient** inner product as a hypothesis, `hassoc : ∀ x y z, ⟪m x y, z⟫ = ⟪y, m x z⟫`.  The
concrete carrier `H_n(𝕜)` discharges it by hand, through `hermitian_jordan_assoc`
(`EuclideanJordan/HermitianCarrier.lean`).  ★ An *abstract* consumer generally cannot.  A
structure that carries a `NormedAddCommGroup`/`InnerProductSpace` pair on `J` and a Jordan
product as an unrelated bilinear field has **no** compatibility between the two, and adding the
Jordan identity, formal reality and a cone-of-squares reading of positivity does not supply one:
associativity of the inner product is an independent assumption.  So a proof that has to run
inside those hypotheses has no associative form to pair against, and every one of the six results
above is inapplicable as stated.

This file builds the missing form *from the algebra*.  Nothing here mentions a norm or an inner
product; the ambient structure is `EuclideanJordan/Peirce.lean`'s (a commutative Jordan ring
    that is an
`ℝ`-module), plus finite-dimensionality and formal reality where the spectral theorem is used.
A consumer working in bilinear-map vocabulary installs `EuclideanJordan/Bridge.lean`'s
`ringOfBilinear` and gets `traceForm` on the nose.

## The associativity argument

`tr(L_·)` is associative because the **quadrilinear** form of the Jordan identity,

`L_{(a∘c)∘y} + L_a L_y L_c + L_c L_y L_a = L_a L_{c∘y} + L_c L_{a∘y} + L_y L_{a∘c}`,

has a right-hand side that is symmetric under permuting `(a, c, y)` — the three pairs
`{(a, c∘y), (c, a∘y), (y, a∘c)}` are permuted among themselves and `tr(fg) = tr(gf)` — while
`tr(L_a L_y L_c) + tr(L_c L_y L_a)` is symmetric by cyclicity of the trace.  Hence
`tr(L_{(a∘c)∘y})` is symmetric in `(a, c, y)`, and that *is* associativity.

★ The quadrilinear identity itself is cheap and this was not expected.  It is the difference of two
instances of Mathlib's own linearized Jordan identity
(`two_nsmul_lie_lmul_lmul_add_add_eq_zero`) with the last two arguments swapped; `jordan_linearized`
and `jordan_quadrilinear` below are the whole of it.

## Positive definiteness

`τ(x, x) = tr(L_{x∘x})`, and the spectral resolution `x = ∑ᵢ λᵢ qᵢ` into orthogonal idempotents
gives `x ∘ x = ∑ᵢ λᵢ² qᵢ`, so `τ(x, x) = ∑ᵢ λᵢ² tr(L_{qᵢ})`.  For an idempotent `c` the split
`L_c = P₁(c) + ½ P_{1/2}(c)` writes `tr(L_c)` as a nonnegative combination of traces of *idempotent
endomorphisms*, which are ranks of their ranges; and `P₁(c) c = c`, so a nonzero `c` forces
`tr(L_c) ≥ 1`.  That inequality is the whole of definiteness: a vanishing `τ(x, x)` kills every
coefficient whose idempotent is nonzero.

★ **What this file does NOT claim.**  `τ` is not shown to be *the* Jordan trace form in the sense of
Faraut–Korányi (the trace of the quadratic representation, or the sum of the eigenvalues of `x`);
for a unit `e` one has `L_e = id` and so `tr(L_e) = finrank ℝ J` rather than the rank of `J` — **a
remark, not a lemma; it is not proved below and nothing uses it.**  Nothing downstream needs the
normalisation, and
`EuclideanJordan/Class.lean`'s `EuclideanJordanAlgebra` deliberately takes an *arbitrary*
    associative positive
definite form rather than a normalised one, so `traceForm` is admissible there as it stands.
-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

open Finset LinearMap

/-! ## The linearized and quadrilinear Jordan identities -/

section Linearised

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

/-- **The multilinearized Jordan identity, elementwise.**

Mathlib states it as `2 • ([L_{ab}, L_c] + [L_{bc}, L_a] + [L_{ca}, L_b]) = 0` in
`AddMonoid.End J`; applying that at `v`, unfolding the commutators and cancelling the `2` gives the
form below.  The `have h3 : … := h2` step works because the `AddMonoid.End` ring operations are
definitionally pointwise, which saves fighting for application `simp` lemmas that do not exist
under the names one would guess. -/
theorem jordan_linearized (a b c v : J) :
    (a * b) * (c * v) + (b * c) * (a * v) + (c * a) * (b * v)
      = c * ((a * b) * v) + a * ((b * c) * v) + b * ((c * a) * v) := by
  have h := congrArg (fun f : AddMonoid.End J => f v)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero (A := J) a b c)
  simp only [Ring.lie_def] at h
  have h2 := nsmul_eq_zero_iff' (J := J) (n := 2) (by norm_num) h
  have h3 : (a * ((b * c) * v) - (b * c) * (a * v))
      + (b * ((c * a) * v) - (c * a) * (b * v))
      + (c * ((a * b) * v) - (a * b) * (c * v)) = 0 := h2
  linear_combination (norm := abel) -h3

/-- **The quadrilinear Jordan identity**, the operator identity of this file read elementwise.

It is `jordan_linearized a c y v - jordan_linearized a c v y`: the *same* identity with its last two
arguments swapped.  The `rw`s only put the two instances into a common shape by commuting
products. -/
theorem jordan_quadrilinear (a c y v : J) :
    ((a * c) * y) * v + a * (y * (c * v)) + c * (y * (a * v))
      = a * ((c * y) * v) + c * ((a * y) * v) + y * ((a * c) * v) := by
  have h1 := jordan_linearized a c y v
  have h2 := jordan_linearized a c v y
  rw [show ((a * c) * y) * v = v * ((a * c) * y) from mul_comm _ _,
      show a * (y * (c * v)) = a * ((c * v) * y) by rw [mul_comm y (c * v)],
      show c * (y * (a * v)) = c * ((v * a) * y) by rw [mul_comm y (a * v), mul_comm a v],
      show c * ((a * y) * v) = c * ((y * a) * v) by rw [mul_comm a y]]
  rw [show (a * c) * (y * v) = (a * c) * (v * y) by rw [mul_comm y v]] at h1
  rw [show (c * y) * (a * v) = (v * a) * (c * y) by rw [mul_comm a v, mul_comm]] at h1
  rw [show (y * a) * (c * v) = (c * v) * (a * y) by rw [mul_comm y a, mul_comm]] at h1
  linear_combination (norm := abel) h1 - h2

end Linearised

/-! ## `tr ∘ L` and its associativity -/

section Trace

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

/-- `EuclideanJordan/Peirce.lean`'s `mulL`, bundled as a linear map in the multiplier — which is
what makes
`jtr` linear. -/
def mulLₗ : J →ₗ[ℝ] J →ₗ[ℝ] J where
  toFun := mulL
  map_add' a b := by ext y; simp only [mulL_apply, LinearMap.add_apply, add_mul]
  map_smul' r a := by
    ext y
    simp only [mulL_apply, LinearMap.smul_apply, RingHom.id_apply, smul_mul_assoc]

omit [IsCommJordan J] in
@[simp] theorem mulLₗ_apply (a : J) : mulLₗ a = mulL a := rfl

/-- **The operator form of the quadrilinear identity**, in `Module.End ℝ J`.

`L_{(a∘c)∘y} + L_a L_y L_c + L_c L_y L_a = L_a L_{c∘y} + L_c L_{a∘y} + L_y L_{a∘c}`. -/
theorem mulL_quad_op (a c y : J) :
    mulL ((a * c) * y) + mulL a * mulL y * mulL c + mulL c * mulL y * mulL a
      = mulL a * mulL (c * y) + mulL c * mulL (a * y) + mulL y * mulL (a * c) := by
  ext v
  simp only [LinearMap.add_apply, Module.End.mul_apply, mulL_apply]
  exact jordan_quadrilinear a c y v

/-- **The Jordan trace functional** `x ↦ tr(L_x)`, as an `ℝ`-linear form.

It is not normalised — see the module docstring.  ★ The carrier here has no `1`
(`NonUnitalNonAssocCommRing`), so the normalisation cannot even be *stated* at this generality;
where a unit `e` is available it is `L_e = id`, so `jtr e` would be `finrank ℝ J` rather than the
rank.  That is a remark, not a lemma: nothing below proves it and nothing needs it. -/
def jtr : J →ₗ[ℝ] ℝ := (LinearMap.trace ℝ J).comp mulLₗ

omit [IsCommJordan J] in
@[simp] theorem jtr_apply (x : J) : jtr x = LinearMap.trace ℝ J (mulL x) := rfl

/-- **`tr(L_·)` is associative.**  Trace the operator identity twice, at `(a, c, y)` and at
`(c, y, a)`; the two right-hand sides agree term by term after commuting products, and the two
triple-trace sums agree by cyclicity, so the two remaining terms agree.

★ Finite-dimensionality is not needed: `LinearMap.trace` is total (it is `0` on a module with no
finite basis) and `trace_mul_cycle` is unconditional.  It enters two theorems below, where the
trace of an idempotent endomorphism has to be its rank. -/
theorem jtr_assoc (a c y : J) : jtr ((a * c) * y) = jtr (a * (c * y)) := by
  have h1 := congrArg (LinearMap.trace ℝ J) (mulL_quad_op a c y)
  have h2 := congrArg (LinearMap.trace ℝ J) (mulL_quad_op c y a)
  simp only [map_add] at h1 h2
  rw [show a * (c * y) = (c * y) * a from mul_comm _ _]
  rw [show y * a = a * y from mul_comm _ _, show c * a = a * c from mul_comm _ _] at h2
  have e1 : trace ℝ J (mulL c * mulL a * mulL y) = trace ℝ J (mulL a * mulL y * mulL c) :=
    (trace_mul_cycle ℝ (mulL a) (mulL y) (mulL c)).symm
  have e2 : trace ℝ J (mulL y * mulL a * mulL c) = trace ℝ J (mulL c * mulL y * mulL a) :=
    trace_mul_cycle ℝ (mulL y) (mulL a) (mulL c)
  simp only [jtr_apply] at *
  linarith [h1, h2, e1, e2]

variable [Module.Finite ℝ J]

/-- **The trace of `L_c` is nonnegative for an idempotent `c`.**

`L_c = P₁(c) + ½ P_{1/2}(c)`, both Peirce projections are idempotent *endomorphisms*, and the trace
of an idempotent endomorphism is the rank of its range. -/
theorem jtr_nonneg_of_idem {c : J} (hc : c * c = c) : 0 ≤ jtr c := by
  have hid1 : IsIdempotentElem (peirceOne c) := by
    ext y; exact peirceOne_of_eigen (mul_peirceOne hc y)
  have hidh : IsIdempotentElem (peirceHalf c) := by
    ext y; exact peirceHalf_of_eigen_half (mul_peirceHalf hc y)
  have hsplit : mulL c = peirceOne c + (2 : ℝ)⁻¹ • peirceHalf c := by
    ext y
    simp only [mulL_apply, LinearMap.add_apply, LinearMap.smul_apply, peirceOne_apply,
      peirceHalf_apply]
    module
  rw [jtr_apply, hsplit, map_add, LinearMap.map_smul, hid1.isProj_range.trace,
    hidh.isProj_range.trace]
  have h1 : (0 : ℝ) ≤ (Module.finrank ℝ (LinearMap.range (peirceOne c)) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (Module.finrank ℝ (LinearMap.range (peirceHalf c)) : ℝ) := Nat.cast_nonneg _
  simp only [smul_eq_mul]
  linarith

/-- **The trace of `L_c` is at least one for a nonzero idempotent `c`** — the whole of positive
definiteness.  `P₁(c) c = c`, so `c` lies in the range of `P₁(c)`; a nonzero `c` makes that range
nonzero, hence of rank at least one. -/
theorem one_le_jtr_of_idem {c : J} (hc : c * c = c) (hc0 : c ≠ 0) : 1 ≤ jtr c := by
  have hid1 : IsIdempotentElem (peirceOne c) := by
    ext y; exact peirceOne_of_eigen (mul_peirceOne hc y)
  have hidh : IsIdempotentElem (peirceHalf c) := by
    ext y; exact peirceHalf_of_eigen_half (mul_peirceHalf hc y)
  have hsplit : mulL c = peirceOne c + (2 : ℝ)⁻¹ • peirceHalf c := by
    ext y
    simp only [mulL_apply, LinearMap.add_apply, LinearMap.smul_apply, peirceOne_apply,
      peirceHalf_apply]
    module
  have hmem : c ∈ LinearMap.range (peirceOne c) := ⟨c, peirceOne_of_eigen (by rw [hc])⟩
  have hne : LinearMap.range (peirceOne c) ≠ ⊥ := fun h => hc0 (by simpa [h] using hmem)
  have hpos : 0 < Module.finrank ℝ (LinearMap.range (peirceOne c)) :=
    Module.finrank_pos_iff.mpr (by rw [Submodule.nontrivial_iff_ne_bot]; exact hne)
  rw [jtr_apply, hsplit, map_add, LinearMap.map_smul, hid1.isProj_range.trace,
    hidh.isProj_range.trace]
  have h1 : (1 : ℝ) ≤ (Module.finrank ℝ (LinearMap.range (peirceOne c)) : ℝ) := by
    exact_mod_cast hpos
  have h2 : (0 : ℝ) ≤ (Module.finrank ℝ (LinearMap.range (peirceHalf c)) : ℝ) := Nat.cast_nonneg _
  simp only [smul_eq_mul]
  linarith

end Trace

/-! ## The form itself -/

section Form

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

/-- **The Jordan trace form** `τ(x, y) = tr(L_{x ∘ y})`. -/
def traceForm : J →ₗ[ℝ] J →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => jtr (x * y))
    (fun x x' y => by rw [add_mul, map_add])
    (fun r x y => by rw [smul_mul_assoc, map_smul, smul_eq_mul])
    (fun x y y' => by rw [mul_add, map_add])
    (fun r x y => by rw [mul_smul_comm' r x y, map_smul, smul_eq_mul])

omit [IsCommJordan J] in
@[simp] theorem traceForm_apply (x y : J) : traceForm x y = jtr (x * y) := rfl

omit [IsCommJordan J] in
theorem traceForm_comm (x y : J) : traceForm x y = traceForm y x := by
  simp only [traceForm_apply, mul_comm]

/-- **The trace form is associative**: `τ(x ∘ y, z) = τ(y, x ∘ z)`.  This is the hypothesis
`hassoc` that `EuclideanJordan/Order.lean`'s Euclidean section and
    `EuclideanJordan/Class.lean`'s class both take, now a
theorem about a form built from the algebra alone. -/
theorem traceForm_assoc (x y z : J) : traceForm (x * y) z = traceForm y (x * z) := by
  simp only [traceForm_apply]
  rw [show x * y = y * x from mul_comm _ _]
  exact jtr_assoc y x z

end Form

/-! ## Positive definiteness -/

section PosDef

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J]

omit [IsCommJordan J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- The square of a diagonal element is diagonal with squared coefficients.  Orthogonality kills
every cross term. -/
theorem sq_of_orthIdem {n : ℕ} {q : Fin n → J} (hq : IsOrthIdemFamily q) {lam : Fin n → ℝ}
    {x : J} (hx : x = ∑ i, lam i • q i) :
    x * x = ∑ i, (lam i * lam i) • q i := by
  classical
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, mul_smul_comm', smul_smul, hq.idem i]
  · intro j _ hji
    rw [smul_mul_assoc, mul_smul_comm', smul_smul, hq.orth i j (Ne.symm hji), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **`τ(x, x) ≥ 0`.**  The spectral resolution turns `x ∘ x` into a nonnegative combination of
idempotents, and `jtr` is nonnegative on each of them. -/
theorem traceForm_self_nonneg (x : J) : 0 ≤ traceForm x x := by
  obtain ⟨n, q, lam, hfam, _, hx⟩ := spectral_resolution x
  rw [traceForm_apply, sq_of_orthIdem hfam hx, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (mul_self_nonneg _) (jtr_nonneg_of_idem (hfam.idem i))

/-- **`τ` is definite.**  A vanishing `τ(x, x) = ∑ᵢ λᵢ² tr(L_{qᵢ})` forces `λᵢ = 0` for every
`qᵢ ≠ 0`, because `tr(L_{qᵢ}) ≥ 1` there; and the terms with `qᵢ = 0` vanish anyway. -/
theorem eq_zero_of_traceForm_self_eq_zero {x : J} (h : traceForm x x = 0) : x = 0 := by
  classical
  obtain ⟨n, q, lam, hfam, _, hx⟩ := spectral_resolution x
  have hterm : ∀ i : Fin n, 0 ≤ (lam i * lam i) * jtr (q i) := fun i =>
    mul_nonneg (mul_self_nonneg _) (jtr_nonneg_of_idem (hfam.idem i))
  have hsum : (∑ i, (lam i * lam i) * jtr (q i)) = 0 := by
    rw [traceForm_apply, sq_of_orthIdem hfam hx, map_sum] at h
    simpa only [map_smul, smul_eq_mul] using h
  have hzero : ∀ i : Fin n, (lam i * lam i) * jtr (q i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum i (Finset.mem_univ i)
  rw [hx]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hq0 : q i = 0
  · rw [hq0, smul_zero]
  · have hpos : (0 : ℝ) < jtr (q i) := lt_of_lt_of_le zero_lt_one (one_le_jtr_of_idem (hfam.idem
      i) hq0)
    have : lam i * lam i = 0 := by
      rcases mul_eq_zero.mp (hzero i) with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hpos)
    rw [mul_self_eq_zero.mp this, zero_smul]

/-- `τ(x, x) = 0 ↔ x = 0`. -/
theorem traceForm_self_eq_zero_iff (x : J) : traceForm x x = 0 ↔ x = 0 :=
  ⟨eq_zero_of_traceForm_self_eq_zero, fun h => by rw [h]; simp⟩

end PosDef

end EuclideanJordan
