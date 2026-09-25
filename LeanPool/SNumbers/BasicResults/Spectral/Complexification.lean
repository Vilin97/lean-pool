/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module

/-!
# Complexification of a real inner product space

*Why this file is needed:* the spectral projection is built with the continuous functional
calculus, which is only available over `ℂ`. To obtain it over `ℝ` (and uniformly over any `RCLike`
field), `RealProjection`/`Representation` complexify the space, run the `ℂ` construction, and
restrict back — and this file supplies the complexification with its complex inner product (a
piece Mathlib does not yet have).

Given a real inner product space `H`, this file builds its **complexification**
`Complexification H`: the complex inner product space whose elements are thought
of as formal sums `x + i·y` with `x, y ∈ H`.

Concretely we model `Complexification H` as the pair type `H × H` (the pair
`(x, y)` standing for `x + i·y`), equip it with

* the complex scalar multiplication
  `(a + b·i) • (x, y) = (a·x - b·y, a·y + b·x)`, and
* the Hermitian inner product
  `⟪(x₁,y₁), (x₂,y₂)⟫ = (⟪x₁,x₂⟫ + ⟪y₁,y₂⟫) + i·(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)`,

and prove that this makes `Complexification H` a complex inner product space
(`InnerProductSpace ℂ`). The canonical real-linear isometric embedding
`x ↦ x + i·0` is provided as `Complexification.ofRealLi`.

**Note.** Mathlib has base change of *modules*
(`ℂ ⊗[ℝ] M` is a `Module ℂ`) but no construction equipping the complexification
of a real *inner product space* with its complex inner product. This file
constructs it, kept deliberately elementary and self-contained.
-/

@[expose] public section

noncomputable section

open RCLike Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The **complexification** of a real inner product space `H`, modelled as the
pair type `H × H`; the pair `(x, y)` represents the formal sum `x + i·y`. -/
def Complexification (H : Type*) :
    Type _ := H × H

namespace Complexification

/-- The underlying additive group is that of `H × H`. -/
instance : AddCommGroup (Complexification H) := inferInstanceAs (AddCommGroup (H × H))

/-- The element `x + i·y` of the complexification.

This is the pair `(x, y)`, but wrapped in a name. Writing a bare pair `(x, y)` at
type `Complexification H` is only type-correct after unfolding `Complexification`,
which `simp` and `rw` refuse to do; going through `mk` together with the
projection lemmas `mk_fst`/`mk_snd` below keeps every goal in this file stated in
terms the simp set can act on. -/
def mk (x y : H) : Complexification H := (x, y)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
@[simp] lemma mk_fst (x y : H) : (mk x y).1 = x := rfl
omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
@[simp] lemma mk_snd (x y : H) : (mk x y).2 = y := rfl

/-- Complex scalar multiplication: `(a + b·i) • (x, y) = (a·x - b·y, a·y + b·x)`. -/
instance : SMul ℂ (Complexification H) where
  smul c u := mk (c.re • u.1 - c.im • u.2) (c.re • u.2 + c.im • u.1)

@[simp] lemma smul_fst (c : ℂ) (u : Complexification H) :
    (c • u).1 = c.re • u.1 - c.im • u.2 := rfl

@[simp] lemma smul_snd (c : ℂ) (u : Complexification H) :
    (c • u).2 = c.re • u.2 + c.im • u.1 := rfl

omit [InnerProductSpace ℝ H] in
@[simp] lemma add_fst (u v : Complexification H) : (u + v).1 = u.1 + v.1 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma add_snd (u v : Complexification H) : (u + v).2 = u.2 + v.2 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma zero_fst : (0 : Complexification H).1 = 0 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma zero_snd : (0 : Complexification H).2 = 0 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma sub_fst (u v : Complexification H) : (u - v).1 = u.1 - v.1 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma sub_snd (u v : Complexification H) : (u - v).2 = u.2 - v.2 := rfl

instance : Module ℂ (Complexification H) where
  one_smul u := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, Complex.one_re, Complex.one_im] <;> module
  mul_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, zero_fst, zero_snd] <;> module
  smul_add c u v := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, add_fst, add_snd] <;> module
  add_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.add_re, Complex.add_im, add_fst, add_snd] <;> module
  zero_smul u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.zero_re, Complex.zero_im, zero_fst, zero_snd] <;>
      module

/-- The Hermitian inner product:
`⟪(x₁,y₁), (x₂,y₂)⟫ = (⟪x₁,x₂⟫ + ⟪y₁,y₂⟫) + i·(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)`. -/
instance : Inner ℂ (Complexification H) where
  inner u v := ⟨inner ℝ u.1 v.1 + inner ℝ u.2 v.2, inner ℝ u.1 v.2 - inner ℝ u.2 v.1⟩

@[simp] lemma inner_re (u v : Complexification H) :
    (inner ℂ u v).re = inner ℝ u.1 v.1 + inner ℝ u.2 v.2 := rfl

@[simp] lemma inner_im (u v : Complexification H) :
    (inner ℂ u v).im = inner ℝ u.1 v.2 - inner ℝ u.2 v.1 := rfl

/-- The `InnerProductSpace.Core` packaging all the axioms of the complex inner
product on the complexification. -/
@[reducible] def core : InnerProductSpace.Core ℂ (Complexification H) where
  inner u v := inner ℂ u v
  conj_inner_symm u v := by
    apply Complex.ext
    all_goals
      simp only [Complex.conj_re, Complex.conj_im, inner_re, inner_im,
        real_inner_comm u.1 v.1, real_inner_comm u.2 v.2,
        real_inner_comm v.1 u.2, real_inner_comm v.2 u.1]
    all_goals ring
  re_inner_nonneg u := by
    rw [RCLike.re_to_complex, inner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, Complex.add_re, Complex.add_im, add_fst, add_snd,
        inner_add_left] <;> ring
  smul_left u v c := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, smul_fst, smul_snd, inner_sub_left, inner_add_left,
        real_inner_smul_left, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  definite u h := by
    have hre : inner ℝ u.1 u.1 + inner ℝ u.2 u.2 = 0 := by
      have := congrArg Complex.re h; simpa using this
    have n1 : (0 : ℝ) ≤ inner ℝ u.1 u.1 := real_inner_self_nonneg
    have n2 : (0 : ℝ) ≤ inner ℝ u.2 u.2 := real_inner_self_nonneg
    have h1 : inner ℝ u.1 u.1 = 0 := le_antisymm (by linarith) n1
    have h2 : inner ℝ u.2 u.2 = 0 := le_antisymm (by linarith) n2
    exact Prod.ext ((inner_self_eq_zero (𝕜 := ℝ)).mp h1) ((inner_self_eq_zero (𝕜 := ℝ)).mp h2)

/-- The norm coming from the complex inner product. -/
instance : NormedAddCommGroup (Complexification H) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Complexification H) _ _ _ core

/-- The complexification of a real inner product space is a complex inner
product space. -/
instance : InnerProductSpace ℂ (Complexification H) :=
  letI : InnerProductSpace.Core ℂ (Complexification H) := core
  InnerProductSpace.ofCore inferInstance

instance [Nontrivial H] : Nontrivial (Complexification H) :=
  inferInstanceAs (Nontrivial (H × H))

/-- The real scalar action (the restriction of the complex one) is component-wise. -/
@[simp] lemma rsmul_fst (r : ℝ) (u : Complexification H) : (r • u).1 = r • u.1 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_fst]; simp

@[simp] lemma rsmul_snd (r : ℝ) (u : Complexification H) : (r • u).2 = r • u.2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_snd]; simp

/-- The canonical embedding `x ↦ x + i·0` of `H` into its complexification. -/
def ofReal (x : H) : Complexification H := mk x 0

omit [InnerProductSpace ℝ H] in
@[simp] lemma ofReal_fst (x : H) : (ofReal x).1 = x := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma ofReal_snd (x : H) : (ofReal x).2 = 0 := rfl

omit [InnerProductSpace ℝ H] in
@[simp] lemma ofReal_add (x y : H) : ofReal (x + y) = ofReal x + ofReal y := by
  apply Prod.ext <;> simp

omit [InnerProductSpace ℝ H] in
@[simp] lemma ofReal_sub (x y : H) : ofReal (x - y) = ofReal x - ofReal y := by
  apply Prod.ext <;> simp

/-- The embedding `ofReal` preserves norms: `‖x + i·0‖ = ‖x‖`. -/
@[simp] lemma norm_ofReal (x : H) : ‖ofReal x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, inner_re, ofReal_fst, ofReal_snd, inner_zero_left, add_zero,
    real_inner_self_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg x)

/-- The embedding `ofReal` as a real-linear isometry `H →ₗᵢ[ℝ] Complexification H`. -/
def ofRealLi : H →ₗᵢ[ℝ] Complexification H where
  toFun := ofReal
  map_add' x y := by apply Prod.ext <;> simp
  map_smul' r x := by apply Prod.ext <;> simp
  norm_map' := norm_ofReal

/-! ### Completeness

The norm `‖(x, y)‖ = √(‖x‖² + ‖y‖²)` controls each component (`‖x‖, ‖y‖ ≤ ‖(x,y)‖`)
and is in turn controlled by them (`‖(x,y)‖ ≤ ‖x‖ + ‖y‖`). Hence a Cauchy sequence
in `Complexification H` has Cauchy components, and converges componentwise; so the
complexification of a *complete* real inner product space is itself complete — a
complex Hilbert space. -/

/-- The squared norm is the sum of the squared component norms. -/
lemma re_inner_self (u : Complexification H) :
    (inner ℂ u u).re = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 := by
  simp only [inner_re, real_inner_self_eq_norm_sq]

lemma norm_sq_eq (u : Complexification H) : ‖u‖ ^ 2 = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), RCLike.re_to_complex, re_inner_self,
    Real.sq_sqrt (by positivity)]

lemma norm_fst_le (u : Complexification H) : ‖u.1‖ ≤ ‖u‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2, sq_nonneg ‖u.2‖]

lemma norm_snd_le (u : Complexification H) : ‖u.2‖ ≤ ‖u‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2, sq_nonneg ‖u.1‖]

lemma norm_le_add (u : Complexification H) : ‖u‖ ≤ ‖u.1‖ + ‖u.2‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2,
    mul_nonneg (norm_nonneg u.1) (norm_nonneg u.2)]

/-- The real-part projection `(x, y) ↦ x` as an `ℝ`-linear map. -/
def fstₗ : Complexification H →ₗ[ℝ] H where
  toFun u := u.1
  map_add' := add_fst
  map_smul' r u := rsmul_fst r u

/-- The real-part projection `(x, y) ↦ x` as a continuous `ℝ`-linear map. -/
def fstL : Complexification H →L[ℝ] H :=
  fstₗ.mkContinuous 1 fun u => by rw [one_mul]; exact norm_fst_le u

@[simp] lemma fstL_apply (u : Complexification H) : fstL u = u.1 := rfl

instance [CompleteSpace H] : CompleteSpace (Complexification H) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have lip1 : LipschitzWith 1 (fun u : Complexification H => u.1) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      simp only [dist_eq_norm, NNReal.coe_one, one_mul]; exact norm_fst_le (u - v)
  have lip2 : LipschitzWith 1 (fun u : Complexification H => u.2) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      simp only [dist_eq_norm, NNReal.coe_one, one_mul]; exact norm_snd_le (u - v)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (lip1.uniformContinuous.comp_cauchySeq hf)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (lip2.uniformContinuous.comp_cauchySeq hf)
  refine ⟨mk a b, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun n => ‖(f n).1 - a‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp ha
  have h2 : Tendsto (fun n => ‖(f n).2 - b‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hb
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
  exact norm_le_add _

/-! ### Conjugation

Complex conjugation `x + i·y ↦ x - i·y` is the canonical conjugate-linear isometric
involution of the complexification. Its set of fixed points is exactly the image of
`ofReal`, i.e. the "real" elements — the fact that lets one detect when a complex
object descends to the real space. -/

/-- Complex conjugation on the complexification: `(x, y) ↦ (x, -y)`. -/
def conj (u : Complexification H) : Complexification H := mk u.1 (-u.2)

omit [InnerProductSpace ℝ H] in
@[simp] lemma conj_fst (u : Complexification H) : (conj u).1 = u.1 := rfl
omit [InnerProductSpace ℝ H] in
@[simp] lemma conj_snd (u : Complexification H) : (conj u).2 = -u.2 := rfl

omit [InnerProductSpace ℝ H] in
@[simp] lemma conj_conj (u : Complexification H) : conj (conj u) = u := by
  apply Prod.ext <;> simp

omit [InnerProductSpace ℝ H] in
@[simp] lemma conj_ofReal (x : H) : conj (ofReal x) = ofReal x := by
  apply Prod.ext <;> simp

omit [InnerProductSpace ℝ H] in
lemma conj_add (u v : Complexification H) : conj (u + v) = conj u + conj v := by
  apply Prod.ext <;> simp only [conj_fst, conj_snd, add_fst, add_snd, neg_add]

/-- Conjugation is conjugate-linear: `conj (c • u) = conj c • conj u`. -/
lemma conj_smul (c : ℂ) (u : Complexification H) :
    conj (c • u) = (starRingEnd ℂ c) • conj u := by
  apply Prod.ext <;>
    simp only [conj_fst, conj_snd, smul_fst, smul_snd, Complex.conj_re, Complex.conj_im] <;> module

@[simp] lemma norm_conj (u : Complexification H) : ‖conj u‖ = ‖u‖ := by
  have h1 := norm_sq_eq (conj u)
  have h2 := norm_sq_eq u
  simp only [conj_fst, conj_snd, norm_neg] at h1
  have hsq : ‖conj u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Conjugation as a real-linear isometry. -/
def conjLi : Complexification H →ₗᵢ[ℝ] Complexification H where
  toFun := conj
  map_add' := conj_add
  map_smul' r u := by apply Prod.ext <;> simp [smul_neg]
  norm_map' := norm_conj

/-- Conjugation as a continuous `ℝ`-linear map. -/
def conjL : Complexification H →L[ℝ] Complexification H := conjLi.toContinuousLinearMap

@[simp] lemma conjL_apply (u : Complexification H) : conjL u = conj u := rfl

/-- The elements fixed by conjugation are exactly the "real" ones, `x + i·0`. -/
lemma conj_eq_self_iff (u : Complexification H) : conj u = u ↔ ∃ x, u = ofReal x := by
  constructor
  · intro h
    have hsnd : -u.2 = u.2 := by simpa only [conj_snd] using congrArg Prod.snd h
    have hz : u.2 = 0 := by
      have h2 : (2 : ℝ) • u.2 = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hsnd.symm
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact ⟨u.1, by apply Prod.ext <;> simp [hz]⟩
  · rintro ⟨x, rfl⟩; exact conj_ofReal x

/-! ### Complexification of operators

A real bounded operator `S : H₁ →L[ℝ] H₂` extends to a complex bounded operator
`Sℂ : Complexification H₁ →L[ℂ] Complexification H₂`, `(x, y) ↦ (S x, S y)`, with the
same operator norm. It commutes with conjugation and is compatible with the real
embedding — the precise senses in which `Sℂ` "is" `S` viewed complex-linearly. -/

section Operator

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- The complexification of `S` as a `ℂ`-linear map, `(x, y) ↦ (S x, S y)`. -/
def complexifyₗ (S : H₁ →L[ℝ] H₂) : Complexification H₁ →ₗ[ℂ] Complexification H₂ where
  toFun u := mk (S u.1) (S u.2)
  map_add' u v := by apply Prod.ext <;> simp
  map_smul' c u := by apply Prod.ext <;> simp [map_sub, map_smul]

@[simp] lemma complexifyₗ_fst (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexifyₗ S u).1 = S u.1 := rfl
@[simp] lemma complexifyₗ_snd (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexifyₗ S u).2 = S u.2 := rfl

lemma norm_complexifyₗ_le (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    ‖complexifyₗ S u‖ ≤ ‖S‖ * ‖u‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (norm_nonneg S) (norm_nonneg u))
  rw [norm_sq_eq (complexifyₗ S u), mul_pow, norm_sq_eq u, mul_add]
  simp only [complexifyₗ_fst, complexifyₗ_snd, ← mul_pow]
  gcongr <;> exact S.le_opNorm _

/-- The complexification of a real bounded operator `S`, as a `ℂ`-linear bounded
operator `(x, y) ↦ (S x, S y)`. -/
def complexify (S : H₁ →L[ℝ] H₂) : Complexification H₁ →L[ℂ] Complexification H₂ :=
  (complexifyₗ S).mkContinuous ‖S‖ (norm_complexifyₗ_le S)

@[simp] lemma complexify_fst (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexify S u).1 = S u.1 := rfl
@[simp] lemma complexify_snd (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexify S u).2 = S u.2 := rfl

/-- `Sℂ` agrees with `S` on the real subspace: `Sℂ (x + i·0) = (S x) + i·0`. -/
@[simp] lemma complexify_ofReal (S : H₁ →L[ℝ] H₂) (x : H₁) :
    complexify S (ofReal x) = ofReal (S x) := by
  apply Prod.ext <;> simp

/-- `Sℂ` commutes with conjugation (this is what it means for `Sℂ` to be "real"). -/
@[simp] lemma complexify_conj (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    complexify S (conj u) = conj (complexify S u) := by
  apply Prod.ext <;> simp [map_neg]

/-- The complexification preserves the operator norm. -/
@[simp] lemma norm_complexify (S : H₁ →L[ℝ] H₂) : ‖complexify S‖ = ‖S‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) (norm_complexifyₗ_le S)
  · refine ContinuousLinearMap.opNorm_le_bound S (norm_nonneg (complexify S)) fun x => ?_
    calc ‖S x‖ = ‖complexify S (ofReal x)‖ := by rw [complexify_ofReal, norm_ofReal]
      _ ≤ ‖complexify S‖ * ‖ofReal x‖ := (complexify S).le_opNorm _
      _ = ‖complexify S‖ * ‖x‖ := by rw [norm_ofReal]

section Adjoint

variable [CompleteSpace H₁] [CompleteSpace H₂]

/-- Complexification commutes with taking adjoints: `(Sℂ)* = (S*)ℂ`. -/
@[simp] lemma adjoint_complexify (S : H₁ →L[ℝ] H₂) :
    ContinuousLinearMap.adjoint (complexify S) = complexify (ContinuousLinearMap.adjoint S) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  apply Complex.ext <;>
    simp only [inner_re, inner_im, complexify_fst, complexify_snd,
      ContinuousLinearMap.adjoint_inner_left]

end Adjoint

end Operator

end Complexification

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
