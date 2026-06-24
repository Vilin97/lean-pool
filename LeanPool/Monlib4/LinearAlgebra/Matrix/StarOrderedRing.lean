/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.PiStarOrderedRing
import LeanPool.Monlib4.LinearAlgebra.PiDirectSum
import LeanPool.Monlib4.LinearAlgebra.InnerAut
import LeanPool.Monlib4.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import LeanPool.Monlib4.LinearAlgebra.KroneckerToTensor
import LeanPool.Monlib4.Preq.Complex
import LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat
import LeanPool.Monlib4.LinearAlgebra.Matrix.Spectra
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Matrix algebras as star ordered rings

This file keeps the upstream monlib4 API around matrix positivity and the
`MatrixOrder` scoped order.  Current Mathlib supplies the underlying matrix
order and `StarOrderedRing` instance, so this file restores the Monlib-facing
negative definiteness definitions, spectral criteria, and compatibility names.
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder

theorem _root_.Matrix.eq_zero_iff {n : Type _} [Fintype n]
    {x : Matrix n n ℂ} :
    x = 0 ↔ ∀ a : n → ℂ, star a ⬝ᵥ x.mulVec a = 0 := by
  classical
  calc
    x = 0 ↔ (Matrix.toLpLin 2 2) x = 0 := by simp only [LinearEquiv.map_eq_zero_iff]
    _ ↔ ∀ a : WithLp 2 (n → ℂ),
        (inner ℂ (((Matrix.toLpLin 2 2) x) a) a : ℂ) = 0 :=
      (inner_map_self_eq_zero (T := (Matrix.toLpLin 2 2) x)).symm
    _ ↔ ∀ a : WithLp 2 (n → ℂ),
        (inner ℂ a (((Matrix.toLpLin 2 2) x) a) : ℂ) = 0 := by
      simp_rw [inner_eq_zero_symm]
    _ ↔ ∀ a : n → ℂ, star a ⬝ᵥ x *ᵥ a = 0 := by
      constructor
      · intro h a
        specialize h (WithLp.toLp 2 a)
        simpa [Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
          RCLike.inner_apply, Matrix.mulVec] using h
      · intro h a
        specialize h a.ofLp
        simpa [Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
          RCLike.inner_apply, Matrix.mulVec] using h

/-- The upstream Monlib order relation, now supplied by Mathlib under `MatrixOrder`. -/
@[reducible]
protected def _root_.Matrix.LE {n : Type _} :
    LE (Matrix n n ℂ) :=
  ⟨fun x y => (y - x).PosSemidef⟩

/-- A matrix is negative semidefinite when its Hermitian quadratic form is nonpositive. -/
def _root_.Matrix.NegSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    (x : Matrix n n 𝕜) : Prop :=
  x.IsHermitian ∧ ∀ a : n → 𝕜, dotProduct (Star.star a) (x *ᵥ a) ≤ 0

/-- A matrix is negative definite when its quadratic form is negative on nonzero inputs. -/
def _root_.Matrix.NegDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    (x : Matrix n n 𝕜) : Prop :=
  x.IsHermitian ∧ ∀ a : n → 𝕜, a ≠ 0 → (star a) ⬝ᵥ (x *ᵥ a) < 0

theorem _root_.Matrix.IsHermitian.neg_iff {𝕜 n : Type _} [RCLike 𝕜]
    (x : Matrix n n 𝕜) :
    (-x).IsHermitian ↔ x.IsHermitian :=
  ⟨fun h => neg_neg x ▸ h.neg, Matrix.IsHermitian.neg⟩

theorem _root_.Matrix.negSemidef_iff_neg_posSemidef {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] (x : Matrix n n 𝕜) :
    x.NegSemidef ↔ (-x).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨Matrix.IsHermitian.neg h.1, fun a => ?_⟩
    simpa [Matrix.neg_mulVec, dotProduct_neg] using neg_nonneg.mpr (h.2 a)
  · intro h
    refine ⟨(Matrix.IsHermitian.neg_iff x).mp h.1, fun a => ?_⟩
    exact neg_nonneg.mp (by simpa [Matrix.neg_mulVec, dotProduct_neg] using h.2 a)

theorem _root_.Matrix.negDef_iff_neg_posDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    (x : Matrix n n 𝕜) :
    x.NegDef ↔ (-x).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨Matrix.IsHermitian.neg h.1, fun a ha => ?_⟩
    simpa [Matrix.neg_mulVec, dotProduct_neg] using neg_pos.mpr (h.2 a ha)
  · intro h
    refine ⟨(Matrix.IsHermitian.neg_iff x).mp h.1, fun a ha => ?_⟩
    exact neg_pos.mp (by simpa [Matrix.neg_mulVec, dotProduct_neg] using h.2 (x := a) ha)

theorem _root_.Matrix.NegDef.re_dotProduct_neg {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n]
    {M : Matrix n n 𝕜} (hM : M.NegDef) {x : n → 𝕜} (hx : x ≠ 0) :
    RCLike.re (dotProduct (star x) (M *ᵥ x)) < 0 :=
  RCLike.neg_iff.mp (hM.2 _ hx) |>.1

theorem _root_.Matrix.NegSemidef.nonpos_eigenvalues {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.NegSemidef) (i : n) :
    hx.1.eigenvalues i ≤ 0 := by
  rw [hx.1.eigenvalues_eq i]
  exact (RCLike.nonpos_def.mp (hx.2 _)).1

theorem _root_.Matrix.NegDef.neg_eigenvalues {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.NegDef) (i : n) :
    hx.1.eigenvalues i < 0 := by
  rw [hx.1.eigenvalues_eq i]
  apply hx.re_dotProduct_neg
  intro h
  exact hx.1.eigenvectorBasis.orthonormal.ne_zero i <| PiLp.ext fun j => by
    simpa using congrFun h j

theorem _root_.Matrix.posSemidef_and_negSemidef_iff_eq_zero {𝕜 n : Type _}
    [RCLike 𝕜] [Fintype n] {x : Matrix n n 𝕜} :
    x.PosSemidef ∧ x.NegSemidef ↔ x = 0 := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h1.1.eigenvalues_eq_zero_iff]
    ext i
    have hpos := h1.eigenvalues_nonneg i
    have hneg := h2.nonpos_eigenvalues i
    exact le_antisymm hneg hpos
  · rintro rfl
    simp only [negSemidef_iff_neg_posSemidef, neg_zero, and_self, PosSemidef.zero]

theorem _root_.Matrix.not_posDef_and_negDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [Nonempty n] (x : Matrix n n 𝕜) :
    ¬ (x.PosDef ∧ x.NegDef) := by
  classical
  let i : n := Nonempty.some (by infer_instance)
  rintro ⟨h1, h2⟩
  linarith [PosDef.pos_eigenvalues h1 i, NegDef.neg_eigenvalues h2 i]

open scoped BigOperators

theorem _root_.Matrix.diagonal_posSemidef_iff {𝕜 n : Type _} [RCLike 𝕜]
    [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ 0 ≤ x := by
  simp [Pi.le_def, Matrix.PosSemidef.diagonal_iff x]

theorem _root_.Matrix.diagonal_negSemidef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).NegSemidef ↔ x ≤ 0 := by
  simp_rw [negSemidef_iff_neg_posSemidef, diagonal_neg, diagonal_posSemidef_iff,
    Pi.le_def, Pi.zero_apply, Left.nonneg_neg_iff]

theorem _root_.Matrix.diagonal_posDef_iff {𝕜 n : Type _} [RCLike 𝕜]
    [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i :=
  Matrix.PosDef.diagonal_iff x

theorem _root_.Matrix.diagonal_negDef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).NegDef ↔ ∀ i, x i < 0 := by
  simp_rw [negDef_iff_neg_posDef, diagonal_neg, diagonal_posDef_iff, Left.neg_pos_iff]

theorem _root_.Matrix.posSemidef_iff_of_isHermitian {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    x.PosSemidef ↔ 0 ≤ hx.eigenvalues :=
  hx.posSemidef_iff_eigenvalues_nonneg

theorem _root_.Matrix.posSemidef_iff_isHermitian_and_nonneg_spectrum {𝕜 n : Type _}
    [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔ x.IsHermitian ∧ spectrum 𝕜 (Matrix.toLin' x) ⊆ {x : 𝕜 | 0 ≤ x} := by
  rw [Matrix.spectrum_toLin']
  exact Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg

theorem _root_.Matrix.posDef_iff_of_isHermitian {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    x.PosDef ↔ ∀ i, 0 < hx.eigenvalues i :=
  hx.posDef_iff_eigenvalues_pos

theorem _root_.Matrix.posDef_iff_isHermitian_and_pos_spectrum {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosDef ↔ x.IsHermitian ∧ spectrum 𝕜 (Matrix.toLin' x) ⊆ {x : 𝕜 | 0 < x} := by
  rw [Matrix.spectrum_toLin']
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [h.1.spectrum_eq_image_range]
    rintro z ⟨_, ⟨i, rfl⟩, rfl⟩
    change 0 < (RCLike.ofReal (h.1.eigenvalues i) : 𝕜)
    exact_mod_cast h.eigenvalues_pos i
  · rintro ⟨h1, h2⟩
    rw [posDef_iff_of_isHermitian h1]
    intro i
    apply (RCLike.zero_lt_real (𝕜 := 𝕜)).mp
    exact h2 (by rw [h1.spectrum_eq_image_range]; exact ⟨_, ⟨i, rfl⟩, rfl⟩)

theorem _root_.Matrix.posSemidef_iff_commute {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    {x y : Matrix n n 𝕜} (hx : x.PosSemidef) (hy : y.PosSemidef) :
    Commute x y ↔ (x * y).PosSemidef := by
  classical
  refine ⟨fun h => ?_, fun h => (Matrix.commute_iff hx.1 hy.1).mpr h.1⟩
  rw [posSemidef_iff_isHermitian_and_nonneg_spectrum]
  refine ⟨(Matrix.commute_iff hx.1 hy.1).mp h, ?_⟩
  obtain ⟨a, rfl⟩ := (posSemidef_iff _).mp hx
  obtain ⟨b, rfl⟩ := (posSemidef_iff _).mp hy
  calc
    spectrum 𝕜 (toLin' (aᴴ * a * (bᴴ * b))) =
        spectrum 𝕜 ((toLin' a) * toLin' (bᴴ * b) * toLin' aᴴ) := by
      rw [Module.End.mul_eq_comp, spectrum.comm]
      simp_rw [Module.End.mul_eq_comp, ← toLin'_mul, mul_assoc]
    _ = spectrum 𝕜 (toLin' ((b * aᴴ)ᴴ * (b * aᴴ))) := by
      simp_rw [conjTranspose_mul, conjTranspose_conjTranspose, Module.End.mul_eq_comp,
        ← toLin'_mul, mul_assoc]
  exact (posSemidef_iff_isHermitian_and_nonneg_spectrum.mp
    (posSemidef_conjTranspose_mul_self _)).2

theorem _root_.Matrix.innerAut_negSemidef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
    (innerAut U a).NegSemidef ↔ a.NegSemidef := by
  simp_rw [negSemidef_iff_neg_posSemidef, ← map_neg, innerAut_posSemidef_iff]

/-- `f_U(x)` is negative definite if and only if `x` is negative definite. -/
theorem _root_.Matrix.innerAut_negDef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    (innerAut U x).NegDef ↔ x.NegDef := by
  simp_rw [negDef_iff_neg_posDef, ← map_neg, innerAut_posDef_iff]

theorem _root_.Matrix.negSemidef_iff_of_isHermitian {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    x.NegSemidef ↔ hx.eigenvalues ≤ 0 := by
  nth_rw 1 [IsHermitian.spectral_theorem'' hx, innerAut_negSemidef_iff,
    diagonal_negSemidef_iff]
  simp_rw [Pi.le_def, Function.comp_apply, Pi.zero_apply, ← @RCLike.ofReal_zero 𝕜,
    RCLike.real_le_real]

theorem _root_.Matrix.negDef_iff_of_isHermitian {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    x.NegDef ↔ ∀ i, hx.eigenvalues i < 0 := by
  nth_rw 1 [IsHermitian.spectral_theorem'' hx, innerAut_negDef_iff, diagonal_negDef_iff]
  simp_rw [Function.comp_apply, ← @RCLike.ofReal_zero 𝕜, RCLike.real_lt_real]

theorem _root_.Matrix.posDef_of_posSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.PosSemidef) :
    x.PosDef ↔ ∀ i, hx.1.eigenvalues i ≠ 0 := by
  rw [posDef_iff_of_isHermitian hx.1]
  simp_rw [lt_iff_le_and_ne, ne_eq, hx.eigenvalues_nonneg, true_and, eq_comm]

theorem _root_.Matrix.negDef_of_negSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.NegSemidef) :
    x.NegDef ↔ ∀ i, hx.1.eigenvalues i ≠ 0 := by
  rw [negDef_iff_of_isHermitian hx.1]
  simp_rw [lt_iff_le_and_ne, ne_eq, NegSemidef.nonpos_eigenvalues hx, true_and]

/-- The matrix partial order induced by positive semidefinite differences. -/
@[reducible]
noncomputable def _root_.Matrix.partialOrder {n : Type _} :
    PartialOrder (Matrix n n ℂ) :=
  inferInstance

theorem _root_.Matrix.starOrderedRing {n : Type _} [Fintype n] :
    StarOrderedRing (Matrix n n ℂ) :=
  inferInstance

theorem _root_.Matrix.Pi.le_iff_sub_nonneg {ι : Type _} {n : ι → Type _}
    [∀ i, Fintype (n i)] (x y : PiMat ℂ ι n) :
    x ≤ y ↔ ∃ z : PiMat ℂ ι n, y = x + star z * z := by
  simp_rw [funext_iff, Pi.add_apply, Pi.mul_apply, Pi.star_apply, Pi.le_def, Matrix.le_iff,
    Matrix.posSemidef_iff, sub_eq_iff_eq_add', Matrix.star_eq_conjTranspose]
  exact ⟨fun hx => ⟨fun i => (hx i).choose, fun i => (hx i).choose_spec⟩,
    fun ⟨y, hy⟩ i => ⟨y i, hy i⟩⟩

theorem _root_.Matrix.PiStarOrderedRing {ι : Type _} {n : ι → Type _}
    [∀ i, Fintype (n i)] :
    StarOrderedRing (PiMat ℂ ι n) :=
  StarOrderedRing.of_le_iff fun a b => by simp_rw [Pi.le_iff_sub_nonneg]

scoped[MatrixOrder] attribute [instance] Matrix.PiStarOrderedRing

theorem _root_.Matrix.negSemidef_iff_nonpos {n : Type _} [Fintype n]
    (x : Matrix n n ℂ) :
    x.NegSemidef ↔ x ≤ 0 := by
  rw [Matrix.negSemidef_iff_neg_posSemidef, Matrix.le_iff, zero_sub]

theorem _root_.Matrix.PosSemidef.conj_by_isHermitian_posSemidef {𝕜 n : Type _}
    [RCLike 𝕜] [Fintype n] {x y : Matrix n n 𝕜}
    (hx : x.PosSemidef) (hy : y.IsHermitian) :
    PosSemidef (y * x * y) := by
  nth_rw 1 [← hy.eq]
  exact PosSemidef.conjTranspose_mul_mul_same hx _

theorem _root_.Matrix.IsHermitian.conj_by_isHermitian_posSemidef {𝕜 n : Type _}
    [RCLike 𝕜] [Fintype n] {x y : Matrix n n 𝕜}
    (hx : x.IsHermitian) (hy : y.PosSemidef) :
    PosSemidef (x * y * x) := by
  nth_rw 1 [← hx.eq]
  exact PosSemidef.conjTranspose_mul_mul_same hy _

alias isHermitian_mul_iff := Matrix.commute_iff

end Matrix

lemma StarAlgEquiv.map_pow {R A₁ A₂ : Type _} [CommSemiring R] [Semiring A₁]
    [Semiring A₂] [Algebra R A₁] [Algebra R A₂] [Star A₁] [Star A₂]
    (e : A₁ ≃⋆ₐ[R] A₂) (x : A₁) (n : ℕ) :
    e (x ^ n) = e x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', map_mul, ih, ← pow_succ']

lemma Matrix.innerAut.map_pow {n : Type _} [Fintype n] [DecidableEq n] {𝕜 : Type _}
    [RCLike 𝕜] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) (n : ℕ) :
    (innerAut U x) ^ n = innerAut U (x ^ n) := by
  simp_rw [← innerAutStarAlg_apply_eq_innerAut_apply, StarAlgEquiv.map_pow]
