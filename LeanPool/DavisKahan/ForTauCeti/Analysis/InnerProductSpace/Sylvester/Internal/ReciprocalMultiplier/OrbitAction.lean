/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.Circle

/-!
# Unitary orbit actions on coordinate matrix units

Seam 1 of 4 of the finite reciprocal multiplier development: the finite-dimensional
linear algebra the whole estimate is expressed in, with no harmonic analysis in it.

* `basisMatrixUnit`, the coordinate matrix unit for a pair of orthonormal bases,
  and its expansion `sum_basisMatrixUnit`;
* `unitaryOrbitAction`, the two-sided action `T ↦ V ∘ T ∘ U⁻¹`, and
  `basisDiagonalUnitary`, the diagonal unitary of a phase family;
* `complexFourierPhase`, the unit complex scalar `exp (i x)` as a `unitary ℂ`;
* the doubled real rotation `basisDoubledRealRotation`, which realizes a complex
  phase on two orthogonal copies of a real space, together with its scalar action
  `doubledComplexScalarAction`, the phase action `doubledPhaseAction`, and the
  norm and summation identities they satisfy.

Everything here is an identity about finitely many basis vectors; the analytic
content enters in the sibling module `…ReciprocalMultiplier.Fourier`.

## Provenance

*Split, not restated.*  This module was part of
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Internal/ReciprocalMultiplier.lean`
before that 2887-line file was divided — the largest in
the library, and nearly 3x Tau Ceti's stated 1000-line limit for a new file
(`ForTauCeti/README.md` §4) — along its four mathematical seams.  **No statement,
signature, proof, attribute or declaration name changed**; the split is a file
boundary plus the imports it forces.  The file itself had carried
`set_option linter.style.longFile 2900` and a note saying a split "is not a
migration lane's business"; SPLIT-1K is the lane whose business it is, and the
option is gone from all four parts.

That file in turn was
`DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean`
before the sin-Θ closure moved into the staging layer.

Literature bridge for the group as a whole:
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.
-/

public section

namespace TauCeti

open TauCeti
open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The coordinate matrix unit sending the `j`th vector of `eE` to the `i`th
vector of `eF` and annihilating the other basis vectors. -/
noncomputable def basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) : E →ₗ[𝕜] F :=
  (InnerProductSpace.rankOne 𝕜 (eF i) (eE j)).toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Pointwise formula for a coordinate matrix unit. -/
@[simp]
theorem basisMatrixUnit_apply
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) (x : E) :
    basisMatrixUnit eF eE i j x = ⟪eE j, x⟫_𝕜 • eF i := by
  rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A rectangular map is the finite sum of its matrix coefficients times the
coordinate matrix units in any pair of orthonormal bases. -/
theorem sum_basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (T : E →ₗ[𝕜] F) :
    T = ∑ i, ∑ j, ⟪eF i, T (eE j)⟫_𝕜 • basisMatrixUnit eF eE i j := by
  classical
  refine eE.toBasis.ext fun q => ?_
  rw [OrthonormalBasis.coe_toBasis]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    basisMatrixUnit_apply, eE.inner_eq_ite]
  rw [← eF.sum_repr' (T (eE q))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single q]
  · simp
  · intro j _ hjq
    simp [hjq]
  · simp

/-- The linear action on rectangular maps induced by left and right unitary
composition. -/
@[expose]
noncomputable def unitaryOrbitAction
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) where
  toFun T := U.toLinearMap ∘ₗ T ∘ₗ V.toLinearMap
  map_add' A B := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' a A := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The two-sided unitary orbit action, unfolded to the composition it is. -/
@[simp]
theorem unitaryOrbitAction_apply
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (T : E →ₗ[𝕜] F) :
    unitaryOrbitAction U V T = U.toLinearMap ∘ₗ T ∘ₗ V.toLinearMap :=
  (rfl)

/-- The unitary diagonal in an orthonormal basis with prescribed unit-modulus
coordinate factors.  This is the finite-dimensional operator attached to one
Fourier character in the reciprocal-multiplier argument. -/
noncomputable def basisDiagonalUnitary {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : Type*} [Fintype ι] 
    (e : OrthonormalBasis ι 𝕜 G) (ζ : ι → unitary 𝕜) : G ≃ₗᵢ[𝕜] G :=
  e.repr.trans <|
    (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
      ζ i • LinearIsometryEquiv.refl 𝕜 𝕜).trans e.repr.symm

/-- A basis diagonal acts on each basis vector by its prescribed phase. -/
@[simp]
theorem basisDiagonalUnitary_apply_basis {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 G) (ζ : ι → unitary 𝕜) (i : ι) :
    basisDiagonalUnitary e ζ (e i) = (ζ i : 𝕜) • e i := by
  rw [← e.repr_symm_single i]
  simp only [basisDiagonalUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [LinearIsometryEquiv.piLpCongrRight_single]
  simp only [LinearIsometryEquiv.smul_apply]
  -- `simp only [LinearIsometryEquiv.smul_apply]` leaves the scalar as `ζ i • 1` inside
  -- `PiLp.single`, where `mul_one` cannot fire: the multiplication is under the
  -- `LinearIsometryEquiv` application, not at the head. Restating exposes it.
  change e.repr.symm (PiLp.single 2 i ((ζ i : 𝕜) * 1)) = _
  rw [mul_one]
  rw [← map_smul]
  congr 1
  ext q
  simp [PiLp.single_apply]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Left and right basis diagonals act on a coordinate matrix unit by the
product of the corresponding coordinate phases.  Taking the left phase at
frequency `α i` and the right phase at frequency `-β j` therefore realizes
the Fourier character at the difference `α i - β j`. -/
theorem unitaryOrbitAction_basisMatrixUnit
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (ζF : Fin (Module.finrank 𝕜 F) → unitary 𝕜)
    (ζE : Fin (Module.finrank 𝕜 E) → unitary 𝕜)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) :
    unitaryOrbitAction (basisDiagonalUnitary eF ζF)
        (basisDiagonalUnitary eE ζE) (basisMatrixUnit eF eE i j) =
      ((ζF i : 𝕜) * (ζE j : 𝕜)) • basisMatrixUnit eF eE i j := by
  refine eE.toBasis.ext fun q => ?_
  rw [OrthonormalBasis.coe_toBasis]
  -- `OrthonormalBasis.coe_toBasis` rewrites the basis but leaves both sides as maps;
  -- the rewrites below act on the *applied* form, and no lemma applies a bundled
  -- `basisDiagonalUnitary` to a point without unfolding the composition first.
  change basisDiagonalUnitary eF ζF
      (basisMatrixUnit eF eE i j (basisDiagonalUnitary eE ζE (eE q))) =
    (((ζF i : 𝕜) * (ζE j : 𝕜)) • basisMatrixUnit eF eE i j) (eE q)
  simp only [basisDiagonalUnitary_apply_basis, map_smul, map_smul,
    basisMatrixUnit_apply, LinearMap.smul_apply, basisMatrixUnit_apply,
    eE.inner_eq_ite]
  by_cases hjq : j = q
  · subst q
    simp only [ite_true, one_smul]
    rw [smul_smul, mul_comm]
  · simp [hjq]

/-- The complex unitary phase with angular frequency parameter `x`. -/
@[expose]
noncomputable def complexFourierPhase (x : ℝ) : unitary ℂ := by
  let z : ℂ := Circle.exp x
  have hz : ‖z‖ = 1 := Circle.norm_coe (Circle.exp x)
  refine ⟨z, ?_⟩
  rw [Unitary.mem_iff]
  constructor
  · rw [RCLike.star_def, RCLike.conj_mul, hz]
    norm_num
  · rw [RCLike.star_def, RCLike.mul_conj, hz]
    norm_num

/-- **Rotating a complex number by `θ` shifts its argument by `θ`.**
`‖a‖ * exp((arg a + θ) i) = a * exp(θ i)`.

Pure scalar arithmetic — split the exponential, re-associate, and close with
`Complex.norm_mul_exp_arg_mul_I` — but it appeared twice as a fifteen-line
`calc` buried inside two *operator* proofs, once here and once in
`DoubledPhase.lean`.  Nothing in either copy mentioned the operators or bases
around it, which is exactly why it read as incidental in both places. -/
theorem norm_mul_exp_arg_add_mul_I (a : ℂ) (theta : ℝ) :
    ((‖a‖ : ℝ) : ℂ) *
        Complex.exp (((Complex.arg a + theta : ℝ) : ℂ) * Complex.I) =
      a * Complex.exp ((theta : ℂ) * Complex.I) := by
  calc
    ((‖a‖ : ℝ) : ℂ) *
        Complex.exp (((Complex.arg a + theta : ℝ) : ℂ) * Complex.I) =
      ((‖a‖ : ℝ) : ℂ) *
        (Complex.exp (((Complex.arg a : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((theta : ℂ) * Complex.I)) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = (((‖a‖ : ℝ) : ℂ) *
          Complex.exp (((Complex.arg a : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((theta : ℂ) * Complex.I) := by ring
    _ = a * Complex.exp ((theta : ℂ) * Complex.I) := by
      rw [Complex.norm_mul_exp_arg_mul_I]

/-- **`cos t * cos t + sin t * sin t = 1`.**

Mathlib states the Pythagorean identity with squares
(`Real.sin_sq_add_cos_sq`), and every rotation-matrix computation in this
cluster needs it with products, so it was being re-derived by `nlinarith` at each
use — six times in this file and, in its cast form below, twice more in
`DoubledPhase.lean`. -/
theorem cos_mul_cos_add_sin_mul_sin (t : ℝ) :
    Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The same identity pushed into `𝕜`, which is the form the doubled-phase
rotation needs when it works through `RCLike` coefficients. -/
theorem cos_mul_cos_add_sin_mul_sin_cast (t : ℝ) :
    ((Real.cos t : ℝ) : 𝕜) * ((Real.cos t : ℝ) : 𝕜) +
      ((Real.sin t : ℝ) : 𝕜) * ((Real.sin t : ℝ) : 𝕜) = 1 := by
  have h := congrArg (fun x : ℝ => (x : 𝕜)) (cos_mul_cos_add_sin_mul_sin t)
  push_cast at h
  simpa using h

/-- The Fourier phase as a complex number is `exp(ix)`. -/
@[simp]
theorem complexFourierPhase_coe (x : ℝ) :
    (complexFourierPhase x : ℂ) =
      Complex.exp ((x : ℂ) * Complex.I) :=
  rfl

/-- Fourier phases multiply by adding arguments -- the group law of the circle, in the coerced
complex form the estimates use. -/

theorem complexFourierPhase_mul (x y : ℝ) :
    (complexFourierPhase x : ℂ) * (complexFourierPhase y : ℂ) =
      (complexFourierPhase (x + y) : ℂ) := by
  exact (congrArg ((↑) : Circle → ℂ) (Circle.exp_add x y)).symm

/-- The real-linear rotation by `theta` on two copies of a real vector space. -/
private noncomputable def realRotationLinearEquiv
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (theta : ℝ) : (G × G) ≃ₗ[ℝ] (G × G) where
  toFun x :=
    (Real.cos theta • x.1 - Real.sin theta • x.2,
      Real.sin theta • x.1 + Real.cos theta • x.2)
  invFun x :=
    (Real.cos theta • x.1 + Real.sin theta • x.2,
      -Real.sin theta • x.1 + Real.cos theta • x.2)
  left_inv x := by
    have htrig := cos_mul_cos_add_sin_mul_sin theta
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  right_inv x := by
    have htrig := cos_mul_cos_add_sin_mul_sin theta
    apply Prod.ext <;> dsimp
    · conv_rhs => rw [← one_smul ℝ x.1, ← htrig]
      module
    · conv_rhs => rw [← one_smul ℝ x.2, ← htrig]
      module
  map_add' x y := by
    apply Prod.ext <;> simp <;> module
  map_smul' r x := by
    apply Prod.ext <;> simp [smul_smul] <;> module

/-- A complex phase acting on a real Hilbert space after doubling is the
ordinary two-dimensional rotation, applied simultaneously in every direction. -/
noncomputable def doubledRealRotation
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (theta : ℝ) : WithLp 2 (G × G) ≃ₗᵢ[ℝ] WithLp 2 (G × G) where
  __ := (realRotationLinearEquiv theta).withLpCongr 2
  norm_map' x := by
    have htrig := cos_mul_cos_add_sin_mul_sin theta
    -- `doubledRealRotation` is a bundled `LinearIsometryEquiv`, so its application to a
    -- `WithLp` pair is not in normal form for the `norm_sq_eq_re_inner` rewrites below;
    -- no simp lemma unfolds a bundled equiv at a point.
    change ‖WithLp.toLp 2
      (Real.cos theta • x.fst - Real.sin theta • x.snd,
        Real.sin theta • x.fst + Real.cos theta • x.snd)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      norm_sq_eq_re_inner ( 𝕜 := ℝ), norm_sq_eq_re_inner ( 𝕜 := ℝ)]
    simp only [WithLp.prod_inner_apply]
    -- `WithLp.prod_inner_apply` normalises the left side only. The right side is still
    -- `⟪x, x⟫` on the L2 product, and stating the componentwise sum is what lets the
    -- `inner_*` lemmas below match; there is no lemma splitting `⟪x, x⟫_ℝ` on `WithLp`.
    change _ = ⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      RCLike.re_to_real]
    rw [real_inner_comm x.fst x.snd]
    linear_combination
      (⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ) * htrig

/-- The doubled real rotation, unfolded. -/
@[simp] theorem doubledRealRotation_apply
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (theta : ℝ) (x : WithLp 2 (G × G)) :
    doubledRealRotation theta x = WithLp.toLp 2
      (Real.cos theta • x.fst - Real.sin theta • x.snd,
        Real.sin theta • x.fst + Real.cos theta • x.snd) :=
  (rfl)

/-- **A diagonal map with real coefficients in an orthonormal basis of a `𝕜`-space.**

Stated over `RCLike 𝕜` rather than over `ℝ`, and not `private`, because the same
construction is needed downstream in `…ReciprocalMultiplier/DoubledPhase.lean`: at
`𝕜 = ℝ` the coercion is the identity, so a separate real version would be this one
under another name.  It lives here rather than there because this file is upstream
in the import order and a `private` definition is not visible across files. -/
noncomputable def basisDiagonalRealCoeffMap
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Fintype ι] 
    (e : OrthonormalBasis ι 𝕜 G) (c : ι → ℝ) : G →ₗ[𝕜] G :=
  e.toBasis.constr 𝕜 fun i => ((c i : ℝ) : 𝕜) • e i

/-- The diagonal map acts on a basis vector by its coefficient. -/
@[simp] theorem basisDiagonalRealCoeffMap_apply_basis
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 G) (c : ι → ℝ) (i : ι) :
    basisDiagonalRealCoeffMap e c (e i) = ((c i : ℝ) : 𝕜) • e i := by
  exact e.toBasis.constr_basis 𝕜 _ i

/-- The diagonal map scales each coordinate by its coefficient.  This is the form the
rotation arguments consume: they work coordinatewise in `e.repr` rather than through the
map itself. -/
@[simp] theorem basisDiagonalRealCoeffMap_repr
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 G) (c : ι → ℝ) (x : G) (i : ι) :
    e.repr (basisDiagonalRealCoeffMap e c x) i = ((c i : ℝ) : 𝕜) * e.repr x i := by
  classical
  rw [← e.sum_repr x]
  simp only [map_sum, map_smul, basisDiagonalRealCoeffMap_apply_basis, smul_smul]
  simp [Pi.single_apply]
  ring

/-- Rotation invariance of the pairwise squared norm over `RCLike` scalars. -/
private theorem rotation_norm_sq_pair {c s : ℝ}
    (h : c * c + s * s = 1) (p q : 𝕜) :
    ‖(c : 𝕜) * p - (s : 𝕜) * q‖ ^ 2 + ‖(s : 𝕜) * p + (c : 𝕜) * q‖ ^ 2 =
      ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  have hcast : (c : 𝕜) * (c : 𝕜) + (s : 𝕜) * (s : 𝕜) = 1 := by
    have hc := congrArg (fun x : ℝ => (x : 𝕜)) h
    push_cast at hc
    simpa using hc
  have key : ((‖(c : 𝕜) * p - (s : 𝕜) * q‖ ^ 2 +
        ‖(s : 𝕜) * p + (c : 𝕜) * q‖ ^ 2 : ℝ) : 𝕜) =
      ((‖p‖ ^ 2 + ‖q‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [← RCLike.mul_conj ((c : 𝕜) * p - (s : 𝕜) * q),
      ← RCLike.mul_conj ((s : 𝕜) * p + (c : 𝕜) * q),
      ← RCLike.mul_conj p, ← RCLike.mul_conj q]
    simp only [map_sub, map_add, map_mul, RCLike.conj_ofReal]
    linear_combination
      (p * (starRingEnd 𝕜) p + q * (starRingEnd 𝕜) q) * hcast
  exact_mod_cast key


section DoubledPhaseRotation

variable {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [Fintype ι] [DecidableEq ι]

/-! The diagonal map with real coefficients and its two lemmas used to be defined here as
well, over the same `𝕜` and with proofs line-for-line identical to the upstream copy.  They
now come from `…ReciprocalMultiplier/OrbitAction.lean`, which is upstream in the import
order; the real-only version that lived there is the same construction at `𝕜 = ℝ`. -/

/-- Coordinatewise phase rotations in an orthonormal basis of a `𝕜`-space,
before transporting the product norm to `WithLp 2`. -/
private noncomputable def basisDoubledPhaseRotationLinearEquiv
    (e : OrthonormalBasis ι 𝕜 G) (theta : ι → ℝ) :
    (G × G) ≃ₗ[𝕜] (G × G) := by
  let C := basisDiagonalRealCoeffMap e fun i => Real.cos (theta i)
  let S := basisDiagonalRealCoeffMap e fun i => Real.sin (theta i)
  refine
    { toFun := fun x => (C x.1 - S x.2, S x.1 + C x.2)
      invFun := fun x => (C x.1 + S x.2, -S x.1 + C x.2)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Prod.ext <;> simp [C, S] <;> module
  · intro r x
    apply Prod.ext <;> simp [C, S, smul_sub, smul_add]
  · intro x
    have htrig (i : ι) := cos_mul_cos_add_sin_mul_sin_cast (𝕜 := 𝕜) (theta i)
    apply Prod.ext
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, C, S, basisDiagonalRealCoeffMap_repr,
        PiLp.add_apply, PiLp.sub_apply]
      linear_combination (e.repr x.1 i) * htrig i
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealCoeffMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.2 i) * htrig i
  · intro x
    have htrig (i : ι) := cos_mul_cos_add_sin_mul_sin_cast (𝕜 := 𝕜) (theta i)
    apply Prod.ext
    · apply e.repr.injective
      ext i
      simp only [map_add, map_sub, map_neg, C, S, basisDiagonalRealCoeffMap_repr,
        PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply]
      linear_combination (e.repr x.1 i) * htrig i
    · apply e.repr.injective
      ext i
      simp only [map_add, map_neg, C, S, basisDiagonalRealCoeffMap_repr,
        PiLp.add_apply, PiLp.neg_apply]
      linear_combination (e.repr x.2 i) * htrig i

/-- Coordinatewise phase rotations on two orthogonal copies of a `𝕜`-Hilbert
space.  This is the generic doubled realization of the diagonal phase
unitary with angles `theta`. -/
noncomputable def basisDoubledPhaseRotation
    (e : OrthonormalBasis ι 𝕜 G) (theta : ι → ℝ) :
    WithLp 2 (G × G) ≃ₗᵢ[𝕜] WithLp 2 (G × G) where
  __ := (basisDoubledPhaseRotationLinearEquiv e theta).withLpCongr 2
  norm_map' x := by
    let C := basisDiagonalRealCoeffMap e fun i => Real.cos (theta i)
    let S := basisDiagonalRealCoeffMap e fun i => Real.sin (theta i)
    have hparseval (z : G) : ∑ i, ‖e.repr z i‖ ^ 2 = ‖z‖ ^ 2 := by
      simp_rw [e.repr_apply_apply]
      exact e.sum_sq_norm_inner_right z
    -- names the application so the norm bound applies to it directly.
    change ‖WithLp.toLp 2 (C x.fst - S x.snd, S x.fst + C x.snd)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    -- names the application so the norm bound applies to it directly.
    change ‖C x.fst - S x.snd‖ ^ 2 + ‖S x.fst + C x.snd‖ ^ 2 =
      ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
    rw [← hparseval (C x.fst - S x.snd), ← hparseval (S x.fst + C x.snd),
      ← hparseval x.fst, ← hparseval x.snd,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_sub, map_add, C, S, basisDiagonalRealCoeffMap_repr,
      PiLp.sub_apply, PiLp.add_apply]
    exact rotation_norm_sq_pair
      (by nlinarith [Real.sin_sq_add_cos_sq (theta i)])
      (e.repr x.fst i) (e.repr x.snd i)

/-- The doubled phase rotation on a basis vector. -/
@[simp] theorem basisDoubledPhaseRotation_apply
    (e : OrthonormalBasis ι 𝕜 G) (theta : ι → ℝ) (x : WithLp 2 (G × G)) :
    basisDoubledPhaseRotation e theta x = WithLp.toLp 2
      (basisDiagonalRealCoeffMap e (fun i => Real.cos (theta i)) x.fst -
          basisDiagonalRealCoeffMap e (fun i => Real.sin (theta i)) x.snd,
        basisDiagonalRealCoeffMap e (fun i => Real.sin (theta i)) x.fst +
          basisDiagonalRealCoeffMap e (fun i => Real.cos (theta i)) x.snd) := by
  rfl

end DoubledPhaseRotation

/-- Coordinatewise phase rotations on two real copies of a Hilbert space. -/
noncomputable def basisDoubledRealRotation
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) :
    WithLp 2 (G × G) ≃ₗᵢ[ℝ] WithLp 2 (G × G) :=
  basisDoubledPhaseRotation e theta

/-- The doubled real rotation on a basis vector. -/
@[simp] theorem basisDoubledRealRotation_apply
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ)
    (x : WithLp 2 (G × G)) :
    basisDoubledRealRotation e theta x = WithLp.toLp 2
      (basisDiagonalRealCoeffMap e (fun i => Real.cos (theta i)) x.fst -
          basisDiagonalRealCoeffMap e (fun i => Real.sin (theta i)) x.snd,
        basisDiagonalRealCoeffMap e (fun i => Real.sin (theta i)) x.fst +
          basisDiagonalRealCoeffMap e (fun i => Real.cos (theta i)) x.snd) := by
  rfl

/-- Its action on the first summand. -/
theorem basisDoubledRealRotation_apply_first
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) (i : ι) :
    basisDoubledRealRotation e theta (WithLp.toLp 2 (e i, 0)) =
      WithLp.toLp 2
        (Real.cos (theta i) • e i, Real.sin (theta i) • e i) := by
  -- `basisDoubledRealRotation` is defined by composing two `basisDiagonalRealCoeffMap`s; no
  -- simp lemma unfolds that composition at a basis vector, and the rewrites below are
  -- stated for the component maps.
  change WithLp.toLp 2
    (basisDiagonalRealCoeffMap e (fun q => Real.cos (theta q)) (e i) -
        basisDiagonalRealCoeffMap e (fun q => Real.sin (theta q)) 0,
      basisDiagonalRealCoeffMap e (fun q => Real.sin (theta q)) (e i) +
        basisDiagonalRealCoeffMap e (fun q => Real.cos (theta q)) 0) = _
  simp

/-- Its action on the second summand. -/
theorem basisDoubledRealRotation_apply_second
    {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ G) (theta : ι → ℝ) (i : ι) :
    basisDoubledRealRotation e theta (WithLp.toLp 2 (0, e i)) =
      WithLp.toLp 2
        (-Real.sin (theta i) • e i, Real.cos (theta i) • e i) := by
  -- As at the previous lemma: the composition defining `basisDoubledRealRotation` has to
  -- be exposed before the component-map rewrites can apply.
  change WithLp.toLp 2
    (basisDiagonalRealCoeffMap e (fun q => Real.cos (theta q)) 0 -
        basisDiagonalRealCoeffMap e (fun q => Real.sin (theta q)) (e i),
      basisDiagonalRealCoeffMap e (fun q => Real.sin (theta q)) 0 +
        basisDiagonalRealCoeffMap e (fun q => Real.cos (theta q)) (e i)) = _
  simp

section DoubledScalarAction

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- The `𝕜`-linear `2 × 2` block action of a complex scalar on a doubled
`𝕜`-linear map.  The real and imaginary parts act as real scalars embedded
in `𝕜`. -/
def doubledComplexScalarMapAction (z : ℂ) (T : E' →ₗ[𝕜] F') :
    WithLp 2 (E' × E') →ₗ[𝕜] WithLp 2 (F' × F') where
  toFun x := WithLp.toLp 2
    (((z.re : ℝ) : 𝕜) • T x.fst - ((z.im : ℝ) : 𝕜) • T x.snd,
      ((z.im : ℝ) : 𝕜) • T x.fst + ((z.re : ℝ) : 𝕜) • T x.snd)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp <;> module
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp [smul_smul] <;> module

/-- The doubled complex scalar map action, unfolded. -/
@[simp] theorem doubledComplexScalarMapAction_apply
    (z : ℂ) (T : E' →ₗ[𝕜] F') (x : WithLp 2 (E' × E')) :
    doubledComplexScalarMapAction z T x = WithLp.toLp 2
      (((z.re : ℝ) : 𝕜) • T x.fst - ((z.im : ℝ) : 𝕜) • T x.snd,
        ((z.im : ℝ) : 𝕜) • T x.fst + ((z.re : ℝ) : 𝕜) • T x.snd) :=
  (rfl)

/-- The doubled realization of multiplication by the phase `exp (θ i)` after
applying a `𝕜`-linear map. -/
noncomputable def doubledPhaseMapAction (theta : ℝ) (T : E' →ₗ[𝕜] F') :
    WithLp 2 (E' × E') →ₗ[𝕜] WithLp 2 (F' × F') :=
  doubledComplexScalarMapAction
    (Complex.exp ((theta : ℂ) * Complex.I)) T

/-- The doubled phase action, unfolded. -/
@[simp]
theorem doubledPhaseMapAction_apply (theta : ℝ) (T : E' →ₗ[𝕜] F')
    (x : WithLp 2 (E' × E')) :
    doubledPhaseMapAction theta T x = WithLp.toLp 2
      (((Real.cos theta : ℝ) : 𝕜) • T x.fst -
          ((Real.sin theta : ℝ) : 𝕜) • T x.snd,
        ((Real.sin theta : ℝ) : 𝕜) • T x.fst +
          ((Real.cos theta : ℝ) : 𝕜) • T x.snd) := by
  simp [doubledPhaseMapAction, doubledComplexScalarMapAction_apply,
    Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- Complex-scalar block action is additive in the scalar. -/
theorem doubledComplexScalarMapAction_add
    (z w : ℂ) (T : E' →ₗ[𝕜] F') :
    doubledComplexScalarMapAction (z + w) T =
      doubledComplexScalarMapAction z T +
        doubledComplexScalarMapAction w T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarMapAction_apply, Complex.add_re,
      Complex.add_im] <;>
    module

/-- Real scaling of the complex-scalar block action agrees with
multiplication of the complex scalar by that real number. -/
theorem doubledComplexScalarMapAction_real_smul
    (r : ℝ) (z : ℂ) (T : E' →ₗ[𝕜] F') :
    ((r : ℝ) : 𝕜) • doubledComplexScalarMapAction z T =
      doubledComplexScalarMapAction ((r : ℂ) * z) T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarMapAction_apply, smul_sub, smul_add, smul_smul]

/-- A real complex scalar acts as the corresponding `𝕜`-scalar on the
orthogonal block sum. -/
theorem doubledComplexScalarMapAction_ofReal
    (r : ℝ) (T : E' →ₗ[𝕜] F') :
    doubledComplexScalarMapAction (r : ℂ) T =
      ((r : ℝ) : 𝕜) •
        UnitarilyInvariantSeminorm.orthogonalBlockSum T T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarMapAction_apply,
      UnitarilyInvariantSeminorm.orthogonalBlockSum_apply]

/-- A finite sum of complex-scalar block actions is the action of the scalar
sum. -/
theorem sum_doubledComplexScalarMapAction
    {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (T : E' →ₗ[𝕜] F') :
    ∑ i, doubledComplexScalarMapAction (z i) T =
      doubledComplexScalarMapAction (∑ i, z i) T := by
  classical
  classical
  have h (s : Finset ι) :
      s.sum (fun i => doubledComplexScalarMapAction (z i) T) =
        doubledComplexScalarMapAction (s.sum z) T := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        ext x
        apply WithLp.ofLp_injective 2
        -- one closing `simp` rather than `simp only` + `exact`: the flexible-tactic
        -- linter objects to a lemma-carrying `simp` that leaves a goal behind.
        simp [doubledComplexScalarMapAction, Prod.ext_iff]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
          doubledComplexScalarMapAction_add]
  exact h Finset.univ

/-- Polar decomposition of one complex Fourier coefficient over `𝕜`: its
norm becomes a nonnegative real weight and its argument an additional
doubled phase angle. -/
theorem norm_smul_doubledPhaseMapAction_arg_add
    (a : ℂ) (theta : ℝ) (T : E' →ₗ[𝕜] F') :
    ((‖a‖ : ℝ) : 𝕜) • doubledPhaseMapAction (Complex.arg a + theta) T =
      doubledComplexScalarMapAction
        (a * Complex.exp ((theta : ℂ) * Complex.I)) T := by
  rw [doubledPhaseMapAction, doubledComplexScalarMapAction_real_smul]
  congr 1
  exact norm_mul_exp_arg_add_mul_I a theta

/-- A finite complex Fourier sum acts on doubled `𝕜`-linear maps as a finite
sum of nonnegatively weighted phase rotations. -/
theorem sum_norm_smul_doubledPhaseMapAction_arg_add
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (theta : ι → ℝ) (T : E' →ₗ[𝕜] F') :
    ∑ r, ((‖a r‖ : ℝ) : 𝕜) •
        doubledPhaseMapAction (Complex.arg (a r) + theta r) T =
      doubledComplexScalarMapAction
        (∑ r, a r * Complex.exp (((theta r : ℝ) : ℂ) * Complex.I)) T := by
  classical
  classical
  simp_rw [norm_smul_doubledPhaseMapAction_arg_add]
  exact sum_doubledComplexScalarMapAction _ T

end DoubledScalarAction

/-- The doubled-real map corresponding to multiplication by the complex phase
`exp (theta * I)` after applying a real rectangular map. -/
noncomputable def doubledPhaseAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR) :=
  doubledPhaseMapAction theta T

/-- The doubled phase action, unfolded. -/
@[simp] theorem doubledPhaseAction_apply
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) (x : WithLp 2 (ER × ER)) :
    doubledPhaseAction theta T x = WithLp.toLp 2
      (Real.cos theta • T x.fst - Real.sin theta • T x.snd,
        Real.sin theta • T x.fst + Real.cos theta • T x.snd) := by
  -- No longer `rfl`: `doubledPhaseAction` is now the general action at `𝕜 = ℝ`, whose
  -- scalar is `exp (θ * I)`, so `cos`/`sin` arrive through `Complex.exp_mul_I` rather
  -- than by unfolding a rotation matrix.
  simp [doubledPhaseAction]

/-- **The real doubled-phase action is the general one at `𝕜 = ℝ`.**

`doubledPhaseAction` (in `OrbitAction.lean`) and `doubledPhaseMapAction` are built by
different routes -- the first composes a real rotation with `orthogonalBlockSum T T`, the
second applies the complex scalar `exp (θ * I)` blockwise over a general `𝕜` -- and this
says the two constructions agree where both are defined.

Recorded because thirteen declarations exist in matched `…Action` / `…MapAction` forms and
three separate duplicated proofs across these files are downstream of that split; anyone
unifying them needs this fact first, and it turning out to be `rfl`-adjacent is the
evidence that the parallelism is presentational rather than load-bearing. -/
theorem doubledPhaseAction_eq_doubledPhaseMapAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    doubledPhaseAction theta T = doubledPhaseMapAction theta T := by
  ext x
  simp

/-- The real `2 × 2` block action of a complex scalar on a doubled real map. -/
noncomputable def doubledComplexScalarAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z : ℂ) (T : ER →ₗ[ℝ] FR) :
    WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR) :=
  doubledComplexScalarMapAction z T

/-- The doubled complex scalar action, unfolded. -/
@[simp] theorem doubledComplexScalarAction_apply
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z : ℂ) (T : ER →ₗ[ℝ] FR) (x : WithLp 2 (ER × ER)) :
    doubledComplexScalarAction z T x = WithLp.toLp 2
      (z.re • T x.fst - z.im • T x.snd,
        z.im • T x.fst + z.re • T x.snd) :=
  (rfl)

/-- A doubled phase action is complex scalar action by its unit phase. -/
theorem doubledPhaseAction_eq_complexScalarAction
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    doubledPhaseAction theta T =
      doubledComplexScalarAction (Complex.exp ((theta : ℂ) * Complex.I)) T := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [doubledPhaseAction_apply, doubledComplexScalarAction_apply,
    Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- Complex-scalar block action is additive in the scalar. -/
theorem doubledComplexScalarAction_add
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (z w : ℂ) (T : ER →ₗ[ℝ] FR) :
    doubledComplexScalarAction (z + w) T =
      doubledComplexScalarAction z T + doubledComplexScalarAction w T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [doubledComplexScalarAction_apply] <;> module

/-- Real scaling of complex-scalar block action agrees with multiplication of
the complex scalar by that real number. -/
theorem doubledComplexScalarAction_real_smul
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (r : ℝ) (z : ℂ) (T : ER →ₗ[ℝ] FR) :
    r • doubledComplexScalarAction z T =
      doubledComplexScalarAction ((r : ℂ) * z) T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarAction_apply, smul_sub, smul_add, smul_smul]

/-- A real complex scalar acts as the same real scalar on two orthogonal
copies of a real map. -/
theorem doubledComplexScalarAction_ofReal
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (r : ℝ) (T : ER →ₗ[ℝ] FR) :
    doubledComplexScalarAction (r : ℂ) T =
      r • UnitarilyInvariantSeminorm.orthogonalBlockSum T T := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [doubledComplexScalarAction_apply,
      UnitarilyInvariantSeminorm.orthogonalBlockSum_apply]

/-- A finite sum of complex-scalar block actions is the action of the scalar
sum. -/
theorem sum_doubledComplexScalarAction
    {ER FR ι : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [Fintype ι]
    (z : ι → ℂ) (T : ER →ₗ[ℝ] FR) :
    ∑ i, doubledComplexScalarAction (z i) T =
      doubledComplexScalarAction (∑ i, z i) T :=
  sum_doubledComplexScalarMapAction z T

/-- Polar decomposition of one complex Fourier coefficient: its norm becomes
a nonnegative real weight and its argument becomes an additional doubled-real
rotation angle. -/
theorem norm_smul_doubledPhaseAction_arg_add
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    (a : ℂ) (theta : ℝ) (T : ER →ₗ[ℝ] FR) :
    ‖a‖ • doubledPhaseAction (Complex.arg a + theta) T =
      doubledComplexScalarAction
        (a * Complex.exp ((theta : ℂ) * Complex.I)) T := by
  rw [doubledPhaseAction_eq_complexScalarAction,
    doubledComplexScalarAction_real_smul]
  congr 1
  exact norm_mul_exp_arg_add_mul_I a theta

/-- A finite complex Fourier sum acts on doubled real maps as a finite sum of
nonnegatively weighted real phase rotations. -/
theorem sum_norm_smul_doubledPhaseAction_arg_add
    {ER FR ι : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    [Fintype ι]
    (a : ι → ℂ) (theta : ι → ℝ) (T : ER →ₗ[ℝ] FR) :
    ∑ r, ‖a r‖ • doubledPhaseAction (Complex.arg (a r) + theta r) T =
      doubledComplexScalarAction
        (∑ r, a r * Complex.exp (((theta r : ℝ) : ℂ) * Complex.I)) T := by
  classical
  classical
  simp_rw [norm_smul_doubledPhaseAction_arg_add]
  exact sum_doubledComplexScalarAction _ T

/-- Coordinatewise doubled-real rotations realize addition of the left and
right phase angles on a doubled coordinate matrix unit. -/
theorem basisDoubledRealRotation_comp_basisMatrixUnit
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (thetaF : Fin (Module.finrank ℝ FR) → ℝ)
    (thetaE : Fin (Module.finrank ℝ ER) → ℝ)
    (i : Fin (Module.finrank ℝ FR))
    (j : Fin (Module.finrank ℝ ER)) :
    (basisDoubledRealRotation eF thetaF).toLinearMap ∘ₗ
        UnitarilyInvariantSeminorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) ∘ₗ
        (basisDoubledRealRotation eE thetaE).toLinearMap =
      doubledPhaseAction (thetaF i + thetaE j)
        (basisMatrixUnit eF eE i j) := by
  apply (eE.prod eE).toBasis.ext
  intro q
  rcases q with q | q
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply,
          Real.cos_add, Real.sin_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite, hq]
  · by_cases hq : j = q
    · subst q
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply,
          real_inner_smul_right, Real.cos_add, Real.sin_add] <;> module
    · apply WithLp.ofLp_injective 2
      apply Prod.ext <;>
        simp [basisDoubledRealRotation_apply,
          UnitarilyInvariantSeminorm.orthogonalBlockSum_apply,
          doubledPhaseAction_apply, basisMatrixUnit_apply, eE.inner_eq_ite,
          real_inner_smul_right, hq]

/-- The complex basis-diagonal orbit realizes the Fourier character at the
coordinate difference `α i - β j`.  This is the exact operator-valued atom
used after obtaining a scalar reciprocal Fourier representation. -/
theorem complexUnitaryOrbitAction_basisMatrixUnit_exp_sub
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC]
    
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℂ FC)) ℂ FC)
    (eE : OrthonormalBasis (Fin (Module.finrank ℂ EC)) ℂ EC)
    (α : Fin (Module.finrank ℂ FC) → ℝ)
    (β : Fin (Module.finrank ℂ EC) → ℝ)
    (t : ℝ) (i : Fin (Module.finrank ℂ FC))
    (j : Fin (Module.finrank ℂ EC)) :
    unitaryOrbitAction
        (basisDiagonalUnitary eF fun q => complexFourierPhase (t * α q))
        (basisDiagonalUnitary eE fun q => complexFourierPhase (-(t * β q)))
        (basisMatrixUnit eF eE i j) =
      Complex.exp ((((t * (α i - β j)) : ℝ) : ℂ) * Complex.I) •
        basisMatrixUnit eF eE i j := by
  rw [unitaryOrbitAction_basisMatrixUnit, complexFourierPhase_mul,
    complexFourierPhase_coe]
  congr 1
  congr 1
  ring_nf

end TauCeti
