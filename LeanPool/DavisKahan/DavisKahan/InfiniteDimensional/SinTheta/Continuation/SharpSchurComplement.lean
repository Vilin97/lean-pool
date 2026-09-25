/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpDiagonalResolvents
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Schur-complement inversion for the sharp continuation argument

This leaf supplies the analytic core missing from the sharp continuation
pipeline. It develops a rectangular `2 × 2` continuous-linear block map and
factors a shifted self-adjoint block operator through its second Schur
complement.

Rectangular block entries always use continuous-linear composition `∘L`.
Multiplication notation is reserved for endomorphisms. This distinction keeps
all intermediate expressions well typed when the two coordinate Hilbert spaces
are different.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

universe u v

section RectangularBlockAlgebra

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A general bounded rectangular `2 × 2` block map on the Hilbert direct sum. -/
noncomputable def rectangularBlockMap
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ E0 E1).symm :
      (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) ∘L
    ((a ∘L WithLp.fstL 2 ℂ E0 E1 + b ∘L WithLp.sndL 2 ℂ E0 E1).prod
      (c ∘L WithLp.fstL 2 ℂ E0 E1 + d ∘L WithLp.sndL 2 ℂ E0 E1))

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The block operator `!![a, b; c, d]` acts on a pair by the usual matrix product. -/
@[simp]
theorem rectangularBlockMap_apply
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1)
    (x : WithLp 2 (E0 × E1)) :
    rectangularBlockMap a b c d x =
      WithLp.toLp 2
        (a (WithLp.fst x) + b (WithLp.snd x),
          c (WithLp.fst x) + d (WithLp.snd x)) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Composition of rectangular block maps is matrix multiplication, with
rectangular entries composed using `∘L`. -/
theorem rectangularBlockMap_mul
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1)
    (a' : E0 →L[ℂ] E0) (b' : E1 →L[ℂ] E0)
    (c' : E0 →L[ℂ] E1) (d' : E1 →L[ℂ] E1) :
    rectangularBlockMap a b c d * rectangularBlockMap a' b' c' d' =
      rectangularBlockMap
        (a ∘L a' + b ∘L c') (a ∘L b' + b ∘L d')
        (c ∘L a' + d ∘L c') (c ∘L b' + d ∘L d') := by
  ext x
  simp only [mul_apply_eq_comp, rectangularBlockMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, add_apply,
    ContinuousLinearMap.comp_apply, map_add]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Addition of rectangular block maps is entrywise. -/
theorem rectangularBlockMap_add
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1)
    (a' : E0 →L[ℂ] E0) (b' : E1 →L[ℂ] E0)
    (c' : E0 →L[ℂ] E1) (d' : E1 →L[ℂ] E1) :
    rectangularBlockMap a b c d + rectangularBlockMap a' b' c' d' =
      rectangularBlockMap (a + a') (b + b') (c + c') (d + d') := by
  ext x
  simp only [add_apply, rectangularBlockMap_apply,
    ← WithLp.toLp_add, Prod.mk_add_mk]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Scalar multiplication of rectangular block maps is entrywise. -/
theorem rectangularBlockMap_smul
    (z : ℂ)
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1) :
    z • rectangularBlockMap a b c d =
      rectangularBlockMap (z • a) (z • b) (z • c) (z • d) := by
  ext x
  simp only [smul_apply, rectangularBlockMap_apply,
    ← WithLp.toLp_smul, Prod.smul_mk, smul_add]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Subtraction of rectangular block maps is entrywise. -/
theorem rectangularBlockMap_sub
    (a : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (d : E1 →L[ℂ] E1)
    (a' : E0 →L[ℂ] E0) (b' : E1 →L[ℂ] E0)
    (c' : E0 →L[ℂ] E1) (d' : E1 →L[ℂ] E1) :
    rectangularBlockMap a b c d - rectangularBlockMap a' b' c' d' =
      rectangularBlockMap (a - a') (b - b') (c - c') (d - d') := by
  ext x
  simp only [sub_apply, rectangularBlockMap_apply,
    ← WithLp.toLp_sub, Prod.mk_sub_mk]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The identity block operator is the identity. -/
@[simp]
theorem rectangularBlockMap_one :
    rectangularBlockMap
      (1 : E0 →L[ℂ] E0) 0 0 (1 : E1 →L[ℂ] E1) = 1 := by
  ext x
  simp only [rectangularBlockMap_apply, one_apply_eq_self,
    zero_apply, add_zero, zero_add, WithLp.fst,
    WithLp.snd, Prod.mk.eta, WithLp.toLp_ofLp]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The shifted bounded block operator is the rectangular block map of the two
shifted diagonal blocks and the unchanged cross blocks. -/
theorem blockOperator_sub_scalar_eq_rectangularBlockMap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1)) (z : ℂ) :
    blockOperator H - z • (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) =
      rectangularBlockMap
        (H.A0 - z • 1) H.B01 H.B10 (H.A1 - z • 1) := by
  change
    rectangularBlockMap H.A0 H.B01 H.B10 H.A1 -
        z • (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) = _
  have hone :
      (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) =
        rectangularBlockMap (1 : E0 →L[ℂ] E0) 0 0 (1 : E1 →L[ℂ] E1) :=
    rectangularBlockMap_one.symm
  rw [hone, rectangularBlockMap_smul, rectangularBlockMap_sub]
  simp only [smul_zero, sub_zero]

/-- The lower unitriangular Schur factor and its explicit inverse. -/
noncomputable def schurLower
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  rectangularBlockMap 1 0 (c ∘L r0) 1

/-- The explicit inverse of the lower unitriangular Schur factor `schurLower`. -/
noncomputable def schurLowerInv
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  rectangularBlockMap 1 0 (-(c ∘L r0)) 1

/-- The upper unitriangular Schur factor and its explicit inverse. -/
noncomputable def schurUpper
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  rectangularBlockMap 1 (r0 ∘L b) 0 1

/-- The explicit inverse of the upper unitriangular Schur factor `schurUpper`. -/
noncomputable def schurUpperInv
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  rectangularBlockMap 1 (-(r0 ∘L b)) 0 1

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The lower Schur factor adds `c (r0 ·)` of the first coordinate into the second. -/
@[simp]
theorem schurLower_apply
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0)
    (x : WithLp 2 (E0 × E1)) :
    schurLower c r0 x =
      WithLp.toLp 2
        (WithLp.fst x, c (r0 (WithLp.fst x)) + WithLp.snd x) := by
  simp only [schurLower, rectangularBlockMap_apply,
    one_apply_eq_self, zero_apply,
    ContinuousLinearMap.comp_apply, add_zero]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The inverse lower Schur factor subtracts `c (r0 ·)` of the first coordinate from the second. -/
@[simp]
theorem schurLowerInv_apply
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0)
    (x : WithLp 2 (E0 × E1)) :
    schurLowerInv c r0 x =
      WithLp.toLp 2
        (WithLp.fst x, -(c (r0 (WithLp.fst x))) + WithLp.snd x) := by
  simp only [schurLowerInv, rectangularBlockMap_apply,
    one_apply_eq_self, zero_apply,
    neg_apply, ContinuousLinearMap.comp_apply,
    add_zero]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The upper Schur factor adds `r0 (b ·)` of the second coordinate into the first. -/
@[simp]
theorem schurUpper_apply
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (x : WithLp 2 (E0 × E1)) :
    schurUpper r0 b x =
      WithLp.toLp 2
        (WithLp.fst x + r0 (b (WithLp.snd x)), WithLp.snd x) := by
  simp only [schurUpper, rectangularBlockMap_apply,
    one_apply_eq_self, zero_apply,
    ContinuousLinearMap.comp_apply, zero_add]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The inverse upper Schur factor subtracts `r0 (b ·)` of the second coordinate from the first. -/
@[simp]
theorem schurUpperInv_apply
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (x : WithLp 2 (E0 × E1)) :
    schurUpperInv r0 b x =
      WithLp.toLp 2
        (WithLp.fst x - r0 (b (WithLp.snd x)), WithLp.snd x) := by
  simp only [schurUpperInv, rectangularBlockMap_apply,
    one_apply_eq_self, zero_apply,
    neg_apply, ContinuousLinearMap.comp_apply,
    zero_add, sub_eq_add_neg]

omit [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [CompleteSpace E0] [NormedAddCommGroup E1] [InnerProductSpace ℂ E1] [CompleteSpace E1] in
/-- Reconstruct a direct-sum vector from its two coordinates. -/
theorem rectangularDirectSum_eta (x : WithLp 2 (E0 × E1)) :
    WithLp.toLp 2 (WithLp.fst x, WithLp.snd x) = x := by
  simp only [WithLp.fst, WithLp.snd, Prod.mk.eta, WithLp.toLp_ofLp]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- `schurLowerInv` is a left inverse of `schurLower`. -/
@[simp]
theorem schurLowerInv_mul_schurLower
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0) :
    schurLowerInv c r0 * schurLower c r0 = 1 := by
  ext x
  calc
    (schurLowerInv c r0 * schurLower c r0) x =
        WithLp.toLp 2
          (WithLp.fst x,
            -(c (r0 (WithLp.fst x))) +
              (c (r0 (WithLp.fst x)) + WithLp.snd x)) := by
      simp only [mul_apply_eq_comp, schurLowerInv_apply,
        schurLower_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    _ = WithLp.toLp 2 (WithLp.fst x, WithLp.snd x) := by
      refine congrArg (WithLp.toLp 2) ?_
      rw [Prod.mk.injEq]
      exact ⟨rfl, by abel⟩
    _ = (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) x := by
      simpa only [one_apply_eq_self] using rectangularDirectSum_eta x

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- `schurLowerInv` is a right inverse of `schurLower`. -/
@[simp]
theorem schurLower_mul_schurLowerInv
    (c : E0 →L[ℂ] E1) (r0 : E0 →L[ℂ] E0) :
    schurLower c r0 * schurLowerInv c r0 = 1 := by
  ext x
  calc
    (schurLower c r0 * schurLowerInv c r0) x =
        WithLp.toLp 2
          (WithLp.fst x,
            c (r0 (WithLp.fst x)) +
              (-(c (r0 (WithLp.fst x))) + WithLp.snd x)) := by
      simp only [mul_apply_eq_comp, schurLower_apply,
        schurLowerInv_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    _ = WithLp.toLp 2 (WithLp.fst x, WithLp.snd x) := by
      refine congrArg (WithLp.toLp 2) ?_
      rw [Prod.mk.injEq]
      exact ⟨rfl, by abel⟩
    _ = (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) x := by
      simpa only [one_apply_eq_self] using rectangularDirectSum_eta x

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- `schurUpperInv` is a left inverse of `schurUpper`. -/
@[simp]
theorem schurUpperInv_mul_schurUpper
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0) :
    schurUpperInv r0 b * schurUpper r0 b = 1 := by
  ext x
  calc
    (schurUpperInv r0 b * schurUpper r0 b) x =
        WithLp.toLp 2
          ((WithLp.fst x + r0 (b (WithLp.snd x))) -
            r0 (b (WithLp.snd x)), WithLp.snd x) := by
      simp only [mul_apply_eq_comp, schurUpperInv_apply,
        schurUpper_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    _ = WithLp.toLp 2 (WithLp.fst x, WithLp.snd x) := by
      refine congrArg (WithLp.toLp 2) ?_
      rw [Prod.mk.injEq]
      exact ⟨by abel, rfl⟩
    _ = (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) x := by
      simpa only [one_apply_eq_self] using rectangularDirectSum_eta x

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- `schurUpperInv` is a right inverse of `schurUpper`. -/
@[simp]
theorem schurUpper_mul_schurUpperInv
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0) :
    schurUpper r0 b * schurUpperInv r0 b = 1 := by
  ext x
  calc
    (schurUpper r0 b * schurUpperInv r0 b) x =
        WithLp.toLp 2
          ((WithLp.fst x - r0 (b (WithLp.snd x))) +
            r0 (b (WithLp.snd x)), WithLp.snd x) := by
      simp only [mul_apply_eq_comp, schurUpper_apply,
        schurUpperInv_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    _ = WithLp.toLp 2 (WithLp.fst x, WithLp.snd x) := by
      refine congrArg (WithLp.toLp 2) ?_
      rw [Prod.mk.injEq]
      exact ⟨by abel, rfl⟩
    _ = (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1)) x := by
      simpa only [one_apply_eq_self] using rectangularDirectSum_eta x

/-- Evaluate an endomorphism inverse law at a vector. -/
theorem apply_apply_eq_of_mul_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : E →L[ℂ] E) (h : S * T = 1) (x : E) :
    S (T x) = x := by
  have hx := congrArg (fun R : E →L[ℂ] E => R x) h
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using hx

/-- Second Schur complement of a shifted rectangular block matrix. -/
def secondSchurComplement
    (l1 : E1 →L[ℂ] E1) (c : E0 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0) : E1 →L[ℂ] E1 :=
  l1 - c ∘L r0 ∘L b

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Exact lower-diagonal-upper factorization of a rectangular block map. -/
theorem rectangularBlockMap_eq_schur_factorization
    (l0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (l1 : E1 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0)
    (hr0l0 : r0 * l0 = 1) (hl0r0 : l0 * r0 = 1) :
    rectangularBlockMap l0 b c l1 =
      schurLower c r0 *
        rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
          schurUpper r0 b := by
  ext x
  have hr0l0x : r0 (l0 (WithLp.fst x)) = WithLp.fst x :=
    apply_apply_eq_of_mul_eq_one r0 l0 hr0l0 (WithLp.fst x)
  have hl0r0bx : l0 (r0 (b (WithLp.snd x))) = b (WithLp.snd x) :=
    apply_apply_eq_of_mul_eq_one l0 r0 hl0r0 (b (WithLp.snd x))
  simp only [mul_apply_eq_comp, schurLower_apply, schurUpper_apply,
    rectangularBlockMap_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    secondSchurComplement, sub_apply,
    ContinuousLinearMap.comp_apply, zero_apply,
    add_zero, zero_add, map_add, hr0l0x, hl0r0bx]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.mk.injEq]
  exact ⟨by abel, by abel⟩

/-- Explicit inverse of the block matrix from inverses of the first diagonal
shift and the second Schur complement. -/
noncomputable def schurBlockInverse
    (b : E1 →L[ℂ] E0) (c : E0 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0) (q : E1 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  schurUpperInv r0 b * rectangularBlockMap r0 0 0 q * schurLowerInv c r0

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A block-diagonal map and its coordinatewise inverse multiply to one. -/
theorem rectangularBlockMap_diagonal_mul
    (r0 l0 : E0 →L[ℂ] E0) (q s : E1 →L[ℂ] E1)
    (h0 : r0 * l0 = 1) (h1 : q * s = 1) :
    rectangularBlockMap r0 0 0 q * rectangularBlockMap l0 0 0 s = 1 := by
  rw [rectangularBlockMap_mul]
  ext x
  have h0x : r0 (l0 (WithLp.fst x)) = WithLp.fst x :=
    apply_apply_eq_of_mul_eq_one r0 l0 h0 (WithLp.fst x)
  have h1x : q (s (WithLp.snd x)) = WithLp.snd x :=
    apply_apply_eq_of_mul_eq_one q s h1 (WithLp.snd x)
  simpa only [rectangularBlockMap_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    add_zero, zero_add, h0x, h1x, one_apply_eq_self] using
      rectangularDirectSum_eta x

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The Schur inverse is a left inverse of the full block map. -/
theorem schurBlockInverse_mul_rectangularBlockMap
    (l0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (l1 : E1 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0) (q : E1 →L[ℂ] E1)
    (hr0l0 : r0 * l0 = 1) (hl0r0 : l0 * r0 = 1)
    (hqS : q * secondSchurComplement l1 c r0 b = 1)
    (_hSq : secondSchurComplement l1 c r0 b * q = 1) :
    schurBlockInverse b c r0 q * rectangularBlockMap l0 b c l1 = 1 := by
  rw [rectangularBlockMap_eq_schur_factorization l0 b c l1 r0 hr0l0 hl0r0]
  unfold schurBlockInverse
  have hdiag :
      rectangularBlockMap r0 0 0 q *
          rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) = 1 :=
    rectangularBlockMap_diagonal_mul r0 l0 q
      (secondSchurComplement l1 c r0 b) hr0l0 hqS
  calc
    (schurUpperInv r0 b * rectangularBlockMap r0 0 0 q * schurLowerInv c r0) *
          (schurLower c r0 *
            rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
              schurUpper r0 b) =
        schurUpperInv r0 b *
          (rectangularBlockMap r0 0 0 q *
            (schurLowerInv c r0 * schurLower c r0) *
              rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b)) *
          schurUpper r0 b := by noncomm_ring
    _ = schurUpperInv r0 b *
          (rectangularBlockMap r0 0 0 q *
            rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b)) *
          schurUpper r0 b := by
      rw [schurLowerInv_mul_schurLower]
      simp only [mul_one]
    _ = schurUpperInv r0 b * 1 * schurUpper r0 b := by rw [hdiag]
    _ = 1 := by simp only [mul_one, schurUpperInv_mul_schurUpper]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The Schur inverse is a right inverse of the full block map. -/
theorem rectangularBlockMap_mul_schurBlockInverse
    (l0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (c : E0 →L[ℂ] E1) (l1 : E1 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0) (q : E1 →L[ℂ] E1)
    (hr0l0 : r0 * l0 = 1) (hl0r0 : l0 * r0 = 1)
    (_hqS : q * secondSchurComplement l1 c r0 b = 1)
    (hSq : secondSchurComplement l1 c r0 b * q = 1) :
    rectangularBlockMap l0 b c l1 * schurBlockInverse b c r0 q = 1 := by
  rw [rectangularBlockMap_eq_schur_factorization l0 b c l1 r0 hr0l0 hl0r0]
  unfold schurBlockInverse
  have hdiag :
      rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
          rectangularBlockMap r0 0 0 q = 1 :=
    rectangularBlockMap_diagonal_mul l0 r0
      (secondSchurComplement l1 c r0 b) q hl0r0 hSq
  calc
    (schurLower c r0 *
          rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
            schurUpper r0 b) *
        (schurUpperInv r0 b * rectangularBlockMap r0 0 0 q *
          schurLowerInv c r0) =
      schurLower c r0 *
        (rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
          (schurUpper r0 b * schurUpperInv r0 b) *
            rectangularBlockMap r0 0 0 q) *
        schurLowerInv c r0 := by noncomm_ring
    _ = schurLower c r0 *
        (rectangularBlockMap l0 0 0 (secondSchurComplement l1 c r0 b) *
          rectangularBlockMap r0 0 0 q) *
        schurLowerInv c r0 := by
      rw [schurUpper_mul_schurUpperInv]
      simp only [mul_one]
    _ = schurLower c r0 * 1 * schurLowerInv c r0 := by rw [hdiag]
    _ = 1 := by simp only [mul_one, schurLower_mul_schurLowerInv]

end RectangularBlockAlgebra

section SchurResolvent

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] in
/-- Neumann inversion of the second Schur complement. -/
theorem secondSchurComplement_has_inverse_of_norm_lt_one
    (l1 : E1 →L[ℂ] E1) (c : E0 →L[ℂ] E1)
    (r0 : E0 →L[ℂ] E0) (b : E1 →L[ℂ] E0)
    (r1 : E1 →L[ℂ] E1)
    (hr1l1 : r1 * l1 = 1) (hl1r1 : l1 * r1 = 1)
    (hsmall : ‖r1 ∘L c ∘L r0 ∘L b‖ < 1) :
    ∃ q : E1 →L[ℂ] E1,
      q * secondSchurComplement l1 c r0 b = 1 ∧
      secondSchurComplement l1 c r0 b * q = 1 := by
  let n : E1 →L[ℂ] E1 := r1 ∘L c ∘L r0 ∘L b
  have hsmall' : ‖n‖ < 1 := by simpa only [n] using hsmall
  -- Mathlib's `Units.oneSub` is the Neumann series: `1 - n` is a unit when `‖n‖ < 1`.
  let u : (E1 →L[ℂ] E1)ˣ := Units.oneSub n hsmall'
  have hval : (↑u : E1 →L[ℂ] E1) = 1 - n := Units.val_oneSub n hsmall'
  let q : E1 →L[ℂ] E1 := (↑u⁻¹ : E1 →L[ℂ] E1) * r1
  have hright : (↑u⁻¹ : E1 →L[ℂ] E1) * (1 - n) = 1 := by
    rw [← hval]; exact u.inv_mul
  have hleft : (1 - n) * (↑u⁻¹ : E1 →L[ℂ] E1) = 1 := by
    rw [← hval]; exact u.mul_inv
  have hr1l1x (x : E1) : r1 (l1 x) = x :=
    apply_apply_eq_of_mul_eq_one r1 l1 hr1l1 x
  have hl1r1x (x : E1) : l1 (r1 x) = x :=
    apply_apply_eq_of_mul_eq_one l1 r1 hl1r1 x
  have hr1S : r1 * secondSchurComplement l1 c r0 b = 1 - n := by
    ext x
    simp only [mul_apply_eq_comp, secondSchurComplement,
      sub_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, map_sub, n, hr1l1x]
  have hSfactor : secondSchurComplement l1 c r0 b = l1 * (1 - n) := by
    ext x
    simp only [secondSchurComplement, sub_apply,
      ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
      one_apply_eq_self, n, map_sub, hl1r1x]
  refine ⟨q, ?_, ?_⟩
  · unfold q
    calc
      ((↑u⁻¹ : E1 →L[ℂ] E1) * r1) *
          secondSchurComplement l1 c r0 b =
        (↑u⁻¹ : E1 →L[ℂ] E1) *
          (r1 * secondSchurComplement l1 c r0 b) := by noncomm_ring
      _ = (↑u⁻¹ : E1 →L[ℂ] E1) * (1 - n) := by rw [hr1S]
      _ = 1 := hright
  · unfold q
    rw [hSfactor]
    calc
      (l1 * (1 - n)) *
          ((↑u⁻¹ : E1 →L[ℂ] E1) * r1) =
        l1 * ((1 - n) * (↑u⁻¹ : E1 →L[ℂ] E1)) * r1 := by
          noncomm_ring
      _ = l1 * 1 * r1 := by rw [hleft]
      _ = 1 := by simpa only [mul_one] using hl1r1

omit [CompleteSpace E0] in
/-- Sharp Schur-product criterion for full block resolvent-set membership. -/
theorem blockOperator_inResolventSet_of_schur_norm_lt_one
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (z : ℂ)
    (h0 : InResolventSet H.A0 z)
    (h1 : InResolventSet H.A1 z)
    (hsmall :
      ‖resolventOperator H.A1 z ∘L H.B10 ∘L
        resolventOperator H.A0 z ∘L H.B01‖ < 1) :
    InResolventSet (blockOperator H) z := by
  let l0 := H.A0 - z • (1 : E0 →L[ℂ] E0)
  let l1 := H.A1 - z • (1 : E1 →L[ℂ] E1)
  let r0 := resolventOperator H.A0 z
  let r1 := resolventOperator H.A1 z
  have hr0l0 : r0 * l0 = 1 := by
    simpa only [r0, l0] using resolventOperator_mul_cancel H.A0 h0
  have hl0r0 : l0 * r0 = 1 := by
    simpa only [r0, l0] using mul_resolventOperator_cancel H.A0 h0
  have hr1l1 : r1 * l1 = 1 := by
    simpa only [r1, l1] using resolventOperator_mul_cancel H.A1 h1
  have hl1r1 : l1 * r1 = 1 := by
    simpa only [r1, l1] using mul_resolventOperator_cancel H.A1 h1
  obtain ⟨q, hqS, hSq⟩ :=
    secondSchurComplement_has_inverse_of_norm_lt_one
      l1 H.B10 r0 H.B01 r1 hr1l1 hl1r1
        (by simpa only [r0, r1] using hsmall)
  refine ⟨schurBlockInverse H.B01 H.B10 r0 q, ?_, ?_⟩
  · change
      schurBlockInverse H.B01 H.B10 r0 q *
          (blockOperator H - z •
            (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1))) = 1
    rw [blockOperator_sub_scalar_eq_rectangularBlockMap]
    exact schurBlockInverse_mul_rectangularBlockMap
      l0 H.B01 H.B10 l1 r0 q hr0l0 hl0r0 hqS hSq
  · change
      (blockOperator H - z •
          (1 : WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1))) *
        schurBlockInverse H.B01 H.B10 r0 q = 1
    rw [blockOperator_sub_scalar_eq_rectangularBlockMap]
    exact rectangularBlockMap_mul_schurBlockInverse
      l0 H.B01 H.B10 l1 r0 q hr0l0 hl0r0 hqS hSq

end SchurResolvent

end DavisKahanExt
end TauCeti
