/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.EllipticSet
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Carrier endomorphisms

This file equips the regular-fields carrier `RegCoeffField d` with the structural
self-maps used by the law layer of the homogenization development: spatial
translation, signed-permutation rotation (isotropy), triadic rescaling and
dilation, restriction to a measurable set, and elliptic truncation.  Each map is
shown to preserve the carrier (entrywise Borel measurability and local
integrability are stable) and, where possible, to be genuinely measurable for the
canonical carrier σ-algebra `pointwiseSigmaR ⊔ entryTestSigmaR`.

The measurability proofs go through the P1 probe-transport criterion
`measurable_of_entryTestR_transport`: each entry generator on the transformed
field equals a scalar multiple of a relabelled entry generator on the input, the
scalar being the Jacobian factor of the underlying change of variables.

`translateReg`, `rotateReg`, `rescaleReg`, `dilateReg` and `restrictReg` are
genuinely measurable at the join.  `ellipticTruncateReg` is a genuine carrier
element and is measurable for the *pointwise* lane; its entry-test lane is a
nonlinear integral functional that is not a transported generator (see the note
at that declaration).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal Classical

noncomputable section

variable {d : ℕ}

/-! ## Local-integrability transport under a homeomorphism -/

/-- **Local integrability is stable under precomposition with a homeomorphism
whose pushforward of Lebesgue measure is a finite nonzero rescaling of Lebesgue
measure.**  This covers translation and rotation (`c = 1`) and triadic
rescaling/dilation (`c` the Jacobian factor). -/
theorem locallyIntegrable_comp_homeomorph_of_map_smul {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (e : Vec d ≃ₜ Vec d) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞) (hmap : Measure.map e volume = c • volume) :
    LocallyIntegrable (fun x => f (e x)) volume := by
  have hcv : LocallyIntegrable f (c • (volume : Measure (Vec d))) := by
    intro x
    obtain ⟨U, hU, hint⟩ := hf x
    refine ⟨U, hU, ?_⟩
    rw [IntegrableOn, Measure.restrict_smul]
    exact (integrable_smul_measure hc0 hctop).2 hint
  have hmapInt : LocallyIntegrable f (Measure.map e volume) := by rw [hmap]; exact hcv
  exact (locallyIntegrable_map_homeomorph e).mp hmapInt

/-- Local-integrability transport under a measure-preserving homeomorphism. -/
theorem locallyIntegrable_comp_homeomorph_of_measurePreserving {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (e : Vec d ≃ₜ Vec d)
    (hmp : MeasurePreserving e volume volume) :
    LocallyIntegrable (fun x => f (e x)) volume :=
  locallyIntegrable_comp_homeomorph_of_map_smul hf e (c := 1) one_ne_zero ENNReal.one_ne_top
    (by rw [hmp.map_eq, one_smul])

/-! ## Matrix-action infrastructure (re-derived, public) -/

/-- Continuity of the linear action `x ↦ R x` (local copy of the raw-layer
private lemma). -/
theorem continuous_matVecMul (R : Mat d) : Continuous (fun x : Vec d => matVecMul R x) := by
  change Continuous fun x : Fin d → ℝ => fun i => ∑ j, R i j * x j
  exact continuous_pi fun i =>
    continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)

private theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- A signed permutation acts as a homeomorphism of the base space. -/
def matVecMulHomeomorph (R : Mat d) (hR : IsSignedPermutationMatrix R) : Vec d ≃ₜ Vec d where
  toEquiv :=
    { toFun := matVecMul R
      invFun := matVecMul (matTranspose R)
      left_inv := fun x => by rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one']
      right_inv := fun x => by rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one'] }
  continuous_toFun := continuous_matVecMul R
  continuous_invFun := continuous_matVecMul (matTranspose R)

@[simp] theorem matVecMulHomeomorph_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (x : Vec d) : matVecMulHomeomorph R hR x = matVecMul R x := rfl

/-- The signed-permutation action preserves Lebesgue measure (`|det R| = 1`). -/
theorem measurePreserving_matVecMul (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    MeasurePreserving (fun x : Vec d => matVecMul R x) volume volume := by
  refine ⟨(continuous_matVecMul R).measurable, ?_⟩
  have hscale : ENNReal.ofReal |(Matrix.det R)⁻¹| = 1 := by
    rw [abs_inv, hR.abs_det_eq_one]; norm_num
  change Measure.map (Matrix.toLin' R) volume = volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hR.det_ne_zero, hscale, one_smul]

/-! ## Translation -/

/-- Precomposition with the spatial translation `x ↦ x + z` is a carrier
endomorphism (mirrors `translateCoeffField` on the raw carrier). -/
def translateReg (z : Vec d) (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => a (x + z)
  entry_measurable := fun i j =>
    (a.entry_measurable i j).comp ((measurable_id.add measurable_const))
  entry_locInt := fun i j =>
    locallyIntegrable_comp_homeomorph_of_measurePreserving (a.entry_locInt i j)
      (Homeomorph.addRight z) (by
        simpa [Homeomorph.coe_addRight] using
          measurePreserving_add_right (volume : Measure (Vec d)) z)

@[simp] theorem translateReg_apply (z : Vec d) (a : RegCoeffField d) (x : Vec d) :
    translateReg z a x = a (x + z) := rfl

/-- Generator transport for translation: the entry test of a translated field is
the entry test against the back-translated probe (Jacobian factor `1`). -/
theorem entryTestR_translateReg (i j : Fin d) (φ : Vec d → ℝ) (z : Vec d)
    (a : RegCoeffField d) :
    entryTestR i j φ (translateReg z a) = entryTestR i j (fun y => φ (y - z)) a := by
  unfold entryTestR
  have hcomp := (measurePreserving_add_right (volume : Measure (Vec d)) z).integral_comp
    (Homeomorph.addRight z).measurableEmbedding (fun y => a y i j * φ (y - z))
  rw [← hcomp]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [translateReg_apply, add_sub_cancel_right]

/-- **Translation is genuinely measurable at the join.** -/
theorem measurable_translateReg (z : Vec d) : Measurable (translateReg (d := d) z) := by
  refine measurable_of_entryTestR_transport ?_ ?_
  · intro y i j
    have hfun : (fun a : RegCoeffField d => translateReg z a y i j)
        = fun a => a (y + z) i j := rfl
    rw [hfun]; exact measurable_apply_entry (y + z) i j
  · intro i j φ hφ
    exact ⟨1, i, j, (fun y => φ (y - z)),
      hφ.comp_homeomorph (Homeomorph.subRight z), fun a => by
        rw [entryTestR_translateReg]; ring⟩

/-! ## Signed-permutation rotation (isotropy) -/

/-- The conjugation-by-`R` collapse for a signed permutation `R` with underlying
permutation `σ` and signs `s`: `(Rᵀ M R)_{ij} = s_i s_j M_{σ i, σ j}`.  This is
the algebraic heart of the isotropy endomorphism. -/
theorem matTranspose_mul_mul_apply {R : Mat d} {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (M : Mat d) (i j : Fin d) :
    (matTranspose R * M * R) i j = s i * s j * M (σ i) (σ j) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · rw [hRdef (σ j) j, if_pos rfl, Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · rw [matTranspose, Matrix.transpose_apply, hRdef (σ i) i, if_pos rfl]; ring
    · intro l _ hl
      rw [matTranspose, Matrix.transpose_apply, hRdef l i, if_neg hl, zero_mul]
    · intro hnot; exact absurd (Finset.mem_univ (σ i)) hnot
  · intro k _ hk; rw [hRdef k j, if_neg hk, mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ (σ j)) hnot

/-- Precomposition-and-conjugation with a signed permutation `R` is a carrier
endomorphism (mirrors `rotateCoeffField`).  The signed-permutation hypothesis is
what makes local integrability stable: `matVecMul R` is a measure-preserving
homeomorphism. -/
def rotateReg (R : Mat d) (hR : IsSignedPermutationMatrix R) (a : RegCoeffField d) :
    RegCoeffField d where
  toFun := fun x => (matTranspose R) * (a (matVecMul R x)) * R
  entry_measurable := fun i j => by
    obtain ⟨σ, s, _hs, hRdef⟩ := id hR
    have hcollapse : (fun x => (matTranspose R * a (matVecMul R x) * R) i j)
        = fun x => s i * s j * a (matVecMul R x) (σ i) (σ j) :=
      funext fun x => matTranspose_mul_mul_apply hRdef _ i j
    rw [hcollapse]
    exact (((a.entry_measurable (σ i) (σ j)).comp
      (continuous_matVecMul R).measurable).const_mul _)
  entry_locInt := fun i j => by
    obtain ⟨σ, s, _hs, hRdef⟩ := id hR
    have hcollapse : (fun x => (matTranspose R * a (matVecMul R x) * R) i j)
        = fun x => s i * s j * a (matVecMul R x) (σ i) (σ j) :=
      funext fun x => matTranspose_mul_mul_apply hRdef _ i j
    rw [hcollapse]
    have hg : LocallyIntegrable
        (fun x => a (matVecMul R x) (σ i) (σ j)) volume :=
      locallyIntegrable_comp_homeomorph_of_measurePreserving (a.entry_locInt (σ i) (σ j))
        (matVecMulHomeomorph R hR) (measurePreserving_matVecMul R hR)
    show LocallyIntegrable
        (fun x => (s i * s j) • a (matVecMul R x) (σ i) (σ j)) volume
    exact hg.smul (s i * s j)

@[simp] theorem rotateReg_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (a : RegCoeffField d) (x : Vec d) :
    rotateReg R hR a x = (matTranspose R) * (a (matVecMul R x)) * R := rfl

/-- **Signed-permutation rotation is genuinely measurable at the join.** -/
theorem measurable_rotateReg (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotateReg R hR) := by
  obtain ⟨σ, s, _hs, hRdef⟩ := id hR
  refine measurable_of_entryTestR_transport ?_ ?_
  · intro y i j
    have hcollapse : (fun a : RegCoeffField d => rotateReg R hR a y i j)
        = fun a => s i * s j * a (matVecMul R y) (σ i) (σ j) :=
      funext fun a => matTranspose_mul_mul_apply hRdef _ i j
    rw [hcollapse]
    exact ((measurable_apply_entry (matVecMul R y) (σ i) (σ j)).const_mul _)
  · intro i j φ hφ
    refine ⟨s i * s j, σ i, σ j, (fun y => φ (matVecMul (matTranspose R) y)),
      hφ.comp_homeomorph (matVecMulHomeomorph (matTranspose R) hR.transpose), fun a => ?_⟩
    unfold entryTestR
    have hcv := (measurePreserving_matVecMul R hR).integral_comp
      (matVecMulHomeomorph R hR).measurableEmbedding
      (fun y => a y (σ i) (σ j) * φ (matVecMul (matTranspose R) y))
    have hleft : (∫ x, rotateReg R hR a x i j * φ x ∂volume)
        = s i * s j * ∫ x, (a (matVecMul R x) (σ i) (σ j) *
            φ (matVecMul (matTranspose R) (matVecMul R x))) ∂volume := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [rotateReg_apply, matTranspose_mul_mul_apply hRdef]
      have hback : matVecMul (matTranspose R) (matVecMul R x) = x := by
        rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one']
      rw [hback]; ring
    rw [hleft, hcv]

/-! ## Spatial scaling (rescale / dilate) -/

/-- Precomposition with a nonzero spatial scaling `x ↦ r • x` is a carrier
endomorphism.  Local integrability is stable because the scaling is a
homeomorphism whose Jacobian is the finite nonzero factor `|r|^{-d}`; the entry
generators transport with exactly this scalar. -/
def smulReg (r : ℝ) (hr : r ≠ 0) (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => a (r • x)
  entry_measurable := fun i j =>
    (a.entry_measurable i j).comp (measurable_id.const_smul r)
  entry_locInt := fun i j =>
    locallyIntegrable_comp_homeomorph_of_map_smul (a.entry_locInt i j)
      (Homeomorph.smulOfNeZero r hr)
      (c := ENNReal.ofReal |(r ^ Module.finrank ℝ (Vec d))⁻¹|)
      (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]
        exact inv_ne_zero (pow_ne_zero _ hr))
      ENNReal.ofReal_ne_top
      (Measure.map_addHaar_smul volume hr)

@[simp] theorem smulReg_apply (r : ℝ) (hr : r ≠ 0) (a : RegCoeffField d) (x : Vec d) :
    smulReg r hr a x = a (r • x) := rfl

/-- Generator transport for a spatial scaling: the entry test of a scaled field is
the Jacobian factor `|r|^{-d}` times the entry test against the inverse-scaled
probe. -/
theorem entryTestR_smulReg (i j : Fin d) (φ : Vec d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (a : RegCoeffField d) :
    entryTestR i j φ (smulReg r hr a)
      = |(r ^ Module.finrank ℝ (Vec d))⁻¹| * entryTestR i j (fun y => φ (r⁻¹ • y)) a := by
  unfold entryTestR
  have hcv := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => a y i j * φ (r⁻¹ • y)) r
  have hleft : (∫ x, smulReg r hr a x i j * φ x ∂volume)
      = ∫ x, (a (r • x) i j * φ (r⁻¹ • (r • x))) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [smulReg_apply, inv_smul_smul₀ hr]
  rw [hleft, hcv, smul_eq_mul]

/-- **Spatial scaling is genuinely measurable at the join.** -/
theorem measurable_smulReg (r : ℝ) (hr : r ≠ 0) : Measurable (smulReg (d := d) r hr) := by
  refine measurable_of_entryTestR_transport ?_ ?_
  · intro y i j
    have hfun : (fun a : RegCoeffField d => smulReg r hr a y i j)
        = fun a => a (r • y) i j := rfl
    rw [hfun]; exact measurable_apply_entry (r • y) i j
  · intro i j φ hφ
    exact ⟨|(r ^ Module.finrank ℝ (Vec d))⁻¹|, i, j, (fun y => φ (r⁻¹ • y)),
      hφ.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)),
      fun a => entryTestR_smulReg i j φ r hr a⟩

/-- Triadic rescaling by `3^n` (mirrors `rescaleCoeffField`): the rescaled field
is `x ↦ a(3^n • x)`. -/
def rescaleReg (n : ℕ) : RegCoeffField d → RegCoeffField d :=
  smulReg ((3 : ℝ) ^ n) (pow_ne_zero n (by norm_num))

@[simp] theorem rescaleReg_apply (n : ℕ) (a : RegCoeffField d) (x : Vec d) :
    rescaleReg n a x = a (((3 : ℝ) ^ n) • x) := rfl

theorem measurable_rescaleReg (n : ℕ) : Measurable (rescaleReg (d := d) n) :=
  measurable_smulReg _ _

/-- Triadic dilation by `3^k` (mirrors `dilateCoeffField`): the dilated field is
`x ↦ a(3^{-k} • x)`. -/
def dilateReg (k : ℤ) : RegCoeffField d → RegCoeffField d :=
  smulReg (((3 : ℝ) ^ k)⁻¹) (inv_ne_zero (zpow_ne_zero k (by norm_num)))

@[simp] theorem dilateReg_apply (k : ℤ) (a : RegCoeffField d) (x : Vec d) :
    dilateReg k a x = a ((((3 : ℝ) ^ k)⁻¹) • x) := rfl

theorem measurable_dilateReg (k : ℤ) : Measurable (dilateReg (d := d) k) :=
  measurable_smulReg _ _

/-! ## Restriction to a measurable set -/

/-- Restriction of a carrier field to a measurable set `U` (zero outside `U`;
mirrors `restrictCoeffField`).  Both regularity conjuncts are stable: the
restricted entries are indicator products. -/
def restrictReg (U : Set (Vec d)) (hU : MeasurableSet U) (a : RegCoeffField d) :
    RegCoeffField d where
  toFun := Set.indicator U a.toFun
  entry_measurable := fun i j => by
    have hEq : (fun x => Set.indicator U a.toFun x i j)
        = Set.indicator U (fun x => a x i j) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hEq]; exact (a.entry_measurable i j).indicator hU
  entry_locInt := fun i j => by
    have hEq : (fun x => Set.indicator U a.toFun x i j)
        = Set.indicator U (fun x => a x i j) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hEq, locallyIntegrable_iff]
    intro K hK
    exact ((a.entry_locInt i j).integrableOn_isCompact hK).indicator hU

@[simp] theorem restrictReg_apply (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : RegCoeffField d) (x : Vec d) :
    restrictReg U hU a x = Set.indicator U a.toFun x := rfl

theorem restrictReg_apply_entry (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : RegCoeffField d) (x : Vec d) (i j : Fin d) :
    restrictReg U hU a x i j = Set.indicator U (fun x => a x i j) x := by
  by_cases hx : x ∈ U
  · simp [restrictReg, Set.indicator_of_mem hx]
  · simp [restrictReg, Set.indicator_of_notMem hx]

/-- Generator transport for restriction: the entry test of a restricted field is
the entry test against the indicator-masked probe (Jacobian factor `1`). -/
theorem entryTestR_restrictReg (i j : Fin d) (φ : Vec d → ℝ) (U : Set (Vec d))
    (hU : MeasurableSet U) (a : RegCoeffField d) :
    entryTestR i j φ (restrictReg U hU a) = entryTestR i j (Set.indicator U φ) a := by
  unfold entryTestR
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [restrictReg_apply_entry]
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- **Restriction is genuinely measurable at the join.** -/
theorem measurable_restrictReg (U : Set (Vec d)) (hU : MeasurableSet U) :
    Measurable (restrictReg U hU) := by
  refine measurable_of_entryTestR_transport ?_ ?_
  · intro y i j
    by_cases hy : y ∈ U
    · have hfun : (fun a : RegCoeffField d => restrictReg U hU a y i j)
          = fun a => a y i j := by
        funext a; rw [restrictReg_apply_entry, Set.indicator_of_mem hy]
      rw [hfun]; exact measurable_apply_entry y i j
    · have hfun : (fun a : RegCoeffField d => restrictReg U hU a y i j)
          = fun _ => (0 : ℝ) := by
        funext a; rw [restrictReg_apply_entry, Set.indicator_of_notMem hy]
      rw [hfun]; exact measurable_const
  · intro i j φ hφ
    exact ⟨1, i, j, Set.indicator U φ, hφ.indicator hU, fun a => by
      rw [entryTestR_restrictReg]; ring⟩

/-! ## Elliptic truncation

`ellipticTruncateReg Θ a` keeps `a x` where it is `(1, Θ)`-elliptic and replaces
it by the identity elsewhere (mirrors the coarse-graining a.e.-bridge
truncation).  It is a genuine carrier element: on the elliptic branch the entries
are bounded by `Θ` (`abs_apply_le_of_isEllipticMatrix`), off it they are entries
of the identity matrix, so each entry is bounded and measurable, hence locally
integrable.

**Measurability (research item).**  The *pointwise* lane is genuinely measurable
(`measurable_pointwiseSigmaR_ellipticTruncateReg`): the elliptic locus is Borel
(`measurableSet_isEllipticMatrix`), so each coordinate `a ↦ (trunc a) y_{ij}` is a
piecewise-measurable function of the evaluations of `a`.  The *entry-test* lane,
however, is **not** a transported generator: `entryTestR i j φ (trunc a)` is the
integral of a genuinely nonlinear (piecewise) function of the matrix values
`a x`, not a scalar multiple of a linear entry generator of `a`.  On the carrier
the joint map `(a, x) ↦ a x` is not measurable for the pointwise product
σ-algebra (uncountably many coordinates), and no monotone-class approximation is
available for merely locally-integrable `a` (Riemann sums need not converge), so
the entry-test lane cannot be discharged from the P1 generators.  We therefore
land `ellipticTruncateReg` with pointwise-lane measurability only and flag the
join measurability as a design signal for the consumer packets (P5/P7). -/
def ellipticTruncateReg (Θ : ℝ) (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => if IsEllipticMatrix 1 Θ (a x) then a x else 1
  entry_measurable := fun i j => by
    have hay : Measurable (fun x : Vec d => a x) :=
      measurable_matrix_of_entries (fun i' j' => a.entry_measurable i' j')
    have hSet : MeasurableSet {x : Vec d | IsEllipticMatrix 1 Θ (a x)} :=
      hay measurableSet_isEllipticMatrix
    have hEq : (fun x => (if IsEllipticMatrix 1 Θ (a x) then a x else 1) i j)
        = fun x => if x ∈ {x | IsEllipticMatrix 1 Θ (a x)}
            then a x i j else (1 : Mat d) i j := by
      funext x; by_cases hx : IsEllipticMatrix 1 Θ (a x) <;> simp [hx, Set.mem_ofPred_eq]
    rw [hEq]
    exact Measurable.ite hSet (a.entry_measurable i j) measurable_const
  entry_locInt := fun i j => by
    have hay : Measurable (fun x : Vec d => a x) :=
      measurable_matrix_of_entries (fun i' j' => a.entry_measurable i' j')
    have hSet : MeasurableSet {x : Vec d | IsEllipticMatrix 1 Θ (a x)} :=
      hay measurableSet_isEllipticMatrix
    have hEq : (fun x => (if IsEllipticMatrix 1 Θ (a x) then a x else 1) i j)
        = fun x => if x ∈ {x | IsEllipticMatrix 1 Θ (a x)}
            then a x i j else (1 : Mat d) i j := by
      funext x; by_cases hx : IsEllipticMatrix 1 Θ (a x) <;> simp [hx, Set.mem_ofPred_eq]
    have hmeas : Measurable
        (fun x => (if IsEllipticMatrix 1 Θ (a x) then a x else 1) i j) := by
      rw [hEq]; exact Measurable.ite hSet (a.entry_measurable i j) measurable_const
    refine RegCoeffField.locallyIntegrable_of_bounded_measurable hmeas
      (C := max Θ 1) (fun x => ?_)
    by_cases hx : IsEllipticMatrix 1 Θ (a x)
    · rw [if_pos hx]
      exact le_trans (abs_apply_le_of_isEllipticMatrix hx i j) (le_max_left _ _)
    · rw [if_neg hx]
      have h1 : |(1 : Mat d) i j| ≤ 1 := by
        rcases eq_or_ne i j with hij | hij
        · subst hij; rw [Matrix.one_apply_eq]; norm_num
        · rw [Matrix.one_apply_ne hij]; norm_num
      exact le_trans h1 (le_max_right Θ 1)

@[simp] theorem ellipticTruncateReg_apply (Θ : ℝ) (a : RegCoeffField d) (x : Vec d) :
    ellipticTruncateReg Θ a x = if IsEllipticMatrix 1 Θ (a x) then a x else 1 := rfl

/-- **The elliptic truncation is measurable for the pointwise lane.**  See the
declaration docstring: the entry-test lane is a design signal (nonlinear integral
functional, no monotone-class route on the carrier), so join measurability is
deliberately not claimed here. -/
theorem measurable_pointwiseSigmaR_ellipticTruncateReg (Θ : ℝ) :
    @Measurable (RegCoeffField d) (RegCoeffField d) _ (pointwiseSigmaR d)
      (ellipticTruncateReg Θ) := by
  refine measurable_into_pointwiseSigmaR (measurable_toFun_of_entries ?_)
  intro y i j
  have hay : Measurable (fun a : RegCoeffField d => a y) :=
    measurable_matrix_of_entries (fun i' j' => measurable_apply_entry y i' j')
  have hSet : MeasurableSet {a : RegCoeffField d | IsEllipticMatrix 1 Θ (a y)} :=
    hay measurableSet_isEllipticMatrix
  have hEq : (fun a : RegCoeffField d => ellipticTruncateReg Θ a y i j)
      = fun a => if a ∈ {a : RegCoeffField d | IsEllipticMatrix 1 Θ (a y)}
          then a y i j else (1 : Mat d) i j := by
    funext a; by_cases ha : IsEllipticMatrix 1 Θ (a y) <;>
      simp [ellipticTruncateReg_apply, ha, Set.mem_ofPred_eq]
  rw [hEq]
  exact Measurable.ite hSet (measurable_apply_entry y i j) measurable_const

end

end Homogenization
