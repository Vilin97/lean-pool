/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import LeanPool.Monlib4.LinearAlgebra.Ips.MatIps
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Pi
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.DeltaForm

/-!
# LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances`.
-/
-- import LeanPool.Monlib4.LinearAlgebra.Ips.Frob

variable {n : Type*} [Fintype n] [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}

open Matrix

open scoped Functional

theorem Module.Dual.IsFaithfulPosMap.sig_trans_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (sig hφ x).trans (sig hφ y) = sig hφ (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply,
    sig_apply, ← mul_assoc, PosDef.rpow_mul_rpow,
    mul_assoc, PosDef.rpow_mul_rpow, neg_add, add_comm]

open scoped ComplexOrder

omit [Fintype n] [DecidableEq n] in
theorem PosDef.smul {𝕜 : Type*} [RCLike 𝕜]
  {x : Matrix n n 𝕜} (hx : x.PosDef) (α : NNRealˣ) :
  ((((α : NNReal) : ℝ) : 𝕜) • x).PosDef :=
  Matrix.PosDef.smul hx (RCLike.ofReal_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt α)))

theorem posSemidefOne_smul_rpow {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] (α : NNReal) (r : ℝ) :
    (Matrix.PosSemidef.smul (Matrix.PosSemidef.one : PosSemidef (1 : Matrix n n 𝕜))
      (RCLike.ofReal_nonneg.mpr (NNReal.coe_nonneg α)) :
      PosSemidef ((((α : NNReal) : ℝ) : 𝕜) • 1 : Matrix n n 𝕜)).rpow r
        = ((((α : NNReal) : ℝ) ^ r : ℝ) : 𝕜) • 1 :=
by
  rw [PosSemidef.rpow, IsHermitian.rpow, innerAut_eq_iff, _root_.map_smul, innerAut_apply_one]
  symm
  nth_rw 1 [← diagonal_one]
  rw [← diagonal_smul]
  rw [diagonal_eq_diagonal_iff]
  intro i
  simp_rw [Pi.smul_apply, Function.comp_apply, Pi.pow_apply]
  rw [← RCLike.ofReal_one, smul_eq_mul, ← RCLike.ofReal_mul,
    RCLike.ofReal_inj, IsHermitian.eigenvalues_eq',
    smul_mulVec_assoc, one_mulVec, dotProduct_smul,
    ← RCLike.real_smul_eq_coe_smul, RCLike.smul_re,
    Real.mul_rpow (NNReal.coe_nonneg _) _]
  all_goals
    simp_rw [dotProduct, Pi.star_apply, transpose_apply, ← conjTranspose_apply,
      ← mul_apply, IsHermitian.eigenvectorMatrix_conjTranspose_mul, one_apply_eq,
      RCLike.one_re]
  · simp only [mul_one, Real.one_rpow]
  · simp only [zero_le_one]

theorem posDefOne_smul_rpow {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] (α : NNRealˣ) (r : ℝ) :
    (Matrix.PosDef.smul (Matrix.posDefOne : PosDef (1 : Matrix n n 𝕜))
      (RCLike.ofReal_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt α))) :
      PosDef ((((α : NNReal) : ℝ) : 𝕜) • 1 : Matrix n n 𝕜)).rpow r
        = ((((α : NNReal) : ℝ) ^ r : ℝ) : 𝕜) • 1 :=
by
  rw [PosDef.rpow_eq, innerAut_eq_iff, _root_.map_smul, innerAut_apply_one]
  symm
  nth_rw 1 [← diagonal_one]
  rw [← diagonal_smul]
  rw [diagonal_eq_diagonal_iff]
  intro i
  simp_rw [Pi.smul_apply, Function.comp_apply, Pi.pow_apply]
  rw [← RCLike.ofReal_one, smul_eq_mul, ← RCLike.ofReal_mul,
    RCLike.ofReal_inj, IsHermitian.eigenvalues_eq',
    smul_mulVec_assoc, one_mulVec, dotProduct_smul,
    ← RCLike.real_smul_eq_coe_smul, RCLike.smul_re,
    Real.mul_rpow (NNReal.coe_nonneg _) _]
  all_goals
    simp_rw [dotProduct, Pi.star_apply, transpose_apply, ← conjTranspose_apply,
      ← mul_apply, IsHermitian.eigenvectorMatrix_conjTranspose_mul, one_apply_eq,
      RCLike.one_re]
  · simp only [mul_one, Real.one_rpow]
  · simp only [zero_le_one]

theorem Module.Dual.IsFaithfulPosMap.sig_zero [hφ : φ.IsFaithfulPosMap] :
  sig hφ 0 = 1 :=
by
  ext1
  simp only [sig_apply, neg_zero, PosDef.rpow_zero, one_mul, mul_one,
    AlgEquiv.one_apply]

lemma AlgEquiv.apply_eq_id {R M : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] {f : M ≃ₐ[R] M} :
  (∀ (x : M), f x = x) ↔ f = 1 :=
by simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]

theorem Matrix.PosDef.rpow_neg_eq_inv_rpow {𝕜 : Type*} [RCLike 𝕜] {n :
    Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
  hQ.rpow (-r) = (hQ.rpow r)⁻¹ :=
by
  haveI := (PosDef.rpow.isPosDef hQ r).invertible
  letI :=  Matrix.PosDef.eigenvaluesInvertible' hQ
  simp_rw [rpow_eq, innerAut.map_inv]
  haveI : Invertible (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r) : n → 𝕜) :=
  { invOf := (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ (-r)) : n → 𝕜)
    invOf_mul_self := by
      ext
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, Pi.one_apply]
      simp only [← RCLike.ofReal_mul]
      rw [← Real.rpow_add (eigenvalues_pos hQ _), neg_add_cancel, Real.rpow_zero,
        RCLike.ofReal_one]
    mul_invOf_self := by
      ext
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, Pi.one_apply]
      simp only [← RCLike.ofReal_mul]
      rw [← Real.rpow_add (eigenvalues_pos hQ _), add_neg_cancel, Real.rpow_zero,
        RCLike.ofReal_one] }
  rw [Matrix.inv_diagonal']
  congr
  ext i
  simp only [Function.comp_apply, Pi.pow_apply, Pi.inv_apply]
  rw [Real.rpow_neg (le_of_lt (eigenvalues_pos hQ i)), RCLike.ofReal_inv]

theorem _root_.RCLike.pos_toNNReal_units {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) :
  0 < r ↔ ∃ s : NNRealˣ, r = (((s : NNReal) : ℝ) : 𝕜) :=
by
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ => by
    simp only [hs, RCLike.ofReal_pos, NNReal.coe_pos,
      Units.zero_lt]⟩
  use Units.mk0 ⟨RCLike.re r, le_of_lt (RCLike.pos_def.mp h).1⟩
    (ne_of_gt (RCLike.pos_def.mp h).1)
  change r = ((RCLike.re r : ℝ) : 𝕜)
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.pos_def.mp h).2)).symm
theorem _root_.RCLike.nonneg_toNNReal {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) :
  0 ≤ r ↔ ∃ s : NNReal, r = (((s : NNReal) : ℝ) : 𝕜) :=
by
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ => by
    simp only [hs, RCLike.ofReal_nonneg, NNReal.zero_le_coe]⟩
  use Real.toNNReal (RCLike.re r)
  nth_rw 1 [← (RCLike.nonneg_def'.mp h).1]
  simp only [algebraMap.coe_inj]
  rw [Real.toNNReal_of_nonneg ((RCLike.nonneg_def.mp h).1)]
  rfl

theorem _root_.Matrix.smulPosDef_isPosDef_iff {𝕜 : Type*} [RCLike 𝕜] {n :
    Type _} [Finite n]
  [H : Nonempty n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : 𝕜) :
  (r • Q).PosDef ↔ 0 < r :=
by
  classical
  letI : Fintype n := Fintype.ofFinite n
  let j : n := H.some
  let a : n → 𝕜 := fun i => if i = j then 1 else 0
  have ha2 : a ≠ 0 := by
    intro h
    have := congrFun h j
    simp [a] at this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2' := (Matrix.posDef_iff_dotProduct_mulVec.mp h).2
    simp_rw [smul_mulVec_assoc, dotProduct_smul, smul_eq_mul] at h2'
    specialize h2' (x := a) ha2
    obtain ⟨b, hb, hb2⟩ := RCLike.pos_iff_exists_ofReal.mp
      (hQ.dotProduct_mulVec_pos ha2)
    rw [← hb2] at h2'
    rw [mul_comm, RCLike.pos_def, RCLike.re_ofReal_mul, RCLike.im_ofReal_mul,
      mul_pos_iff] at h2'
    simp_rw [hb, true_and, not_lt_of_gt hb, false_and, or_false,
      mul_eq_zero, ne_of_gt hb, false_or] at h2'
    exact RCLike.pos_def.mpr h2'
  · obtain ⟨s, rfl⟩ := (RCLike.pos_toNNReal_units r).mp h
    exact PosDef.smul hQ _

theorem smul_onePosDef_rpow_eq {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {α : 𝕜}
    (h : ((α : 𝕜) • (1 : Matrix n n 𝕜)).PosDef) (r : ℝ) :
    h.rpow r = ((RCLike.re α ^ r : ℝ) : 𝕜) • 1 :=
by
  by_cases H : IsEmpty n
  · simp only [← Matrix.ext_iff]
    simp only [IsEmpty.forall_iff, smul_apply]
  · rw [not_isEmpty_iff] at H
    have := (smulPosDef_isPosDef_iff
      (Matrix.posDefOne : PosDef (1 : Matrix n n 𝕜)) α).mp h
    let p : NNRealˣ := Units.mk0 ⟨RCLike.re α, le_of_lt (RCLike.pos_def.mp this).1⟩
        (ne_of_gt (RCLike.pos_def.mp this).1)
    have : α = (((p : NNReal) : ℝ) : 𝕜) := by
      rw [← RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.pos_def.mp this).2)]
      rfl
    -- rw [this] at h
    rw [PosDef.rpow_cast h _ (by rw [this]), posDefOne_smul_rpow]
    exact rfl

theorem _root_.Matrix.smulPosSemidef_isPosSemidef_iff {𝕜 : Type*} [RCLike 𝕜] {n :
    Type _} [Finite n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) (r : 𝕜) :
  (r • Q).PosSemidef ↔ 0 ≤ r ∨ Q = 0 :=
by
  classical
  letI : Fintype n := Fintype.ofFinite n
  by_cases hr : r = 0
  · simp only [hr, zero_smul, le_refl, true_or, PosSemidef.zero]
  · by_cases hQQ : Q = 0
    · simp_rw [hQQ, smul_zero, or_true, PosSemidef.zero]
    · simp only [hQQ, or_false]
      rw [Matrix.posSemidef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_smul, hQ.1.eq]
      rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]
      simp_rw [smul_mulVec_assoc, dotProduct_smul,
        RCLike.nonneg_def (K := 𝕜), ← RCLike.conj_eq_iff_im,
        starRingEnd_apply, star_smul, smul_eq_mul, RCLike.mul_re,
        (RCLike.nonneg_def.mp (hQ.dotProduct_mulVec_nonneg _)), mul_zero, sub_zero,
        mul_nonneg_iff, RCLike.nonneg_def.mp (hQ.dotProduct_mulVec_nonneg _), and_true,
        ← star_dotProduct, star_mulVec, hQ.1.eq, ← dotProduct_mulVec]
      simp only [hQQ, or_false]
      constructor
      · rintro ⟨h, h2⟩
        rw [← Matrix.IsHermitian.eigenvalues_eq_zero_iff hQ.1] at hQQ
        simp only [funext_iff, Pi.zero_apply, not_forall] at hQQ
        obtain ⟨i, hi⟩ := hQQ
        specialize h2 (hQ.1.eigenvectorMatrixᵀ i)
        rw [← IsHermitian.eigenvalues_eq'] at h2
        nth_rw 3 [le_iff_eq_or_lt] at h2
        simp only [hi, not_lt_of_ge (hQ.eigenvalues_nonneg _),
          and_false, or_false, h, and_true] at h2
        exact ⟨h2, h⟩
      · simp only [RCLike.star_def, mul_eq_mul_right_iff, and_imp]
        intro h hi
        refine ⟨hi, ?_⟩
        simp only [h, true_or, true_and, hi, implies_true]

theorem smul_onePosSemidef_rpow_eq {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {α : 𝕜}
    (h : ((α : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef) (r : ℝ) :
    h.rpow r = ((RCLike.re α ^ r : ℝ) : 𝕜) • 1 :=
by
  by_cases H : IsEmpty n
  · simp only [← Matrix.ext_iff]
    simp only [IsEmpty.forall_iff, smul_apply]
  · rw [not_isEmpty_iff] at H
    have := (smulPosSemidef_isPosSemidef_iff
      (Matrix.PosSemidef.one : PosSemidef (1 : Matrix n n 𝕜)) α).mp h
    simp only [one_ne_zero, or_false] at this
    obtain ⟨s, rfl⟩ := (RCLike.nonneg_toNNReal α).mp this
    rw [posSemidefOne_smul_rpow]
    simp only [RCLike.ofReal_re]

theorem _root_.Matrix.smulOneInv {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {s : NNRealˣ} :
    ((((s : NNReal) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))⁻¹
      = (((s⁻¹ : NNReal) : ℝ) : 𝕜) • 1 :=
by
  simp only [NNReal.coe_inv, RCLike.ofReal_inv]
  letI : Invertible (((s : NNReal) : ℝ) : 𝕜) := by
    use (((s⁻¹ : NNReal) : ℝ) : 𝕜) <;> aesop
  rw [Matrix.inv_smul]
  · simp only [invOf_eq_inv, inv_one]
  · simp only [det_one, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]

theorem _root_.Matrix.PosDef.commutes_iff_rpow_commutes {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝˣ) :
  (∀ x, Commute x (hQ.rpow (r : ℝ))) ↔ ∀ x, Commute x Q :=
by
  by_cases H : IsEmpty n
  · simp only [commute_iff_eq, ← Matrix.ext_iff]
    simp only [IsEmpty.forall_iff, implies_true]
  · rw [not_isEmpty_iff] at H
    simp_rw [commutes_with_all_iff]
    constructor
    · rintro ⟨α, hα⟩
      have hα' := hα
      obtain ⟨s, rfl⟩ := (RCLike.pos_toNNReal_units α).mp ((smulPosDef_isPosDef_iff
        (Matrix.posDefOne : PosDef (1 : Matrix n n 𝕜)) α).mp
        (by rw [← hα']; exact PosDef.rpow.isPosDef _ _))
      rw [PosDef.rpow_eq, innerAut_eq_iff, _root_.map_smul,
        innerAut_apply_one, smul_one_eq_diagonal, diagonal_eq_diagonal_iff] at hα
      simp_rw [Function.comp_apply, Pi.pow_apply] at hα
      simp only [algebraMap.coe_inj] at hα
      use ((RCLike.re (((s : NNReal) : ℝ) : 𝕜) ^ ((1 / r) : ℝ) : ℝ) : 𝕜)
      have : ∀ i, hQ.1.eigenvalues i = ((s : NNReal) : ℝ) ^ (1/r : ℝ) :=
      by
        intro i
        rw [← hα i, one_div, Real.rpow_rpow_inv (le_of_lt (PosDef.eigenvalues_pos hQ _))
          (Units.ne_zero r)]
      rw [IsHermitian.spectral_theorem'' hQ.1]
      rw [innerAut_eq_iff, _root_.map_smul, innerAut_apply_one, smul_one_eq_diagonal,
        diagonal_eq_diagonal_iff]
      simp only [Function.comp_apply, RCLike.ofReal_re, one_div, algebraMap.coe_inj]
      simp only [this, one_div, implies_true]
    · rintro ⟨α, hα⟩
      use ((RCLike.re α ^ (r : ℝ) : ℝ) : 𝕜)
      rw [PosDef.rpow_cast hQ _ hα, smul_onePosDef_rpow_eq]

theorem Module.Dual.IsPosMap.isTracial_iff
  {n : Type _} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsPosMap) :
    φ.IsTracial ↔ ∃ α : ℂ, φ.matrix = α • 1 :=
by
  have := isTracial_pos_map_iff_of_matrix φ
  simp only [hφ, true_and] at this
  rw [this]
  constructor
  · rintro ⟨α, h⟩
    exact ⟨((α : ℝ) : ℂ), h⟩
  · rintro ⟨α, h⟩
    by_cases H : (1 : Matrix n n ℂ) = 0
    · use 0
      simp only [NNReal.coe_zero, Complex.ofReal_zero, h, H, smul_zero]
    · use Real.toNNReal (RCLike.re α)
      rw [h]
      congr
      have := smulPosSemidef_isPosSemidef_iff
        (Matrix.PosSemidef.one : PosSemidef (1 : Matrix n n ℂ)) α
      simp_rw [H, or_false, ← h, (isPosMap_iff_of_matrix _).mp hφ, true_iff] at this
      simp_rw [Real.toNNReal_of_nonneg (RCLike.nonneg_def.mp this).1]
      simp only [NNReal.coe_mk]
      exact (RCLike.nonneg_def'.mp this).1.symm

/-- `σ_k = 1` iff either `k = 0` or `φ` is tracial -/
theorem sig_eq_id_iff [hφ : φ.IsFaithfulPosMap] (k : ℝ) :
  sig hφ k = 1 ↔ k = 0 ∨ φ.IsTracial :=
by
  by_cases hk : k = 0
  · simp_rw [hk, true_or, iff_true, Module.Dual.IsFaithfulPosMap.sig_zero]
  · by_cases H : IsEmpty n
    · simp only [Module.Dual.IsTracial, Module.Dual.apply,
        trace_iff, AlgEquiv.ext_iff, sig_apply,
        ← Matrix.ext_iff]
      simp only [AlgEquiv.one_apply, IsEmpty.forall_iff, implies_true, Finset.univ_eq_empty,
        Finset.sum_empty, or_true]
    · rw [not_isEmpty_iff] at H
      let nk : ℝˣ := Units.mk0 k hk
      have nk2 : k = (nk : ℝ) := rfl
      simp_rw [hk, false_or, nk2]
      rw [(Module.Dual.IsPosMap.isTracial_iff hφ.1)]
      refine ⟨fun h => ?_, ?_⟩
      on_goal 2 =>
        rintro ⟨α, hα⟩
        ext1
        rw [sig_apply]
        simp_rw [PosDef.rpow_cast hφ.matrixIsPosDef _ hα]
        simp_rw [smul_onePosDef_rpow_eq]
        have := (smulPosDef_isPosDef_iff
          (Matrix.posDefOne : PosDef (1 : Matrix n n ℂ)) α).mp
          (by rw [← hα]; exact hφ.matrixIsPosDef)
        simp_rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
          smul_smul, ← RCLike.ofReal_mul]
        rw [← Real.rpow_add (RCLike.pos_def.mp this).1, neg_add_cancel,
          Real.rpow_zero]
        simp_rw [algebraMap.coe_one, one_smul, AlgEquiv.one_apply]
      by_cases Hy : ∃ α : ℂ, hφ.matrixIsPosDef.rpow k = α • 1
      · rw [← commutes_with_all_iff,
          ← Matrix.PosDef.commutes_iff_rpow_commutes hφ.matrixIsPosDef nk, commutes_with_all_iff]
        exact Hy
      · have this1 := calc (∀ x, Commute x (hφ.matrixIsPosDef.rpow k))
          ↔ (∀ x, x * hφ.matrixIsPosDef.rpow k = hφ.matrixIsPosDef.rpow k * x) := Iff.rfl
          _ ↔ (∀ x, hφ.matrixIsPosDef.rpow (-k) * x * hφ.matrixIsPosDef.rpow k = x) := by
            haveI := (PosDef.rpow.isPosDef hφ.matrixIsPosDef k).invertible
            simp_rw [PosDef.rpow_neg_eq_inv_rpow,
              ← Matrix.inv_mul_eq_iff_eq_mul_of_invertible, mul_assoc]
          _ ↔ (∀ x, sig hφ k x = x) := Iff.rfl
          _ ↔ sig hφ k = 1 := AlgEquiv.apply_eq_id
        rw [← commutes_with_all_iff, this1] at Hy
        contradiction

theorem Module.Dual.pi_isTracial_iff {k : Type*} [Fintype k]
  {s : k → Type*}
  [∀ i, Fintype (s i)]
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} :
    (Module.Dual.pi φ).IsTracial ↔ ∀ i, (φ i).IsTracial :=
by
  classical
  constructor
  · intro h i x y
    specialize h (includeBlock x) (includeBlock y)
    simp [Module.Dual.pi_apply, includeBlock_hMul_includeBlock] at h
    simpa only [← Module.Dual.pi_apply, Module.Dual.pi.apply_single_block'] using h
  · intro h x y
    simp [h _ _]

/-- The modular star-algebra structure on matrices induced by a faithful positive functional. -/
@[reducible]
noncomputable def Matrix.isStarAlgebra [hφ : φ.IsFaithfulPosMap] :
    starAlgebra (Matrix n n ℂ) where
  modAut := sig hφ
  modAut_trans := Module.Dual.IsFaithfulPosMap.sig_trans_sig
  modAut_star r x := by
    simp_rw [sig_apply, star_mul, star_eq_conjTranspose,
      neg_neg, (Matrix.PosDef.rpow.isPosDef _ _).1.eq,
      mul_assoc]

@[reducible, instance]
noncomputable def Module.Dual.IsFaithfulPosMap.innerProductAlgebra [hφ : φ.IsFaithfulPosMap] :
    @InnerProductAlgebra (Matrix n n ℂ) (Matrix.isStarAlgebra (φ := φ)) := by
  letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
  exact withMatrixInner[φ] {
  -- norm_smul_le _ _ := by rw [← norm_smul]
  norm_smul_le := norm_smul_le
  norm_sq_eq_inner := norm_sq_eq_re_inner (𝕜 := ℂ)
  dist_eq x y := by
    rw [dist_eq_norm']
    congr 1
    abel
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left }

@[reducible, instance]
noncomputable
def Module.Dual.IsFaithfulPosMap.quantumSet [hφ : φ.IsFaithfulPosMap] :
    @QuantumSet (Matrix n n ℂ) (Matrix.isStarAlgebra (φ := φ)) := by
  letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
  exact withMatrixInner[φ] {
  -- modAut r := hφ.sig r
  -- modAut_trans r s := sig_trans_sig _ _
  -- modAut_zero := by
    -- ext1
    -- exact Module.Dual.IsFaithfulPosMap.sig_zero _ _
  -- modAut_star r x := sig_conjTranspose _ _ _
  modAut_isSymmetric r x y := by
    simp_rw [← AlgEquiv.toLinearMap_apply, modAut, AlgEquiv.toLinearMap_apply, sig_apply,
      mul_assoc]
    rw [inner_left_hMul, inner_right_conj]
    simp_rw [(PosDef.rpow.isPosDef _ _).1.eq]
    nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
    nth_rw 1 [← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
    simp_rw [PosDef.rpow_mul_rpow, mul_assoc]
    ring_nf
  k := 0
  -- modAut_isCoalgHom r := Module.Dual.IsFaithfulPosMap.sig_isCoalgHom _ _
  inner_star_left x y z := by simp_rw [neg_zero,
    inner_left_hMul, star_eq_conjTranspose,
    modAut, sig_apply, neg_zero, PosDef.rpow_zero, one_mul, mul_one]
  inner_conj_left x y z := by
    simp_rw [neg_zero, zero_sub,
      Module.Dual.IsFaithfulPosMap.inner_right_conj,
      modAut, sig_apply, neg_neg,
      PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
    rfl
  n := n × n
  nIsFintype := by infer_instance
  nIsDecidableEq := by infer_instance
  onb := hφ.orthonormalBasis }

/-- Elaborate a term using the matrix quantum-set structure induced by a faithful
positive functional. -/
syntax "withMatrixQuantum[" term "] " term : term
macro_rules
  | `(withMatrixQuantum[$φ] $p) =>
      `(letI := Matrix.isStarAlgebra (φ := $φ)
        letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ)
        letI := Module.Dual.NormedAddCommGroup $φ
        letI := (Module.Dual.NormedAddCommGroup
          $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        letI := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup
        letI := Module.Dual.InnerProductSpace (φ := $φ)
        $p)

  -- map_one' := rfl
  -- mapMul' x y := _root_.map_mul _ _ _
  -- map_zero' := _root_.map_zero _
  -- map_add' := _root_.map_add _
  -- commutes' := Algebra.commutes
  -- smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

section MatrixPsi

open scoped TensorProduct

variable {p : Type*} [Fintype p] [DecidableEq p]
  {ψ : Module.Dual ℂ (Matrix p p ℂ)}

/-- Matrix-specialized `Psi` equivalence for faithful positive functionals. -/
noncomputable def Module.Dual.IsFaithfulPosMap.psi
    (hφ : φ.IsFaithfulPosMap) [hψ : ψ.IsFaithfulPosMap] (t r : ℝ) :
    (Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) ≃ₗ[ℂ]
      (Matrix p p ℂ ⊗[ℂ] (Matrix n n ℂ)ᵐᵒᵖ) := by
  letI : φ.IsFaithfulPosMap := hφ
  letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
  letI : QuantumSet (Matrix n n ℂ) :=
    Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI : starAlgebra (Matrix p p ℂ) := Matrix.isStarAlgebra (φ := ψ)
  letI : QuantumSet (Matrix p p ℂ) :=
    Module.Dual.IsFaithfulPosMap.quantumSet (φ := ψ)
  exact QuantumSet.Psi (A := Matrix n n ℂ) (B := Matrix p p ℂ) t r

end MatrixPsi

variable {k : Type*} [Fintype k] [DecidableEq k] {s : k → Type*} [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] {ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

-- theorem Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
--     (x y : ℝ) :
--     (Module.Dual.pi.IsFaithfulPosMap.sig hψ x).trans (Module.Dual.pi.IsFaithfulPosMap.sig hψ y) =
--       Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y) :=
-- by rw [Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig, add_comm]

-- theorem Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
--     (r : ℝ) (x y : PiMat ℂ k s) :
--   ⟪sig hψ r x, y⟫_ℂ = ⟪x, sig hψ r y⟫_ℂ :=
-- by rw [← AlgEquiv.toLinearMap_apply, ← sig_adjoint, LinearMap.adjoint_inner_left,
  -- AlgEquiv.toLinearMap_apply]

private noncomputable def piSig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s where
  toFun x i := sig (hψ i) z (x i)
  invFun x i := (sig (hψ i) z).symm (x i)
  left_inv x := by
    funext i
    exact (sig (hψ i) z).left_inv (x i)
  right_inv x := by
    funext i
    exact (sig (hψ i) z).right_inv (x i)
  map_mul' x y := by
    funext i
    exact map_mul (sig (hψ i) z) (x i) (y i)
  map_add' x y := by
    funext i
    exact map_add (sig (hψ i) z) (x i) (y i)
  commutes' r := by
    funext i
    exact AlgEquiv.commutes (sig (hψ i) z) r

omit [Fintype k] [DecidableEq k] in
@[simp]
private theorem piSig_apply (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) (x : PiMat ℂ k s) (i : k) :
    piSig hψ z x i = sig (hψ i) z (x i) :=
  rfl

omit [Fintype k] [DecidableEq k] in
private theorem piSig_trans_sig [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : ℝ) :
    (piSig hψ x).trans (piSig hψ y) = piSig hψ (x + y) := by
  ext a i j l
  change sig (hψ i) y (sig (hψ i) x (a i)) j l =
    sig (hψ i) (x + y) (a i) j l
  rw [← AlgEquiv.trans_apply, Module.Dual.IsFaithfulPosMap.sig_trans_sig]

omit [Fintype k] [DecidableEq k] in
private theorem piSig_star (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) (x : PiMat ℂ k s) :
    star (piSig hψ z x) = piSig hψ (-z) (star x) := by
  funext i
  change star (sig (hψ i) z (x i)) = sig (hψ i) (-z) (star (x i))
  simp [sig_apply, star_eq_conjTranspose, neg_neg,
    (Matrix.PosDef.rpow.isPosDef (hψ i).matrixIsPosDef z).1.eq,
    (Matrix.PosDef.rpow.isPosDef (hψ i).matrixIsPosDef (-z)).1.eq,
    mul_assoc]

/-- The modular star-algebra structure on a finite product of matrix blocks. -/
@[reducible]
noncomputable def PiMat.isStarAlgebra [_hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    starAlgebra (PiMat ℂ k s) where
  modAut := piSig _hψ
  modAut_trans := piSig_trans_sig
  modAut_star := piSig_star _hψ


-- attribute [-instance] Pi.module.Dual.isNormedAddCommGroupOfRing
@[reducible, instance]
noncomputable
def Module.Dual.pi.IsFaithfulPosMap.innerProductAlgebra
  [∀ i, (ψ i).IsFaithfulPosMap] :
    @InnerProductAlgebra (PiMat ℂ k s) (PiMat.isStarAlgebra (ψ := ψ)) :=
by
  letI : starAlgebra (PiMat ℂ k s) := PiMat.isStarAlgebra (ψ := ψ)
  letI : _root_.NormedAddCommGroup (PiMat ℂ k s) :=
    Module.Dual.PiNormedAddCommGroup (φ := ψ)
  letI : _root_.SeminormedAddCommGroup (PiMat ℂ k s) :=
    (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (PiMat ℂ k s) :=
    Module.Dual.pi.InnerProductSpace (φ := ψ)
  letI : ∀ i, _root_.NormedAddCommGroup (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.NormedAddCommGroup (ψ i)
  letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.InnerProductSpace (φ := ψ i)
  exact
    { toNorm := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toNorm
      toMetricSpace := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toMetricSpace
      inner := fun x y => @inner ℂ (PiMat ℂ k s) _ x y
      norm_smul_le := by
        intro c x
        letI : InnerProductSpace.Core ℂ (PiMat ℂ k s) :=
          Module.Dual.PiInnerProductCore (φ := ψ)
        letI : NormedSpace ℂ (PiMat ℂ k s) :=
          InnerProductSpace.Core.toNormedSpace
        exact NormedSpace.norm_smul_le c x
      norm_sq_eq_inner := by
        intro x
        exact norm_sq_eq_re_inner (𝕜 := ℂ) x
      dist_eq := by
        intro x y
        simpa [sub_eq_add_neg, add_comm] using
          (Module.Dual.PiNormedAddCommGroup (φ := ψ)).dist_eq x y
      conj_symm := by
        intro x y
        exact inner_conj_symm x y
      add_left := by
        intro x y z
        exact inner_add_left x y z
      smul_left := by
        intro x y r
        exact inner_smul_left x y r }
-- letI : _root_.NormedAddCommGroup (PiMat ℂ k s) := by infer_instance
-- letI : _root_.NormedSpace ℂ (PiMat ℂ k s) := by infer_instance
-- letI : _root_.InnerProductSpace ℂ (PiMat ℂ k s) := by infer_instance
-- { norm_smul_le := fun r x => by
--     rw [← norm_smul_le]
    -- exact @norm_smul_le ℂ (PiMat ℂ k s) _ _ _ _ r x
    -- rw [norm_eq_sqrt_inner (𝕜 := ℂ), inner_smul_left, inner_smul_right]
    -- simp only [RCLike.re_to_complex, Complex.norm_eq_abs, ← mul_assoc,
    --   Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    -- rw [Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq, norm_eq_sqrt_inner (𝕜 := ℂ)]
    -- rfl
    -- simp only [apply_nonneg]
  -- norm_sq_eq_inner := norm_sq_eq_inner (𝕜 := ℂ)
  -- conj_symm := inner_conj_symm
  -- add_left := inner_add_left
  -- smul_left := inner_smul_left }

-- set_option synthInstance.checkSynthOrder false in
@[reducible, instance]
noncomputable instance Module.Dual.pi.IsFaithfulPosMap.quantumSet
  [hψ : Π i, (ψ i).IsFaithfulPosMap] :
    @QuantumSet (PiMat ℂ k s) (PiMat.isStarAlgebra (ψ := ψ)) := by
  letI : starAlgebra (PiMat ℂ k s) := PiMat.isStarAlgebra (ψ := ψ)
  exact withPiInner[ψ]
  { k := 0
    modAut_isSymmetric r x y := by
      rw [inner_pi_eq_sum, inner_pi_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      letI : starAlgebra (Matrix (s i) (s i) ℂ) := Matrix.isStarAlgebra (φ := ψ i)
      letI : QuantumSet (Matrix (s i) (s i) ℂ) :=
        Module.Dual.IsFaithfulPosMap.quantumSet (φ := ψ i)
      exact QuantumSet.modAut_isSymmetric (A := Matrix (s i) (s i) ℂ) r (x i) (y i)
    inner_star_left x y z := by
      rw [inner_pi_eq_sum, inner_pi_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      change inner ℂ ((x i) * (y i)) (z i) =
        inner ℂ (y i) ((piSig hψ (-0) (star x)) i * z i)
      simp only [neg_zero, piSig_apply, Pi.star_apply, sig_apply,
        PosDef.rpow_zero, one_mul, mul_one, star_eq_conjTranspose]
      exact Module.Dual.IsFaithfulPosMap.inner_left_hMul (φ := ψ i) (x i) (y i) (z i)
    inner_conj_left x y z := by
      rw [inner_pi_eq_sum, inner_pi_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      change inner ℂ ((x i) * (y i)) (z i) =
        inner ℂ (x i) (z i * (piSig hψ (-0 - 1) (star y)) i)
      simp only [neg_zero, zero_sub, piSig_apply, Pi.star_apply, sig_apply,
        neg_neg, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self,
        star_eq_conjTranspose]
      exact Module.Dual.IsFaithfulPosMap.inner_right_conj (hψ i) (x i) (y i) (z i)
    n := Σ i, (s i) × (s i)
    nIsFintype := by infer_instance
    nIsDecidableEq := by infer_instance
    onb := Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ }

/-- Elaborate a term using the product quantum-set structure induced by faithful
positive functionals on matrix blocks. -/
syntax "withPiQuantum[" term "] " term : term
macro_rules
  | `(withPiQuantum[$ψ] $p) =>
      `(letI := PiMat.isStarAlgebra (ψ := $ψ)
        letI := Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := $ψ)
        letI := Module.Dual.PiNormedAddCommGroup (φ := $ψ)
        letI := (Module.Dual.PiNormedAddCommGroup (φ :=
          $ψ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        letI := (Module.Dual.PiNormedAddCommGroup (φ := $ψ)).toSeminormedAddCommGroup
        letI := Module.Dual.pi.InnerProductSpace (φ := $ψ)
        $p)

  -- modAut r := (Module.Dual.pi.IsFaithfulPosMap.sig hψ r : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s)
  -- modAut_trans r s := Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig hψ _ _
  -- modAut_zero := Module.Dual.pi.IsFaithfulPosMap.sig_zero'
  -- modAut_star r x := Module.Dual.pi.IsFaithfulPosMap.sig_star _ _ _
  -- modAut_isSymmetric r x y :=
  --   by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric hψ _ _ _
  -- -- modAut_isCoalgHom r :=
  -- --   by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom hψ r
  -- k := 0
  -- inner_star_left x y z := by
  --   simp_rw [neg_zero, sig_zero, inner_left_hMul]
  -- inner_conj_left x y z := by
  --   simp_rw [neg_zero, zero_sub, Module.Dual.pi.IsFaithfulPosMap.inner_right_conj']
  -- commutes' a f := by ext1; simp only [RingHom.coe_mk, MonoidHom.coe_mk, Pi.mul_apply]
  -- smul_def' a f := by ext1; simp only [Pi.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk,
  --   Pi.mul_apply]

open scoped TensorProduct BigOperators Kronecker Matrix

theorem LinearMap.mul'_comp_mul'_adjoint_of_delta_form {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] :
    letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
    letI : QuantumSet (Matrix n n ℂ) :=
      Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ Coalgebra.comul = φ.matrix⁻¹.trace • 1 :=
by
  letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
  letI : QuantumSet (Matrix n n ℂ) :=
    Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) :=
    Module.Dual.InnerProductSpace (φ := φ)
  change LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ
    LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) = φ.matrix⁻¹.trace • 1
  rw [Qam.Nontracial.mul_comp_mul_adjoint]

theorem LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form [∀ i, Nontrivial (s i)] {δ : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    letI : starAlgebra (PiMat ℂ k s) := PiMat.isStarAlgebra (ψ := φ)
    letI : QuantumSet (PiMat ℂ k s) :=
      Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := φ)
    letI : ∀ i, starAlgebra (Matrix (s i) (s i) ℂ) :=
      fun i => Matrix.isStarAlgebra (φ := φ i)
    letI : ∀ i, QuantumSet (Matrix (s i) (s i) ℂ) :=
      fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i)
    letI : ∀ i, Coalgebra ℂ (Matrix (s i) (s i) ℂ) :=
      fun _ => Coalgebra.ofFiniteDimensionalHilbertAlgebra
    letI : CoalgebraStruct ℂ (PiMat ℂ k s) := inferInstance
    LinearMap.mul' ℂ (PiMat ℂ k s) ∘ₗ Coalgebra.comul = δ • 1 :=
by
  letI : starAlgebra (PiMat ℂ k s) := PiMat.isStarAlgebra (ψ := φ)
  letI : QuantumSet (PiMat ℂ k s) :=
    Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := φ)
  letI : ∀ i, starAlgebra (Matrix (s i) (s i) ℂ) :=
    fun i => Matrix.isStarAlgebra (φ := φ i)
  letI : ∀ i, QuantumSet (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i)
  letI : _root_.NormedAddCommGroup (PiMat ℂ k s) :=
    Module.Dual.PiNormedAddCommGroup (φ := φ)
  letI : _root_.SeminormedAddCommGroup (PiMat ℂ k s) :=
    (Module.Dual.PiNormedAddCommGroup (φ := φ)).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (PiMat ℂ k s) :=
    Module.Dual.pi.InnerProductSpace (φ := φ)
  letI : ∀ i, _root_.NormedAddCommGroup (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.NormedAddCommGroup (φ i)
  letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.InnerProductSpace (φ := φ i)
  letI : ∀ i, Coalgebra ℂ (Matrix (s i) (s i) ℂ) :=
    fun _ => Coalgebra.ofFiniteDimensionalHilbertAlgebra
  letI : CoalgebraStruct ℂ (PiMat ℂ k s) := inferInstance
  ext i a j r c
  rw [LinearMap.comp_assoc, Pi.comul_comp_single]
  simp_rw [LinearMap.comp_apply]
  change
    (LinearMap.mul' ℂ (PiMat ℂ k s))
        ((TensorProduct.map
            (Matrix.includeBlock : Matrix (s i) (s i) ℂ →ₗ[ℂ] PiMat ℂ k s)
            (Matrix.includeBlock : Matrix (s i) (s i) ℂ →ₗ[ℂ] PiMat ℂ k s))
          (Coalgebra.comul a)) j r c =
      (δ • Matrix.includeBlock a : PiMat ℂ k s) j r c
  rw [LinearMap.pi_mul'_apply_includeBlock]
  rw [show LinearMap.mul' ℂ (Matrix (s i) (s i) ℂ) (Coalgebra.comul a) = δ • a by
    rw [← LinearMap.comp_apply, LinearMap.mul'_comp_mul'_adjoint_of_delta_form (φ := φ i),
      hφ₂ i]
    rfl]
  simp [Matrix.includeBlock_apply, Pi.smul_apply]

theorem Qam.Nontracial.delta_pos [Nonempty n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] : 0 < φ.matrix⁻¹.trace :=
by
  exact Matrix.PosDef.trace_pos (Matrix.PosDef.inv hφ.matrixIsPosDef)

omit [Fintype k] [DecidableEq k] in
theorem Pi.Qam.Nontracial.delta_ne_zero [Nonempty k] [∀ i, Nontrivial (s i)] {δ : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) : 0 < δ :=
by
  let j : k := Classical.arbitrary k
  rw [← hφ₂ j]
  exact Qam.Nontracial.delta_pos

/-- The delta-form quantum-set structure for a single matrix algebra. -/
@[reducible]
noncomputable
def Matrix.quantumSetDeltaForm [Nonempty n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] := by
  letI : starAlgebra (Matrix n n ℂ) := Matrix.isStarAlgebra (φ := φ)
  letI : QuantumSet (Matrix n n ℂ) :=
    Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) :=
    Module.Dual.InnerProductSpace (φ := φ)
  letI : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  exact show QuantumSetDeltaForm (Matrix n n ℂ) from
    { delta := φ.matrix⁻¹.trace
      delta_pos := Qam.Nontracial.delta_pos
      mul_comp_comul_eq := by
        exact LinearMap.mul'_comp_mul'_adjoint_of_delta_form (φ := φ) }

/-- The delta-form quantum-set structure for a finite product of matrix algebras. -/
@[reducible]
noncomputable def PiMat.quantumSetDeltaForm [Nonempty k] [∀ i, Nontrivial (s i)] {d : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] [hφ₂ : Fact (∀ i, (φ i).matrix⁻¹.trace = d)] := by
  letI : starAlgebra (PiMat ℂ k s) := PiMat.isStarAlgebra (ψ := φ)
  letI : QuantumSet (PiMat ℂ k s) :=
    Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := φ)
  letI : _root_.NormedAddCommGroup (PiMat ℂ k s) :=
    Module.Dual.PiNormedAddCommGroup (φ := φ)
  letI : _root_.SeminormedAddCommGroup (PiMat ℂ k s) :=
    (Module.Dual.PiNormedAddCommGroup (φ := φ)).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (PiMat ℂ k s) :=
    Module.Dual.pi.InnerProductSpace (φ := φ)
  letI : Coalgebra ℂ (PiMat ℂ k s) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  exact show QuantumSetDeltaForm (PiMat ℂ k s) from
    { delta := d
      delta_pos := Pi.Qam.Nontracial.delta_ne_zero hφ₂.out
      mul_comp_comul_eq := by
        change LinearMap.mul' ℂ (PiMat ℂ k s) ∘ₗ
          LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s)) = d • 1
        exact (LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff
          (k := k) (s := s) (ψ := φ) d).mpr hφ₂.out }
