/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Defs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingEnergyReduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomEqScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeqPred

/-! # Matrix algebra of `e.left.to.show`

Source: `enhance.tex` 8271–8470.  The partition of unity turns the identity parts of
`F = ∑_k ξ_{m,k} (I + ∇Χ_{m,k}) ∘ X⁻¹` into `I`, and the orthogonality `e.alt.orth` of adjacent
odd shear gradients (in two independent points) kills the cross terms of `FᵗF`
(`e.Emkappa.formula`).  Also the elementary quadratic-form bounds and the scalar value
`⟨⟨J_m^{κ_m}⟩⟩ = κ_{m-1} I`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Abstract Gram expansion: if the cross products vanish for distinct indices of `S`, then
`(1 + ∑ ξ_k A_k)ᵀ (1 + ∑ ξ_k A_k) = 1 + ∑ (ξ_k (A_kᵀ + A_k) + ξ_k² A_kᵀ A_k)`. -/
theorem gram_expansion_of_cross_eq_zero {ι : Type*} (S : Finset ι) (ξ : ι → ℝ)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (hcross : ∀ k ∈ S, ∀ l ∈ S, k ≠ l →
      (A k).transpose * A l = 0) :
    (1 + ∑ k ∈ S, ξ k • A k).transpose * (1 + ∑ k ∈ S, ξ k • A k) =
      1 + ∑ k ∈ S, (ξ k • ((A k).transpose + A k) + ξ k ^ 2 • ((A k).transpose * A k)) := by
  classical
  have hdiag : (∑ k ∈ S, ∑ l ∈ S, (ξ k • A k).transpose * (ξ l • A l)) =
      ∑ k ∈ S, ξ k ^ 2 • ((A k).transpose * A k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_eq_single k]
    · rw [Matrix.transpose_smul, smul_mul_smul_comm, pow_two]
    · intro l hl hkl
      rw [Matrix.transpose_smul, smul_mul_smul_comm, hcross k hk l hl (Ne.symm hkl), smul_zero]
    · intro hnot
      exact (hnot hk).elim
  have hT : (1 + ∑ k ∈ S, ξ k • A k).transpose = 1 + ∑ k ∈ S, (ξ k • A k).transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_one]
  have hmid : (∑ k ∈ S, (ξ k • A k).transpose) * (∑ l ∈ S, ξ l • A l) =
      ∑ k ∈ S, ∑ l ∈ S, (ξ k • A k).transpose * (ξ l • A l) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
  rw [hT, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hmid, hdiag]
  simp only [Finset.sum_add_distrib, Matrix.transpose_smul, smul_add]
  abel

/-- `F` as a finite sum: the partition of unity `∑_{k odd} ξ_{m,k} = 1` turns the `I` parts
into `I`. -/
theorem leadingMatrix_eq_finset (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ)
    (x : Vec 2) :
    leadingMatrix I hΦ m κm t x =
      1 + ∑ k ∈ (xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m k.1 t •
          gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) := by
  classical
  set S := (xiMK_odd_support_finite I hm t).toFinset with hS
  have hzero : ∀ k ∉ S, I.xiMK m k.1 t •
      (1 + gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)) = 0 := by
    intro k hk
    have : I.xiMK m k.1 t = 0 := by
      by_contra hne
      exact hk (by simpa [hS] using hne)
    simp [this]
  unfold leadingMatrix
  rw [tsum_eq_sum (L := SummationFilter.unconditional {k : ℤ // Odd k}) (s := S) hzero]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, xiMK_odd_partition_finset I hm t, one_smul]

/-- Source 8402–8435: `FᵗF` with the cross terms killed (`e.alt.orth` for `|k-k'| = 2`, disjoint
supports for `|k-k'| ≥ 4`). -/
theorem leadingMatrix_transpose_mul (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ)
    (x : Vec 2) :
    (leadingMatrix I hΦ m κm t x).transpose * leadingMatrix I hΦ m κm t x =
      1 + ∑ k ∈ (xiMK_odd_support_finite I hm t).toFinset,
        (I.xiMK m k.1 t •
            ((gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose +
              gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)) +
          I.xiMK m k.1 t ^ 2 •
            ((gradMatrix (I.chiMK κm m k.1 t)
                (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose *
              gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x))) := by
  classical
  rw [leadingMatrix_eq_finset I hΦ hm κm t x]
  apply gram_expansion_of_cross_eq_zero
  intro k hk l hl hkl
  have hne : k.1 ≠ l.1 := fun h => hkl (Subtype.ext h)
  have hk' : I.xiMK m k.1 t ≠ 0 := by simpa using hk
  have hl' : I.xiMK m l.1 t ≠ 0 := by simpa using hl
  exact chiMK_grad_cross_eq_zero_of_odd_overlap I κm k.2 l.2 hne t hk' hl' _ _

theorem vecNormSq_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2) :
    vecNormSq (A.mulVec v) = vecDot v ((A.transpose * A).mulVec v) := by
  simp only [vecNormSq, vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

theorem Matrix.abs_mul_mul_le {a B x y : ℝ} (ha : |a| ≤ B) :
    |a * x * y| ≤ B * ((x ^ 2 + y ^ 2) / 2) := by
  have hxy : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  calc |a * x * y| = |a| * |x * y| := by rw [mul_assoc, abs_mul]
    _ ≤ B * ((x ^ 2 + y ^ 2) / 2) :=
      mul_le_mul ha hxy (abs_nonneg _) ((abs_nonneg a).trans ha)

theorem abs_vecDot_mulVec_le {A : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hA : ∀ i j, |A i j| ≤ B)
    (v : Vec 2) : |vecDot v (A.mulVec v)| ≤ 2 * B * vecNormSq v := by
  have hexp : vecDot v (A.mulVec v) =
      A 0 0 * v 0 * v 0 + A 0 1 * v 1 * v 0 + A 1 0 * v 0 * v 1 + A 1 1 * v 1 * v 1 := by
    simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hnorm : vecNormSq v = v 0 ^ 2 + v 1 ^ 2 := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    ring
  have h00 := Matrix.abs_mul_mul_le (x := v 0) (y := v 0) (hA 0 0)
  have h01 := Matrix.abs_mul_mul_le (x := v 1) (y := v 0) (hA 0 1)
  have h10 := Matrix.abs_mul_mul_le (x := v 0) (y := v 1) (hA 1 0)
  have h11 := Matrix.abs_mul_mul_le (x := v 1) (y := v 1) (hA 1 1)
  rw [hexp, hnorm]
  calc _ ≤ |A 0 0 * v 0 * v 0| + |A 0 1 * v 1 * v 0| + |A 1 0 * v 0 * v 1| +
        |A 1 1 * v 1 * v 1| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- The positivity of the sequence `κ_m` from a positive terminal value. -/
theorem kappaSeq_pos {κ : ℝ} (hκ : 0 < κ) (M m : ℕ) : 0 < I.kappaSeq κ M m :=
  kappaAt_pos I hκ m (M - m)

/-- Fourth term of `e.ergodic.break.up` is zero: `⟨⟨J_m^{κ_m}⟩⟩ = KBar_m^{κ_m} = κ_{m-1} I`
(source 8395; the printed "κ_m I_2" is a typo for κ_{m-1} I_2). -/
theorem timeAvgMat_flux_kappaSeq (κ : ℝ) {M m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    (hκm : 0 < I.kappaSeq κ M m) :
    timeAvgMat (fun t => I.flux (I.kappaSeq κ M m) m t) =
      I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := (I.Khom_eq_scalar (I.kappaSeq κ M m) hκm m hm).1
  rw [I.kappaSeq_pred κ hm hmM]
  exact h

end AVenhance.Infra.Section5.LeftToShow

end
